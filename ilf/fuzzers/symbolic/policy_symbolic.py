import abc
import math
import json
from collections import defaultdict
from collections import OrderedDict
import random
from ...execution import Tx
import z3
from ..policy_base import PolicyBase
from ...ethereum import SolType
from ...ethereum import Method
from ...symbolic.symbolic import constraints
from ...symbolic.symbolic import svm_utils
from ..random import policy_random
import logging
from copy import copy, deepcopy

class PolicySymbolic(PolicyBase):

    def __init__(self, execution, contract_manager, account_manager):
        super().__init__(execution, contract_manager, account_manager)

        self.policy_random = policy_random.PolicyRandom(execution, contract_manager, account_manager)
        self.last_picked_pc_traces = []

        self.tx_count = 0

    def select_tx(self, obs):
        self.tx_count += 1
        svm = obs.svm
        visited = set()
        gstates = []

        def collect_all_nodes(wstate):
            for trace, children in getattr(wstate, "trace_to_children", {}).items():
                for child in children:
                    trace_key = tuple(child.get_full_trace())
                    if trace_key not in visited:
                        visited.add(trace_key)
                        gstates.append(child)
                        collect_all_nodes(child)

        for address in svm.fuzz_addresses:
            roots = svm.sym_call_address(address, svm.root_wstate)
            for root in roots:
                if hasattr(root, 'wstate'):
                    gstates.append(root)
                    collect_all_nodes(root.wstate)

        logging.info(f'found {len(gstates)} states')

        sorted_gstates = sorted(
            gstates,
            key=lambda g: (-self.evaluate_pc_set_gain(obs.sym_stat, set(g.pc_trace)), -len(g.pc_trace))
        )

        for gstate in sorted_gstates:
            tx = self.fuzz_node(gstate, obs, svm)
            if tx:
                return tx

        return None

    def fuzz_node(self, gstate, obs, svm):
        solver = self.get_state_solver(gstate)
        if solver is None:
            return None

        model = solver.model()
        sender_value = model.eval(gstate.environment.sender).as_long()
        sender = svm.possible_caller_addresses.index(sender_value)
        amount = model.eval(gstate.environment.callvalue).as_long()
        method_name = gstate.wstate.trace.split('.')[1].split('(')[0]
        address = hex(gstate.environment.active_address)

        if address not in obs.contract_manager.address_to_contract:
            return None

        contract = obs.contract_manager.address_to_contract[address]
        timestamp = self._select_timestamp(obs)

        if method_name == 'fallback':
            if Method.FALLBACK not in contract.abi.methods_by_name:
                return None
            method_name = Method.FALLBACK
            logging.info(f'Fuzzing node - executing fallback at {hex(sender_value)}')
            return Tx(self, contract.name, address, method_name, bytes(), [], amount, sender, timestamp, True)

        method = contract.abi.methods_by_name[method_name]
        inputs = method.inputs
        arguments = []
        random_args = self.policy_random._select_arguments(contract, method, sender, obs)

        for i, arg in enumerate(inputs):
            calldata = svm.sym_bv_generator.get_sym_bitvec(constraints.ConstraintType.CALLDATA,
                                                           gstate.wstate.gen,
                                                           index=4 + i * 32)
            calldata_eval = model.eval(calldata)
            if svm_utils.is_bv_concrete(calldata_eval):
                arg_eval = calldata_eval.as_long()
            else:
                arg_eval = random_args[i]
            arguments.append(arg_eval)

        logging.info(f'Fuzzing node - executing {method.name} at {hex(sender_value)}')

        return Tx(self, contract.name, address, method.name, bytes(), arguments, amount, sender, timestamp, True)

    @staticmethod
    def add_pc_set_to_stat(stat, pc_set):
        for contract_name, pc in pc_set:
            stat.covered_pcs_dict[contract_name].add(pc)

    @staticmethod
    def evaluate_pc_set_gain(stat, pc_set):
        covered_pcs_dict = deepcopy(stat.covered_pcs_dict)
        for contract_name, pc in pc_set:
            covered_pcs_dict[contract_name].add(pc)
        total_coverage = 0
        stat_total_coverage = 0
        for contract_name, coverages in covered_pcs_dict.items():
            total_coverage += len(coverages)
        for contract_name, coverages in stat.covered_pcs_dict.items():
            stat_total_coverage += len(coverages)
        return total_coverage - stat_total_coverage

    @staticmethod
    def get_state_solver(gstate):
        solver = z3.Solver()
        solver.set('timeout',  3 * 60 * 1000)
        solver.add(gstate.wstate.constraints)
        res = solver.check()
        if res == z3.unknown:
            logging.info(f'{gstate.wstate.trace} gstate check timeout')
        return solver if res == z3.sat else None
