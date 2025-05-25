
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
from ...symbolic.symbolic.world_state import WorldStateStatus
from ..random import policy_random
import logging
from copy import copy, deepcopy


class PolicySymPlus(PolicyBase):

    def __init__(self, execution, contract_manager, account_manager, K):
        super().__init__(execution, contract_manager, account_manager)

        self.policy_random = policy_random.PolicyRandom(execution, contract_manager, account_manager)
        self.last_picked_pc_traces = []

        self.tx_count = 0
        self.idd_to_gstates = {}
        self.all_gstates = []
        #added---- VerifSmart---------------------------------------------------
        self.K = K
        #added---- VerifSmart---------------------------------------------------

    def select_tx(self, obs):
        tx, idd = self.select_new_tx(obs)
        if tx is not None:
            return tx
        svm = obs.svm
        tx, idd = self.get_best_tx(obs, svm, self.all_gstates)
        if tx is not None:
            logging.info('jump to {}'.format(idd))
            self.jump_state(idd)
            svm.change_root(idd)
            return tx
        logging.info(f'no gain found globally')
        return None

    def select_new_tx(self, obs):
        self.tx_count += 1
        svm = obs.svm
        gstates = []
        for address in svm.fuzz_addresses:
            root_gstates = svm.sym_call_address(address, svm.root_wstate)
            for g in root_gstates:
                # print(g)
                gstates.append(g)
                # print(svm.executor.execute_gstate(g))
                gstates.extend(svm.executor.execute_gstate(g))  # Fuzz every reachable state
        
        for gstate in gstates:
            gstate.wstate_idd = obs.active_idd

        # Deduplicate based on pc_trace to avoid redundant fuzzing
        unique_traces = set()
        unique_gstates = []
        for g in gstates:
            trace_key = tuple(g.pc_trace)
            if trace_key not in unique_traces:
                unique_traces.add(trace_key)
                unique_gstates.append(g)

        logging.info(f'[PolicySymPlus] Collected {len(unique_gstates)} unique gstates from symbolic tree')

        self.all_gstates.extend(unique_gstates)
        self.idd_to_gstates[obs.active_idd] = unique_gstates

        # Sort by estimated gain and depth to prioritize deeper unexplored paths
        sorted_gstates = sorted(
            unique_gstates,
            key=lambda g: (-self.evaluate_pc_set_gain(obs.sym_stat, set(g.pc_trace)), -len(g.pc_trace))
        )

        # Sort only by depth to prioritize deeper unexplored paths
        # sorted_gstates = sorted(
        #     unique_gstates,
        #     key=lambda g: -len(g.pc_trace)
        # )

        # if self.K != -1:
        #     k = self.K  #bounded
        #     tx_old = None
        #     iid_old = None
        #     for gstate in sorted_gstates:
        #         k= k-1
        #         tx, iid = self.fuzz_node(gstate, obs, svm)
        #         if k >=0:
        #             if tx:
        #                 print("K IS THIS", k)
        #                 print(gstate)
        #                 print(" ")
        #                 return tx, iid
        #             else:
        #                 print(k)
        #                 print("CALLLLLLLLLLLLLLLLL OLD")
        #                 print(tx_old == None)
        #                 return tx_old, iid_old
        #         if tx:
        #             tx_old = tx 
        #             iid_old = iid
        #     return tx_old, iid_old
        # else:
        #     for gstate in sorted_gstates:
        #         tx, iid = self.fuzz_node(gstate, obs, svm)
        #         if tx:
        #             print(gstate)
        #             return tx, iid

        if self.K != -1:
            k = self.K  # bounded
            tx_best = None
            iid_best = None

            # reversed_gstates = sorted_gstates[::-1][:k]  # Take the last K elements in reverse (right to left)
            updated_gstates = sorted_gstates[:k]  # Take the last K elements

            index = 0

            while index < len(updated_gstates):
                gstate = reversed_gstates[index]
                tx, iid = self.fuzz_node(gstate, obs, svm)

                if tx:
                    # Update the best tx found so far (leftmost valid one in reverse traversal)
                    print("indexxxxxxxxxxxxxxxx: ", index)
                    tx_best = tx
                    iid_best = iid

                index += 1

            if tx_best:
                print("[Reverse-K] Leftmost valid transaction found:")
                print(tx_best)
                return tx_best, iid_best

            print("[Reverse-K] No valid transaction found in top K")
            return None, None



        else:
            p = 0
            for gstate in sorted_gstates:
                p= p + 1
                tx, iid = self.fuzz_node(gstate, obs, svm)
                if tx:
                    print("index p is", p)
                    print(gstate)
                    return tx, iid

        return None, None

    #added---- VerifSmart---------------------------------------------------
    def fuzz_node(self, gstate, obs, svm):
        solver = self.get_state_solver(gstate)
        if solver is None:
            return None, None

        model = solver.model()
        sender_value = model.eval(gstate.environment.sender).as_long()
        sender = svm.possible_caller_addresses.index(sender_value)
        amount = model.eval(gstate.environment.callvalue).as_long()
        method_name = gstate.wstate.trace.split('.')[1].split('(')[0]
        address = hex(gstate.environment.active_address)

        if address not in obs.contract_manager.address_to_contract:
            return None, None

        contract = obs.contract_manager.address_to_contract[address]
        timestamp = self._select_timestamp(obs)

        if method_name == 'fallback':
            if Method.FALLBACK not in contract.abi.methods_by_name:
                return None, None
            method_name = Method.FALLBACK
            logging.info(f'Fuzzing node - executing fallback at {hex(sender_value)}')
            self.add_pc_set_to_stat(obs.sym_stat, set(gstate.pc_trace))
            return Tx(self, contract.name, address, method_name, bytes(), [], amount, sender, timestamp, True)

        method = contract.abi.methods_by_name[method_name]
        inputs = method.inputs
        arguments = []
        random_args = self.policy_random._select_arguments(contract, method, sender, obs)

        for i, arg in enumerate(inputs):
            calldata = svm.sym_bv_generator.get_sym_bitvec(constraints.ConstraintType.CALLDATA, gstate.wstate.gen, index=4 + i * 32)
            calldata_eval = model.eval(calldata)
            if svm_utils.is_bv_concrete(calldata_eval):
                arg_eval = calldata_eval.as_long()
            else:
                arg_eval = random_args[i]
            arguments.append(arg_eval)

        logging.info(f'Fuzzing node - executing {method.name} at {hex(sender_value)}')
        self.add_pc_set_to_stat(obs.sym_stat, set(gstate.pc_trace))
        return Tx(self, contract.name, address, method.name, bytes(), arguments, amount, sender, timestamp, True), gstate.wstate_idd
    #added---- VerifSmart---------------------------------------------------

    def get_best_tx(self, obs, svm, gstates):
        gain_to_gstates = defaultdict(list)
        for gstate in gstates:
            pc_set = set(gstate.pc_trace)
            gain = self.evaluate_pc_set_gain(obs.sym_stat, pc_set)
            gain_to_gstates[gain].append(gstate)

        for gain in sorted(gain_to_gstates.keys(), key=lambda k: -k):
            if gain == 0:
                logging.info('No feasible gain')
                return None, None

            for gstate in sorted(gain_to_gstates[gain], key=lambda g: (-self.evaluate_pc_set_gain(obs.sym_stat, set(g.pc_trace)), -len(g.pc_trace))):
                if len(self.last_picked_pc_traces) and self.last_picked_pc_traces[-1] == gstate.pc_trace:
                    continue
                solver = self.get_state_solver(gstate)
                if solver is None:
                    continue
                model = solver.model()
                sender_value = model.eval(gstate.environment.sender).as_long()
                sender = svm.possible_caller_addresses.index(sender_value)
                amount = model.eval(gstate.environment.callvalue).as_long()
                method_name = gstate.wstate.trace.split('.')[1].split('(')[0]
                address = hex(gstate.environment.active_address)
                if address not in obs.contract_manager.address_to_contract:
                    raise Exception('unknown address')
                contract = obs.contract_manager.address_to_contract[address]
                timestamp = self._select_timestamp(obs)
                if method_name == 'fallback':
                    if Method.FALLBACK not in contract.abi.methods_by_name:
                        continue
                    method_name = Method.FALLBACK
                    self.add_pc_set_to_stat(obs.sym_stat, set(gstate.pc_trace))
                    logging.info(f'sending tx {method_name} {hex(sender_value)} {gain}')
                    return Tx(self, contract.name, address, method_name, bytes(), [], amount, sender, timestamp, True), gstate.wstate_idd

                method = contract.abi.methods_by_name[method_name]
                timestamp = model.eval(gstate.environment.timestamp).as_long()
                arguments = []
                random_args = self.policy_random._select_arguments(contract, method, sender, obs)

                for i, arg in enumerate(method.inputs):
                    calldata = svm.sym_bv_generator.get_sym_bitvec(constraints.ConstraintType.CALLDATA, gstate.wstate.gen, index=4+i*32)
                    calldata_eval = model.eval(calldata)
                    arg_eval = calldata_eval.as_long() if svm_utils.is_bv_concrete(calldata_eval) else random_args[i]
                    arguments.append(arg_eval)

                self.add_pc_set_to_stat(obs.sym_stat, set(gstate.pc_trace))
                return Tx(self, contract.name, address, method.name, bytes(), arguments, amount, sender, timestamp, True), gstate.wstate_idd

        return None, None

    @staticmethod
    def add_pc_set_to_stat(stat, pc_set):
        for contract_name, pc in pc_set:
            stat.covered_pcs_dict[contract_name].add(pc)

    @staticmethod
    def evaluate_pc_set_gain(stat, pc_set):
        covered_pcs_dict = deepcopy(stat.covered_pcs_dict)
        for contract_name, pc in pc_set:
            covered_pcs_dict[contract_name].add(pc)
        total_coverage = sum(len(c) for c in covered_pcs_dict.values())
        stat_total = sum(len(c) for c in stat.covered_pcs_dict.values())
        return total_coverage - stat_total

    @staticmethod
    def get_state_solver(gstate):
        if gstate.wstate.status == WorldStateStatus.INFEASIBLE:
            return None
        solver = z3.Solver()
        solver.set('timeout', 3 * 60 * 1000)
        solver.add(gstate.wstate.constraints)
        res = solver.check()
        if res == z3.unknown:
            logging.info(f'{gstate.wstate.trace} gstate check timeout')
        gstate.wstate.status = WorldStateStatus.FEASIBLE if res == z3.sat else WorldStateStatus.INFEASIBLE
        return solver if res == z3.sat else None

    @staticmethod
    def get_state_solver(gstate):
        if not hasattr(gstate, 'wstate') or not hasattr(gstate.wstate, 'constraints'):
            logging.warning(f'[get_state_solver] Invalid GlobalState without constraints: {gstate}')
            return None

        status = getattr(gstate.wstate, 'status', None)
        if status == WorldStateStatus.INFEASIBLE:
            return None

        solver = z3.Solver()
        solver.set('timeout', 3 * 60 * 1000)
        solver.add(gstate.wstate.constraints)
        res = solver.check()

        if res == z3.unknown:
            logging.info(f'{getattr(gstate.wstate, "trace", "unknown_trace")} gstate check timeout')

        gstate.wstate.status = WorldStateStatus.FEASIBLE if res == z3.sat else WorldStateStatus.INFEASIBLE
        return solver if res == z3.sat else None
