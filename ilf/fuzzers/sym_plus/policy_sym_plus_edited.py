import abc
import math
import json
import time
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

    def __init__(self, execution, contract_manager, account_manager):
        super().__init__(execution, contract_manager, account_manager)

        self.policy_random = policy_random.PolicyRandom(execution, contract_manager, account_manager)
        self.last_picked_pc_traces = []
        self.last_picked_methods = []  # Track recently picked methods
        self.transaction_history = []  # Track transaction history
        
        self.tx_count = 0
        self.idd_to_gstates = {}
        self.all_gstates = []
        
        # Parameters for coverage improvement
        self.max_history_length = 10  # Remember last N transactions
        self.diversity_weight = 0.3   # Weight for diversity in method selection
        self.retry_timeout_factor = 2 # Gradually increase solver timeout
        self.max_retry_attempts = 3   # Max retries for solver
        self.exploration_rate = 0.15  # Chance to pick random transaction

    def select_tx(self, obs):
        # Occasionally explore randomly to escape local maximum
        if random.random() < self.exploration_rate:
            logging.info("Exploring randomly to increase coverage")
            return self.policy_random.select_tx(obs)

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
            
        logging.info(f'no gain found globally, trying deeper symbolic analysis')
        # Try deeper analysis when no gain is found
        return self.perform_deeper_analysis(obs)

    def perform_deeper_analysis(self, obs):
        """Attempt deeper analysis when standard approach fails to find new coverage"""
        svm = obs.svm
        
        # Try addresses that haven't been explored much
        address_coverage = defaultdict(int)
        for gstate in self.all_gstates:
            addr = hex(gstate.environment.active_address)
            address_coverage[addr] += 1
        
        # Find least explored addresses
        sorted_addresses = sorted(address_coverage.items(), key=lambda x: x[1])
        if sorted_addresses:
            least_explored = sorted_addresses[0][0]
            if least_explored in obs.contract_manager.address_to_contract:
                contract = obs.contract_manager.address_to_contract[least_explored]
                sender = random.randint(0, len(svm.possible_caller_addresses) - 1)
                method = self._select_least_used_method(contract)
                
                if method:
                    logging.info(f"Trying least explored method {method.name} on {contract.name}")
                    arguments = self.policy_random._select_arguments(contract, method, sender, obs)
                    amount = random.randint(0, 100)
                    timestamp = self._select_timestamp(obs)
                    
                    return Tx(self, contract.name, least_explored, method.name, 
                              bytes(), arguments, amount, sender, timestamp, True)
        
        # Fall back to random as last resort
        logging.info(f"Falling back to random selection")
        return self.policy_random.select_tx(obs)

    def _select_least_used_method(self, contract):
        """Select method that has been used least frequently"""
        method_counts = defaultdict(int)
        
        for tx_info in self.transaction_history:
            if tx_info.get('contract_name') == contract.name:
                method_counts[tx_info.get('method_name')] += 1
        
        # Filter methods that exist in the contract
        available_methods = []
        for method_name in contract.abi.methods_by_name:
            if method_name not in method_counts:
                return contract.abi.methods_by_name[method_name]  # Return unused method immediately
            available_methods.append((method_name, method_counts[method_name]))
        
        if available_methods:
            # Sort by usage count
            available_methods.sort(key=lambda x: x[1])
            return contract.abi.methods_by_name[available_methods[0][0]]
            
        # Fallback to random selection if all have been used
        method_names = list(contract.abi.methods_by_name.keys())
        if method_names:
            return contract.abi.methods_by_name[random.choice(method_names)]
        return None

    def select_new_tx(self, obs):
        self.tx_count += 1
        svm = obs.svm
        gstates = []
        
        # Get symbolic states for each address
        for address in svm.fuzz_addresses:
            gstates.extend(svm.sym_call_address(address, svm.root_wstate))
            
        for gstate in gstates:
            gstate.wstate_idd = obs.active_idd
            
        self.all_gstates.extend(gstates)
        self.idd_to_gstates[obs.active_idd] = gstates
        logging.info(f'found {len(gstates)} states')
        
        return self.get_best_tx(obs, svm, gstates)

    def get_best_tx(self, obs, svm, gstates):
        gain_to_gstates = defaultdict(list)
        diversified_gain = {}
        
        # Calculate coverage gain for each state
        for gstate in gstates:
            pc_set = set(gstate.pc_trace)
            gain = self.evaluate_pc_set_gain(obs.sym_stat, pc_set)
            
            # Store the state by its gain
            gain_to_gstates[gain].append(gstate)
            
            # Calculate diversified gain (combining coverage gain with method diversity)
            method_name = gstate.wstate.trace.split('.')[1].split('(')[0]
            address = hex(gstate.environment.active_address)
            
            # Diversity bonus: Add bonus if this method wasn't used recently
            diversity_bonus = 0
            if method_name not in self.last_picked_methods:
                diversity_bonus = len(pc_set) * self.diversity_weight
                
            diversified_gain[gstate] = gain + diversity_bonus
        
        # Sort by diversified gain (combined regular gain + diversity bonus)
        sorted_gstates = sorted(diversified_gain.items(), key=lambda x: -x[1])
        
        # Try each state in order of diversified gain
        for gstate, gain in sorted_gstates:
            if gain == 0:
                logging.info('No feasible gain')
                return None, None
                
            # Skip if this is the exact same path we just took
            if len(self.last_picked_pc_traces) and self.last_picked_pc_traces[-1] == gstate.pc_trace:
                continue
                
            # Try with progressively higher timeouts
            for attempt in range(self.max_retry_attempts):
                timeout = (self.retry_timeout_factor ** attempt) * 60 * 1000
                solver = self.get_state_solver(gstate, timeout)
                
                if solver is not None:
                    return self._create_tx_from_solver(obs, svm, gstate, solver, gain)
        
        return None, None

    def _create_tx_from_solver(self, obs, svm, gstate, solver, gain):
        """Create transaction from solver model"""
        model = solver.model()
        sender_value = model.eval(gstate.environment.sender).as_long()
        sender = svm.possible_caller_addresses.index(sender_value)
        amount = model.eval(gstate.environment.callvalue).as_long()
        method_name = gstate.wstate.trace.split('.')[1].split('(')[0]
        address = hex(gstate.environment.active_address)
        
        if address not in obs.contract_manager.address_to_contract:
            raise Exception('unknown address')
            
        contract = obs.contract_manager.address_to_contract[address]
        timestamp = model.eval(gstate.environment.timestamp).as_long()
        
        # Track method usage for diversity
        if len(self.last_picked_methods) >= self.max_history_length:
            self.last_picked_methods.pop(0)
        self.last_picked_methods.append(method_name)
        
        # Track PC traces to avoid immediate repetition
        if len(self.last_picked_pc_traces) >= self.max_history_length:
            self.last_picked_pc_traces.pop(0)
        self.last_picked_pc_traces.append(gstate.pc_trace)
        
        # Handle fallback method
        if method_name == 'fallback':
            if Method.FALLBACK not in contract.abi.methods_by_name:
                return None, None
                
            method_name = Method.FALLBACK
            self.add_pc_set_to_stat(obs.sym_stat, set(gstate.pc_trace))
            logging.info(f'sending tx {method_name} {hex(sender_value)} {gain}')
            
            tx = Tx(self, contract.name, address, method_name, bytes(), [], amount, sender, timestamp, True)
            
            # Track transaction for diversity
            self._track_transaction(contract.name, method_name)
            
            return tx, gstate.wstate_idd
        
        # Handle regular methods
        if method_name not in contract.abi.methods_by_name:
            return None, None
            
        method = contract.abi.methods_by_name[method_name]
        inputs = method.inputs
        arguments = []
        random_args = self.policy_random._select_arguments(contract, method, sender, obs)
        
        logging.info(f'sending tx {method.name} {hex(sender_value)} {gain}')
        arguments = self._extract_arguments(model, gstate, svm, inputs, random_args, sender_value)
        
        self.add_pc_set_to_stat(obs.sym_stat, set(gstate.pc_trace))
        tx = Tx(self, contract.name, address, method.name, bytes(), arguments, amount, sender, timestamp, True)
        
        # Track transaction for diversity
        self._track_transaction(contract.name, method.name)
        
        return tx, gstate.wstate_idd

    def _extract_arguments(self, model, gstate, svm, inputs, random_args, sender_value):
        """Extract arguments from model with smart fallback to random values"""
        arguments = []
        
        for i, arg in enumerate(inputs):
            using_random = False
            t = arg.evm_type.t
            arg_eval = None
            
            calldata = svm.sym_bv_generator.get_sym_bitvec(
                constraints.ConstraintType.CALLDATA,
                gstate.wstate.gen,
                index=4+i*32
            )
            
            calldata_eval = model.eval(calldata)
            
            if svm_utils.is_bv_concrete(calldata_eval):
                arg_eval = calldata_eval.as_long()
            else:
                logging.debug(f'Using random variable for {arg.name}')
                using_random = True
                arg_eval = random_args[i]
                
            if not using_random:
                if t == SolType.AddressTy:
                    # Try to use a non-sender address when possible
                    try:
                        solver = z3.Solver()
                        solver.set('timeout', 10000)  # 10 seconds timeout
                        caller_constraint = z3.Or([calldata == p for p in svm.possible_caller_addresses if p != sender_value])
                        solver.add(gstate.wstate.constraints)
                        solver.add(caller_constraint)
                        
                        if solver.check() == z3.sat:
                            calldata_eval = solver.model().eval(calldata)
                            arg_eval = calldata_eval.as_long()
                    except:
                        pass
                    arg_eval = hex(arg_eval % (2**160))
                elif t == SolType.FixedBytesTy:
                    arg_eval = arg_eval % (8 * arg.evm_type.size)
                    arg_bytes = arg_eval.to_bytes(arg.evm_type.size, 'big')
                    arg_eval = [int(b) for b in arg_bytes]
                elif t == SolType.ArrayTy:
                    arg_eval = random_args[i]
                elif t == SolType.BoolTy:
                    # Try both true and false values with equal probability for better coverage
                    arg_eval = bool(arg_eval % 2)
                elif t == SolType.StringTy:
                    size = random.randint(max(1, int(math.log(max(2, arg_eval)) / math.log(8))), 40)
                    try:
                        arg_eval = arg_eval.to_bytes(size, 'big')
                        arg_eval = bytearray([c % 128 for c in arg_eval]).decode('ascii')
                    except:
                        arg_eval = random_args[i]
            
            # Fall back to random if types don't match
            if not isinstance(arg_eval, type(random_args[i])):
                arg_eval = random_args[i]
                
            arguments.append(arg_eval)
            
        return arguments

    def _track_transaction(self, contract_name, method_name):
        """Track transaction for diversity calculations"""
        tx_info = {
            'timestamp': time.time(),
            'contract_name': contract_name,
            'method_name': method_name
        }
        
        self.transaction_history.append(tx_info)
        if len(self.transaction_history) > self.max_history_length:
            self.transaction_history.pop(0)

    @staticmethod
    def add_pc_set_to_stat(stat, pc_set):
        for contract_name, pc in pc_set:
            stat.covered_pcs_dict[contract_name].add(pc)

    @staticmethod
    def evaluate_pc_set_gain(stat, pc_set):
        """Evaluate potential coverage gain with weight on new blocks"""
        covered_pcs_dict = deepcopy(stat.covered_pcs_dict)
        
        # Count new PCs that would be covered
        new_pcs = 0
        for contract_name, pc in pc_set:
            if pc not in covered_pcs_dict[contract_name]:
                new_pcs += 1
                covered_pcs_dict[contract_name].add(pc)
                
        # Calculate total coverage after adding new PCs
        total_coverage = 0
        stat_total_coverage = 0
        
        for contract_name, coverages in covered_pcs_dict.items():
            total_coverage += len(coverages)
            
        for contract_name, coverages in stat.covered_pcs_dict.items():
            stat_total_coverage += len(coverages)
            
        # Return gain with emphasis on discovering new blocks
        return (total_coverage - stat_total_coverage) + (new_pcs * 0.5)

    @staticmethod
    def get_state_solver(gstate, timeout=3*60*1000):
        """Get solver for state with configurable timeout"""
        if gstate.wstate.status == WorldStateStatus.INFEASIBLE:
            return None
            
        solver = z3.Solver()
        solver.set('timeout', timeout)
        solver.add(gstate.wstate.constraints)
        res = solver.check()
        
        if res == z3.unknown: 
            logging.info(f'{gstate.wstate.trace} gstate check timeout')
            
        gstate.wstate.status = WorldStateStatus.FEASIBLE if res == z3.sat else WorldStateStatus.INFEASIBLE
        return solver if res == z3.sat else None