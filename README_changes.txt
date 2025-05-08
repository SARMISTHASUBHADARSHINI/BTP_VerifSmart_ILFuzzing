Modified version of the Interpreted Language Fuzzer (ILF) tailored for symbolic-assisted fuzzing of Solidity smart contracts. It combines symbolic execution and fuzzing to explore smart contract behaviors more deeply and efficiently.
Fuzzes at every Node of the symbolic tree.
All changes—like symbolic enhancements, new fuzzing policies, and execution logic
Structure:
----------
- svm.py                --> Refactored symbolic execution engine.
- policy_symbolic.py    --> Updated fuzzing policy using get_all_nodes().
- policy_sym_plus.py    --> New hybrid fuzzing strategy with fuzz_node() function. Fuzzes at each node and it checks if the path is feasible using Z3, and if it is, it creates a valid transaction for it.
                        --> and select_new_tx() function. Earlier, it would just pick the best transaction. But now, it gives priority to our fuzz_node() approach.
