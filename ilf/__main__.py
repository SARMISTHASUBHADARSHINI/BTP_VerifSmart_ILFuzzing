import sys
import numpy
import torch
import random
import argparse
import logging

from .fuzzers import Environment
from .fuzzers.random import PolicyRandom, ObsRandom
from .fuzzers.imitation import PolicyImitation, ObsImitation
from .fuzzers.symbolic import PolicySymbolic, ObsSymbolic
from .fuzzers.sym_plus import PolicySymPlus, ObsSymPlus
from .fuzzers.mix import PolicyMix, ObsMix
from .execution import Execution
from .common import set_logging

global runs
global bugs

def get_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--execution', dest='execution', type=str, default='./execution.so')
    parser.add_argument('--proj', dest='proj', type=str, default=None)
    parser.add_argument('--contract', dest='contract', type=str, default=None)
    #added---- VerifSmart---------------------------------------------------
    parser.add_argument('--runs', dest='runs', type=int, default=1)
    parser.add_argument('--depth', dest='depth', type=int, default=-1)
    #added---- VerifSmart---------------------------------------------------


    parser.add_argument('--limit', dest='limit', type=int, default=100)
    parser.add_argument('--fuzzer', dest='fuzzer', choices=['random', 'imitation', 'symbolic', 'sym_plus', 'mix'], default='random')

    parser.add_argument('--model', dest='model', type=str, default=None)

    parser.add_argument('--seed', dest='seed', type=int, default=1)
    parser.add_argument('--log_to_file', dest='log_to_file', type=str, default=None)
    parser.add_argument('-v', dest='v', type=int, default=1, metavar='LOG_LEVEL',
                        help='Log levels: 0 - NOTSET, 1 - INFO, 2 - DEBUG, 3 - ERROR')

    parser.add_argument('--train_dir', dest='train_dir', type=str, default=None)
    parser.add_argument('--dataset_dump_path', dest='dataset_dump_path', type=str, default=None)

    args = parser.parse_args()
    print(args)
    return args


def init(args):
    random.seed(args.seed)
    set_logging(args.v, args.log_to_file)
    torch.manual_seed(args.seed)
    numpy.random.seed(args.seed)
    sys.setrecursionlimit(8000)


def main(args):
    
    init(args)
    

    LOG = logging.getLogger(__name__)
    LOG.info('fuzzing start')

    if args.proj is not None:
        execution = Execution(args.execution)
        backend_loggers = execution.set_backend(args.proj)
        contract_manager = execution.get_contracts()
        if args.contract is not None:
            contract_manager.set_fuzz_contracts([args.contract])
        account_manager = execution.get_accounts()

    if args.fuzzer == 'random':
        policy = PolicyRandom(execution, contract_manager, account_manager)
        obs = ObsRandom(contract_manager, account_manager, args.dataset_dump_path)
    elif args.fuzzer == 'imitation':
        assert args.model is not None, 'please specify model directory for using imitation learning policy'

        if args.train_dir is not None:
            policy = PolicyImitation(None, None, None, args)
            policy.start_train()
            return
        else:
            policy = PolicyImitation(execution, contract_manager, account_manager, args)
            policy.load_model()
        obs = ObsImitation(contract_manager, account_manager, args.dataset_dump_path)
    elif args.fuzzer == 'symbolic':
        policy = PolicySymbolic(execution, contract_manager, account_manager)
        obs = ObsSymbolic(contract_manager, account_manager, args.dataset_dump_path, backend_loggers)
    elif args.fuzzer == 'sym_plus':
        K = args.depth
        policy = PolicySymPlus(execution, contract_manager, account_manager, K) #added k depth
        print("sym_plus hi")
        print(" ")
        obs = ObsSymPlus(contract_manager, account_manager, args.dataset_dump_path, backend_loggers)
        print("sym_plus end")
        print(" ")
    elif args.fuzzer == 'mix':
        policy = PolicyMix(execution, contract_manager, account_manager, args)
        obs = ObsMix(contract_manager, account_manager, args.dataset_dump_path, backend_loggers)

    inst_cov = 0;
    environment = Environment(args.limit, args.seed)
    print("hi")
    print(" ")
    inst_cov_cur, bug_found = environment.fuzz_loop(policy, obs)
    inst_cov = max(inst_cov,inst_cov_cur)
    print("end")
    print(" ")
    return inst_cov, bug_found
    



if __name__ == '__main__':
    # ---------------- VerifSmart ----------------
    args = get_args()
    runs = args.runs
    K = args.depth
    FINALbugs = {}

    if K != -1 and K <= 0:
        print("Please enter a valid depth [Default: -1 (no depth consideration)]")
        exit(1)  # Use exit instead of return at the top level

    cov = 0
    print("Number of runs:", runs)
    c1 = 0
    c2 = 0
    
    for i in range(runs):
        cur_cov, bugs = main(args)
        print("Completed run:", i + 1)
        print("Bugs found", bugs)
        for bug_type, methods in bugs.items():
            if bug_type not in FINALbugs:
                FINALbugs[bug_type] = set()
            FINALbugs[bug_type].update(methods)

        print("Current Inst Coverage found", cur_cov)
        cov = max(cur_cov, cov)
    print(" ")
    print("FINAL Bugs Found after {} runs: {}".format(runs, FINALbugs))
    print("FINAL INST cov after {} runs: {}".format(runs, cov))
    with open("/go/src/ilf/result.txt", "a") as f:
        f.write(f"Depth {K} Results:\n")
        f.write(f"Final Instruction Coverage after {runs} runs: {cov}\n")
        f.write(f"Final Bugs Found after {runs} runs: {FINALbugs}\n")   
    # ---------------- VerifSmart ----------------

