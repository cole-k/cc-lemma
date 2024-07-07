timeout = 2
memory_limit = 16

dataset_root = "/home/artifact/cc-lemma/benchmarks"
cclemma_path = "/home/artifact/cc-lemma"
hipspec_path = "/home/artifact/hipspec"
thesy_path = "/home/artifact/TheSy"
cvc4_bin_name = "cvc4-vmcai2015"
output_path = "/home/artifact/cc-lemma/results"

hipspec_expensive_props = {
    "clam": [81],
    "isaplanner": [33, 34, 35, 84, 85, 86],
}

cvc4_args = "--quant-ind --quant-cf --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant --stats"
hipspec_args = "--auto --verbosity=85 --cg -luU"
hipspec_expensive_args = "--pvars --size 7"
cclemma_args = "--no-generalization --exclude-bid-reachable --saturate-only-parent -r"
thesy_args = ""
