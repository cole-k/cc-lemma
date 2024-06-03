import os 
from tqdm import tqdm
from scripts.cache import load_cache, save_cache
import scripts.util as util
import scripts.config as config
import scripts.hipspec_runner as hipspec_runner
import scripts.cclemma_runner as cclemma_runner
import scripts.thesy_runner as thesy_runner
import scripts.cvc_runner as cvc_runner

import argparse

TOOLS = ['cclemma', 'cvc4', 'hipspec', 'thesy']
BENCHMARKS = ['isaplanner', 'clam', 'optimization']

def parse_arguments():
    parser = argparse.ArgumentParser(
        description='''Runs all of the tools (default cclemma) on the specified
        benchmarks (default all) and collects their results. Tracks which
        results have been run already so if it gets interrupted it will not
        resume from the start.'''
    )

    parser.add_argument(
        '--clear-cache',
        action='store_true',
        help='Clears the cache (start a new fresh run). Warning: this will overwrite any previous data.'
    )

    parser.add_argument(
        '--all-tools',
        action='store_true',
        help='Run on all tools.'
    )

    parser.add_argument(
        '--tools',
        type=str,
        nargs='+',
        choices=TOOLS,
        default=['cclemma'],
        help='A list of which tools to run. Defaults to cclemma.'
    )

    parser.add_argument(
        '--benchmarks',
        type=str,
        nargs='+',
        choices=BENCHMARKS,
        default=BENCHMARKS,
        help='A list of which benchmarks to run. Defaults to running on all.'
    )

    return parser.parse_args()

def run(runner_info, dataset_list, ignore_cache):
	solver_name, dataset_collector, runner = runner_info["name"], runner_info["dataset"], runner_info["runner"]
	
	cache_file = os.path.join(config.output_path, solver_name + "_res.json")
	if ignore_cache:
		cache = {}
	else:
		cache = load_cache(cache_file)
	is_cover = False

	considered_dataset = [dataset for dataset in dataset_list]

	for dataset in considered_dataset:
		benchmarks = dataset_collector(dataset)
		output_path = os.path.join(config.output_path, solver_name, dataset)
		util.create_path(output_path)
		print("run", solver_name, "on", dataset)
		if dataset not in cache: cache[dataset] = {}
		for task_name, inp_file, extra_flag in tqdm(benchmarks):
			if task_name in cache[dataset]: continue
			status, info = runner(task_name, inp_file, output_path, extra_flag)
			if status:
				cache[dataset][task_name] = {"status": True, "info": info}
			else:
				cache[dataset][task_name] = {"status": False}
			save_cache(cache_file, cache, is_cover)
			is_cover = True
		if "post" in runner_info:
			summary_path = os.path.join(config.output_path, "summary", solver_name)
			runner_info["post"](output_path, summary_path, dataset)

if __name__ == "__main__":
	args = parse_arguments()
	dataset_list = args.benchmarks
	tools = args.tools
	if args.all_tools:
		tools = TOOLS
	if 'cclemma' in tools:
		run(cclemma_runner.get_runner(), dataset_list, args.clear_cache)
	if 'thesy' in tools:
		run(thesy_runner.get_runner(), dataset_list, args.clear_cache)
	if 'cvc4' in tools:
		run(cvc_runner.get_runner(), dataset_list, args.clear_cache)
	if 'hipspec' in tools:
		run(hipspec_runner.get_runner(), dataset_list, args.clear_cache)
