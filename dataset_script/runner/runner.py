import os 
from tqdm import tqdm
from cache import *
import util
import config
import hipspec_runner
import cclemma_runner
import thesy_runner
import cvc_runner

def run(runner_info, dataset_list):
	solver_name, dataset_collector, runner = runner_info["name"], runner_info["dataset"], runner_info["runner"]
	
	cache_file = os.path.join(config.output_path, solver_name + "_res.json")
	cache = load_cache(cache_file)
	is_cover = False

	considered_dataset = [dataset for dataset in dataset_list]
	#if solver_name == "cclemma": considered_dataset.append("sufu-ite")

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
	dataset_list = ["isaplanner", "clam", "sufu"]
	run(thesy_runner.get_runner(), dataset_list)
	run(cvc_runner.get_runner(), dataset_list)
	run(hipspec_runner.get_runner(), dataset_list)
	run(cclemma_runner.get_runner(), dataset_list)
