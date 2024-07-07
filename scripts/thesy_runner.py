import os
import scripts.config as config
import scripts.thesy_stats_processor as stats_processor
import scripts.thesy_stats_postprocessor as stats_postprocessor
import scripts.util as util
import time
import json
import subprocess
import sys

def _get_dataset(dataset_name):
    dataset_path = os.path.join(config.dataset_root, "thesy", dataset_name)
    return [(name[:-5] if name[-5:] == ".smt2" else name, file, "") for (name, file) in util.collect_benchmarks(dataset_path, ".th")]

def _run_thesy(task_name, inp_file, output_path, extra_flag):
    oup_file = os.path.join(output_path, task_name + ".out")
    err_file = os.path.join(output_path, task_name + ".err")
    json_file = os.path.join(output_path, task_name + ".stats.json")
    util.create_path(oup_file)
    if os.path.exists(json_file): os.system("rm " + json_file)
    command = ["cd", config.thesy_path, ";", "timeout " + str(config.timeout),  os.path.join(config.thesy_path, "target/release/TheSy"), "--prove ", extra_flag, config.thesy_args, inp_file, ">", oup_file, "2>", err_file]
    command = " ".join(command)

    try:
        result = subprocess.run(command, shell=True, check=True)
    except subprocess.CalledProcessError as e:
        # output is noisy and unhelpful since it's just the error code -
        # should check the .err files instead
        # print(f"Command '{command}' failed with return code {e.returncode}")
        pass
    except KeyboardInterrupt:
        print("\nExecution halted by user")
        sys.exit(0)

    inp_dir = os.path.dirname(inp_file)
    task_base = os.path.basename(os.path.splitext(inp_file)[0])
    for new_file in os.listdir(inp_dir):
        if task_base + "." in new_file and new_file != task_base + ".th":
            suffix = ".".join(new_file.split(".")[1:])
            if suffix[:5] == "smt2.": suffix = suffix[5:]
            os.rename(os.path.join(inp_dir, new_file), os.path.join(output_path, task_name + "." + suffix))

    if not os.path.exists(json_file): return False, None 

    with open(json_file, "r") as inp:
        res = json.load(inp)

    if len(res["goals_proved"]) == 0: 
        return False, None
    return True, res["total_time"]["secs"] + res["total_time"]["nanos"] * (10 ** -9)

def _collect_result(output_dir, summary_path, dataset):
    outfile = os.path.join(summary_path, dataset + '.csv')
    stats_processor.write_stats(output_dir, outfile)

def get_runner():
    return {"dataset": _get_dataset, "runner": _run_thesy, "post": _collect_result, "name": "thesy"}
