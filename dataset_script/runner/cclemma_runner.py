import os
import config
import util
import time
import glob
import subprocess
import sys

def _get_dataset(dataset_name):
    dataset_path = os.path.join(config.dataset_root, "cclemma", dataset_name)
    return [(name, file, "") for (name, file) in util.collect_benchmarks(dataset_path, ".ceg")]

def _run_cclemma(task_name, inp_file, output_path, extra_flag):
    oup_file = os.path.join(output_path, task_name + ".out")
    err_file = os.path.join(output_path, task_name + ".err")
    original_csv_file = os.path.join(config.cclemma_path, "target/results.csv")
    csv_file = os.path.join(output_path, task_name + ".csv")
    util.create_path(oup_file)
    command = ["cd", config.cclemma_path, ";",
               'ulimit -v ' + str(config.memory_limit * 1024 * 1024) + ';',
               os.path.join(config.cclemma_path, "target/release/cc-lemma"), inp_file, config.cclemma_args, "-t", str(config.timeout * 2), ">", oup_file, "2>" + err_file]
    try:
        result = subprocess.run(command_str, shell=True, check=True, timeout=config.timeout * 1.25)
    except subprocess.CalledProcessError as e:
        print(f"Command '{command_str}' failed with return code {e.returncode}")
    except subprocess.TimeoutExpired:
        # we expect this may happen since our timekeeping is not 100% accurate
        pass
    except KeyboardInterrupt:
        print("\nExecution halted by user")
        sys.exit(0)

    with open(oup_file, "r") as res:
        line = "\n".join(res.readlines())
    if os.path.exists(original_csv_file):
        os.system("mv " + original_csv_file + " " + csv_file)
        
    if " VALID (" in line:
        ti = line.split(" VALID (")[1].split(" ms)")[0]
        return True, float(ti) / 1000
    return False, None 

def _collect_result(output_dir, summary_path, dataset):
    res = []
    for file in glob.glob(output_dir + '/*.csv'):
        with open(file, "r") as inp:
            lines = inp.readlines()
            if len(res) == 0: res.append(lines[0])
            if dataset == "sufu":
                assert len(lines) <= 2
                if len(lines) == 1: continue 
                
                task_name = os.path.basename(os.path.splitext(file)[0])
                new_line = lines[1].split(",")
                new_line[0] = task_name 
                res.append(",".join(new_line))
            else:
                res.extend(lines[1:])
    output_file = os.path.join(summary_path, dataset + ".csv")
    util.create_path(output_file)
    with open(output_file, "w") as oup:
        oup.write("".join(res))

def get_runner():
    return {"dataset": _get_dataset, "runner": _run_cclemma, "name": "cclemma", "post": _collect_result}
