import os
import config
import util
import time
import glob
import re
import json
import csv

def _get_dataset(dataset_name):
    # special case for sufu: each property and its definitions are in a separate
    # file and we will run hipspec with the expensive args for each of them
    # because it will struggle otherwise due to the grammar size.
    if dataset_name == "sufu":
        dataset_path = os.path.join(config.dataset_root, "hipspec/sufu")
        return [(name, file, config.hipspec_expensive_args) for (name, file) in util.collect_benchmarks(dataset_path, ".hs")]
    dataset_path = os.path.join(config.dataset_root, "hipspec", dataset_name)
    property_file = os.path.join(dataset_path, "Properties.hs")
    definition_file = os.path.join(dataset_path, "Definitions.hs")
    
    target_definition_file = os.path.join(config.hipspec_path, "Definitions.hs")
    if os.path.exists(target_definition_file):
        os.system("rm " + target_definition_file)
    os.system("cp " + definition_file + " " + target_definition_file)

    with open(property_file, "r") as inp:
        lines = "".join(inp.readlines())
    tasks = []

    expensive_list = config.hipspec_expensive_props.get(dataset_name, default=[])

    for i in range(100):
        task_name = "prop_" + str(i)
        if task_name + " " not in lines: continue
        extra_flag = "--only=" + task_name
        if i in expensive_list: extra_flag += " " + config.hipspec_expensive_args
        tasks.append((task_name, property_file, extra_flag))
    return tasks


def _run_hipspec(task_name, inp_file, output_path, extra_flag):
    oup_file = os.path.join(output_path, task_name + ".out")
    err_file = os.path.join(output_path, task_name + ".err")
    json_file = os.path.join(output_path, task_name + ".json")

    moved_inp_file = util.switch_dir(inp_file, config.hipspec_path)
    os.system("cp " + inp_file + " " + moved_inp_file)
    task_name = os.path.basename(inp_file)
    util.create_path(oup_file)

    command = ["cd", config.hipspec_path, ";", 'ulimit -v ' + str(config.memory_limit * 1024 * 1024) + ';', "timeout " + str(config.timeout), "stack-1.9.3 exec hipspec --", task_name, config.hipspec_args, "--json=" + json_file, extra_flag, ">", oup_file, "2>", err_file]
    command = " ".join(command)
    start_time = time.time()
    os.system(command)
    end_time = time.time()
    os.system("rm " + moved_inp_file)

    with open(oup_file, "r") as res:
        line = "\n".join(res.readlines())
    with open(err_file, "r") as inp:
        err_line = "\n".join(inp.readlines())
    if "Compilation failed!" in line or "parse error" in line:
        print("HipSepc failed in parsing", os.path.basename(task_name))
        return False, None
    if "Proved optimize" in line or "Proved prop" in line:
        return True, {"time": end_time - start_time}
    return False, None 

PROVED_PREFIX = r'[034m[1mProved '
PROVED_SUFFIX_1 = ' by induction'
PROVED_SUFFIX_2 = ' without induction'
UNPROVED_PREFIX = 'Failed to prove '

def collect_lemma_from_line(log_line):
    '''
    Returns (is_proven, lemma).
    lemma is None if there is no lemma to collect.
    '''
    if log_line.startswith(PROVED_PREFIX):
        stripped = log_line[len(PROVED_PREFIX):]
        end_index = stripped.find(PROVED_SUFFIX_1) or stripped.find(PROVED_SUFFIX_2)
        return (True, stripped[:end_index])
    if log_line.startswith(UNPROVED_PREFIX):
        return (False, log_line[len(UNPROVED_PREFIX):].rstrip('\n'))

    return (False, None)

def collect_evaluations_and_raw_equations(log_line):
    m = re.match(r"Depth 3: .*?(\d+) evaluations, .*?(\d+) raw equations\.", log_line)
    if m:
        evaluations = int(m.group(1))
        raw_equations = int(m.group(2))
        return evaluations, raw_equations


def collect_stats(prop_name, log_file_name):
    proven_lemmas = set()
    lemmas = set()
    num_evaluations = None
    num_raw_eqs = None
    with open(log_file_name) as log_file:
        for line in log_file:
            (is_proven, lemma) = collect_lemma_from_line(line)
            if lemma:
                lemmas.add(lemma)
                if is_proven:
                    proven_lemmas.add(lemma)
            evals_and_raw_eqs = collect_evaluations_and_raw_equations(line)
            if evals_and_raw_eqs:
                assert(not num_evaluations)
                assert(not num_raw_eqs)
                num_evaluations, num_raw_eqs = evals_and_raw_eqs
    return (proven_lemmas, lemmas, num_evaluations, num_raw_eqs)

def parse_lemma_name(lemma_name):
    '''
    The names are an array like
    ```
    ['m<=m == True', None]
    ['prop_T50', 'count x (isort y) == count x y']
    ```

    From what I gather this is so that named lemmas have their definition
    alongside them. We don't care about the names, so we take the definition,
    falling back to the name (which is the definition for the "anonymous
    lemmas")
    '''
    return lemma_name[1] or lemma_name[0]

def read_result(json_file, log_file):
    prop_name = os.path.basename(os.path.splitext(json_file)[0])
    if os.path.exists(json_file):
        result_json = json.load(open(json_file))
        time, result_obj = result_json[-1]
        unproved_lemmas = list(map(parse_lemma_name, result_obj['qs_unproved']))
        proved_lemmas = list(map(parse_lemma_name, result_obj['qs_proved']))
        num_unproved_lemmas = len(unproved_lemmas)
        num_proved_lemmas = len(proved_lemmas)
        num_lemmas = num_unproved_lemmas + num_proved_lemmas
        # We expect that there is only one top-level property. If this expectation
        # is violated we will have to do more parsing to figure out if the prop is
        # proved.
        proved_props = list(map(parse_lemma_name, result_obj['proved']))
        unproved_props = list(map(parse_lemma_name, result_obj['unproved']))
        assert(len(proved_props) + len(unproved_props) == 1)
        prop_proven = len(proved_props) > 0
        # there should be only one prop between these two, so extract it
        prop = (proved_props + unproved_props)[0]
    else:
        time, unproved_lemmas, proved_lemmas, num_unproved_lemmas, num_proved_lemmas, num_lemmas, prop = [None for _ in range(7)]
        prop_proven = False
        

    # parse log file
    proven_lemmas, lemmas, num_evals, num_raw_eqs, = collect_stats(prop_name, log_file)
    # they can differ by 1 because if the prop is proved it will be among the
    # proven lemmas
    if num_proved_lemmas is not None:
        assert(abs(len(proven_lemmas) - num_proved_lemmas) <= 1)
    return {
        'prop_name': prop_name,
        'prop_proven': prop_proven,
        'time': time,
        'num_lemmas_attempted': len(lemmas),
        'num_lemmas': num_lemmas,
        'num_raw_eqs': num_raw_eqs,
        'num_evals': num_evals,
        'num_proved_lemmas': num_proved_lemmas,
        'num_unproved_lemmas': num_unproved_lemmas,
        'proved_lemmas': proved_lemmas,
        'unproved_lemmas': unproved_lemmas,
        'prop': prop,
    }


def _collect_result(output_dir, summary_path, dataset):
    results = [read_result(filename[:-3] + "json", filename) for filename in glob.glob(output_dir + '/*.out')]
    output_file = os.path.join(summary_path, dataset + ".csv")
    util.create_path(output_file)
    with open(output_file, 'w') as csvfile:
        writer = csv.DictWriter(csvfile, ['prop_name', 'prop_proven', 'time', 'num_lemmas_attempted', 'num_lemmas', 'num_raw_eqs', 'num_evals', 'num_proved_lemmas', 'num_unproved_lemmas', 'proved_lemmas', 'unproved_lemmas', 'prop'])
        writer.writeheader()
        for result in sorted(results, key=lambda result: result['prop_name']):
            writer.writerow(result)
    

def get_runner():
    return {"dataset": _get_dataset, "runner": _run_hipspec, "name": "hipspec", "post": _collect_result}
