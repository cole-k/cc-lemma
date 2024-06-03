import json
import os

def load_cache(cache_path: str):
    if not os.path.exists(cache_path):
        return {}
    with open(cache_path, "r") as inp:
        return json.load(inp)

def backup_cache(cache_path: str):
    if not os.path.exists(cache_path): return
    name, ext_name = os.path.splitext(cache_path)
    name += "_bk"
    backup_id = 0
    while os.path.exists(name + str(backup_id) + ext_name):
        backup_id += 1
    backup_path = name + str(backup_id) + ext_name
    os.system("cp %s %s" % (cache_path, backup_path))

def clear_cache(cache_path: str, cond):
    if not os.path.exists(cache_path): return 
    cache = load_cache(cache_path)
    new_cache = {}
    for solver_name, solver_res in cache.items():
        new_solver_res = {}
        for benchmark_name, res in solver_res.items():
            print(solver_name, benchmark_name)
            new_res = list(filter(lambda r: not cond(solver_name, benchmark_name, r), res))
            new_solver_res[benchmark_name] = new_res
        if len(solver_res) > len(new_solver_res): print("remove", solver_name, benchmark_name)
        new_cache[solver_name] = new_solver_res
    save_cache(cache_path, new_cache, False)

def save_cache(cache_path: str, cache, is_cover: bool):
    if os.path.exists(cache_path) and not is_cover:
        backup_cache(cache_path)
    with open(cache_path, "w") as oup:
        json.dump(cache, oup, indent=4)
