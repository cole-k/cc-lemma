import os 

def switch_dir(path, output_path):
	file_name = os.path.basename(path)
	return os.path.join(output_path, file_name)

def create_path(file):
	dir_path = os.path.dirname(file)
	os.makedirs(dir_path, exist_ok=True)

def split_suffix(file):
	return os.path.splitext(file)

def collect_benchmarks(dataset_path, expected_suffix):
	all_files = []
	for file in os.listdir(dataset_path):
		if "." not in file: continue
		name, suffix = split_suffix(file)
		if suffix != expected_suffix: continue
		all_files.append((name, os.path.join(dataset_path, file)))
	return all_files