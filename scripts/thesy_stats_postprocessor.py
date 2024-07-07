#!/usr/bin/env python3

# There was a lot of ad-hoc processing and transformations going on; this surely
# could be done in a single pass but it's easier to just do the inefficient
# thing.

import csv
import sys
from collections import defaultdict

def parse_row(row):
    # ,,,time,stop_reasons,success,lemma_count,failed_proof_count,proofs_later_filtered,file_name
    proof_type            = row[0]
    test_suite            = row[1]
    suite_order           = row[2]
    time                  = float(row[3])
    stop_reasons          = eval(row[4])
    success               = eval(row[5])
    lemma_count           = int(row[6])
    failed_proof_count    = int(row[7])
    proofs_later_filtered = int(row[8])
    file_name             = row[9]
    return {'proof_type': proof_type,
            'test_suite': test_suite,
            'suite_order': suite_order,
            'time': time,
            'stop_reasons': stop_reasons,
            'success': success,
            'lemma_count': lemma_count,
            'failed_proof_count': failed_proof_count,
            'proofs_later_filtered': proofs_later_filtered,
            'file_name': file_name}

def postprocess_stats(infile, outfile_prefix):
    proofs_by_proof_type_and_test_suite = defaultdict(lambda: defaultdict(list))
    with open(infile) as csv_file:
        # ignore the header
        csv_file.readline()
        reader = csv.reader(csv_file)
        for row in reader:
            parsed_row = parse_row(row)
            proof_type = parsed_row['proof_type']
            test_suite = parsed_row['test_suite']
            proofs_by_proof_type_and_test_suite[proof_type][test_suite].append(parsed_row)

    for (proof_type, proofs_by_test_suite) in proofs_by_proof_type_and_test_suite.items():
        filename = f"{outfile_prefix}-{proof_type.replace(' ', '-')}.csv"
        with open(filename, 'w') as csv_file:
            fieldnames = ['test_suite', 'file_name', 'success', 'time', 'stop_reasons', 'lemma_count', 'failed_proof_count', 'proofs_later_filtered']
            writer = csv.DictWriter(csv_file, fieldnames=fieldnames, extrasaction='ignore')
            writer.writeheader()
            for (_, proof_results) in proofs_by_test_suite.items():
                sorted_rows = sorted(proof_results, key=lambda r: r['file_name'])
                for row in sorted_rows:
                    # we don't need to add the test_suite because it's already a part of the row
                    writer.writerow(row)

if __name__ == '__main__':
    infile = sys.argv[1]
    outfile_prefix = sys.argv[2]
    postprocess_stats(infile, outfile_prefix)
