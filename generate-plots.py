#!/usr/bin/env python3

import argparse
import os
import sys
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

def read_cvc4_results(filename, prefix='goal', timeout=60.0):
    '''
    Each of the different tools records their outputs slightly differently.
    These functions parse them into a format amenable to making a graph.
    '''
    df = pd.read_csv(filename)
    fix_name = lambda s: s.split('/')[-1].removeprefix(prefix).lstrip('0')
    df['name'] = df['name'].apply(fix_name)
    # sub any default values
    df.loc[df['result'] == False, 'time'] = df.loc[df['result'] == False, 'time'].replace(0.0, timeout)
    return df

def read_cclemma_results(filename, prefix, timeout=60.0):
    df = pd.read_csv(filename)
    fix_name = lambda s: s.removeprefix(prefix).lstrip('0')
    df['name'] = df['name'].apply(fix_name)
    df['time'] = df['time'] / 1000
    df['result'] = df['result'] == 'Valid'
    df.loc[df['result'] == False, 'time'] = df.loc[df['result'] == False, 'time'].replace(0.0, timeout)
    return df

def read_hipspec_results(filename, prefix='prop_', timeout=60.0):
    df = pd.read_csv(filename)
    fix_name = lambda s: s.split('/')[-1].removeprefix(prefix).lstrip('0')
    df['name'] = df['prop_name'].apply(fix_name)
    df['result'] = df['prop_proven']
    df.loc[df['result'] == False, 'time'] = df.loc[df['result'] == False, 'time'].replace(0.0, timeout)
    return df

def read_thesy_results(filename, prefix='goal', suffix='.stats.json'):
    thesy_df = pd.read_csv(filename)
    # remove prefix/suffix
    thesy_df['name'] = thesy_df['file_name'].str[len(prefix):].str.removesuffix(suffix)
    thesy_df['result'] = thesy_df['success']
    # not available
    thesy_df['num_lemmas'] = -1
    thesy_df['num_lemmas_proven'] = thesy_df['lemma_count']
    return thesy_df

def read_thesy_results_precomputed(filename, test_suite, prefix='goal', suffix='.smt2.stats.json'):
    thesy_df = pd.read_csv(filename)
    # filter to the test suite
    thesy_df = thesy_df[thesy_df['test_suite'] == test_suite]
    # remove prefix/suffix
    thesy_df['name'] = thesy_df['file_name'].str[len(prefix):].str.removesuffix(suffix)
    thesy_df['result'] = thesy_df['success']
    # not available
    thesy_df['num_lemmas'] = -1
    thesy_df['num_lemmas_proven'] = thesy_df['lemma_count']
    return thesy_df

def filter_clam_results(clam_results, name_column, name_prefix, results_to_keep, name_suffix='', ignore_missing=False):
    '''
    Filters a dataframe containing clam results to only those
    that require lemmas.
    '''
    # Create a new list result_names by prepending name_prefix to results_to_keep
    result_names = [name_prefix + str(result) + name_suffix for result in results_to_keep]

    # Filter clam_results to keep only results where name_column is contained in results_to_keep
    filtered_results = clam_results[clam_results[name_column].isin(result_names)]

    # for result in result_names:
    #     if not any(result == clam_results[name_column]):
    #         print(result)
    if not ignore_missing:
        assert(len(filtered_results) == 50)

    return filtered_results

def make_clam_lemma_props():
    '''
    All of our CLAM datasets have more properties than the original 50
    (labeled with prefix T in the paper, these are properties 1-50 in our dataset).

    These additional properties correspond to lemmas thought to be necessary
    to prove the originals (labeled with L and G).

    We do not use T1-T50, but instead a combination of the T and G properties
    which are thought to require lemmas. If you are familiar with CVC4's
    benchmarks, these are the goals which have "sg" versions, i.e. lemmas thought
    to be necessary to prove them.
    '''
    # Range from 1 to 35 inclusive
    range1 = map(str, range(1, 36))
    # Handle the case where there's a prefix 0 (hacky, I know)
    range_single_digit = map(lambda x: '0' + str(x), range(1,10))
    # Range from 48 to 50 inclusive
    range2 = map(str, range(48, 51))
    # Range from 75 to 86 inclusive
    range3 = map(str, range(75, 87))

    # Combine all ranges
    clam_lemma_props = list(range_single_digit) + list(range1) + list(range2) + list(range3)
    return clam_lemma_props

def make_comparison_table(*dfs, time_cutoff=None, verbose=True):
    '''
    This constructs a table comparing each of the results to the first.
    '''
    comparison_data = []

    # Compute comparison data for each dataframe
    for i, (name, d) in enumerate(dfs):
        # the first dataframe is our anchor
        if i == 0:
            base_df = d.copy()
            if time_cutoff:
                base_df = base_df[base_df['time'] <= time_cutoff]
            base_count = base_df['result'].sum()
            count = base_count
            avg_time = base_df[base_df['result']]['time'].mean()
            median_time = base_df[base_df['result']]['time'].median()
            max_time = base_df[base_df['result']]['time'].max()
            # "time out" the results that are out of time,
            # but don't filter them
            if time_cutoff:
                base_df = d.copy()
                base_df.loc[base_df['time'] > time_cutoff, 'result'] = False
            can_prove = []
            num_can_prove = 0
            cant_prove = []
            num_cant_prove = 0
        else:
            df = d.copy()
            if time_cutoff:
                df = d[d['time'] <= time_cutoff]
            count = df['result'].sum()
            avg_time = df[df['result']]['time'].mean()
            median_time = df[df['result']]['time'].median()
            max_time = df[df['result']]['time'].max()
            # "time out" the results that are out of time,
            # but don't filter them
            if time_cutoff:
                df = d.copy()
                df.loc[df['time'] > time_cutoff,'result'] = False
            # Merge the two dataframes on the 'name' column
            merged_df = base_df.merge(df, on='name', suffixes=('_1', '_2'), how='left', validate='one_to_one')
            # this took me way too long to figure out
            with pd.option_context('future.no_silent_downcasting', True):
                merged_df['result_1'] = merged_df['result_1'].fillna(False).astype(bool)
                merged_df['result_2'] = merged_df['result_2'].fillna(False).astype(bool)
            can_prove = merged_df[~merged_df['result_1'] & merged_df['result_2']]['name'].tolist()
            num_can_prove = len(can_prove)
            cant_prove = merged_df[merged_df['result_1'] & ~merged_df['result_2']]['name'].tolist()
            num_cant_prove = len(cant_prove)
            if verbose and count + (num_cant_prove - num_can_prove) != base_count:
                print(f'WARN: num_cant_proe - num_can_prove = {num_cant_prove - num_can_prove} is not base_count - count {base_count - count}')

        comparison_data.append({
            'name': name,
            'count': count,
            'avg_time': avg_time,
            'median_time': median_time,
            'max_time': max_time,
            'can_prove': can_prove,
            'num_can_prove': num_can_prove,
            'cant_prove': cant_prove,
            'num_cant_prove': num_cant_prove,
        })

    comparison_table = pd.DataFrame(comparison_data)
    return comparison_table

def table_to_latex(table):
    '''
    Makes a nice latex table out of the comparison results.
    '''
    header = r'''\begin{tabular}{l l r r r r r}
Tool & \# proved & Median time & Max time & \# we can't prove & \# they can't prove\\
\hline
'''
    body = ''
    for _, row in table.iterrows():
        body += f"& {row['name']} & {row['count']} & {row['median_time']:.2f} & {row['max_time']:.2f} & {row['num_can_prove']} & {row['num_cant_prove']}\\\\ \n"
    footer = '''\end{tabular}'''
    return header + body + footer

def normalized_df_valid_times(df):
    return df[df['result']]['time']

def names_not_in_intersection(*dataframes):
    # Extract 'name' columns from all DataFrames
    name_sets = [set(df['name']) for df in dataframes]

    # Find the intersection of all 'name' sets
    intersection = set.intersection(*name_sets)

    # Find names not in the intersection
    names_not_in_intersection = set.union(*[name_set - intersection for name_set in name_sets])

    return names_not_in_intersection

def cactus_plot(filtered_times, tool_names, title, output_dir, end_range=10,
                scale=0.01, add_legend=False, show_plot=True, save_plot=False):
    '''
    Takes in a list of times
    and makes a cactus plot for them.
    '''

    # Generate times
    times = np.arange(0, end_range, scale)

    # Iterate over time_range and count the number of valid results for each time step
    for i, time_data in enumerate(filtered_times):
        num_valid_at_time = []
        for t in times:
            num_valid = time_data[time_data <= t].shape[0]
            num_valid_at_time.append(num_valid)
        plt.plot(times, num_valid_at_time, label = tool_names[i])

    # print(list(zip(times, num_valid_at_time)))
    # print([f'{times[i]}ms' for i in range(0, len(times), len(times) // 10)])

    # Plot
    plt.xlabel('Time (s)')
    plt.ylabel('# Benchmarks')
    if add_legend:
        plt.legend(loc='lower right')
    plt.title(title)
    plt.rc('axes', labelsize=16, titlesize=16)
    if save_plot:
        plt.savefig(output_dir + '/' + title.lower() + '.png')
    if show_plot:
        plt.show()
    plt.close()

def zoomed_in_cactus_plot(filtered_times, tool_names, title, output_dir,
                          end_zoom_range=1, end_range=10, num_points=1000, add_legend=False,
                          show_plot=True, save_plot=False):
    '''
    Takes in a list of times
    and makes a cactus plot for them which is zoomed in on 1s.

    This was a huge pain to get correct and while I am apologetic about all of
    the code, I am especially apologetic about this. It's half
    ChatGPT-almost-right code and half terrible hackery to fix it.
    '''

    # Generate times
    first_len = num_points // 2
    rest_len = (num_points // 2)
    times_first_segment = np.linspace(start=0, stop=end_zoom_range, num=first_len)
    times_second_segment = np.linspace(start=end_zoom_range, stop=end_range, num=rest_len)
    times = np.concatenate((times_first_segment, times_second_segment))

    # Iterate over time_range and count the number of valid results for each time step
    for i, time_data in enumerate(filtered_times):
        num_valid_at_time = []
        for t in times:
            num_valid = time_data[time_data <= t].shape[0]
            num_valid_at_time.append(num_valid)
        plt.plot(range(len(num_valid_at_time)), num_valid_at_time, label = tool_names[i])

    # print(list(zip(times, num_valid_at_time)))
    # print([f'{times[i]}ms' for i in range(0, len(times), len(times) // 10)])

    # Plot
    plt.xlabel('Time (s)')
    plt.ylabel('# Benchmarks')
    initial_xticks = np.arange(0, len(times) // 2, len(times) // 10)
    latter_xticks = []
    # add 6 more ticks
    for x in range(10, end_range+1, end_range // 6):
        for i, time in enumerate(times):
            if time >= x:
                latter_xticks.append(i)
                break
    ticks = np.concatenate((initial_xticks, [len(times_first_segment)], latter_xticks))
    initial_labels = [f'{times[i]:.1f}s' for i in initial_xticks]
    midpoint = [f'{end_zoom_range}']
    end_labels = [f'{round(times[i])}' for i in latter_xticks]
    labels = initial_labels + midpoint + end_labels
    plt.xticks(ticks=ticks, labels=labels)

    # Add vertical line at the point where the time scale changes
    plt.axvline(len(times_first_segment), color='gray', linestyle='--')

    # Annotate the plot to indicate the transition
    plt.annotate('Time scale changes', xy=(len(times_first_segment), 0), xytext=(len(times_first_segment)-400, 0.5),
                 arrowprops=dict(facecolor='black', arrowstyle='->'))
    if add_legend:
        plt.legend(loc='lower right')
    plt.title(title)
    plt.rc('axes', labelsize=16, titlesize=16)
    if save_plot:
        plt.savefig(output_dir + '/' + title.lower() + '.png')
    if show_plot:
        plt.show()
    plt.close()

def make_plot(dir, dataset, dataset_name, cclemma_prefix, output_dir,
              end_range=60, end_zoom_range=1, no_zoom=False, add_legend=False,
              verbose=True, exclude=[], show_plot=True, save_plot=False):
    '''
    Reads the data from dir and produces a cactus plot for it.

    Expects that dataset is either 'isaplanner', 'clam', or 'optimization'.
    '''

    tool_res = []
    for tool in ['cclemma', 'hipspec', 'cvc4', 'thesy', 'thesy-precomputed']:
        if tool in exclude:
            continue
        res = None
        if tool == 'cclemma':
                res = read_cclemma_results(dir + '/cclemma/' + dataset.lower() + '.csv', cclemma_prefix)
        if tool == 'hipspec':
                res = read_hipspec_results(dir + '/hipspec/' + dataset.lower() + '.csv')
        if tool == 'cvc4':
                res = read_cvc4_results(dir + '/cvc4/' + dataset.lower() + '.csv')
        if tool == 'thesy':
                res = read_thesy_results(dir + '/thesy/' + dataset.lower() + '.csv')
        if tool == 'thesy-precomputed':
                # Yes, there is a lot of special-casing...
                if dataset == 'clam':
                    res = read_thesy_results_precomputed(dir + '/thesy-no-expl-proofs.csv', test_suite='clam_trimmed')
                elif dataset == 'optimization':
                    res = read_thesy_results_precomputed(dir + '/thesy-no-expl-proofs.csv', test_suite=dataset.lower(), prefix='', suffix='.stats.json')
                else:
                    res = read_thesy_results_precomputed(dir + '/thesy-no-expl-proofs.csv', test_suite=dataset.lower())
        if dataset == 'clam':
            clam_lemma_props = make_clam_lemma_props()
            # TheSy will sometimes have missing entries if it fails, so we ignore missing data on it.
            res = filter_clam_results(res, 'name', '', clam_lemma_props, ignore_missing= tool == 'thesy' or tool == 'thesy-precomputed')
        assert(res is not None)
        tool_res.append((tool, res))

    missing_names = names_not_in_intersection(*[res for _, res in tool_res])

    if verbose:
        # For some tools - such as TheSy - failing to prove a result can result in
        # an empty or missing entry in the dataframe.
        #
        # This is especially true on the Optimization benchmark, for which we timed
        # out many tools.
        #
        # For the baseline benchmarks this is a sanity check to make sure no properties
        # are missing. It's mostly noise for the Optimization benchmark due to the above.
        for tool, res in tool_res:
            names = set(res['name'])
            if any(name not in names for name in missing_names):
                print(tool, f'is missing {len(missing_names - names)} entries for {dataset}')
                if tool == 'thesy' or tool == 'thesy-precomputed':
                    print('Note: TheSy will sometimes have missing entries if it cannot prove a property.')
                print(list(sorted(missing_names - names)))
                print()

    names_map = {'cclemma': 'CCLemma',
                 'hipspec': 'HipSpec',
                 'cvc4': 'CVC4',
                 'thesy': 'TheSy',
                 'thesy-precomputed': 'TheSy'}
    times = [ normalized_df_valid_times(res) for _, res in tool_res ]
    names = [ names_map[tool] for tool, _ in tool_res ]
    if no_zoom:
        cactus_plot(times,
                    names,
                    dataset_name,
                    output_dir,
                    end_range=end_range, add_legend=add_legend, show_plot=show_plot, save_plot=save_plot)
    else:
        zoomed_in_cactus_plot(times,
                              names,
                              dataset_name,
                              output_dir,
                              end_zoom_range=end_zoom_range, end_range=end_range, add_legend=add_legend, show_plot=show_plot, save_plot=save_plot)

    return make_comparison_table(*tool_res,time_cutoff=end_range)

def parse_arguments():
    parser = argparse.ArgumentParser(description='Process and plots results.')

    # Positional argument
    parser.add_argument('results_dir', type=str, help='the directory where the result summaries are located (using defaults, this should be results/summary)')

    # Optional flags
    parser.add_argument('--no-save-plots', action='store_true', default=False, help='Do not save the output plots as PNGs in OUTPUT_DIR')
    parser.add_argument('-o', '--output-dir', type=str, default=os.getcwd(), help='Where to output saved plots')
    parser.add_argument('-d', '--display-plots', action='store_true', default=False, help='Display the plots')
    parser.add_argument('-e', '--exclude-tools', nargs='*', default=[], help='''
    List of tools to exclude from plotting the results. Any number of cclemma,
    thesy, hipspec, cvc4. Excluding cclemma will change how the comparison
    tables are generated. Not sure why you would exclude cclemma though.''')
    parser.add_argument('-p', '--precomputed', action='store_true',
                        default=False, help='Use precomputed results (only relevant for TheSy)')

    return parser.parse_args()

if __name__ == '__main__':
    args = parse_arguments()

    if not os.path.isdir(args.results_dir):
        print(f"Error: The directory {args.results_dir} does not exist.")
        sys.exit(1)

    # By default exclude thesy precomputed
    args.exclude_tools.append('thesy-precomputed')

    if args.precomputed:
        # if we aren't skipping thesy, replace it with the precomputed version
        if 'thesy' not in args.exclude_tools:
            args.exclude_tools.append('thesy')
            args.exclude_tools.remove('thesy-precomputed')

    # If you want to create plots for custom results, you will need to modify
    # the below code.
    #
    # Parsing the results is very brittle so I do not recommend this unless you
    # want to add your own parsing code.
    table = make_plot(args.results_dir, 'isaplanner', 'IsaPlanner', 'goal_',
                      args.output_dir, end_zoom_range=1, add_legend=True,
                      save_plot=not args.no_save_plots, show_plot=args.display_plots, exclude=args.exclude_tools)
    print('IsaPlanner table:')
    print(table_to_latex(table))
    print()
    table = make_plot(args.results_dir, 'clam', 'CLAM', 'clam_',
                      args.output_dir, end_zoom_range=1, add_legend=True,
                      save_plot=not args.no_save_plots, show_plot=args.display_plots,
                      exclude=args.exclude_tools)
    print('CLAM table:')
    print(table_to_latex(table))
    print()
    table = make_plot(args.results_dir, 'optimization', 'Optimization', '',
                      args.output_dir, end_range=60, no_zoom=True,
                      add_legend=True, verbose=False, save_plot=not args.no_save_plots,
                      show_plot=args.display_plots, exclude=args.exclude_tools)
    print('Optimization table:')
    print(table_to_latex(table))
    print()
