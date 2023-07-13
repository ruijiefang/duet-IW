
import sys
import os
import glob
from string import Template
import subprocess
import tempfile
import types
import statistics

# Configuration -- can be reconfigured via the command line
tools = ['CRAMC','Ultimate','CRA']
suites = ['thesis-all']
timeout = 600
cache = True
replace_cached = False

table_begin = """<?xml version="1.0" ?>
<!DOCTYPE table PUBLIC "+//IDN sosy-lab.org//DTD BenchExec table 1.10//EN" "https://www.sosy-lab.org/benchexec/table-1.10.dtd">
<table>
"""
table_end = "</table>"

# tables are formatted with 1 column for the benchmark name & 3 columns for each tool
#  column 0: benchmark name
#  column 3i + 1: result (output of tool)
#  column 3i + 2: category (whether that result is correct)
#  column 3i + 3: time (s)

def get_name(row):
    return row[0]

def get_result(row, index):
    return row[-3]

def get_category(row, index):
    return row[-2]
    #print('get_category: ', row[-2])
    #if row[-2] == 'correct' or row[-2] == 'wrong':
    #    return 'correct'
    #else: 
    #    return row[-2]
#        if row[-2] == 'TIMEOUT': 
#            return row[-2]
#        if row[-2] == 'unknown':
#            return row[-2]
#        print('wtf:', row[-2])
#        exit(1)

def get_time(row, index):
    return float(row[-1])

def has_result(tool, suite):
    return len(glob.glob("results/%s.*.%s.xml" % (tool, suite))) > 0

def run():
    for suite in suites:
        for tool in tools:
            if replace_cached and has_result(tool,suite):
                recent = recent_result(tool, suite)
                os.remove(recent)

            if cache and has_result(tool, suite):
                print("Result of %s on suite %s is cached" % (tool, suite))
            else:
                print("Running %s on suite %s" % (tool, suite))
                # Add bench dir to PYTHONPATH so benchexec can find the
                # tool module
                my_env = os.environ.copy()
                my_env["PYTHONPATH"] = os.getcwd()
                my_env["PATH"] = my_env["PATH"] + ":" + os.path.abspath('..')
                subprocess.call(["benchexec",
                                #"--read-only-dir",
                                #"/",
                                #"--overlay-dir",
                                #".",
                                #"--full-access-dir",
                                #".",
                                "--no-container",
                                "--no-tmpfs",
                                "-W", str(timeout),
                                 "-t", suite,
                                 "benchmark-defs/%s.xml" % tool],
                                env=my_env)


def recent_result(tool, suite):
    results = glob.glob("results/%s.*.%s.xml" % (tool, suite))
    results.sort()
    if len(results) == 0:
        print("No results for %s on suite %s" % (tool, suite))
        exit(-1)
    else:
        return results[-1]

def recent_result_data(tools, suites):
    data = []
    for suite in suites:
        with tempfile.TemporaryDirectory() as tmp_dir:
            p = subprocess.run(['table-generator',
                                '-f', 'csv',
                                '-o', tmp_dir,
                                '-x', 'simplecsv.xml',
                                '-q']
                               + list(map(lambda x: recent_result(x, suite), tools)))
            table = os.path.join(tmp_dir, "simplecsv.table.csv")
            # strip 3 rows of header info
            with open(table) as fd:
                w=fd.readlines()
                with open('/home/rjf/fast/table.csv', 'w+') as fd2:
                    fd2.writelines(w)
            print('------------------')
            data += list(map(lambda row: row.rstrip().split('\t'),
                             open(table).readlines()))[3:]
    return data
    
def summarize_result(tool, suite, tp, present=set()):
    data = recent_result_data([tool],[suite])
    result = types.SimpleNamespace()
    result.total = 0
    result.time = 0
    result.correct = 0
    result.timeout = 0
    result.unknown = 0
    result.safe = 0
    result.safe_time = 0.0
    result.unsafe_time = 0.0
    result.unsafe = 0
    result.actual_safe=0
    result.actual_unsafe=0
    result.times_excluding_timeouts = []
    nrecursive=0
    self_present = set()
    if tp=='Recursive':
        for entry in data:
            if ('recursive' in entry[0].split('/') or 'recursive-simple' in entry[0].split('/')):
                print("data entry looks like: ", entry)
                nrecursive+=1
                result.total += 1
                result.time += get_time(entry, 0)
                
                if (entry[1]=='true'):
                    result.actual_safe+=1
                else:
                    result.actual_unsafe+=1

                if (get_result(entry, 0) == "TIMEOUT"):
                    result.timeout += 1
                elif (get_category(entry, 0) == "correct"):
                    result.correct += 1
                    if (entry[1]=='true'):
                        result.safe+=1
                        result.safe_time += (get_time(entry, 0))
                    elif (entry[1]=='false'):
                        result.unsafe_time += (get_time(entry, 0))
                        result.unsafe+=1
                    else:
                        print('errrrrr: ',entry)
                        exit(1)
                    result.times_excluding_timeouts.append(get_time(entry, 0))
                elif (get_category(entry, 0) == "unknown"):
                    result.unknown += 1
                    result.times_excluding_timeouts.append(get_time(entry, 0))
                else:
                    result.times_excluding_timeouts.append(get_time(entry, 0))
        print('total in Recursive suite: ', nrecursive)
    if tp=='Loops':
        for entry in data:
            if (not ('recursive' in entry[0].split('/'))):
                if present!=set():
                    if not (entry[0] in present):
                        continue
#                print("data entry looks like: ", entry)
                result.total += 1
                result.time += get_time(entry, 0)
                if (entry[1]=='true'):
                    result.actual_safe+=1
                else:
                    result.actual_unsafe+=1

                if (get_result(entry, 0) == "TIMEOUT"):
                    result.timeout += 1
                    self_present.add(entry[0])
                elif (get_category(entry, 0) == "correct"):
                    self_present.add(entry[0])
                    result.correct += 1
                    if (entry[1]=='true'):
                        result.safe+=1
                        result.safe_time += (get_time(entry, 0))
                    elif (entry[1]=='false'):
                        result.unsafe_time += (get_time(entry, 0))
                        result.unsafe+=1
                    result.times_excluding_timeouts.append(get_time(entry, 0))
                elif (get_category(entry, 0) == "unknown"):
                    result.unknown += 1
                    #result.times_excluding_timeouts.append(get_time(entry, 0))
                else:
                    pass#result.times_excluding_timeouts.append(get_time(entry, 0))
    return result, self_present

def summary():
    matrix = {}

    best_time = {}
    best_correct = {}
    num = {}
    total_correct = {}
    total_time = {}
    num_timeout = {}
    times_excluding_timeout = {}
    mean_time_excluding_timeout = {}
    median_time_excluding_timeout = {}

    for tool in tools:
        total_correct[tool] = 0
        total_time[tool] = 0
        times_excluding_timeout[tool] = []
        num_timeout[tool] = 0

    suites = ['Loops']
    num_safe={}
    num_unsafe={}
    for suite in suites:
        row = {}
        best_time_suite = 999999999.0
        best_correct_suite = 0
        num_suite = 0
        num_suite_safe = 0
        num_suite_unsafe = 0
        firstRun = True 
        present=set()
        for tool in tools:
            if firstRun == True:
                r, present = summarize_result(tool, 'thesis-all', suite)
                firstRun = False 
            else: 
                r, _ = summarize_result(tool, 'thesis-all', suite, present=present)
            best_time_suite = min(best_time_suite, r.time)
            best_correct_suite = max(best_correct_suite, r.correct)
            num_suite = r.total
            num_suite_safe = r.actual_safe 
            num_suite_unsafe = r.actual_unsafe 
            row[tool] = r
            total_correct[tool] += r.correct
            total_time[tool] += r.time
            times_excluding_timeout[tool].extend(r.times_excluding_timeouts)
            num_timeout[tool] += r.timeout
        best_time[suite] = best_time_suite
        best_correct[suite] = best_correct_suite
        num[suite] = num_suite
        matrix[suite] = row
        num_safe[suite]=num_suite_safe 
        num_unsafe[suite]=num_suite_unsafe

    for tool in tools:
        mean_time_excluding_timeout[tool] = statistics.mean(times_excluding_timeout[tool])
        median_time_excluding_timeout[tool] = statistics.median(times_excluding_timeout[tool])

    print("\\begin{tabular}{@{}lc|%s@{}}" % ("|".join(["c@{}r"] * (len(tools)))))
    print("\\toprule")
    print(" &",end='')
    for tool in tools[:-1]:
        print(" & \\multicolumn{2}{c|}{%s}" % tool, end='')
    print(" & \\multicolumn{2}{c}{%s}\\\\" % tools[-1])

    print(" & \#tasks & %s\\\\\\midrule" % " & ".join(["\#correct & time"] * len(tools)))

    for suite in suites:
        print("\multicolumn{2}{c}{%s & %d}" % (suite, num[suite]),end='')
        for tool in tools:
            if (matrix[suite][tool].correct == best_correct[suite]):
                print(" & \\textbf{%d}" % (best_correct[suite]),end='')
            else:
                print(" & %d" % (matrix[suite][tool].correct),end='')

            if (matrix[suite][tool].time == best_time[suite]):
                print(" & \\textbf{%.1f}" % best_time[suite],end='')
            else:
                print(" & %.1f" % matrix[suite][tool].time,end='')
        print("\\\\")
        print (" & safe & %d" % (num_safe[suite]))
        for tool in tools:
            print(" & %d " % (matrix[suite][tool].safe), end='')
            print(" & %.1f" % matrix[suite][tool].safe_time, end='')
        print("\\\\")
        print(" & unsafe & %d"%(num_unsafe[suite]))
        for tool in tools:
            print(" & %d " % (matrix[suite][tool].unsafe), end='')
            print(" & %.1f" % matrix[suite][tool].unsafe_time, end='')
        print('\\\\')
    print("\\midrule")

    best_total_time = min(total_time.values())
    best_total_correct = max(total_correct.values())

    print("Total & %d " % sum(num.values()), end='')
    for tool in tools:
        if (total_correct[tool] == best_total_correct):
            print(" & \\textbf{%d}" % best_total_correct,end='')
        else:
            print(" & %d" % total_correct[tool],end='')

        if (total_time[tool] == best_total_time):
            print(" & \\textbf{%.1f}" % best_total_time,end='')
        else:
            print(" & %.1f" % total_time[tool],end='')
    print("\\\\")

    print("Timeouts & ", end='');
    for tool in tools:
        print(" & \\multicolumn{2}{c}{%d}" % num_timeout[tool], end='')

    print("\\\\")

    print("Mean time & ", end='');
    for tool in tools:
        print(" & \\multicolumn{2}{c}{%.1f}" % mean_time_excluding_timeout[tool], end='')

    print("\\\\")

    print("Median time & ", end='');
    for tool in tools:
        print(" & \\multicolumn{2}{c}{%.1f}" % median_time_excluding_timeout[tool], end='')

    print("\\\\")

    print("\\bottomrule")
    print("\\end{tabular}")

def make_table():
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_file = os.path.join(tmp_dir, "results.xml")
        tmp = open(tmp_file, "w")
        tmp.write(table_begin)
        for tool in tools:
            tmp.write("<union>\n")
            for suite in suites:
                tmp.write('<result filename="')
                tmp.write(os.path.join(os.getcwd(), recent_result(tool,suite)))
                tmp.write('" />\n')
            tmp.write("</union>\n")
        tmp.write(table_end)            
        tmp.close()
        os.system("table-generator -x %s -o results" % tmp_file)


def cactus_data(data, out):
    times = []
    for entry in data:
        # Only include correct benchmarks
        if get_category(entry, 0) == "correct":
            times.append(get_time(entry, 0))
    times = sorted(times)
    prev = times[0]
    last = len(times)
    for instance in range (1, last):
        if prev != times[instance]:
            prev = times[instance]
            out.write("%d %f\n" % (instance, times[instance - 1]))
    out.write("%d %f\n" % (last, times[last - 1]))

def cactus_plot():

    legend = ""
    data = ""

    for tool_name in tools:
        matrix = recent_result_data([tool_name], suites)

        print ("Writing data to %s.dat" % tool_name)
        f = open("%s.dat" % tool_name, "w")
        cactus_data(matrix, f)
        f.close()
        if legend == "":
            legend = tool_name
        else:
            legend += "," + tool_name
        data += ('    \\addplot table {%s.dat};\n' % tool_name)

    subst = dict(legend = legend,
                 data = data,
                 bench_size = len(matrix))
    print (Template(open("cactus.template").read()).substitute(subst))

def scatter_plot():
    if (len(tools) != 2):
        print("For scatter plot, must supply exactly two tools to compare")
        exit(-1)

    m1 = recent_result_data([tools[0]],[suites[0]])
    m2 = recent_result_data([tools[1]],[suites[0]])
    # Don't include points where one tool gave a wrong answer
    ok_results = ["correct", "TIMEOUT", "unknown"]

    min_time = 1
    max_time = 1

    # both correct figure
    filename_tt = "scatter_%s_%s_tt.dat" % (tools[0], tools[1])
    print ("Writing data to %s" % filename_tt)
    out = open(filename_tt, "w")
    legendentry_tt = "%s vs %s" % (tools[0], tools[1])

    for i in range(len(m1)):
        time1 = get_time(m1[i],0)
        time2 = get_time(m2[i],0)
        out.write("%f %f\n" % (time1,time2))
        min_time = min(min_time,time1,time2)
        max_time=max(max_time,time1,time2)
    out.close()
    subst = dict(min = min_time,
                 max = max_time,
                 x = tools[0],
                 y = tools[1],
                 datatt = filename_tt,
                 ttlegend = legendentry_tt
                 )
    print (Template(open("scatter.template").read()).substitute(subst))

if __name__ == "__main__":
    if (len(sys.argv) <= 1):
        print("No command provided")

    command = sys.argv[1]
    opts = sys.argv[2:]
    while(len(opts) > 0):
        if (opts[0] == "--timeout"):
            timeout = int(opts[1])
            opts = opts[2:]
        elif (opts[0] == "--tools"):
            tools = opts[1].split(",")
            opts = opts[2:]
        elif (opts[0] == "--suites"):
            suites = opts[1].split(",")
            opts = opts[2:]
        elif (opts[0] == "--no-cache"):
            cache = False
            opts = opts[1:]
        elif (opts[0] == "--replace-cached"):
            cache = False
            replace_cached = True
            opts = opts[1:]
        else:
            print("Unrecognized option: %s" % opts[0])
            exit (-1)

    if (command == "run"):
        run()
    elif (command == "table"):
        make_table()
    elif (command == "cactus"):
        cactus_plot()
    elif (command == "scatter"):
        scatter_plot()
    elif (command == "summary"):
        summary()
    else:
        print("Unknown command")
