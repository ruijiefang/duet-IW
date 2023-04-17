

import subprocess as sp

logs = list(filter(lambda x: '.c.out.log' in x, sp.getoutput('ls').split('\n')))

def isin(s, f):
    for line in f:
        if s in line:
            return True
    return False

def pt(fname):
    return fname.rstrip('.out.log')

def runningtime(f):
    for line in f:
        if 'real\t' in line:
            return line.lstrip('real\t').rstrip('\n') 
    return None

print('filename, status, runtime')

for logfile in logs:
    with open(logfile) as fd:
        f = fd.readlines()
    if isin('proven safe', f):
        print(pt(logfile), ', SAFE, ', runningtime(f))
    elif isin('proven unsafe', f):
        print(pt(logfile), ', UNSAFE, ', runningtime(f))
    elif isin('Failure', f):
        #print(pt(logfile), ', CALLUIMPT, ', '0')
        continue
    elif isin('execution timeout', f):
        print(pt(logfile), ', TIMEOUT, ', '0')
    else:
        #print(pt(logfile), ", MYSTERY, ", '0')
        continue

#print('#logfiles: ', len(logs))

#print(logs)
