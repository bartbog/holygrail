#!/usr/bin/env python3
# run the pipline for one file
# run in the 'main' folder!

import sys
import subprocess

def get_names(plname):
    # get last line of the file, parse to list
    # % name1, name2, ...
    with open(plname, "r") as plfile:
        lines = plfile.read().splitlines()
        lastline = lines[-1]
        if lastline.startswith('%'):
            elems = lastline[2:].split(',')
            return [e.strip() for e in elems]
    return []

# run BOS on probname, test only
def pl_test(probname):
    cmd = f"swipl -g testAll([{probname}]) -g halt main.pl"

    result = subprocess.run(cmd.split(' '), stdout = subprocess.PIPE)
    out = result.stdout
    if result.returncode != 0:
        print(f"Problem {probname}: [] --> error {result.returncode}")
    if not len(out):
        print(f"Problem {probname}: [] --> no output")
    else:
        lastline = out.splitlines()[-1]
        print(lastline.decode())

if __name__ == "__main__":
    plname = "problemsHolyGrail.pl"

    names = get_names(plname)

    for name in names:
        pl_test(name)
