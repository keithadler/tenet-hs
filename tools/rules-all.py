#!/usr/bin/env python3
"""Sum rule-coverage counts over many exports.

usage: rules-all.py BIN FILE_OR_DIR...

Runs `BIN check FILE --summary --rules` on every .ndjson file (directories are searched recursively) and adds up
how often each kernel rule fired. A rule left at zero is a part of the kernel no input has exercised, however
many declarations passed through. Rules that cannot be reached by construction are listed separately.
"""
import os
import re
import subprocess
import sys


def files(args):
    for a in args:
        if os.path.isdir(a):
            for root, _, names in os.walk(a):
                for n in sorted(names):
                    if n.endswith(".ndjson"):
                        yield os.path.join(root, n)
        else:
            yield a


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    binary, inputs = sys.argv[1], list(files(sys.argv[2:]))
    totals, desc, subsumed, order = {}, {}, {}, []
    for f in inputs:
        r = subprocess.run([binary, "check", f, "--summary", "--rules"], capture_output=True, text=True, timeout=1800)
        for line in r.stdout.splitlines():
            m = re.match(r"  (\w+)\s+(\d+)\s+(.*?)(?:  \[unreachable: (.*)\])?$", line)
            if m:
                name, n, d, why = m.group(1), int(m.group(2)), m.group(3), m.group(4)
                if name not in totals:
                    order.append(name)
                totals[name] = totals.get(name, 0) + n
                desc[name] = d
                if why:
                    subsumed[name] = why
    print(f"{len(inputs)} files")
    for name in order:
        note = f"  [unreachable: {subsumed[name]}]" if name in subsumed and totals[name] == 0 else ""
        print(f"  {name:20}{totals[name]:>14}  {desc[name]}{note}")
    missing = [n for n in order if totals[n] == 0 and n not in subsumed]
    print("every reachable rule fired" if not missing else "never fired: " + ", ".join(missing))


main()
