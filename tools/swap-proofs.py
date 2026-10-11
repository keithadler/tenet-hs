#!/usr/bin/env python3
"""Give every theorem in an export the previous theorem's proof.

usage: swap-proofs.py IN.ndjson OUT.ndjson

A kernel whose check returns true reports zero failures on a real library too, so a clean run proves nothing
about soundness. This is the negative control that goes next to it: after the swap almost every theorem is
wrong, and a kernel has to say so. Theorems whose new proof happens to have a definitionally equal type
(`eq_comm` given a proof of the same statement, say) are correctly still accepted, so the count to look for is
"nearly all", and, more usefully, the same set rejected by an independent kernel.

Streams the file, so it works on the 350 MB export of all of Init.
"""
import json
import sys


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    prev = None
    mutated = total = 0
    with open(sys.argv[1]) as src, open(sys.argv[2], "w") as out:
        for line in src:
            if line.startswith('{"thm"'):
                j = json.loads(line)
                t = j["thm"]
                t = t[0] if isinstance(t, list) else t
                total += 1
                if prev is not None and t["value"] != prev:
                    cur = t["value"]
                    t["value"] = prev
                    prev = cur
                    mutated += 1
                    line = json.dumps(j, separators=(",", ":")) + "\n"
                else:
                    prev = t["value"]
            out.write(line)
    print(f"{total} theorems, {mutated} given another theorem's proof")


main()
