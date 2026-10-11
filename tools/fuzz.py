#!/usr/bin/env python3
"""Differential fuzzer: damage an export at random points and compare two kernels' verdicts.

usage: fuzz.py EXPORT.ndjson --seeds N [--mutations K] [--hs BIN] [--tenet BIN]

Each variant changes K references in the expression table to another, earlier table entry, so the file stays
well formed and only the meaning changes. Both kernels must reject exactly the same declarations. A
disagreement is a bug in one of them, which is the point.
"""
import argparse, json, os, random, re, subprocess, sys, tempfile

def load(path):
    with open(path) as f:
        return f.read().split('\n')

def mutate(lines, rng, k):
    expr_idx = [i for i, l in enumerate(lines) if l.startswith('{"ie"') or ('"ie":' in l[:40])]
    out = list(lines)
    changed = []
    for _ in range(k):
        i = rng.choice(expr_idx)
        j = json.loads(out[i])
        me = j['ie']
        if me == 0:
            continue
        kind = [x for x in j if x != 'ie'][0]
        body = j[kind]
        other = rng.randrange(0, me)
        if kind == 'app':
            body[rng.choice(['fn', 'arg'])] = other
        elif kind in ('lam', 'forallE'):
            body[rng.choice(['type', 'body'])] = other
        elif kind == 'letE':
            body[rng.choice(['type', 'value', 'body'])] = other
        elif kind == 'proj':
            if rng.random() < 0.5:
                body['idx'] = max(0, body['idx'] + rng.choice([-1, 1]))
            else:
                body['struct'] = other
        elif kind == 'bvar':
            j['bvar'] = max(0, body + rng.choice([-1, 1]))
        elif kind == 'natVal':
            j['natVal'] = str(int(body) + rng.choice([-1, 1, 7]) if int(body) > 1 else int(body) + 1)
        elif kind == 'const':
            body['us'] = body['us']  # keep: level mutations would need the level table
        else:
            continue
        out[i] = json.dumps(j, separators=(',', ':'))
        changed.append((i, kind))
    return out, changed

def fails(output):
    return set(re.findall(r'^FAIL (\S+) (\S+)', output, re.M))

def run(cmd, env=None):
    r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=900)
    return r.stdout + r.stderr

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('export')
    ap.add_argument('--seeds', type=int, default=10)
    ap.add_argument('--first-seed', type=int, default=0)
    ap.add_argument('--mutations', type=int, default=3)
    ap.add_argument('--hs', default=os.path.expanduser('~/tenet-hs/dist-newstyle/build/aarch64-osx/ghc-9.14.1/tenet-hs-0.1.0/x/tenet-hs/build/tenet-hs/tenet-hs'))
    ap.add_argument('--tenet', default=os.path.expanduser('~/tenet/src/Tenet.Cli/bin/Release/net10.0/tenet'))
    ap.add_argument('--unfolds', type=int, default=1000000)
    a = ap.parse_args()
    lines = load(a.export)
    env = dict(os.environ, DOTNET_ROOT=os.path.expanduser('~/.dotnet'), TENET_MAX_UNFOLDS=str(a.unfolds))
    disagreements = 0
    total_fail = 0
    for seed in range(a.first_seed, a.first_seed + a.seeds):
        rng = random.Random(seed)
        mutated, changed = mutate(lines, rng, a.mutations)
        with tempfile.NamedTemporaryFile('w', suffix='.ndjson', delete=False) as f:
            f.write('\n'.join(mutated))
            path = f.name
        try:
            hs = fails(run([a.hs, 'check', path, '--quiet', '--max-unfolds', str(a.unfolds)]))
            te = fails(run([a.tenet, 'check', path], env))
        finally:
            os.unlink(path)
        total_fail += len(hs)
        status = 'agree' if hs == te else 'DISAGREE'
        print(f'seed {seed}: {len(hs)} rejected by tenet-hs, {len(te)} by tenet: {status}  {changed}')
        if hs != te:
            disagreements += 1
            print('  only tenet-hs:', sorted(hs - te)[:8])
            print('  only tenet:   ', sorted(te - hs)[:8])
    print(f'{a.seeds} variants, {total_fail} rejections in total, {disagreements} disagreements')
    sys.exit(1 if disagreements else 0)

main()
