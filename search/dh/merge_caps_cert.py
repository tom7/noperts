#!/usr/bin/env python3
"""Merges capcert --export certificates: charts of later files (targeted
reruns, e.g. with --only/--z_override) replace the charts of the base file with
the same kind, side, axis, sign and ratio data. The header, frame, vertices and
witnesses must agree.

Usage: merge_caps_cert.py BASE PATCH... > merged"""
import sys

def load(path):
    head, charts, cur = [], [], None
    for line in open(path):
        if line.startswith('chart '):
            cur = [line]
            charts.append(cur)
        elif line.startswith('tree '):
            cur.append(line)
        elif not line.startswith('exported'):
            head.append(line)
    return head, charts

def key(chart):
    t = chart[0].split()
    return tuple(t[1:8])  # kind side axis sign ratio ratio_coord ratio_sign

head, charts = load(sys.argv[1])
order = [key(c) for c in charts]
by = {key(c): c for c in charts}
for path in sys.argv[2:]:
    h2, c2 = load(path)
    def strip(h):  # ratio_z fields may differ between runs
        return [l for l in h if not l.startswith('cap ')]
    assert strip(h2) == strip(head), path
    for c in c2:
        assert key(c) in by, (path, key(c))
        by[key(c)] = c
bad = [k for k in order if 'F' in by[k][1].split()[1]]
sys.stdout.writelines(head)
for k in order:
    sys.stdout.writelines(by[k])
print(f'merged {len(order)} charts, {len(bad)} with failed leaves: {bad}', file=sys.stderr)
