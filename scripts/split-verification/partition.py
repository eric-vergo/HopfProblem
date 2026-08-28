#!/usr/bin/env python3
"""Split a single-file Lean development into a thematic module tree.

This is the pipeline that produced `HopfProblem/` from the original `Solution.lean`,
reconstructed as one script from the session that ran it (2026-08-27).  It is
deterministic given its inputs:

  1. the original single file (default `Solution.lean` at the pre-split commit), and
  2. the in-module dependency dump written by `01-deps-dump.lean` against the ORIGINAL
     build (`.deps-dump.txt`: a numbered constant table followed by adjacency by index).

Stages (each writes its artifact next to the previous one):

  index      parse top-level declarations (Unicode-aware identifiers, `_root_.` escapes),
             attach the leading attribute / `attribute … in` lines to the declaration they
             precede, and record line spans;
  fold       map every environment constant of the dump onto its source declaration
             (private mangling stripped, auxiliaries such as `._proof_N`, `match_N`,
             `instDecidableEq…` contracted onto their users), drop physically impossible
             forward edges (a single file elaborates top to bottom), and write the
             source-level true dependency graph;
  partition  assign a theme to every declaration (namespace rules), union private lemmas
             with all of their users (co-location atoms), run the greedy scheduler that
             closes a theme's open part whenever adding a declaration would create a cycle
             among open parts (or the part exceeds the line cap), then a merge pass that
             joins consecutive same-theme parts when no intervening part depends on the
             earlier one, and name the modules;
  emit       write the module files (per-file preamble replicated from the original;
             each module imports its predecessor), the root aggregator, and the thin
             `Solution.lean`.

The output is a linear extension of the true dependency order: a declaration may
elaborate before some declarations that textually preceded it, never before anything it
depends on.  The verification scripts in this directory check the result against a
rebuild of the original.

Usage:
  python3 partition.py index    --source Solution.lean --out work/
  python3 partition.py fold     --work work/ --dump .deps-dump.txt
  python3 partition.py partition --work work/ [--line-cap 5500] [--merge-cap 6500]
  python3 partition.py emit     --work work/ --source Solution.lean --dest . --lib HopfProblem
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
from collections import Counter, defaultdict, deque

# --------------------------------------------------------------------------- identifiers
IDCH = r"[A-Za-z0-9_'!?₀-₉ₐ-ₜᵃ-ᵸʰ-ʸΑ-ωϱ]"
DECL_RE = re.compile(
    r'^(private\s+)?(protected\s+)?(noncomputable\s+)?'
    r'(theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+'
    r'((?:_root_\.)?(?:' + IDCH + r'+\.)*' + IDCH + r'+)')
NAMESPACE = 'Mathoverflow1973'


# --------------------------------------------------------------------------- stage: index
def stage_index(source: str, out: str) -> None:
    lines = open(source, encoding='utf-8').read().split('\n')
    decls = []
    for i, ln in enumerate(lines):
        m = DECL_RE.match(ln)
        if not m:
            continue
        name = m.group(5)
        root = name.startswith('_root_.')
        decls.append({'line': i + 1, 'kind': m.group(4), 'name': name[7:] if root else name,
                      'root': root, 'private': bool(m.group(1))})
    for j, d in enumerate(decls):
        d['end'] = decls[j + 1]['line'] - 1 if j + 1 < len(decls) else len(lines)
    # head-adjusted block starts: attribute lines and multi-line `attribute … in` blocks
    # immediately above a declaration belong to it.
    for d in decls:
        h = d['line']
        while h - 2 >= 0:
            prev = lines[h - 2]
            if prev.startswith('@['):
                h -= 1
                continue
            if prev.rstrip().endswith(' in'):
                j = h - 1
                while j - 1 >= 1 and not re.match(r'^(attribute |open |set_option )', lines[j - 1]):
                    j -= 1
                if j >= 1 and re.match(r'^(attribute |open |set_option )', lines[j - 1]):
                    h = j
                    continue
            break
        d['head'] = h
    os.makedirs(out, exist_ok=True)
    json.dump(decls, open(os.path.join(out, 'decls.json'), 'w'))
    print(f'index: {len(decls)} declarations')


# --------------------------------------------------------------------------- stage: fold
def stage_fold(work: str, dump: str) -> None:
    decls = json.load(open(os.path.join(work, 'decls.json')))
    names = {d['name'] for d in decls}
    lineof = {d['name']: d['line'] for d in decls}
    raw = open(dump, encoding='utf-8').read().split('\n')
    count = int(raw[0].split()[1])
    envnames = raw[1:1 + count]
    assert raw[1 + count] == 'EDGES'
    adj_env = {}
    for ln in raw[2 + count:]:
        if not ln.strip():
            continue
        i, _, rest = ln.partition('\t')
        adj_env[int(i)] = [int(x) for x in rest.split()] if rest.strip() else []

    def to_source(e: str):
        if e.startswith('_private.'):
            e = e.split('.0.', 1)[1] if '.0.' in e else e
        if e.startswith(NAMESPACE + '.'):
            e = e[len(NAMESPACE) + 1:]
        parts = e.split('.')
        for k in range(len(parts), 0, -1):
            c = '.'.join(parts[:k])
            if c in names:
                return c
        return None

    env2src = {i: to_source(e) for i, e in enumerate(envnames)}
    memo: dict[int, set] = {}

    def expand(i: int) -> set:
        # an unmatched (compiler-generated) constant contributes its own dependencies
        if i in memo:
            return memo[i]
        s = env2src.get(i)
        if s is not None:
            return {s}
        out: set = set()
        memo[i] = out
        for j in adj_env.get(i, []):
            out |= expand(j)
        return out

    sadj: dict[str, set] = defaultdict(set)
    for i, deps in adj_env.items():
        si = env2src.get(i)
        if si is None:
            continue
        for j in deps:
            for sj in ({env2src[j]} if env2src.get(j) else expand(j)):
                if sj != si:
                    sadj[si].add(sj)
    for a in list(sadj):
        sadj[a] = {b for b in sadj[a] if lineof[b] < lineof[a]}  # forward edges are fold artifacts
    json.dump({k: sorted(v) for k, v in sadj.items()}, open(os.path.join(work, 'true-deps.json'), 'w'))
    unmatched = sum(1 for v in env2src.values() if v is None)
    print(f'fold: {sum(len(v) for v in sadj.values())} source-level edges; {unmatched} compiler-generated constants contracted')


# --------------------------------------------------------------------------- themes
def cluster_of(n: str):
    P = n.startswith
    if P(('Smale.ManifoldMorse', 'Smale.MorseHandle', 'SmoothMorseLemma', 'AdaptedWindows')) or (P('Smale') and n.count('.') == 1):
        return 'Morse'
    if P('Smale.'):
        return 'Cancellation'
    if P(('MorseCancel', 'NoExotic')):
        return 'Cancellation'
    if P('Degree'):
        return 'HomotopyEquiv'
    if P(('FirstHurewicz', 'SingularMayerVietoris', 'SphereHomology')):
        return 'HomologyTheory'
    if P(('SecondHurewicz', 'ThirdHurewicz', 'FourthHurewicz', 'FifthHurewicz', 'SixthHurewicz', 'HigherHurewicz')):
        return 'Hurewicz'
    if P(('CuspCentralHomology', 'CuspBoundaryTopVanishing', 'CuspBoundaryGammaZero')):
        return 'CuspFibre'
    if P('PeriodTorusHigherHomology'):
        return 'TorusHomology'
    if P(('FundamentalGroupVanKampen', 'MappingTorusHomology', 'MappingTorus', 'ThreefoldOverlapMappingTorus')):
        return 'Pi1'
    if P(('ThreefoldHomology', 'ThreefoldGluing')):
        return 'HomologyOfX'
    if P(('ToricCharts', 'ToricFan', 'ToricSpace', 'CuspQuotient', 'DiagonalQuotient', 'CuspHoneycombHexagon', 'CuspHoneycombTiling')):
        return 'Toric'
    if P(('CuspRetraction', 'CuspPositiveRetraction', 'CuspPositive', 'CuspControlledRetraction', 'CuspCollapse', 'CuspSpecialization', 'CuspNegation')):
        return 'CuspFibre'
    if P(('RiemannMapping', 'RiemannBoundary', 'RiemannSphere', 'AnalyticRootCover', 'TriangleUniformizationGluing', 'CuspUniformization', 'HolomorphicCousin')):
        return 'Analysis'
    if P(('SpecialPeriods.Triangle', 'SpecialPeriods.MuTorsor', 'SpecialPeriods.BetaTorsor', 'SpecialPeriods.MuGenerator', 'SpecialPeriods.ModularGermLift')) or (P('SpecialPeriods') and n.count('.') == 1):
        return 'Orbifold'
    if P(('SpecialPeriods.', 'SixSphereComplexAtlas', 'ManifoldAtlasTransport')):
        return 'Threefold'
    if P('PeriodFamily'):
        return 'PeriodFamily'
    if P('Elliptic'):
        return 'Elliptic'
    return None


def misc_theme(n: str) -> str:
    if n == 'mathoverflow_1973' or n.startswith(('SixSphereComplexAtlas', 'ManifoldAtlasTransport', 'SixSphere', 'unitSphere', 'complexManifold')):
        return 'MainTheorem'
    if re.match(r'(T₀|T₁|T₂|M₀|A₁|A₂|B₀|Lattice$|Lattice\.|LocalSystemMatrices)', n):
        return 'Lattice'
    if n.startswith(('TwistGroup', 'LatticeCuspNormalClosure')):
        return 'Pi1'
    if n.startswith(('PeriodPoint', 'PeriodDomain', 'FullPeriodMatrix', 'HolomorphicPeriodMap')):
        return 'PeriodFamily'
    if n.startswith(('CuspCoinvariants', 'TrianglePeriodFamilyHomologyAlgebra', 'TrianglePeriodFamilyHomologyLattice', 'SmallChainBiprod')):
        return 'HomologyOfX'
    if n.startswith(('ToricComponent', 'ToricSeparation', 'CuspHoneycomb')):
        return 'Toric'
    return 'Foundations'


COARSE = {'Morse': 'Recognition', 'Cancellation': 'Recognition', 'HomotopyEquiv': 'Recognition',
          'Analysis': 'Uniformization', 'Orbifold': 'Uniformization'}


def theme_of(n: str) -> str:
    t = cluster_of(n) or misc_theme(n)
    return COARSE.get(t, t)


# --------------------------------------------------------------------------- stage: partition
def stage_partition(work: str, line_cap: int, merge_cap: int) -> None:
    decls = json.load(open(os.path.join(work, 'decls.json')))
    sadj = {k: set(v) for k, v in json.load(open(os.path.join(work, 'true-deps.json'))).items()}
    lineof = {d['name']: d['line'] for d in decls}
    span = {d['name']: (d['line'], d['end']) for d in decls}  # raw spans, as in the original run
    theme = {d['name']: theme_of(d['name']) for d in decls}

    # private lemmas stay with ALL their users (union-find atoms; the atom's theme is the majority)
    users_of = defaultdict(set)
    for a, deps in sadj.items():
        for b in deps:
            users_of[b].add(a)
    parent: dict[str, str] = {}

    def find(x):
        parent.setdefault(x, x)
        r = x
        while parent[r] != r:
            r = parent[r]
        while parent[x] != r:
            parent[x], x = r, parent[x]
        return r

    for d in decls:
        if d['private']:
            for u in users_of.get(d['name'], ()):
                parent[find(d['name'])] = find(u)
    members_of_atom = defaultdict(list)
    for d in decls:
        members_of_atom[find(d['name'])].append(d['name'])
    atom_theme = {a: Counter(theme[m] for m in ms).most_common(1)[0][0] for a, ms in members_of_atom.items()}

    # greedy scheduler over open parts
    part_of, part_theme, open_part = {}, {}, {}
    seq = 0
    closed, open_parts = [], set()
    constraints, dependents = defaultdict(set), defaultdict(set)  # q in constraints[p]: q closes before p

    def open_ancestors(p):
        out, stack, seen = set(), list(constraints[p]), set()
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            if x in open_parts:
                out.add(x)
            stack.extend(constraints[x])
        return out

    def reaches_before(a, b):  # a must close before ... b ?
        stack, seen = [a], set()
        while stack:
            x = stack.pop()
            if x == b:
                return True
            if x in seen:
                continue
            seen.add(x)
            stack.extend(dependents.get(x, ()))
        return False

    def close(p):
        for a in list(open_ancestors(p)):
            if a in open_parts:
                close(a)
        if p in open_parts:
            open_parts.discard(p)
            closed.append(p)
            if open_part.get(part_theme[p]) == p:
                del open_part[part_theme[p]]

    part_lines = defaultdict(int)
    for d in decls:
        n = d['name']
        t = atom_theme[find(n)]
        p = open_part.get(t)
        if p is None:
            seq += 1
            p = seq
            part_theme[p] = t
            open_part[t] = p
            open_parts.add(p)
        for dep in sadj.get(n, ()):
            q = part_of.get(dep)
            if q is None or q == p or q not in open_parts:
                continue
            if reaches_before(p, q):
                close(p)
                seq += 1
                p = seq
                part_theme[p] = t
                open_part[t] = p
                open_parts.add(p)
            constraints[p].add(q)
            dependents[q].add(p)
        part_of[n] = p
        part_lines[p] += span[n][1] - span[n][0] + 1
        if part_lines[p] >= line_cap:
            close(p)
    while open_parts:
        for p in sorted(open_parts):
            if not (open_ancestors(p) & open_parts):
                close(p)
                break
        else:
            close(sorted(open_parts)[0])
    order = closed

    # merge pass: consecutive same-theme parts join when no part in between depends on the earlier one
    for _ in range(6):
        members = defaultdict(list)
        for d in decls:
            members[part_of[d['name']]].append(d['name'])
        plines = {p: sum(span[n][1] - span[n][0] + 1 for n in ms) for p, ms in members.items()}
        pos = {p: i for i, p in enumerate(order)}
        users_parts = defaultdict(set)
        for d in decls:
            p = part_of[d['name']]
            for dep in sadj.get(d['name'], ()):
                q = part_of[dep]
                if q != p:
                    users_parts[q].add(pos[p])
        merged, acc, merges = {}, {}, 0
        for i, P in enumerate(order):
            t = part_theme[P]
            if t in acc:
                A, ai = acc[t]
                if not any(ai < u < i for u in users_parts[A]) and plines[A] + plines[P] <= merge_cap:
                    merged[A] = P
                    plines[P] += plines[A]
                    users_parts[P] |= users_parts[A]
                    for n in members[A]:
                        part_of[n] = P
                    members[P] = members[A] + members[P]
                    merges += 1
            acc[t] = (P, i)
        order = [p for p in order if p not in merged]
        if merges == 0:
            break

    members = defaultdict(list)
    for d in decls:
        members[part_of[d['name']]].append(d['name'])
    for p in members:
        members[p].sort(key=lambda n: lineof[n])
    pos = {p: i for i, p in enumerate(order)}
    bad = sum(1 for d in decls for dep in sadj.get(d['name'], ()) if pos[part_of[dep]] > pos[part_of[d['name']]])
    assert bad == 0, f'{bad} cross-part order violations'

    def dominant(ms):
        c = Counter((n.split('.')[0] if '.' in n else '_root') for n in ms)
        return c.most_common(1)[0][0]

    namecount = Counter()
    files = []
    for p in order:
        t = part_theme[p]
        dom = dominant(members[p])
        base = 'Core' if dom in ('_root', t) else dom.replace('_', '')
        namecount[(t, base)] += 1
        files.append({'part': p, 'theme': t, 'base': base, 'n': namecount[(t, base)], 'decls': len(members[p])})
    for f in files:
        suffix = '' if namecount[(f['theme'], f['base'])] == 1 else str(f['n'])
        f['module'] = f"{f['theme']}.{f['base']}{suffix}"
    json.dump({'order': order, 'members': {str(p): members[p] for p in order}, 'files': files},
              open(os.path.join(work, 'split-plan.json'), 'w'))
    print(f'partition: {len(files)} modules across {len(set(f["theme"] for f in files))} themes; 0 order violations')


# --------------------------------------------------------------------------- stage: emit
SHORT_HDR = """/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

This module is part of the split of the original single-file `Solution.lean`
of plby/HopfProblem into a thematic module tree.  Full provenance, attribution
and copyright notices are retained in `Solution.lean` at the repository root.
Declarations are verbatim from the original file and keep their original
relative order within each module.  The modules form a single import chain
whose concatenation is a linear extension of the true dependency order of the
original file (computed from the compiled environment): a declaration may
elaborate before some declarations that textually preceded it, but never
before anything it depends on.
-/
"""


def stage_emit(work: str, source: str, dest: str, lib: str) -> None:
    decls = json.load(open(os.path.join(work, 'decls.json')))
    plan = json.load(open(os.path.join(work, 'split-plan.json')))
    mono = open(source, encoding='utf-8').read().split('\n')
    order_decls = sorted(decls, key=lambda d: d['line'])
    print_line = next(i + 1 for i, l in enumerate(mono) if l.startswith('#print axioms'))
    block = {}
    for i, d in enumerate(order_decls):
        s = d['head']
        e = order_decls[i + 1]['head'] - 1 if i + 1 < len(order_decls) else print_line - 1
        block[d['name']] = (s, e)
    first = block[order_decls[0]['name']][0]
    hdr_end = max(i + 1 for i, l in enumerate(mono[:60]) if l.strip() == '-/')
    pre = [l for l in mono[hdr_end:first - 1] if not l.startswith('import ')]
    while pre and pre[0] == '':
        pre.pop(0)
    while pre and pre[-1] == '':
        pre.pop()
    modules = []
    prev = None
    for f in plan['files']:
        mod = f"{lib}.{f['module']}"
        path = os.path.join(dest, mod.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(path), exist_ok=True)
        imp = f'import {prev}' if prev else 'import Mathlib'
        body = ['\n'.join(mono[block[n][0] - 1:block[n][1]]).strip('\n') for n in plan['members'][str(f['part'])]]
        content = SHORT_HDR + imp + '\n\n' + '\n'.join(pre) + '\n\n' + '\n\n'.join(body) + f'\n\nend {NAMESPACE}\n\nend\n'
        open(path, 'w', encoding='utf-8').write(content)
        modules.append(mod)
        prev = mod
    open(os.path.join(dest, f'{lib}.lean'), 'w', encoding='utf-8').write(SHORT_HDR + '\n'.join(f'import {m}' for m in modules) + '\n')
    big_hdr = '\n'.join(mono[:hdr_end])
    sol = big_hdr + '\n\n' + f'import {lib}\n\n' + f'#print axioms {NAMESPACE}.mathoverflow_1973\n' + (mono[print_line] + '\n' if mono[print_line].startswith('--') else '')
    open(os.path.join(dest, 'Solution.lean'), 'w', encoding='utf-8').write(sol)
    print(f'emit: {len(modules)} modules under {lib}/, {lib}.lean and Solution.lean written')


# --------------------------------------------------------------------------- main
def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('index'); p.add_argument('--source', default='Solution.lean'); p.add_argument('--out', default='work')
    p = sub.add_parser('fold'); p.add_argument('--work', default='work'); p.add_argument('--dump', default='.deps-dump.txt')
    p = sub.add_parser('partition'); p.add_argument('--work', default='work'); p.add_argument('--line-cap', type=int, default=5500); p.add_argument('--merge-cap', type=int, default=6500)
    p = sub.add_parser('emit'); p.add_argument('--work', default='work'); p.add_argument('--source', default='Solution.lean'); p.add_argument('--dest', default='.'); p.add_argument('--lib', default='HopfProblem')
    a = ap.parse_args()
    if a.cmd == 'index':
        stage_index(a.source, a.out)
    elif a.cmd == 'fold':
        stage_fold(a.work, a.dump)
    elif a.cmd == 'partition':
        stage_partition(a.work, a.line_cap, a.merge_cap)
    elif a.cmd == 'emit':
        stage_emit(a.work, a.source, a.dest, a.lib)


if __name__ == '__main__':
    main()
