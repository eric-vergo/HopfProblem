# Formalization of the solution to the Hopf problem

The six-sphere admits a complex manifold structure compatible with its standard topology.

Based on [*A compact complex threefold fibred by tori over the projective line, and the six-sphere*](https://alpo.ge/s6.pdf), originally [shared on X](https://x.com/__alpoge__/status/2091639597193368014) by [Levent Alpöge](https://alpo.ge/).

The repository includes a Comparator setup, with the statement adapted from the [Formal Conjectures project](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Mathoverflow/1973.lean).

```sh
lake update
lake exe cache get
lake build lean4export
lake exe comparator comparator/config.json
```

[Type-check it online!](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2Fplby%2FHopfProblem%2Frefs%2Fheads%2Fmaster%2FSolution.lean)

## Repository layout (this fork)

This fork of [plby/HopfProblem](https://github.com/plby/HopfProblem) keeps the
formalization byte-for-byte at the level of declarations, but splits the original
single 248,818-line `Solution.lean` into a thematic module tree, and adds a
[blueprint website](site/) presenting it.

- `Solution.lean` — the certified module. It now carries the full original file header
  (provenance, attribution, licence notices), `import HopfProblem`, and the
  `#print axioms Mathoverflow1973.mathoverflow_1973` check. The comparator
  configuration in `comparator/config.json` is unchanged.
- `HopfProblem.lean` — imports every module of the tree, in elaboration order.
- `HopfProblem/` — 146 modules in 15 directories. Each module imports its
  predecessor, so the tree is a single import chain whose concatenation is a linear
  extension of the original file's true dependency order (computed from the compiled
  environment, term-level `usedConstants`): a declaration may elaborate before some
  declarations that textually preceded it, never before anything it depends on. Within
  a module, declarations keep their original relative order. Private lemmas stay in the
  same module as their users, with two exceptions that were made public
  (`SpecialPeriods.TauCusp.exists_upperHalfPlane_qParam_small_mo1973_17412`,
  `…isOpen_qParam_norm_lt_mo1973_17413`); no other declaration text was edited.

| Directory | modules | declarations | lines | contents |
|---|---:|---:|---:|---|
| `HopfProblem/Recognition/` | 16 | 4,290 | 82,822 | Morse theory, critical-point cancellation and Smale's theorem (a homotopy 6-sphere is homeomorphic to $S^6$), plus the Hurewicz/Whitehead route from homology to a homotopy equivalence (`Degree.*`) |
| `HopfProblem/Uniformization/` | 15 | 3,232 | 31,543 | complex analysis (Riemann mapping, Hurwitz, root covers, Cousin patching, quotient-manifold constructions) and the uniformization of the $(3,4,\infty)$ orbifold |
| `HopfProblem/Hurewicz/` | 5 | 2,192 | 22,155 | the degree-by-degree Hurewicz ladder on $X$ |
| `HopfProblem/PeriodFamily/` | 14 | 1,909 | 21,460 | the period functions $\tau,\mu,\beta$, admissibility, and the family of 2-tori over the thrice-punctured line (paper §3) |
| `HopfProblem/CuspFibre/` | 8 | 2,031 | 20,702 | homology of the cusp fibre $W$ and the retraction/collapse machinery (paper §7.2) |
| `HopfProblem/Threefold/` | 13 | 1,424 | 15,558 | the star-shaped gluing that assembles $X$, its compactness and complex structure, simple connectivity, and the vertical $\mathbb C^\times$-action (paper §6) |
| `HopfProblem/HomologyOfX/` | 11 | 917 | 10,603 | the global Mayer–Vietoris assembly $H_*(X;\mathbb Z)\cong H_*(S^6;\mathbb Z)$ (paper §7) |
| `HopfProblem/Toric/` | 7 | 1,074 | 9,554 | the toric filling at the cusp: honeycomb fan, toric threefold, the $\mathbb Z^2$-quotient and the central fibre $W$ (paper §4) |
| `HopfProblem/TorusHomology/` | 9 | 784 | 9,235 | homology of tori and product tori |
| `HopfProblem/Elliptic/` | 8 | 1,009 | 8,687 | the logarithmic transforms at the two elliptic points (paper §5) |
| `HopfProblem/Pi1/` | 7 | 625 | 5,931 | the fundamental group: mapping tori, van Kampen, the twist-group arithmetic $\pi_1(X)\cong\mathbb Z/|12\ell_0-4\ell_1-3\ell_2|$ (paper §7) |
| `HopfProblem/HomologyTheory/` | 7 | 604 | 5,193 | singular homology from scratch: simplices, chains, Mayer–Vietoris, sphere homology, the first Hurewicz map |
| `HopfProblem/Foundations/` | 18 | 438 | 4,809 | shared infrastructure that no single theme owns (covering quotients, van Kampen helpers, from-scratch classical topology) |
| `HopfProblem/MainTheorem/` | 6 | 55 | 382 | the endgame: atlas transport along the homeomorphism and the final theorem |
| `HopfProblem/Lattice/` | 2 | 25 | 106 | the lattice $V=\mathbb Z^4$, the monodromy matrices $T_1,T_2,T_0$ and their duals (paper §2) |

### Verification of the split

The split tree was checked against a rebuild of the original single-file module on the
same toolchain (both builds green, `#print axioms Mathoverflow1973.mathoverflow_1973`
reporting `[propext, Classical.choice, Quot.sound]` in each):

- the set of non-auxiliary constants (22,232 declarations, `private` names compared
  after de-mangling) is identical before and after; the only differences in the full
  constant list are compiler-generated auxiliaries (`_proof_N`, `_simp_N_M`,
  `match_N` splitters) whose numbering is per module;
- the statement (type) of every one of those declarations was compared by hash after
  de-mangling private names: 22,134 hash identically, and the remaining 98 pretty-print
  identically except for a single `match` on `Elliptic.Kind` whose matcher the original
  file shared with an earlier declaration (`Elliptic.Kind.order.match_1`) and the split
  mints afresh — matcher reuse in Lean is module-local. No statement changed meaning.

Module names within a directory follow the dominant namespace of the module
(`Recognition/MorseCancel3.lean`, `Toric/ToricSpace.lean`, …); numbered suffixes mark
successive slices of one namespace forced apart by the interleaving of the original
file.

### Building

```sh
lake exe cache get      # Mathlib oleans (toolchain v4.33.0, mathlib tag v4.33.0)
lake build              # Challenge + Solution (pulls the whole HopfProblem tree)
```

The blueprint site lives in [`site/`](site/) and has its own README section below.

## The blueprint site (`site/`)

A browsable presentation of the formalization, generated from the Lean sources with the
[Showcase](https://github.com/eric-vergo/Showcase) blueprint genre for
[Verso](https://github.com/eric-vergo/verso): an introduction and seventeen chapters
following Alpöge's paper, 429 declaration nodes with informal statements (and proof
sketches for the main results), a dependency graph, a registry of all ~20,600
declarations with per-declaration pages, and trust surfaces that separate what a machine
established from what a person asserted (axiom audit, comparator verdict, statement
provenance).

The node prose was written by Opus 5 agents from the Lean statements, the paper and
cluster digests, then put through an independent adversarial faithfulness pass (one
checker per chapter, three-judge panels on disputed verdicts): 405 of 429 nodes were
confirmed faithful as written, 23 minor slips and 1 misstatement were rewritten. The
per-node ledger is part of the external review record (`codex-audit/`).

```sh
cd site
lake build Contents                                  # compiles the site against the subject
rm -rf _out/site && lake env lean --run Main.lean --output _out/site
```

The site pins the same toolchain and Mathlib tag as the subject and imports the
`Solution` module by name; the generated output is fully self-contained (no off-origin
assets). `Challenge.lean` is never imported by the site, since it states the goal with
`sorry`.

| Chapter | Subject directory |
|---|---|
| Introduction | — |
| The lattice and monodromy data | `HopfProblem/Lattice/` |
| Analytic and quotient-manifold foundations · Uniformizing the (3,4,∞) orbifold | `HopfProblem/Uniformization/`, `HopfProblem/Foundations/` |
| The period family over the thrice-punctured line | `HopfProblem/PeriodFamily/` |
| The toric filling at the cusp | `HopfProblem/Toric/` |
| The logarithmic transforms at the elliptic points | `HopfProblem/Elliptic/` |
| Assembling the threefold | `HopfProblem/Threefold/` |
| Singular homology from scratch | `HopfProblem/HomologyTheory/` |
| Homology of tori | `HopfProblem/TorusHomology/` |
| The cusp fibre and its collapse | `HopfProblem/CuspFibre/` |
| The fundamental group | `HopfProblem/Pi1/` |
| The homology of the threefold | `HopfProblem/HomologyOfX/` |
| The Hurewicz ladder | `HopfProblem/Hurewicz/` |
| The homotopy equivalence with the six-sphere · Morse theory on manifolds · Cancellation and the two-critical-point theorem | `HopfProblem/Recognition/` |
| The main theorem | `HopfProblem/MainTheorem/` |
