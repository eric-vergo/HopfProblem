/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
/-
The Hopf Problem blueprint — Introduction chapter.

The question, the shape of Alpöge's construction, what the Lean development contains,
and what this site does and does not establish.  No nodes here — the presented `uses`
graph starts in the Main Theorem chapter.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Introduction" =>

Does the six-sphere carry a complex structure? The sphere $`S^6` is one of exactly two
spheres — the other is $`S^2` — admitting an almost complex structure, in its case the
one induced by the octonion cross product on the tangent spaces of the unit sphere in
the imaginary octonions. Whether $`S^6` carries an *integrable* complex structure, that
is a holomorphic atlas rather than a bundle-level one, is Hopf's question
{citep hopf48}[], open since 1948 and restated many times since, including as
{citet mathoverflow1973}[].

The question is answered affirmatively in {citet alpoge.s6}[]: there is a compact
complex threefold, fibred by two-dimensional complex tori over the projective line,
whose underlying topological space is the six-sphere. The family is the $`(3,4,\infty)`
modular family of $`2`-tori, completed over three special points of the base. What makes
the construction usable is that the completed total space is *homotopy equivalent* to
$`S^6`; a compact smooth six-manifold homotopy equivalent to the six-sphere is
homeomorphic to it, by Smale's resolution of the generalized Poincaré conjecture in
dimensions above four {citep smale61}[]. Transporting the threefold's holomorphic
atlas along such a homeomorphism produces an atlas of $`\C^3`-charts on the standard
unit sphere in $`\R^7` with holomorphic transition maps.

The formalization presented here is Boris Alexeev's, at
[`plby/HopfProblem`](https://github.com/plby/HopfProblem); the header of its
`Solution.lean` records that the majority of the Lean code was written by Codex, and
that parts of the complex-analysis and algebraic-topology developments were adapted
from Mathlib work by Yury Kudryashov and Sebastian Kumar that had not yet landed
upstream. Upstream it is a single module of some 249,000 lines carrying roughly 20,600
declarations in one namespace, `Mathoverflow1973`, built against Mathlib at tag
`v4.33.0`; this fork splits that file, declaration for declaration and in a
dependency-respecting order, into a tree of 146 modules under `HopfProblem/` whose
directories follow the chapters of this site. The final statement is not this repository's own wording: it is taken from
the Formal Conjectures rendering of the MathOverflow question
{citep formal.conjectures}[], which is also what the repository's `Challenge.lean`
states as an open goal.

This site is a presentation of that formalization, generated from the Lean sources. It
does not contribute mathematics. What it adds is navigation — a declaration registry
over the whole module, per-declaration pages with verbatim statements and proof terms,
and a dependency graph — together with the trust surfaces that say, for each claim on
the page, whether a machine established it or a person asserted it.

Read the distinction carefully, because at this scale it is the whole point. That the
Lean development compiles, is free of `sorry`, and reaches only the three standard
axioms is mechanical and rechecked on every build of this site. That
`Mathoverflow1973.mathoverflow_1973` *says* that the six-sphere admits a complex
structure — that the formal statement is the intended mathematical claim — is a reading,
not a computation, and the statement's provenance in Formal Conjectures is the evidence
offered for it rather than a proof of it. And the mathematics itself is very recent: at
the time of writing, Alpöge's argument has not been through peer review, and a
kernel-checked Lean proof is a statement about the Lean development, not a substitute
for that review.
