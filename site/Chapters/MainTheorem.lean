/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — The main theorem chapter.

The certified statement and the short chain that produces it: restriction of scalars to
the real smooth structure on X, the model change onto EuclideanSpace ℂ (Fin 3), and the
weakening of the analytic atlas to the C¹ statement taken from Challenge.lean.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import Solution

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "The main theorem" =>

The result occupies the last sixty lines of the subject. Stated informally: the unit
sphere $`S^6 \subset \R^7` carries an atlas of $`\C^3`-valued charts whose transition
maps are holomorphic. Everything upstream — the $`(3,4,\infty)` modular family of
$`2`-tori, its three fillings, the compact complex threefold $`X` they assemble into,
the computation $`\pi_1(X) = 1`, the homology $`H_*(X;\Z) \cong H_*(S^6;\Z)`, the
Whitehead argument and the Morse theory — exists to produce one homeomorphism
$`X \simeq_t S^6`. What remains is to carry the atlas across it and to say the result
in the words the question was asked in.

Those words matter, because the whole value of a machine-checked proof rests on the
statement being the intended claim. The certified name is
`Mathoverflow1973.mathoverflow_1973`; the comparator configuration lists exactly that
name, together with the three permitted axioms `propext`, `Classical.choice` and
`Quot.sound`, and checks it against the proposition asserted in `Challenge.lean`. That
challenge statement is not this repository's own wording. It is the Formal Conjectures
rendering of MathOverflow question 1973 {citep formal.conjectures}[], reproduced with
its Apache header and its docstrings intact; the file's own note records that the
project-specific import and the conjecture metadata were removed and that the theorem
statement was aligned with `Solution.lean`. What that alignment amounts to can be
checked by eye: the `unitSphere` abbreviation and the existential that follows it are
character for character the same text in the two files, and only the proof differs —
`sorry` in one, `exact SixSphereComplexAtlas.exists_complex_atlas` in the other.

Read the formal statement in two halves. The first is
`IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1`, and the load-bearing part of it is the
field, not the index. The model with corners is taken over $`\C`, so the smoothness
index counts $`\C`-derivatives of the chart transitions. A map between open subsets of a
complex normed space that is $`\C`-differentiable once is holomorphic there, and being
holomorphic it is $`\C`-differentiable to every order. The index $`1` is therefore not a
weak form of holomorphy but holomorphy itself, and the atlas is a holomorphic atlas
rather than a smooth atlas whose charts happen to be complex-valued. The formalization
does not lean on that equivalence: it proves the $`\omega` statement, that the
transitions are complex-analytic, and weakens it — so the certified claim is a corollary
of a strictly stronger one the same file establishes.

The second half is the carrier. `unitSphere 6` unfolds to
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`, the standard sphere with the subspace
topology it inherits from $`\R^7`. That topology is supplied by instance resolution
*outside* the existential quantifier: `ChartedSpace H M` presupposes a topology on $`M`,
and the atlas produced must consist of partial homeomorphisms for the one already there.
Compatibility with the standard topology is consequently not an additional clause that
could have been forgotten, but a consequence of where the quantifier sits — no
construction is permitted to hand the sphere a topology of its own choosing.

One thing the statement does not claim is worth naming precisely. It asserts a
holomorphic atlas on the standard *topological* six-sphere; it does not assert that the
underlying smooth structure of that atlas is the standard one. The paper obtains the
stronger reading — an integrable almost complex structure on the standard *smooth*
$`S^6` — from its recognition theorem {citep alpoge.s6}[], which upgrades Smale's
homeomorphism to a diffeomorphism using the $`h`-cobordism theorem {citep milnor65}[]
and the vanishing of the group of exotic six-spheres {citep kervaire.milnor63}[]. Hopf's
question {citep hopf48}[], and the MathOverflow restatement the challenge file follows,
ask for a complex manifold whose underlying topological space is $`S^6`, and that is
what is formalized.

The saving is not an accident of drafting: it is why the endgame is a handful of
declarations long. Transporting a charted space along a bare homeomorphism
$`h : M \simeq_t N` lifts each chart through the open embedding $`h`, and the transition
maps of the lifted charts are the transition maps of the originals *unchanged*. Compatibility in any groupoid is
therefore inherited verbatim, and `ManifoldAtlasTransport.isManifold` moves
`IsManifold I n` across for every model with corners $`I` and every index $`n`,
$`\omega` included. Smale's theorem {citep smale61}[], which produces a homeomorphism,
is all the topology the transport needs; the $`h`-cobordism theorem and the computation
$`\Theta_6 = 0` are never invoked anywhere in the development, and no diffeomorphism
between $`X` and $`S^6` is ever constructed.

:::group "main-theorem"
The bridge that lets real Morse theory run on a complex manifold, the model change from
the construction's coordinates to the coordinates the question is posed in, and the two
final statements — the complex-analytic atlas on the unit six-sphere and the certified
$`C^1` form of it taken verbatim from `Challenge.lean`.
:::


Smale's recognition theorem is a statement about real smooth manifolds, and $`X` arrives
as a complex-analytic one. The two are not the same structure on the same charted space:
`IsManifold 𝓘(ℂ, E) n M` and `IsManifold 𝓘(ℝ, E) n M` assert membership of the chart
transitions in two different groupoids over the same atlas. Passing from the first to
the second is restriction of scalars, and the development isolates it as a general
lemma before applying it to $`X`.

:::theorem "thm:complex-manifold-is-real-manifold" (lean := "Mathoverflow1973.complexManifold_isRealManifold") (parent := "main-theorem")
*Theorem.* Let $`E` be a normed space over $`\R` and over $`\C` with the scalar tower
$`\R \subset \C`, and let $`M` be a topological space charted on $`E`. If $`M` is a
manifold for the model with corners $`\mathcal{I}(\C,E)` at smoothness $`n`, then it is
a manifold for $`\mathcal{I}(\R,E)` at the same $`n`.

The index ranges over `ℕ∞ω`, so the analytic case $`n = \omega` is covered along with
the finite and infinite ones. No hypothesis is placed on $`M` beyond the charted
structure: the atlas, its charts, and the topology are untouched, and only the field
against which the transition maps are differentiated changes.
:::

:::proof "thm:complex-manifold-is-real-manifold"
Manifold structure is characterized chart-locally: it suffices that for any two charts
$`e, e'` of $`M` the transition $`e^{-1} \circ e'` be $`n`-times continuously
differentiable over $`\R` on its source. Compatibility of $`e` and $`e'` in the
$`\C`-groupoid gives that transition as $`n`-times continuously differentiable over
$`\C`, and a $`\C`-differentiable map between real normed spaces obtained by restriction
of scalars is $`\R`-differentiable of the same order. The argument is three lines in
Lean and carries no geometric content, but it is the hinge on which the endgame turns:
without it the Morse-theoretic half of the proof could not see the space that the
complex-geometric half constructs. $`\blacksquare`
:::

:::theorem "thm:space-is-real-analytic-manifold" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.space_isRealAnalyticManifold") (parent := "main-theorem") (uses := "thm:complex-manifold-is-real-manifold, thm:space-is-manifold")
*Theorem.* $`X` is a real-analytic manifold on the model $`\C \times \C^2` regarded as a
real normed space: `IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ω Space`.

The complex structure on $`X` is analytic to begin with — every transition of the
star-shaped gluing is holomorphic — so restriction of scalars returns the real structure
at the same index rather than at a finite one. The model space is unchanged; only its
scalar field is. Its real dimension is $`6`, which is the numerical hypothesis the
recognition theorem consumes.
:::

:::theorem "thm:space-is-smooth-real-manifold" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.space_isSmoothRealManifold") (parent := "main-theorem") (uses := "thm:space-is-real-analytic-manifold")
*Theorem.* $`X` is a smooth real manifold: `IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ∞ Space`.

Weakening $`\omega` to $`\infty` is instance-level in Mathlib, an analytic atlas being in
particular a $`C^\infty` one. This is the hypothesis in exactly the shape Smale's
theorem takes it — `IsManifold 𝓘(ℝ, E) ∞ M` for a compact, Hausdorff, second countable
$`M` charted on a real normed space $`E` of finite rank $`6`. Every one of those side
conditions is already available for $`X`: compactness from properness of the fibration
over the projective line, the Hausdorff and second-countability properties from the
gluing, and the rank from the model space $`\C \times \C^2` itself.
:::


No mathematics remains. What is left is to name the sphere, to change coordinates on the
model space, and to say the conclusion at the regularity the question was asked at.

:::definition "def:unit-sphere" (lean := "Mathoverflow1973.unitSphere") (parent := "main-theorem")
$`\mathrm{unitSphere}\ n \;=\; \{\, x \in \mathrm{EuclideanSpace}\ \R\ (\mathrm{Fin}\ (n+1)) \;:\; \|x\| = 1 \,\}`,
the metric sphere of radius $`1` about the origin, with the subspace topology.

For $`n = 6` this is the standard six-sphere in $`\R^7`. The abbreviation is shared
character for character with `Challenge.lean`, and it also agrees definitionally with
the sphere the Morse-theoretic development works with: `Smale.SixSphere` is
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`, which is `unitSphere 6` after
unfolding $`\mathrm{Fin}\ (6+1)`. No reindexing, completion or transfer of topology
intervenes between the homeomorphism Morse theory produces and the sphere the final
statement quantifies over.
:::

:::definition "def:model-equiv" (lean := "Mathoverflow1973.SixSphereComplexAtlas.modelEquiv") (parent := "main-theorem") (uses := "def:threefold-cusp-model-equiv")
The continuous $`\C`-linear equivalence
$$`\C \times \C^2 \;\xrightarrow{\ \sim\ }\; \mathrm{EuclideanSpace}\ \C\ (\mathrm{Fin}\ 3),`
obtained as the inverse of the cusp splitting `cuspModelEquiv` followed by the inverse of
the standard identification `EuclideanSpace.equiv (Fin 3) ℂ`.

The first factor undoes the splitting-off of the base coordinate,
$`x \mapsto (x_0, (x_1,x_2))`, which put the toric cusp charts on the same model as the
regular family; the second replaces the bare function type $`\mathrm{Fin}\ 3 \to \C` by its
Euclidean-normed copy. Both are linear homeomorphisms, so re-charting along the composite
alters neither the underlying space nor the regularity of any transition map. What
changes is only the normed space in which the charts take values — from the one the
construction found convenient to the one the question is posed in.
:::

:::theorem "thm:exists-complex-atlas" (lean := "Mathoverflow1973.SixSphereComplexAtlas.exists_complex_atlas") (parent := "main-theorem") (uses := "def:model-equiv, def:unit-sphere, thm:exists-complex-analytic-atlas")
*Theorem.* There is a `ChartedSpace (EuclideanSpace ℂ (Fin 3))` structure on
`unitSphere 6` for which `IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6)`.

The same atlas as the analytic statement, with $`\omega`-compatibility weakened to
$`C^1`. The weakening is stated separately because the index $`1` is what the challenge
file asks for, and stating it separately keeps the strong form visible: the sphere does
not merely admit a complex structure in the sense of once-differentiable transitions, it
admits one with complex-analytic transitions.
:::

:::proof "thm:exists-complex-atlas"
Take the analytic atlas. Transport carries the atlas of $`X` across the homeomorphism
$`X \simeq_t S^6` with its transition maps unchanged, and re-charting along the model
equivalence $`\C \times \C^2 \simeq \mathrm{EuclideanSpace}\ \C\ (\mathrm{Fin}\ 3)`
leaves them holomorphic, so the sphere carries a `ChartedSpace (EuclideanSpace ℂ (Fin 3))`
structure that is an $`\omega`-manifold for the corresponding model with corners over
$`\C`. Keeping that atlas and asking only for index $`1` is then instance resolution:
the analytic groupoid is contained in the $`C^1` one over the same model.
$`\blacksquare`
:::

:::theorem "thm:mathoverflow-1973" (lean := "Mathoverflow1973.mathoverflow_1973") (parent := "main-theorem") (uses := "def:unit-sphere, thm:exists-complex-atlas")
*Theorem.* There is an atlas `ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6)`
making the unit six-sphere a complex manifold:
`IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6)`.

The six-sphere admits a complex structure, and Hopf's question {citep hopf48}[] — posed
in 1948, restated as {citet mathoverflow1973}[] — is answered affirmatively. The
declaration is a separate name for the proposition proved immediately above it, because
this is the proposition `Challenge.lean` states and the comparator certifies. The
in-file `#print axioms` records its dependencies as `propext`, `Classical.choice` and
`Quot.sound`, and nothing else.
:::

:::proof "thm:mathoverflow-1973"
The proof term is the previous statement, applied. Behind it stands the whole
development: the $`(3,4,\infty)` modular family of complex $`2`-tori over
the thrice-punctured projective line is completed at its three special points by a
Mumford toroidal degeneration at the cusp {citep mumford72}[] and by Kodaira logarithmic
transforms of multiplicities $`3` and $`4` at the elliptic points {citep kodaira64}[],
giving a compact complex threefold $`X` with holomorphic transitions; the twist data
$`(\ell_0,\ell_1,\ell_2) = (0,1,-1)` makes $`|12\ell_0 - 4\ell_1 - 3\ell_2| = 1`, so
$`\pi_1(X) = 1`; Mayer–Vietoris over the star-shaped cover gives
$`H_*(X;\Z) \cong H_*(S^6;\Z)`; Hurewicz and a Whitehead argument turn that into a
homotopy equivalence $`X \simeq_h S^6`, and Morse theory in the form of Smale's
generalized Poincaré theorem {citep smale61}[] turns the homotopy equivalence into a
homeomorphism; and the atlas of $`X` is transported across it and re-modelled.

Two uses of choice survive into the final term, and both are genuine: the generating
$`6`-cube of $`\pi_6(X)`, extracted from an existence statement, and the homeomorphism
$`X \simeq_t S^6` itself, which Smale's theorem delivers as a nonempty type rather than
as a preferred map. Neither is eliminable from the statement as posed, which asserts the
existence of an atlas and names none. $`\blacksquare`
:::
