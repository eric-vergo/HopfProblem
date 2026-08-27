/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — the cusp fibre and its collapse.

Paper §7.2–§7.3 and Appendix A: the toric filling of the cusp neighbourhood strongly
deformation retracts onto its normal-crossings central fibre W, and the integral homology
of W is computed, both directly and as the monodromy coinvariants of the nearby 4-torus.
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

#doc (Manual) "The cusp fibre and its collapse" =>

The fibration $`f:X\to\PP^1` of {citet alpoge.s6}[] degenerates over three points of the
base. Over two of them the fibre is a multiple bielliptic surface and the local monodromy
has finite order; over the third, the cusp $`p_0`, the monodromy $`M_0` is unipotent and
the fibre is not a torus at all. What sits there instead is $`W`, a compact reduced
normal-crossings surface: in the paper's description, a degree-six del Pezzo surface glued
to itself along three rational curves through two triple points, with Euler number $`2`.
It arises as the central fibre of a Mumford-style toric degeneration divided by a lattice
of twisted deck transformations — the filling constructed in §4 and formalized in the
cusp-model chapters.

Two things about that filling are needed downstream, and this chapter establishes both.
The first is geometric: the filling retracts onto $`W`, strongly and with enough control
that the retraction's restriction to each nearby fibre is a named map rather than an
unknown one. That is the paper's Proposition 7.2, and it is what licenses replacing the
cusp tube by $`W` in every Mayer–Vietoris argument. The second is homological: $`H_*(W;\Z)`
is free of ranks $`(1,2,4,2,1)`, and the specialization map from a nearby fibre — a real
$`4`-torus — onto $`W` is surjective in every degree with kernel exactly the image of
$`\Lambda^q M_0-I`. That is Propositions 7.11 and 7.12, the vanishing-cycle description
of the cusp fibre as the module of monodromy coinvariants. A third, narrower fact closes
the chapter: the fundamental degree-$`4` class of the boundary of the cusp neighbourhood
dies in the filling, which is the local input that forces $`H_4(X)=0` in the global ladder.

None of this is imported from a library. There is no cofibration theory, no CW structure,
no nearby-cycle sheaf and no spectral sequence anywhere in the development: the homology is
the file's own singular theory with $`\Z` coefficients, every retraction is an explicit
continuous map with hand-written continuity proofs, and the $`A_2` honeycomb cell structure
of Appendix A is reduced to a single hexagonal Minkowski gauge — three absolute values —
so that collars, annuli and frontiers become elementary inequalities. The price is
redundancy, paid openly: the same radial Mayer–Vietoris analysis is executed three times,
on $`W`, on the base torus and on their product, solely to obtain naturality of the
connecting homomorphisms.

# The retraction

:::group "cusp-retraction"
The cusp filling deformation retracts onto its central fibre, and the retraction can be
forced to realise a prescribed collapse map on any chosen level of the tube. The
construction is run for a constant, purely imaginary period matrix, where the deck action
preserves the positive orthant of each toric chart, and then transported back by a gauge
change and a polar decomposition.
:::

The period family enters as a holomorphic matrix-valued function $`C` on a disc, twisting
the $`\Z^2` deck action by $`\exp(2\pi i\,C(t)v)`. Nothing in the retraction depends on
$`C` varying, so the first move is to freeze it.

:::definition "def:cusp-retraction-change-twist" (lean := "Mathoverflow1973.CuspRetraction.changeTwist") (parent := "cusp-retraction") (uses := "def:cusp-uniformization-exponential, def:toric-space-time")
For two period-matrix families $`C,D:\C\to M_2(\C)`, the gauge transformation
`changeTwist C D` moves a point $`x` of the toric total space by the exponential fibre
action of the correction vector
$`\bigl(D(t)-C(t)\bigr)\cdot\mathrm{invDisp}_C\bigl(t,\mathrm{position}\,x\bigr)`, where
$`t=\mathrm{time}\,x`. It preserves the time coordinate and is the identity wherever
$`t=0`, so it fixes the central fibre pointwise; under the small-drift bounds it is
continuous, with inverse `changeTwist D C`. Its purpose is the intertwining lemma proved
just after it: `changeTwist C D` carries the $`C`-twisted deck action to the $`D`-twisted
one. Taking $`D` to be the constant family $`t\mapsto C(0)` straightens a varying period
family to a frozen one, which is Lemma 7.5 of the paper.
:::

:::definition "def:cusp-positive-positive-twist" (lean := "Mathoverflow1973.CuspPositive.positiveTwist") (parent := "cusp-retraction")
$`\mathrm{positiveTwist}(C_0)` is the constant family whose value is the purely imaginary
matrix with entries $`i\,\mathrm{Im}(C_0)_{jk}`. It has the same drift matrix as the frozen
family $`t\mapsto C_0`, so the two are interchangeable in every estimate, but its deck
multipliers are positive reals: the $`\Z^2`-action it defines preserves the positive part
of each toric chart. The entire retraction is built there, on the closed orthant where the
local equation of the central fibre is the product of the coordinates, and only afterwards
spread by phases and conjugated back. The bridge is the polar decomposition of the frozen
deck action: translation by $`v` for the frozen twist equals a compact-torus phase times
translation by $`v` for the positive twist.
:::

On the orthant $`\{r\in\R^3:r\ge0\}` with height $`r_0r_1r_2`, the elementary collapse
$`r\mapsto r-s\cdot\min_i r_i` pushes every point to the boundary and fixes it once there.
Turning that local move into a global deformation is the only genuinely soft step in the
construction, and it is done with a small reusable theory rather than with regular
neighbourhoods.

:::definition "def:patching-local-collapse" (lean := "Mathoverflow1973.CuspRetraction.Patching.LocalCollapse") (parent := "cusp-retraction")
Fix $`f\in C(X,\R)`. A local collapse for $`f` is a homotopy $`h:[0,1]\times X\to X` with
$`h_0=\mathrm{id}`, fixing the zero set $`\{f=0\}` pointwise and never increasing $`f` —
so $`f(h_s(x))\le f(x)` for all $`s` and $`x` — together with an open set on which the
endpoint already lies in the zero set, $`f(h_1(x))=0`. The Lean structure carries seven
fields: the homotopy and the collapse set as data, and the five conditions they satisfy.
Local collapses compose and finitely combine, and the point of the theory is the patching
lemma: if $`f` is nonnegative, $`\{f\le r\}` is compact for some $`r>0`, and every point
of $`\{f=0\}` lies in the collapse set of some local collapse, then a single local
collapse absorbs an entire sublevel $`\{f\le\eta\}` with $`0<\eta\le r`. This is what
stands in for the usual assertion that a regular neighbourhood deformation retracts onto
its core.
:::

:::definition "def:quotient-central-fibre" (lean := "Mathoverflow1973.CuspRetraction.QuotientCentralFibre") (parent := "cusp-retraction") (uses := "def:cusp-quotient-quotient-space")
$`W` is the subspace of the cusp filling $`\mathrm{QuotientSpace}\,C\,\varepsilon` on which
the projection to the base vanishes. In Lean it is a subtype cut out by the single equation
$`\mathrm{projection}\,q=0`, so membership carries no other data. It is the target of every
retraction in this chapter and the space whose homology is computed — the most heavily
referenced object of the cusp development. Its classical description as a normal-crossings
surface with three double curves and two triple points is never used directly; what is used
is the honeycomb parametrisation established below, which presents $`W` as a quotient of
$`T^2_{\mathrm{fib}}\times(\text{closed hexagon})`.
:::

:::theorem "thm:exists-closed-quotient-strong-deformation-retraction" (lean := "Mathoverflow1973.CuspPositiveRetraction.exists_closed_quotient_strongDeformationRetraction") (parent := "cusp-retraction") (uses := "def:cusp-positive-positive-twist, def:cusp-retraction-change-twist, def:patching-local-collapse, def:quotient-central-fibre, thm:cusp-quotient-proper-action")
*Theorem.* Let $`C` be analytic on the ball of radius $`r` about the origin, entry by
entry. Then there is $`\eta_0\in(0,\min(r,1))` such that for every $`0<\eta\le\eta_0` the
closed tube $`\{\,\|\mathrm{projection}\|\le\eta\,\}` inside the cusp filling admits a
retraction $`R` onto $`W`: $`R\circ\iota=\mathrm{id}_W`, and there is a homotopy rel $`W`
from the identity of the tube to $`\iota\circ R` along which $`\|\mathrm{projection}\|`
never increases. Analyticity is `ContDiffOn ℂ ω` on `Metric.ball 0 r` for each entry; the
monotonicity clause is not in the paper's statement, and is what later permits the
retraction to be cut down to a level set.
:::

:::proof "thm:exists-closed-quotient-strong-deformation-retraction"
Straighten $`C` to the frozen family by `changeTwist`, and replace the frozen family by its
positive twist, which has the same drift bound and acts on the positive part of the toric
space with positive real multipliers. On the closed positive tube the lattice acts freely
and properly discontinuously, so the quotient is a compact Hausdorff space carrying the
continuous height $`\|\mathrm{time}\|`. Every point of the central fibre has an orthant
chart in which that height is the product of the coordinates, and the elementary shrink
$`r\mapsto r-s\cdot\min_i r_i` is a local collapse there; the patching lemma turns this
family of local collapses into one deformation absorbing a whole sublevel. Lifting through
the covering gives an equivariant deformation $`P` of the closed positive tube with
$`P_0=\mathrm{id}`, $`P` fixing the central fibre, $`P_1` landing in it and
$`\|\mathrm{time}\|` non-increasing. Spreading $`P` over the whole tube along the proper
polar quotient map, and conjugating back by the straightening homeomorphism, yields the
corresponding deformation for the true family $`C`; it is equivariant, so it descends
along the quotient map to the filling. This is the paper's Lemmas 7.5 through 7.9 in the
order they are used. $`\blacksquare`
:::

The retraction alone gives $`W\simeq` the cusp neighbourhood, which settles the low-degree
homology. For the specialization map it is not enough to know that some retraction exists:
one has to know what it does on a nearby fibre. The next three items supply an explicit
model of $`W`, then a retraction whose endpoint on a chosen level is that model's collapse.

:::definition "def:central-collapse-equiv" (lean := "Mathoverflow1973.CuspCollapse.centralCollapseEquiv") (parent := "cusp-retraction") (uses := "def:cusp-positive-positive-twist, def:quotient-central-fibre, def:toric-space-ray-divisor")
Write $`C_0=C(0)`. The central collapse model is the quotient of
$`T^2_{\mathrm{fib}}\times(\text{positive central fibre})` by the relation declaring
$`(u',q')\sim(u,q)` when $`q'` is the positive deck translate of $`q` by some $`v\in\Z^2`
and $`u'^{-1}\bigl(\mathrm{deckFibrePhase}\,C_0\,v\cdot u\bigr)` stabilises $`q'` in the
compact fibre torus. `centralCollapseEquiv` is a bijection of this model with $`W`. It
depends on $`C` only through $`C_0` and not at all on the tube radius: the combinatorial
type of the central fibre is frozen at the cusp. The statement is an equivalence of types,
not a homeomorphism — continuity of the collapse comes separately, from the proper-quotient
lemmas for the polar map.
:::

:::theorem "thm:exists-closed-quotient-controlled-strong-deformation-retraction" (lean := "Mathoverflow1973.CuspControlledRetraction.exists_closed_quotient_controlled_strongDeformationRetraction") (parent := "cusp-retraction") (uses := "def:cusp-retraction-change-twist, def:patching-local-collapse, def:quotient-central-fibre, thm:compatible-cell-homeomorph-opposite")
*Theorem.* Same hypotheses, stronger conclusion: for analytic $`C` there is $`\eta_0` such
that for every $`0<\eta\le\eta_0` and every level radius $`0<\rho\le\eta` the retraction
$`R` of the closed $`\eta`-tube onto $`W` — rel $`W`, with non-increasing projection norm —
can be chosen so that at every point of time-norm exactly $`\rho` it equals
$`\mathrm{centralProject}\circ\mathrm{straightenedPrescribedCollapse}`, the explicit
honeycomb collapse. The proof splices that endpoint into the deformation by a tent-shaped
interpolation weight and pushes the result through the same polar and straightening
transports as before.
:::

:::definition "def:actual-quotient-fibre" (lean := "Mathoverflow1973.CuspControlledRetraction.ActualQuotientFibre") (parent := "cusp-retraction") (uses := "def:cusp-quotient-quotient-space")
For $`t\in\C`, the fibre of the cusp filling over $`t` is the subtype of
$`\mathrm{QuotientSpace}\,C\,r` cut out by $`\mathrm{projection}\,q=t`. For $`t\ne0` it is
one of the tori of the family — a complex $`2`-torus, hence a real $`4`-torus — and for
$`t=0` it is $`W`. The type is defined uniformly in $`t`; the conditions $`t\ne0` and
$`\|t\|\le\eta` are carried as explicit hypotheses on each statement about it rather than
built into the definition.
:::

:::definition "def:prescribed-actual-fibre-collapse" (lean := "Mathoverflow1973.CuspControlledRetraction.prescribedActualFibreCollapse") (parent := "cusp-retraction") (uses := "def:actual-quotient-fibre, def:cusp-retraction-change-twist, def:quotient-central-fibre, thm:compatible-cell-homeomorph-opposite")
For $`t\ne0` with $`\|t\|\le\eta<r`, the specialization map
$`\mathrm{ActualQuotientFibre}\,C\,r\,t\to W` is the descent, along the homeomorphism
identifying the level $`\{\mathrm{projection}=t\}` of the closed tube with the fibre, of
$`\mathrm{centralProject}\circ\mathrm{straightenedPrescribedCollapse}`. It is the formal
stand-in for "include the nearby smooth fibre and retract onto the special fibre", written
as a map in its own right so that it can be compared with a standard torus model.
Continuity is deliberately not part of the definition: it is obtained only once a
retraction is known to realise this map.
:::

:::theorem "thm:exists-controlled-actual-fibre-retraction" (lean := "Mathoverflow1973.CuspControlledRetraction.exists_controlled_actual_fibre_retraction") (parent := "cusp-retraction") (uses := "def:prescribed-actual-fibre-collapse, thm:exists-closed-quotient-controlled-strong-deformation-retraction")
*Theorem.* There is $`\eta_0>0` such that for every $`0<\eta\le\eta_0` and every $`t\ne0`
with $`\|t\|\le\eta` the closed $`\eta`-tube admits a strong deformation retraction onto
$`W`, rel $`W` and with non-increasing projection norm, whose restriction to the fibre over
$`t` is exactly `prescribedActualFibreCollapse` — which is therefore continuous. In
homology this says the specialization map is the inclusion of the fibre into the tube
followed by the retraction. Every later comparison of $`H_*(\text{fibre})` with $`H_*(W)`
runs through this equality.
:::

The fibre over $`t\ne0` is a $`4`-torus, but abstractly so; to compute with it one needs a
marking. The source of the honeycomb collapse is untwisted by a phase character into a
product and then identified with the standard torus $`(S^1)^4`, and the resulting map is
the model against which every nearby fibre is measured.

:::definition "def:marked-collapse" (lean := "Mathoverflow1973.CuspSpecialization.markedCollapse") (parent := "cusp-retraction") (uses := "def:period-torus-higher-homology-product-torus, def:quotient-central-fibre, thm:compatible-cell-homeomorph-opposite")
The source model of the honeycomb collapse is the quotient of
$`T^2_{\mathrm{fib}}\times(\text{honeycomb plane})` by the deck action. Shearing by the
source phase character, which sends each lattice cusp vector to the corresponding deck
fibre phase, untwists it into a product, and a further marking identifies that product with
the standard torus $`(S^1)^4`. `markedCollapse` is the honeycomb collapse read through the
identification: a continuous map $`(S^1)^4\to W`. Its structural property is monodromy
invariance — precomposition with the torus map of the integral matrix $`M_0` changes it
only up to homotopy — so the induced map on homology annihilates the image of
$`(M_0)_*-\mathrm{id}` and factors through the coinvariants.
:::

:::theorem "thm:exists-original-marked-specialization-models" (lean := "Mathoverflow1973.CuspSpecialization.exists_original_marked_specialization_models") (parent := "cusp-retraction") (uses := "def:homeomorph-homology-equiv, def:marked-collapse, def:prescribed-actual-fibre-collapse, def:singular-homology-map")
*Theorem.* There is $`\eta_0>0` such that every $`t\ne0` with $`\|t\|\le\eta_0` admits a
homeomorphism $`E:(S^1)^4\cong\mathrm{ActualQuotientFibre}\,C\,r\,t` with the following
property for every admissible $`\eta`: the prescribed fibre collapse is continuous, its
composite with $`E` is homotopic to `markedCollapse`, and the two induce the same map on
singular homology once $`E`'s homology isomorphism is inserted. Every nearby fibre is thus
a marked $`4`-torus whose specialization to $`W` is the standard model one — the formal
counterpart of the paper's remark that at any other level the retraction restricts to a map
homotopic to one of the same description.
:::

:::theorem "thm:exists-controlled-retraction-all-levels" (lean := "Mathoverflow1973.CuspCentralHomology.exists_controlled_retraction_all_levels") (parent := "cusp-retraction") (uses := "def:singular-homology-map, thm:exists-controlled-actual-fibre-retraction")
*Theorem.* There is $`\eta_0>0` such that for all $`0<\eta\le\eta_0` with $`\eta<r`, and
any base level $`t_0\ne0` with $`\|t_0\|\le\eta`, the closed $`\eta`-tube admits a
retraction $`R` onto $`W`, rel $`W` and with non-increasing projection norm, which on the
fibre over $`t_0` is literally the prescribed collapse and on the fibre over every other
$`t\ne0` of norm at most $`\eta` is homotopic to it — hence induces the same map on
homology in every degree. A single retraction therefore computes the specialization at all
levels of the tube simultaneously, which is the form the global gluing consumes.
:::

The cusp piece also carries a symmetry that the gluing needs. The point symmetry of the
$`A_2` triangulation lifts to a holomorphic involution of the toric model, and the last two
items of this section record that it extends the fibrewise $`-1` of the boundary.

:::definition "def:cusp-negation-toric-negation" (lean := "Mathoverflow1973.CuspNegation.toricNegation") (parent := "cusp-retraction") (uses := "def:toric-fan-triangle, def:toric-space-space")
On the chart of the triangle $`s=(a,b,\mathrm{upper})` the negation reverses the three
coordinates and lands in the chart of
$`\mathrm{triangleNeg}\,s=(-a-1,-b-1,\lnot\,\mathrm{upper})`, the point symmetry of the
$`A_2` triangulation. These chart maps agree on overlaps and so descend to a map
`toricNegation` of the toric total space. It preserves the time coordinate, is an
involution, is holomorphic as a map of complex manifolds, and conjugates the twisted deck
translation by $`v` to the one by $`-v`; consequently it descends to the tube and to the
cusp quotient, giving the $`-1` involution of the filling.
:::

:::theorem "thm:boundary-to-filling-neg" (lean := "Mathoverflow1973.CuspNegation.boundaryToFilling_neg") (parent := "cusp-retraction") (uses := "def:cusp-negation-toric-negation, def:piece-mapping-torus-homotopy-equiv, def:punctured-cusp-cover, def:threefold-projection")
*Theorem.*
$`\mathrm{boundaryToFilling}\circ\mathrm{boundaryNeg}=\mathrm{specialCapMap}\circ\mathrm{boundaryToFilling}`,
where `boundaryNeg` is $`x\mapsto-x` on each $`4`-torus fibre of the cusp boundary mapping
torus and `specialCapMap` is the involution that `toricNegation` induces on the threefold's
special cusp piece. The fibrewise negation of the boundary therefore extends over the cusp
filling.
:::

:::proof "thm:boundary-to-filling-neg"
Both sides are continuous maps out of the boundary mapping torus, so it suffices to compare
them pointwise. The boundary-to-filling map at the cusp factors through the boundary
cylinder of the cusp family, and on that cylinder the toric negation acts by
$`(t,x)\mapsto(t,-x)` — this is the computation `quotientNegation_boundaryCylinder`, which
in turn is the statement that `toricNegation` conjugates twisted translation by $`v` into
twisted translation by $`-v`. Reading the identity through the descent to the special cusp
piece gives `specialCapMap_specialBoundaryToPiece`, and the theorem is that identity with
the composition written the other way round. $`\blacksquare`
:::

# The homology of the central fibre

:::group "cusp-homology"
The integral homology of $`W` is computed by Mayer–Vietoris over a radial cover coming from
the $`A_2` honeycomb cell structure, and is then identified with the module of monodromy
coinvariants of the nearby $`4`-torus. The degree-$`4` class of the cusp boundary is shown
to die in the filling.
:::

Everything rests on one soft lemma about covers by two contractible open sets, and on an
unreduced suspension built by hand to supply examples of such covers. Both are general
constructions, reused elsewhere in the development for the homology of spheres.

:::definition "def:cusp-central-homology-suspension" (lean := "Mathoverflow1973.CuspCentralHomology.Suspension") (parent := "cusp-homology")
The unreduced suspension of a space $`X` is the quotient of $`[0,1]\times X` in which
$`(t,x)` and $`(s,y)` are identified exactly when $`t=s` and either $`t=0`, or $`t=1`, or
$`x=y`: each end of the cylinder is crushed to a single point and nothing else is
collapsed. The Lean object is a bare setoid quotient, with `mk` for the quotient map and
`height` for the descent of the first coordinate. It carries the open cover by the north
set $`\{\,\mathrm{height}<3/4\,\}` and the south set $`\{\,\mathrm{height}>1/4\,\}`, each
contractible by an explicit contraction towards its pole, and a deformation retraction of
the middle band onto $`X`. No mapping cone and no CW input is used; this is what the
development has instead.
:::

:::definition "def:contractible-cover-homology-higher-equiv" (lean := "Mathoverflow1973.CuspCentralHomology.contractibleCoverHomologyHigherEquiv") (parent := "cusp-homology") (uses := "def:homotopy-equiv-homology-equiv, thm:exact-at-ambient, thm:exact-at-intersection")
If $`X=U\cup V` with $`U` and $`V` open and contractible, then for every $`n` the
Mayer–Vietoris connecting homomorphism is an isomorphism of $`\Z`-modules
$`H_{n+2}(X;\Z)\cong H_{n+1}(U\cap V;\Z)`. Contractibility enters as a `ContractibleSpace`
instance on each of the two subtypes; the isomorphism is the connecting map itself,
assembled by `LinearEquiv.ofBijective` from separate injectivity and surjectivity lemmas,
each read off exactness of the Mayer–Vietoris sequence at the ambient and at the
intersection once $`H_*(U)` and $`H_*(V)` vanish above degree zero. A companion statement
identifies $`H_1(X)` with the kernel of $`H_0(U\cap V)\to H_0(U)\oplus H_0(V)`.
:::

The cell structure of $`W` is the one of Appendix A, taken modulo the lattice: the $`A_2`
triangulation has one vertex, three edges and two triangles there, so its dual honeycomb has
a single hexagon.

:::definition "def:fundamental-cell" (lean := "Mathoverflow1973.CuspCentralHomology.FundamentalCell") (parent := "cusp-homology") (uses := "def:cusp-honeycomb-tiling-base-cell")
The fundamental cell is the product of the compact fibre torus $`(S^1)^2` with `baseCell`,
the closed hexagon
$`\{\,|2x_0+x_1|\le1,\ |x_0-x_1|\le1,\ |x_0+2x_1|\le1\,\}\subset\R^2` that is the
fundamental domain of the $`A_2` honeycomb tiling. Both factors are compact, and the
instance recording that the product is compact is what makes the properness arguments below
available. This single cell is the whole cell structure of $`W`.
:::

:::definition "def:fundamental-cell-map" (lean := "Mathoverflow1973.CuspCentralHomology.fundamentalCellMap") (parent := "cusp-homology") (uses := "def:fundamental-cell, def:quotient-central-fibre, thm:compatible-cell-homeomorph-opposite")
The characteristic map of the cell is the honeycomb collapse restricted to
$`T^2_{\mathrm{fib}}\times(\text{hexagon})`, landing in $`W`. It is proved surjective,
proper and closed, hence a quotient map, and its identifications are given explicitly: two
points have the same image exactly when they differ by a deck translation of the plane
coordinate together with a phase lying in the stabiliser of the relevant edge character.
Since the source is compact and the target Hausdorff, functions on $`W` may be — and
throughout are — defined by descending functions along this map. The radial gauge and the
base-torus projection are both obtained that way.
:::

:::definition "def:radial-cell-gauge" (lean := "Mathoverflow1973.CuspCentralHomology.Radial.cellGauge") (parent := "cusp-homology")
$`g(x)=\max\bigl(|2x_0+x_1|,\,|x_0-x_1|,\,|x_0+2x_1|\bigr)` is the Minkowski functional of
the honeycomb hexagon: $`\mathrm{baseCell}=\{g\le1\}`, its interior is $`\{g<1\}`, its
frontier is $`\{g=1\}`, and $`g(cx)=|c|\,g(x)`. Descended along the characteristic map, $`g`
becomes a continuous radial function `centralRadius` on $`W`, and every piece of the cell
structure is one of its level or sublevel sets: the inner region $`\{r<1\}`, the outer
collar $`\{r>a\}`, their overlap, and the frontier $`\{r=1\}`. Trading CW machinery for
three absolute values is the largest single simplification in this part of the development.
:::

:::definition "def:central-boundary-suspension-homeomorph" (lean := "Mathoverflow1973.CuspCentralHomology.centralBoundarySuspensionHomeomorph") (parent := "cusp-homology") (uses := "def:cusp-central-homology-suspension, def:fundamental-cell-map, def:radial-cell-gauge")
The frontier $`\{q\in W:\mathrm{centralRadius}(q)=1\}` of the radial cell structure is
homeomorphic to the unreduced suspension of three disjoint circles. Concretely: the three
pairs of opposite hexagon edges are glued in pairs, and over each edge the fibre torus is
collapsed along that edge's character to a circle, producing three cylinders
$`[0,1]\times S^1`; all six ends land on the two triple points, which become the poles. The
result is three $`2`-spheres sharing both poles, whose Betti numbers $`(1,2,3)` are computed
from the north–south cover by the contractible-cover lemma. The hypotheses are the running
ones: $`C` analytic on the $`\varepsilon`-ball, $`\varepsilon<1`, and the small-drift bound.
:::

:::definition "def:overlap-phase-homeomorph" (lean := "Mathoverflow1973.CuspCentralHomology.overlapPhaseHomeomorph") (parent := "cusp-homology") (uses := "def:fundamental-cell-map, def:radial-cell-gauge")
For $`a<1`, the overlap of the collar $`\{\mathrm{centralRadius}>a\}` with the inner region
$`\{\mathrm{centralRadius}<1\}` is homeomorphic to
$`T^2_{\mathrm{fib}}\times\{x:a<g(x)<1\}`, the fibre torus times a hexagonal annulus. The
annulus deformation-retracts onto a circle by radial normalisation, so the overlap is
homotopy equivalent to $`T^2\times S^1=T^3`. This is the intersection term of the
Mayer–Vietoris sequence for the radial cover of $`W`, and it is where the connecting
homomorphisms out of the top degrees land.
:::

Running that sequence — inner region homotopy equivalent to $`T^2`, collar homotopy
equivalent to the suspension of three circles, overlap homotopy equivalent to $`T^3` —
gives degrees $`2` through $`4` and the vanishing above $`4`. Degrees $`0` and $`1` come
instead from the retraction of the previous section, which makes $`W` homotopy equivalent
to a small cusp neighbourhood whose first homology is already known.

:::definition "def:cusp-central-homology-central-betti" (lean := "Mathoverflow1973.CuspCentralHomology.centralBetti") (parent := "cusp-homology")
The Betti numbers of the central cusp fibre, as a function $`\mathbb{N}\to\mathbb{N}` defined by pattern
matching: $`b_0=1`, $`b_1=2`, $`b_2=4`, $`b_3=2`, $`b_4=1`, and $`b_n=0` for $`n\ge5`. The
alternating sum is $`2`, matching the stratification of $`W` into a two-dimensional torus
orbit, three one-dimensional ones and two points.
:::

:::definition "def:central-singular-homology-equiv" (lean := "Mathoverflow1973.CuspCentralHomology.centralSingularHomologyEquiv") (parent := "cusp-homology") (uses := "def:actual-quotient-fibre, def:central-boundary-suspension-homeomorph, def:central-collapse-equiv, def:contractible-cover-homology-higher-equiv, def:cross-product-homology, def:cusp-central-homology-central-betti, def:overlap-phase-homeomorph, def:product-torus-homology-equiv, thm:exists-closed-quotient-strong-deformation-retraction, thm:singular-mayer-vietoris-exact-at-pair")
For every $`n` there is an isomorphism of $`\Z`-modules $`H_n(W;\Z)\cong\Z^{b_n}`, that is
$`H_*(W;\Z)=(\Z,\Z^2,\Z^4,\Z^2,\Z,0,\dots)`. This is Proposition 7.11 of the paper and
Lemma A.3 of its appendix. Degree $`0` is path-connectedness, visible from surjectivity of
the honeycomb collapse; degree $`1` is imported through the homotopy equivalence of $`W`
with a small cusp neighbourhood supplied by the strong deformation retraction. Degrees
$`2,3,4` and the vanishing above $`4` come from the radial Mayer–Vietoris sequence, with
$`H_2(W)` a split extension of a connecting kernel $`\Z` by the $`\Z^3` of the collar. Each
group is free, so $`H_*(W;\Z)` is torsion free and finitely generated, with Euler
characteristic $`2`.
:::

The second description of $`H_*(W)` is the one the global argument actually uses: not the
ranks, but the specialization map from a nearby fibre. Two auxiliary structures are needed
— a projection of $`W` onto the base torus, which splits off a summand and later detects
the top class, and the surjectivity of the product collapse.

:::definition "def:base-torus-projection" (lean := "Mathoverflow1973.CuspCentralHomology.baseTorusProjection") (parent := "cusp-homology") (uses := "def:period-torus-higher-homology-product-torus, def:quotient-central-fibre, thm:compatible-cell-homeomorph-opposite")
Descending the plane coordinate through the honeycomb collapse gives a continuous
projection $`W\to T^2=(\R/\Z)^2` onto the base torus. It admits a continuous section
$`t\mapsto\mathrm{productCollapse}(1,t)`, so the composite section-then-projection is the
identity and $`H_*(T^2)` splits off $`H_*(W)` in every degree. In degree $`2` the summand it
splits off is generated by the paper's torus class $`\mathbb{T}_B`, complementary to the
three double-curve classes; in degree $`4` its first coordinate is what detects the
generator, which is the use made of it at the end of this chapter.
:::

:::theorem "thm:product-collapse-homology-two-surjective-of-holomorphic" (lean := "Mathoverflow1973.CuspCentralHomology.productCollapse_homologyTwo_surjective_of_holomorphic") (parent := "cusp-homology") (uses := "def:actual-quotient-fibre, def:base-torus-projection, def:central-boundary-suspension-homeomorph, def:central-collapse-equiv, def:circle-homology-one-equiv, def:contractible-cover-homology-higher-equiv, def:cross-product-homology, def:flat-torus-circle-homeomorph, def:overlap-phase-homeomorph, def:product-torus-top-class, def:torus-matrix-map, thm:exists-closed-quotient-strong-deformation-retraction, thm:singular-mayer-vietoris-exact-at-pair")
*Theorem.* For $`C` holomorphic on the disc of radius $`r`, the collapse
$`T^2_{\mathrm{fib}}\times T^2\to W` is surjective on $`H_2(\cdot;\Z)`. The proof is the
reason the development carries three copies of the same radial analysis: the
inner/outer/overlap cover is replayed on the base torus and on
$`T^2_{\mathrm{fib}}\times T^2` — the latter with a shear correcting the source phase
character — purely so that the connecting homomorphisms become natural for the collapse.
The companion statement gives surjectivity in degrees $`3` and above, and the two together
feed the marked-torus computation.
:::

:::theorem "thm:marked-collapse-homology-surjective" (lean := "Mathoverflow1973.CuspSpecialization.markedCollapse_homology_surjective") (parent := "cusp-homology") (uses := "def:marked-collapse, thm:product-collapse-homology-two-surjective-of-holomorphic")
*Theorem.* For every $`n`, the map $`H_n((S^1)^4;\Z)\to H_n(W;\Z)` induced by
`markedCollapse` is surjective. Degrees $`0` and $`1` are handled directly, degree $`2` and
degrees $`3` and above by transport from the product collapse. Surjectivity in all degrees
at once is what makes the coinvariants description of $`H_*(W)` an identification of the
homology rather than a mere comparison map.
:::

:::theorem "thm:marked-collapse-homology-kernel" (lean := "Mathoverflow1973.CuspSpecialization.markedCollapse_homology_kernel") (parent := "cusp-homology") (uses := "def:coordinate-h1-four-equiv, def:coordinate-torus-h2-exterior-equiv, def:coordinate-torus-h3-exterior-equiv, def:m, def:marked-collapse, def:period-torus-higher-homology-pontryagin-product, thm:product-collapse-homology-two-surjective-of-holomorphic")
*Theorem.* The kernel of $`H_n((S^1)^4;\Z)\to H_n(W;\Z)` is the image of
$`(M_0)_*-\mathrm{id}`, where $`(M_0)_*` is induced by the torus automorphism of the
integral cusp monodromy matrix $`M_0`. With surjectivity this identifies $`H_*(W;\Z)` with
the coinvariants $`H_*(T^4)/(M_0-1)`: Proposition 7.12 of the paper, in homological rather
than cohomological form.
:::

:::proof "thm:marked-collapse-homology-kernel"
The inclusion of the image of $`(M_0)_*-\mathrm{id}` in the kernel is formal, from the
homotopy `markedCollapse_comp_matrix` between `markedCollapse` and its precomposition with
the torus map of $`M_0`. The reverse inclusion is proved degree by degree. Degree $`0` is
trivial and degree $`1` reduces, through the coordinate identification of $`H_1((S^1)^4)`
with the lattice $`\Lambda`, to the statement that $`\ker(M_0-I)` and $`\mathrm{im}(M_0-I)`
both equal the rank-two toric sublattice — the Smith normal form
$`\mathrm{diag}(1,1,0,0)` of Lemma A.1. Degrees $`2` and $`3` are transported to the
exterior powers $`\Lambda^2\Lambda` and $`\Lambda^3\Lambda` through the Pontryagin-product
description of torus homology, where the maps become $`\Lambda^qM_0-I` and the ranks of
kernel and cokernel are again finite integral linear algebra. Degree $`4` uses the top
class, and degrees five and above are covered uniformly since both sides vanish. Comparing
the resulting ranks $`(1,2,4,2,1)` with `centralBetti` is the consistency check the
development performs implicitly by proving surjectivity separately. $`\blacksquare`
:::

:::theorem "thm:exists-actual-specialization-homology" (lean := "Mathoverflow1973.CuspCentralHomology.exists_actual_specialization_homology") (parent := "cusp-homology") (uses := "thm:exists-original-marked-specialization-models, thm:marked-collapse-homology-kernel, thm:marked-collapse-homology-surjective")
*Theorem.* There is $`\eta_0>0` such that for every $`t` with $`0<\|t\|\le\eta_0` there is a
homeomorphism $`E:(S^1)^4\cong\mathrm{ActualQuotientFibre}\,C\,r\,t` for which, writing
$`f` for the prescribed collapse of that fibre onto $`W`: the composite $`f\circ E` is
homotopic to `markedCollapse`; $`f_*` is surjective on $`H_n` for every $`n`; and
$`f_*a=0` if and only if $`E_*^{-1}a` lies in the image of $`(M_0)_*-\mathrm{id}`. The
degree-$`2` and degree-$`3` kernels are restated on the exterior powers of the lattice, as
the images of $`\Lambda^2M_0-\mathrm{id}` and $`\Lambda^3M_0-\mathrm{id}`. This is the
input the Mayer–Vietoris computation of $`H_*(X)` consumes at the cusp.
:::

:::proof "thm:exists-actual-specialization-homology"
Take the $`\eta_0` produced by the marked-model theorem and, for each $`t`, the
homeomorphism $`E` it provides. That theorem already gives the homotopy between
`markedCollapse` and $`f\circ E` and the equality of the two induced maps on homology.
Surjectivity of $`f_*` and the description of its kernel then transport across $`E`: a
class $`a` is killed by $`f_*` precisely when $`E_*^{-1}a` is killed by the marked
collapse, which by the kernel theorem happens precisely when it lies in the image of
$`(M_0)_*-\mathrm{id}`. The degree-$`2` and degree-$`3` restatements are the same
transport composed with the exterior-power coordinates for $`H_2` and $`H_3` of the
standard $`4`-torus, under which $`(M_0)_*` becomes $`\Lambda^qM_0`. $`\blacksquare`
:::

What remains is the boundary of the cusp neighbourhood. It is a mapping torus of the
$`4`-torus over the monodromy $`M_0`, and the global ladder needs one fact about its top
homology: a distinguished generator of $`H_4` bounds in the filling. The class is produced
on a $`3`-torus sub-model, where the Wang sequence degenerates.

:::theorem "thm:central-homology-four-map-eq-zero-of-base-first-zero" (lean := "Mathoverflow1973.CuspBoundaryTopVanishing.central_homologyFourMap_eq_zero_of_baseFirstZero") (parent := "cusp-homology") (uses := "def:base-torus-projection, def:central-boundary-suspension-homeomorph, def:contractible-cover-homology-higher-equiv, def:overlap-phase-homeomorph, def:product-torus-homology-equiv")
*Theorem.* Let $`f:X\to W` be continuous and suppose the first coordinate of
$`\mathrm{baseTorusProjection}\circ f` vanishes identically. Then $`f_*=0` on $`H_4`. Since
$`H_4(W)\cong\Z`, the content is that the top class is detected by the first base circle
direction alone: a map missing that direction cannot carry a $`4`-cycle onto the generator.
The proof factors $`f` up to homotopy through the overlap region at radius $`1/2`, where
the phase and annulus coordinates separate and the degree-$`4` map is visibly zero. The
hypotheses on $`C` are analyticity, the small-drift bound and $`r<1`.
:::

:::definition "def:restricted-monodromy" (lean := "Mathoverflow1973.CuspBoundaryGammaZero.restrictedMonodromy") (parent := "cusp-homology") (uses := "def:torus-matrix-map")
The unipotent matrix
$`\begin{pmatrix}1&0&0\\1&1&0\\0&0&1\end{pmatrix}\in\mathrm{SL}_3(\Z)` acts on
$`T^3=(\R/\Z)^3` by a homeomorphism, built from the matrix together with its explicit
inverse. It is the cusp monodromy restricted to the sublattice
$`\ker\gamma=\langle\hat u,\hat w,\hat\delta\rangle`, on which $`M_0` sends $`\hat u` to
$`\hat u+\hat w` and fixes the other two basis vectors. Determinant one, and the fact that
the displayed inverse really is one, are both discharged by `decide`.
:::

:::definition "def:cusp-boundary-gamma-zero-boundary" (lean := "Mathoverflow1973.CuspBoundaryGammaZero.Boundary") (parent := "cusp-homology") (uses := "def:mapping-torus-torus, def:restricted-monodromy")
The $`\Gamma_0`-model of the cusp-neighbourhood boundary is the mapping torus of
`restrictedMonodromy`: a $`T^3`-bundle over $`S^1` with unipotent monodromy, hence a
nilmanifold. It maps into the boundary mapping torus of the global gluing through the
monodromy-equivariant inclusion of the $`\gamma=0` slice $`T^3\hookrightarrow T^4`, by the
general construction of a map of mapping tori from an equivariant map of fibres.
:::

:::theorem "thm:gamma-boundary-to-full-homology-four-eq-zero" (lean := "Mathoverflow1973.CuspBoundaryTopVanishing.gammaBoundaryToFull_homologyFour_eq_zero") (parent := "cusp-homology") (uses := "def:cusp-boundary-gamma-zero-boundary, def:flat-torus-circle-homeomorph, def:holomorphic-period-map, def:prescribed-actual-fibre-collapse, def:punctured-cusp-cover, def:punctured-mapping-torus-homotopy-equiv, thm:central-homology-four-map-eq-zero-of-base-first-zero, thm:exists-closed-quotient-controlled-strong-deformation-retraction")
*Theorem.* For any cusp-family datum $`D` and any height $`h`, the map from the $`\Gamma_0`
boundary mapping torus into the full cusp neighbourhood induces the zero map on $`H_4`. The
proof assembles the chapter: choose a controlled retraction of a small closed tube onto
$`W` prescribed simultaneously on a whole circle of levels, compose it with the boundary
map, verify that the composite kills the first base-torus coordinate, and apply the
detection lemma. Varying the height changes the map only by a homotopy, so the choice of
$`h` is immaterial.
:::

:::definition "def:cusp-boundary-gamma-zero-top-wang-equiv" (lean := "Mathoverflow1973.CuspBoundaryGammaZero.topWangEquiv") (parent := "cusp-homology") (uses := "def:mapping-torus-homology-wang-boundary, def:product-torus-homology-equiv, def:restricted-monodromy, thm:exact-at-ambient, thm:exact-at-intersection, thm:intersection-to-v-twisted-fold")
The Wang sequence of the mapping torus $`\mathcal B\to S^1` reads
$`H_4(T^3)\to H_4(\mathcal B)\to H_3(T^3)\xrightarrow{\,M_*-\mathrm{id}\,}H_3(T^3)`. Here
$`H_4(T^3)=0`, and because the monodromy matrix has determinant $`1` it acts as the
identity on $`H_3(T^3)\cong\Z` — a fact settled by `decide` on the matrix. The Wang
boundary is therefore an isomorphism $`H_4(\mathcal B;\Z)\cong H_3(T^3;\Z)`. Composing with
the coordinate isomorphism of $`H_3(T^3)` with $`\Z` gives `H4Coordinates`, and the
preimage of $`1` is the generator `fundamentalClass`. The paper's nilmanifold-boundary
argument leaves a pleasingly small formal footprint here.
:::

:::definition "def:cusp-boundary-gamma-zero-native-class" (lean := "Mathoverflow1973.CuspBoundaryGammaZero.nativeClass") (parent := "cusp-homology") (uses := "def:cusp-boundary-gamma-zero-boundary, def:cusp-boundary-gamma-zero-top-wang-equiv, def:flat-torus-circle-homeomorph, def:singular-homology-map")
The pushforward of `fundamentalClass` along the comparison map from the $`\Gamma_0` mapping
torus into the cusp boundary of the global gluing: a distinguished element of $`H_4` of that
boundary. Two further facts make it the right generator to track. Its image under the Wang
boundary of the full boundary is the coordinate class $`e_3\in H_3(T^4)`; and under the map
into the regular part of the period family it lies in the range of $`H_4` of the $`\gamma=0`
sub-family. The global ladder needs a named degree-$`4` class on the cusp boundary, and this
is it.
:::

:::theorem "thm:boundary-filling-homology-map-native-class-eq-zero" (lean := "Mathoverflow1973.CuspBoundaryTopVanishing.boundaryFillingHomologyMap_nativeClass_eq_zero") (parent := "cusp-homology") (uses := "def:cusp-boundary-gamma-zero-native-class, def:piece-mapping-torus-homotopy-equiv, def:threefold-projection, thm:gamma-boundary-to-full-homology-four-eq-zero")
*Theorem.* The image of `nativeClass` under the degree-$`4` boundary-to-filling map is zero:
the fundamental $`4`-cycle of the cusp boundary bounds in the cusp filling. In the indexing
of the three special fibres by `Option Elliptic.Kind`, the cusp is the puncture
`Option.none` and the filling is the corresponding local piece of the threefold.
:::

:::proof "thm:boundary-filling-homology-map-native-class-eq-zero"
The class is by construction the image of the fundamental class of the $`\Gamma_0` mapping
torus, so it suffices to show that the composite from that mapping torus into the filling
kills $`H_4`. That composite is the map into the full cusp neighbourhood followed by the
identification of the neighbourhood with the local piece, and the previous theorem says the
first factor is already zero on $`H_4`. Its proof, in turn, runs the whole chapter in
miniature: a controlled retraction takes the neighbourhood onto $`W`, and the composite
into $`W` has vanishing first base-torus coordinate because the $`\gamma=0` slice is
precisely the direction the base projection forgets — so the top class is not detected.
Since $`H_4(W)\cong\Z` is detected by that coordinate alone, the map is zero, and the class
bounds. This is the top-vanishing input that forces $`H_4(X)=0` in the global Mayer–Vietoris
ladder, and with it $`H_*(X;\Z)\cong H_*(S^6;\Z)`. $`\blacksquare`
:::
