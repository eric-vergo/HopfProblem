/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — Morse theory on manifolds chapter.

The from-scratch differential topology behind the recognition step: Morse functions and
the Morse lemma, handle attachment and gradient-like flows, the Whitney trick, and the
Reeb-type endpoint that turns a homotopy six-sphere into a topological six-sphere.
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

#doc (Manual) "Morse theory on manifolds" =>

By the time the threefold $`X` reaches this chapter it is a closed smooth six-manifold
that is homotopy equivalent to $`S^6`. Section 8 of {citet alpoge.s6}[] converts that
into a diffeomorphism by quoting four classical theorems in sequence: Smale's generalised
Poincaré theorem in dimensions $`\ge 5` {citep smale61}[], the $`h`-cobordism theorem
{citep milnor65}[], the identification of $`h`-cobordism classes of oriented homotopy
$`n`-spheres with their oriented diffeomorphism classes, and the vanishing of the
Kervaire–Milnor group $`\Theta_6` {citep kervaire.milnor63}[]. None of these is available
in a proof assistant, so the formalization builds the first one from nothing.

The last three can be dispensed with entirely. The paper needs a *diffeomorphism*
$`X \to S^6` because it transports an almost complex structure — a tensor — and a mere
homeomorphism does not move tensors. The formalization transports a *holomorphic atlas*
instead, and a charted-space structure pushes forward along a bare homeomorphism with its
transition maps unchanged on the nose. Only Smale's homeomorphism is therefore needed,
and the exotic-sphere group never appears. What has to be proved is the single statement
that a compact smooth six-manifold homotopy equivalent to $`S^6` is homeomorphic to it.

That statement is proved here in the classical way, and every ingredient is constructed
from the ground up: Morse functions exist and are generic; near a nondegenerate critical
point a function is a signed sum of squares; crossing such a point attaches a handle;
handles can be reordered, cancelled in pairs, and traded, the geometric work being an
honest Whitney trick in dimension six; and a Morse function with exactly two critical
points forces the manifold to be a sphere. The handle-cancellation ladder that reduces an
arbitrary Morse function on a homotopy six-sphere to a two-critical-point one belongs to
the companion cancellation chapter; what follows is the machinery it runs on, together
with the two endpoints — Reeb's theorem and its six-dimensional wrapper.

:::group "morse"
Morse functions, critical points and the Morse lemma on charted manifolds; the model
handle and its descent flow; the surgery datum attached to each critical point and the
global window systems carrying a gradient-like field; the intersection theory of belt
spheres with the Whitney trick and Smale's rearrangement lemma; and the Reeb-type
theorem producing a homeomorphism onto the standard six-sphere.
:::

Everything local is done once, in a fixed pair of normed spaces $`N` (the negative
directions) and $`P` (the positive ones), against the model quadratic
$$`q(z_1, z_2) \;=\; -\|z_1\|^2 + \|z_2\|^2`
on $`N \times P`. The global constructions then reduce to this model through charts, and
the reduction is recorded explicitly in the side conditions of the structures below —
which is what lets flow arguments on a manifold be settled by closed-form computation.

:::definition "def:morse-handle-model-map" (lean := "Mathoverflow1973.Smale.MorseHandle.modelMap") (parent := "morse")
For a radius $`\rho` the model handle is the map
$$`(u, v) \;\longmapsto\; \bigl(\rho\sqrt{1 + \|v\|^2}\,u,\; \rho v\bigr)`
from $`D_N \times D_P` to $`N \times P`, where $`D_V` denotes the closed unit ball of $`V`
about the origin. The radial factor is chosen so that the attaching face is exactly a
piece of a level set: substituting into $`q` gives
$`q = \rho^2\|v\|^2 - \rho^2(1 + \|v\|^2)\|u\|^2`, which equals $`-\rho^2` identically on
$`\|u\| = 1`, equals $`-\rho^2\|u\|^2` on the core disc $`v = 0`, and equals
$`\rho^2\|v\|^2` on the transverse disc $`u = 0`. The image is the standard handle block
sitting between the levels $`\mp\rho^2` of $`q`, with its old face $`S(N) \times D_P`
lying in the lower level and its core disc $`D_N \times \{0\}` running across the block.
:::

:::definition "def:morse-handle-descent-flow" (lean := "Mathoverflow1973.Smale.MorseHandle.descentFlow") (parent := "morse")
The dynamics of the model, $`t \cdot (z_1, z_2) = (e^{t} z_1,\, e^{-t} z_2)`, recorded as
an honest `Flow ℝ (N × P)`: a genuine additive action of $`\R` by homeomorphisms, defined
for all times, so no escape-time or completeness hypothesis is ever needed downstream. It
integrates the vector field $`z \mapsto (z_1, -z_2)`, and
$$`\frac{d}{dt}\, q\bigl(e^{t}z_1, e^{-t}z_2\bigr) \;=\; -2e^{2t}\|z_1\|^2 - 2e^{-2t}\|z_2\|^2,`
which is strictly negative away from the origin. So $`q` decreases strictly along every
non-constant orbit, the orbits leaving the origin are the ones in $`N \times \{0\}` and
those entering it lie in $`\{0\} \times P`.
:::

A function on a manifold has no intrinsic second derivative at a point where its first
derivative fails to vanish, and the development declines to build one. Nondegeneracy is
asserted in a chart instead, and the assertion is existential: *some* chart of the maximal
atlas exhibits the point as regular or as a nondegenerate critical point. At a critical
point the second derivative transforms by congruence under a change of chart, so
bijectivity does not depend on which chart witnesses it, and the existential and universal
readings agree.

:::definition "def:manifold-morse-is-morse" (lean := "Mathoverflow1973.Smale.ManifoldMorse.IsMorse") (parent := "morse")
A function $`f : M \to \R` on a manifold charted on a real normed space $`E` is *Morse*
when every point $`x` is Morse: there is a chart $`e` in the maximal $`C^\infty` atlas of
$`M` with $`x \in \mathrm{source}\,e` such that either
$$`D(f \circ e^{-1})(e\,x) \neq 0 \qquad\text{or}\qquad D^2(f \circ e^{-1})(e\,x) \colon E \to (E \to \R) \ \text{is bijective.}`
The disjunction is inclusive and the two branches are the two cases of the local picture:
a regular point, or a critical point whose Hessian — read as the Fréchet derivative of the
derivative, a continuous linear map $`E \to E \to_L \R` — is an isomorphism onto the dual.
No Hessian is ever formed on $`M` itself.
:::

:::definition "def:critical-points" (lean := "Mathoverflow1973.Smale.ManifoldMorse.criticalPoints") (parent := "morse")
The critical set of $`f : M \to \R` is
$$`\mathrm{crit}(f) \;=\; \{\, x \in M \;:\; \mathrm{mfderiv}\,f\,x = 0 \,\},`
defined through the manifold derivative, hence chart-free. For a smooth Morse function
this set is closed, because the manifold derivative is continuous, and discrete, because a
nondegenerate critical point is isolated by the inverse function theorem applied to
$`D(f \circ e^{-1})` in a witnessing chart; on a compact $`M` it is therefore finite. Every
structure below is indexed over it, and it is the most heavily used definition of the
subject.
:::

:::theorem "thm:exists-morse-function" (lean := "Mathoverflow1973.Smale.ManifoldMorse.exists_morse_function") (parent := "morse") (uses := "def:manifold-morse-is-morse")
*Theorem.* Let $`E` be a finite-dimensional real normed space and $`M` a compact
Hausdorff smooth manifold charted on $`E`. Then there is a smooth $`f : M \to \R` that is
Morse.

Sard's theorem is not used, and is not available. Its role is played by a measure: $`E`
is given its Borel structure and an additive Haar measure, in each chart $`f` is perturbed
by a small linear functional $`\ell`, and the perturbations $`\ell` for which
$`f + \ell \circ e` fails to be Morse on a fixed compact plateau form a null set. A finite
induction over a plateau cover of the compact $`M` then produces a single perturbation
that works everywhere.
:::

The local normal form is proved in a normed space and imported to manifolds through a
chart. The proof has three moves: an integral form of second-order Taylor expansion writes
$`f - f(a)` as a symmetric bilinear form with smoothly varying coefficients, an
inverse-function-theorem argument factors that family of forms through a fixed reference
form by a smoothly varying congruence, and diagonalisation over $`\R` reduces the reference
form to a signature.

:::theorem "thm:exists-signed-morse-chart-of-cont-diff-on" (lean := "Mathoverflow1973.SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn") (parent := "morse")
*Theorem (Morse lemma).* Let $`f` be $`C^\infty` on an open $`U \subseteq E`, let
$`a \in U` satisfy $`Df(a) = 0`, and let $`D^2f(a)` be bijective. Then there are signs
$`w_i \in \{-1, +1\}`, $`i` ranging over $`\mathrm{Fin}(\dim_\R E)`, and a $`C^\infty`
partial diffeomorphism $`e` from $`E` to $`\mathrm{Fin}(\dim_\R E) \to \R` with
$`a \in \mathrm{source}\,e \subseteq U` and $`e(a) = 0`, such that
$$`f(x) \;=\; f(a) + \sum_i w_i\,(e\,x)_i^{\,2} \qquad (x \in \mathrm{source}\,e).`
The conclusion also records the inverse equation
$`f(e^{-1}y) = f(a) + \sum_i w_i y_i^2` on the target of $`e`. Both directions are stated
because later arguments read level sets off the model and push them back: having the
equation on the target avoids re-deriving it from injectivity every time a sublevel set is
transported.
:::

:::definition "def:signed-morse-chart" (lean := "Mathoverflow1973.Smale.ManifoldMorse.SignedMorseChart") (parent := "morse")
A *Morse chart* for $`f` at $`x \in M` packages the normal form on the manifold: weights
$`w_i \in \{-1, +1\}` indexed by $`\mathrm{Fin}(\dim_\R E)`, a $`C^\infty` partial
diffeomorphism from $`M` to $`\mathrm{Fin}(\dim_\R E) \to \R` whose source contains $`x`
and which sends $`x` to $`0`, together with the equation
$`f(y) = f(x) + \sum_i w_i (\mathrm{chart}\,y)_i^2` on the source and its counterpart on
the target. The index of the critical point is the number of $`i` with $`w_i = -1`.
Splitting the coordinates by the sign of $`w_i` into a negative and a positive Euclidean
factor turns the equation into $`f = f(x) - \|z_-\|^2 + \|z_+\|^2`, which is precisely the
model quadratic; that split chart is the interface between this structure and the model
handle.
:::

:::theorem "thm:nonempty-signed-morse-chart" (lean := "Mathoverflow1973.Smale.ManifoldMorse.nonempty_signedMorseChart") (parent := "morse") (uses := "def:critical-points, def:manifold-morse-is-morse, def:signed-morse-chart, thm:exists-signed-morse-chart-of-cont-diff-on")
*Theorem (Morse lemma on manifolds).* If $`f` is smooth and Morse and
$`x \in \mathrm{crit}(f)`, then a Morse chart for $`f` at $`x` exists.

Being critical rules out the regular branch of the definition, so the witnessing chart
$`e` supplied by the Morse hypothesis has $`D^2(f \circ e^{-1})(e\,x)` bijective; the
Morse lemma applies to $`f \circ e^{-1}` on the open set $`\mathrm{target}\,e`, and the
resulting normal form is composed with $`e` to give a partial diffeomorphism of $`M`.
:::

:::theorem "thm:exists-adapted-descent-field" (lean := "Mathoverflow1973.Smale.ManifoldMorse.exists_adaptedDescentField") (parent := "morse") (uses := "def:critical-points, thm:nonempty-signed-morse-chart")
*Theorem.* On a compact Hausdorff smooth manifold carrying a smooth Morse function $`f`
there is a smooth vector field $`V` — smooth as a section, i.e. as a map into the tangent
bundle — with
$$`V|_{\mathrm{crit}(f)} = 0, \qquad df_x(V_x) < 0 \ \text{ for } x \notin \mathrm{crit}(f),`
and such that near each critical point $`p` the field agrees with the model descent field
of some Morse chart at $`p`. The second condition forces $`V_x \neq 0` off the critical
set, so the zero set of $`V` is exactly $`\mathrm{crit}(f)`; this is a gradient-like field
in the classical sense, with no metric chosen. It is assembled by gluing the model descent
fields, transported through the split Morse charts, over pairwise disjoint neighbourhoods
of the finitely many critical points, with a bump-function interpolation elsewhere that
preserves strict descent.
:::

Crossing a nondegenerate critical point of index $`\lambda` replaces the sublevel set by
one with a $`\lambda`-handle attached, and the two neighbouring regular level sets differ
by a surgery. Both halves of that statement have to be made into data before they can be
manipulated, because the arguments downstream compare the two sides through explicit maps
rather than up to unspecified homeomorphism.

:::definition "def:surgery-boundary-pair" (lean := "Mathoverflow1973.Smale.SurgeryBoundaryPair") (parent := "morse")
A presentation of two spaces $`X` and $`Y` as the two sides of a surgery in normed spaces
$`E` (of dimension $`\lambda`) and $`F`. It consists of four closed embeddings — a common
exterior $`R \to X` and $`R \to Y`, an old piece
$`S(E) \times D(F) \to X` and a new piece $`D(E) \times S(F) \to Y` — whose ranges cover
$`X` and $`Y` respectively, together with a map $`S(E) \times S(F) \to R` and the two
overlap conditions saying that exterior meets piece exactly along that common boundary
torus. The *attaching sphere* $`u \mapsto \mathrm{oldPiece}(u, 0)` is then a closed
embedded $`S^{\lambda-1}` in $`X`, and the *belt sphere*
$`v \mapsto \mathrm{newPiece}(0, v)` a closed embedded $`S^{\dim F - 1}` in $`Y`. These two
spheres, and their intersections with other spheres, are what all the geometry below is
about.
:::

:::theorem "thm:exists-morse-function-with-distinct-critical-values" (lean := "Mathoverflow1973.Smale.ManifoldMorse.exists_morse_function_with_distinct_critical_values") (parent := "morse") (uses := "def:critical-points, def:manifold-morse-is-morse, thm:exists-morse-function")
*Theorem.* A compact Hausdorff smooth manifold charted on a finite-dimensional $`E`
carries a smooth Morse function $`f` whose critical set is finite and on which $`f` is
injective.

Distinct critical values are not automatic and they are not cosmetic: they are what makes
the passage through a critical point a local matter, one handle at a time. A second
perturbation pass shifts the finitely many critical values apart by adding small constants
supported near each critical point, which changes neither the critical set nor the
nondegeneracy.
:::

:::definition "def:morse-surgery-data" (lean := "Mathoverflow1973.Smale.ManifoldMorse.MorseSurgeryData") (parent := "morse") (uses := "def:critical-points, def:morse-handle-descent-flow, def:morse-handle-model-map, def:signed-morse-chart, def:surgery-boundary-pair")
The complete local package at a critical point $`p`: a radius $`\rho > 0`; a Morse chart at
$`p` whose split chart's target contains the block
$`\bar B(0, 2\rho) \times \bar B(0, 2\rho)`; a homeomorphism
$$`\{f \le f(p) - \rho^2\} \,\cup\, \mathrm{range}\bigl(\text{attaching handle of radius } \rho\bigr) \;\xrightarrow{\ \simeq\ }\; \{f \le f(p) + \rho^2\}`
which is the identity on the top level and whose value at a frontier point is exactly
$`f(p) + \rho^2`; the requirement that this homeomorphism follows the model boundary
orbits, i.e. that a frontier point is sent to the endpoint of its own descent-flow orbit
computed in the split chart; a `SurgeryBoundaryPair` between the levels
$`\{f = f(p) - \rho^2\}` and $`\{f = f(p) + \rho^2\}` whose four maps are the ones
induced by the handle and whose belt sphere is the chart's belt core; and regularity of
both levels. The handle itself is the model handle pushed through the split chart, so the
whole package is anchored to closed-form formulas.
:::

:::theorem "thm:exists-morse-surgery-data-lt" (lean := "Mathoverflow1973.Smale.ManifoldMorse.exists_morseSurgeryData_lt") (parent := "morse") (uses := "def:critical-points, def:morse-surgery-data, thm:exists-adapted-descent-flow")
*Theorem.* Let $`f` be a smooth Morse function on a compact Hausdorff smooth manifold, let
$`p` be a critical point whose critical value is attained by no other critical point, and
let $`\varepsilon > 0`. Then surgery data at $`p` exists with radius $`< \varepsilon` and
with the closed window $`[f(p) - \rho^2,\, f(p) + \rho^2]` containing no critical value
other than $`f(p)`.

Shrinking the radius is what buys the second conclusion: since the critical values are a
finite set, a small enough $`\rho` isolates $`f(p)` among them. The attachment
homeomorphism is produced by flowing the region between the two levels down along an
adapted descent flow, off the handle block where the flow is the model one.
:::

:::definition "def:surgery-windows" (lean := "Mathoverflow1973.Smale.ManifoldMorse.SurgeryWindows") (parent := "morse") (uses := "def:critical-points, def:morse-surgery-data")
A global system of surgery data for $`f`: the critical set is finite and $`f` is injective
on it; a `MorseSurgeryData` is chosen at every critical point; each window
$`[f(p) - \rho_p^2,\, f(p) + \rho_p^2]` contains no critical value but $`f(p)`; and
windows belonging to distinct critical values are separated,
$$`f(p) < f(q) \ \Longrightarrow\ f(p) + \rho_p^2 \;<\; f(q) - \rho_q^2.`
Separation is what makes the handles independent: between two consecutive windows the
function is regular, so the sublevel sets there are all homeomorphic and the manifold is
presented as a linearly ordered sequence of handle attachments.
:::

:::theorem "thm:nonempty-surgery-windows" (lean := "Mathoverflow1973.Smale.ManifoldMorse.nonempty_surgeryWindows") (parent := "morse") (uses := "def:surgery-windows, thm:exists-morse-surgery-data-lt")
*Theorem.* A smooth Morse function on a compact Hausdorff smooth manifold whose critical
values are pairwise distinct admits a system of surgery windows.

First choose radii $`r_p` realising the separation inequality — possible because finitely
many distinct reals can be surrounded by disjoint intervals — and then choose surgery data
at each $`p` with $`\rho_p < r_p`. Monotonicity of $`t \mapsto t^2` on the positives turns
the strict inequality on radii into the strict inequality on windows.
:::

:::definition "def:adapted-windows" (lean := "Mathoverflow1973.AdaptedWindows") (parent := "morse") (uses := "def:critical-points, def:surgery-windows")
A system of surgery windows together with the dynamics that connects consecutive handles:
a vector field on $`M`, smooth as a section of the tangent bundle, and a `Flow ℝ M`
integrating it, such that the field vanishes on the critical set, satisfies
$`df_x(V_x) < 0` off it, and — the essential compatibility — agrees near every point of the
$`2\rho`-block of each critical point's split chart with that chart's model descent field.
The last condition is what makes the flow computable: inside a block, orbits are the
explicit exponential curves of the model, so basins of critical points can be identified
with attaching and belt spheres by a calculation rather than by a limiting argument. This
structure is the substrate on which every isotopy, handle slide and cancellation argument
in the subject runs.
:::

Passing one critical point changes homology in exactly the way the corresponding cell
attachment does. The subject computes this against its own singular homology theory, built
from a Mayer–Vietoris argument for small chains rather than imported, and against explicit
cell presentations rather than any cofibration or CW machinery — which is why the three
exactness statements are proved separately at the three positions of the sequence rather
than extracted from one long exact sequence.

:::theorem "thm:morse-exact-at-lower" (lean := "Mathoverflow1973.Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_lower") (parent := "morse") (uses := "def:morse-surgery-data")
*Theorem.* For surgery data at $`p` with $`f` continuous and $`k \neq 0`,
$$`\mathrm{im}\bigl(\partial_k\bigr) \;=\; \ker\Bigl(H_k\bigl(\{f \le f(p) - \rho^2\}\bigr) \longrightarrow H_k\bigl(\{f \le f(p) + \rho^2\}\bigr)\Bigr),`
where $`\partial_k` is the boundary map of the attached cell and the second map is induced
by inclusion. With its companions at the upper sublevel and at the attaching sphere this is
the long exact sequence of a single handle attachment. The statement is universe-monomorphic
— $`E` and $`M` are taken in `Type`, not `Type*` — because the singular homology theory it
is proved against is built there.
:::

In dimension six the middle handles have index $`2` and $`3`, and cancelling a
$`3`-handle against a $`2`-handle requires the attaching sphere of the former to meet the
belt sphere of the latter in a single point. Algebra gives intersection number $`\pm 1`;
geometry has to remove the surplus pairs. That is the Whitney trick, and here it is
carried out in full, in the one case the proof needs: a $`2`-sphere against a $`3`-sphere
in a $`5`-dimensional level of a $`6`-manifold.

:::definition "def:belt-intersection-count" (lean := "Mathoverflow1973.Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionCount") (parent := "morse") (uses := "def:morse-surgery-data")
For a map $`g : S^m \to \mathrm{UpperLevel}` meeting the belt sphere transversally in a
finite set, the algebraic intersection number
$$`\sum_{x \,\in\, g^{-1}(\mathrm{belt})} \mathrm{sign}\,J(x) \;\in\; \Z,`
where each sign is the `SignType` of a normal Jacobian: the determinant, read through a
fixed linear identification of $`\R \times (\text{negative coordinates})` with the ambient
$`\R^{m+1}` of $`S^m`, of the derivative of $`g` against the belt sphere's normal
coordinates. The count is an integer invariant of the isotopy class, whereas the
cardinality of the intersection set is not; the whole point of the Whitney trick is to
make the two agree.
:::

:::definition "def:smale-tubular-bigon" (lean := "Mathoverflow1973.Smale.TubularBigon") (parent := "morse") (uses := "def:whitney-pair-model-bigon")
An embedded Whitney bigon in a level manifold, given two sheets $`S`, $`T`, two boundary
curves $`a, b : \R \to M` and two strip germs $`k, l`. The data is a continuous map
$`\R^2 \to M`, smooth and with everywhere injective differential on the plane bigon of
height $`h`, restricting there to a closed embedding whose interior avoids $`S \cup T`;
its lower edge $`t \mapsto (2t - 1, 0)` traverses $`a` and its upper edge
$`t \mapsto (2t - 1, h(1 - (2t-1)^2))` traverses $`b`, with the germs along both edges
matching $`k` and $`l` through the model strip coordinates. On top of that sits a tubular
chart: a partial diffeomorphism of $`(\R \times \R) \times \R^{n}` into $`M`, with $`n = 4`
by default, whose source contains the bigon times a ball of positive radius and whose zero
section is the bigon itself. The tubular chart is what makes the cancelling isotopy
constructible — it turns a statement about a disc in a manifold into a statement about a
neighbourhood of the disc that is a product.
:::

:::theorem "thm:exists-signed-belt-cancellation-step" (lean := "Mathoverflow1973.Smale.ManifoldMorse.MorseSurgeryData.exists_signed_belt_cancellation_step") (parent := "morse") (uses := "def:isotopic-to-identity, def:morse-surgery-data, def:regular-level-charted-space, def:smale-tubular-bigon")
*Theorem (Whitney trick).* Let the surgery data $`D` sit in a six-manifold at a critical
point of index $`2`, so that the upper level is a $`5`-manifold containing a belt
$`3`-sphere, and suppose every circle in the lower level is nullhomotopic. Let
$`g : S^2 \to \mathrm{UpperLevel}` be a smooth injective immersion transverse to the belt
sphere, and let $`x_0, x_1` be intersection points with
$$`\mathrm{sign}(x_0) \cdot \mathrm{sign}(x_1) = -1.`
Then there is a diffeomorphism $`e` of the upper level, joined to the identity by a smooth
isotopy through diffeomorphisms, such that $`g' = e \circ g` is again a smooth injective
immersion transverse to the belt sphere with
$$`g'^{-1}(\mathrm{belt}) \;=\; g^{-1}(\mathrm{belt}) \smallsetminus \{x_0, x_1\},`
and with $`g'` agreeing with $`g` near every surviving intersection point — so all
surviving signs are unchanged. The nullhomotopy hypothesis on the lower level is where
simple connectivity enters: it is what allows the two arcs joining $`x_0` to $`x_1`, one
in the sphere and one in the belt, to bound a disc, which is then thickened to a
`TubularBigon` and used to push the two points together and off each other.
:::

:::theorem "thm:exists-minimal-signed-belt-sphere" (lean := "Mathoverflow1973.Smale.ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere") (parent := "morse") (uses := "def:belt-intersection-count, def:isotopic-to-identity, def:morse-surgery-data, def:regular-level-charted-space, thm:exists-signed-belt-cancellation-step")
*Theorem.* Under the same hypotheses, any transverse $`2`-sphere $`g` in the upper level
can be moved by an ambient isotopy to a transverse $`g'` with
$$`\#\,g'^{-1}(\mathrm{belt}) \;=\; \bigl|\,\text{algebraic count of } g\,\bigr|,`
the algebraic count being unchanged. The intersection set of $`g'` is a subset of that of
$`g` and $`g'` agrees with $`g` near each of its points.

Repeated application of the cancellation step strictly decreases a finite intersection set,
so the process terminates; it terminates only when no two surviving signs are opposite, and
a finite family of $`\pm 1`'s with no opposite pair has cardinality equal to the absolute
value of its sum. In particular an algebraic count of $`\pm 1` yields a single geometric
intersection point, which is exactly the hypothesis for cancelling a handle pair.
:::

:::theorem "thm:remove-connections-of-index-le" (lean := "Mathoverflow1973.AdaptedWindows.remove_connections_of_index_le") (parent := "morse") (uses := "def:adapted-windows, def:critical-points, def:flow-construction-compact-flow, thm:exists-ambient-disjoint-diffeomorph-of-dimension, thm:exists-native-level-flow-cylinder")
*Theorem (Smale's rearrangement lemma).* Let $`S` be an adapted window system, and let
$`p, q` be critical points with $`f(p) < f(q)` and no critical value strictly between
them, whose indices satisfy
$$`1 \;\le\; \mathrm{index}(q) \;\le\; \mathrm{index}(p) \;\le\; \dim M - 1.`
Then there are a smooth vector field $`V` and a flow $`G` integrating it such that $`V`
vanishes on the critical set, satisfies $`df(V) < 0` off it, agrees with the original
field near every critical point, and admits no orbit running from $`q` down to $`p`:
$$`\neg\ \Bigl(\lim_{t \to -\infty} G_t z = q \ \wedge\ \lim_{t \to +\infty} G_t z = p\Bigr) \qquad \text{for every } z \in M.`
Agreement of the germs at the critical points is what makes the conclusion usable: the
Morse function, its critical points and their indices are untouched, only the connecting
dynamics changes.
:::

:::proof "thm:remove-connections-of-index-le"
An orbit from $`q` to $`p` meets the intermediate regular level once, and the two ends of
the flow identify the traces there: the points flowing backwards to $`q` form the attaching
sphere of $`q`, transported down to the upper level of $`p` along the flow, and the points
flowing forwards to $`p` form the belt sphere of $`p`. So the assertion is that these two
embedded spheres can be made disjoint. Their dimensions are $`\mathrm{index}(q) - 1` and
$`\dim M - \mathrm{index}(p) - 1`, and the index hypothesis makes the sum of these strictly
less than the dimension $`\dim M - 1` of the level; general position therefore supplies an
ambient diffeomorphism of the level carrying one off the other. That diffeomorphism is
isotopic to the identity, and an isotopy of a regular level is realised as a modification
of the flow, supported in a compact cylinder around the level and leaving the field near
the critical points alone. The resulting field integrates to a flow whose basins of $`q`
and $`p` at the level are disjoint, which is the stated absence of connecting orbits.
$`\blacksquare`
:::

With all the machinery in place, the cancellation ladder of the companion chapter reduces a
homotopy six-sphere to a Morse function with exactly two critical points. What such a
function forces is the classical theorem of Reeb, and the formalization proves it in the
form that tolerates a twisted gluing — which is why the output is a homeomorphism and not
a diffeomorphism, and why no smoothing theory is needed.

:::definition "def:two-disk-decomposition" (lean := "Mathoverflow1973.Smale.TwoDiskDecomposition") (parent := "morse")
A covering of a space $`M` by two injectively embedded closed $`n`-balls, `left` and
`right`, whose ranges together exhaust $`M` and which overlap exactly along their
boundaries: $`\mathrm{left}(x) = \mathrm{right}(y)` holds precisely when $`x` and $`y` are
the images of a boundary point $`z` and of its image $`\varphi(z)` under a fixed
self-homeomorphism $`\varphi` of $`S^{n-1}`. The gluing homeomorphism $`\varphi` is
arbitrary — it is data, not a hypothesis to be normalised — and the twisted-double theory
then produces $`M \simeq_t S^n` regardless of which $`\varphi` occurs. This is the exact
point where the argument gives up on smooth structures: a smooth statement would need
$`\varphi` to extend over the ball, and it need not.
:::

:::definition "def:sublevel-disk" (lean := "Mathoverflow1973.Smale.SublevelDisk") (parent := "morse")
A witness that a sublevel set is a ball: a homeomorphism from the model $`n`-ball onto
$`\{x \in M : f(x) \le a\}` under which the boundary sphere corresponds exactly to the
level set,
$$`f\bigl(\mathrm{homeo}(v)\bigr) = a \iff \|v\| = 1.`
Below the first critical value above a nondegenerate minimum such a disc exists: near the
minimum a Morse chart gives one directly, since all weights are $`+1` there and the
sublevel sets are the model balls, and the flow of a gradient-like field carries that
picture out to any level below the next critical value.
:::

:::theorem "thm:nonempty-homeomorph-sphere-of-two-critical-points" (lean := "Mathoverflow1973.Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points") (parent := "morse") (uses := "def:critical-points, def:sublevel-disk, def:two-disk-decomposition, thm:nonempty-signed-morse-chart")
*Theorem (Reeb).* Let $`f` be a smooth Morse function on a compact Hausdorff smooth
manifold charted on a finite-dimensional $`E`, and suppose
$`\mathrm{crit}(f) = \{p, q\}` with $`f(p) < f(q)`. Then $`M` is homeomorphic to the
sphere $`S^{\dim_\R E}`.
:::

:::proof "thm:nonempty-homeomorph-sphere-of-two-critical-points"
With only two critical values, $`p` is the unique minimum and $`q` the unique maximum:
$`f` attains its extrema on the compact $`M` at critical points, and there are only two.
Fix the intermediate value $`a = (f(p) + f(q))/2`; no critical point has value in
$`(f(p), a]`, so the sublevel set $`\{f \le a\}` is a disc with boundary the level
$`\{f = a\}`. Applying the same argument to $`-f`, whose critical points are those of
$`f` and whose unique minimum is $`q`, presents $`\{f \ge a\}` as a second disc with the
same boundary. The two discs cover $`M` and meet exactly along that level, so they
constitute a two-disc decomposition whose gluing homeomorphism is whatever
self-homeomorphism of $`S^{\dim E - 1}` the two boundary parametrisations differ by. The
twisted-double construction identifies any such union with $`S^{\dim E}`.
$`\blacksquare`
:::

:::theorem "thm:homeomorphic-six-sphere-of-homotopy-six-sphere" (lean := "Mathoverflow1973.Smale.homeomorphic_sixSphere_of_homotopySixSphere") (parent := "morse") (uses := "thm:nonempty-homeomorph-of-homotopy-six-sphere")
*Theorem (generalised Poincaré in dimension six).* Let $`E` be a $`6`-dimensional real
normed space and $`M` a compact, Hausdorff, second-countable smooth manifold charted on
$`E`. If $`M` is homotopy equivalent to $`S^6 \subset \R^7`, then $`M` is homeomorphic to
$`S^6`.

This is the theorem {citet alpoge.s6}[] quotes from {citet smale61}[], and it is the only
one of §8's four classical inputs the formalization needs. Instantiated at
$`M = X` and $`E = \C \times \C^2` it produces the homeomorphism along which the
threefold's holomorphic atlas is transported onto the standard six-sphere.
:::

:::proof "thm:homeomorphic-six-sphere-of-homotopy-six-sphere"
The cancellation ladder produces from the homotopy equivalence a smooth Morse function on
$`M` with exactly two critical points, and Reeb's theorem finishes. That the ladder
terminates is the substance: an arbitrary Morse function with distinct critical values is
first rearranged so that indices increase with the critical value, using the rearrangement
lemma; handles of index $`0` and $`6` beyond the first and last are cancelled against
their neighbours; index $`1` and $`5` handles are traded for index $`3` ones by birth and
cancellation moves, which is legitimate because $`M` is simply connected; and the middle
handles are then cancelled in pairs. The pairing is possible because the vanishing of
$`H_2` and $`H_3` for a homotopy six-sphere makes the integer matrix of index-$`2` against
index-$`3` handles invertible, and handle slides realise integer column operations on it
geometrically; reduction to the identity leaves each index-$`3` attaching sphere meeting
one index-$`2` belt sphere in a single algebraic point, which the Whitney trick converts
into a single geometric point, the hypothesis for cancelling the pair.
$`\blacksquare`
:::
