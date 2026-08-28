/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — cancellation and the two-critical-point theorem chapter.

The h-cobordism-style engine of the recognition step: gradient-like flows, regular levels,
general position, the Whitney trick, handle cancellation and rearrangement, and the proof
that a compact smooth 6-manifold homotopy equivalent to the 6-sphere is homeomorphic to it.
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

#doc (Manual) "Cancellation and the two-critical-point theorem" =>

Section 8 of {citet alpoge.s6}[] disposes of the recognition step in a page. The threefold
$`X` is a closed smooth $`6`-manifold, simply connected, with the integral homology of
$`S^6`; Hurewicz and the homology Whitehead theorem make it a homotopy $`6`-sphere;
Smale's generalised Poincaré theorem {citep smale61}[] makes it homeomorphic to $`S^6`;
the $`h`-cobordism theorem {citep milnor65}[] together with $`\Theta_6 = 0`
{citep kervaire.milnor63}[] upgrades that to a diffeomorphism. Four classical theorems,
each cited rather than proved. The formalization has to supply one of them outright, and
it stops exactly where the statement being proved permits: what is constructed here is a
*homeomorphism* $`X \cong_{\mathrm{top}} S^6`, obtained from Reeb's theorem applied to a
Morse function with two critical points. Smoothing theory, the exotic-sphere group, and
the cobordism category are never touched, because transporting a complex atlas along a
homeomorphism is enough for the atlas-transport finale.

Nothing of the required machinery exists in Mathlib. Manifolds, `ContMDiff`, tangent
bundles, `Flow`, integral curves and Hausdorff dimension are imported; Morse theory,
transversality, tubular neighbourhoods, ambient isotopy, handle calculus, and Sard's
theorem are not, and all of them are built here over the manifold library. Two design
decisions shape the whole chapter. Everything is phrased as *one Morse function on a
closed manifold* — no cobordism category is ever defined, so the classical statements
about $`h`-cobordisms reappear as statements about critical points of a single
$`f : M \to \R`. And every cancellation theorem is used to contradict the minimality of a
critical-count-minimal system chosen by `Nat.find`, rather than to drive an induction; the
same device, applied to an index-disorder statistic, proves the rearrangement theorem.
Sard's theorem is replaced throughout by a Hausdorff-dimension count.

The route runs as follows. A Morse function acquires a gradient-like vector field and its
flow; regular levels are smooth hypersurfaces and critical-point-free bands are product
regions. Rearranging critical values puts them in index order. A handle trade removes
index $`1` and, dually, index $`5`. What remains is the middle: an $`r \times n` integer
matrix records how the descending $`2`-spheres of the index-$`3` points sit against the
index-$`2` handles, its surjectivity comes from the vanishing of $`H_2` and $`H_3` of a
homotopy sphere, and integer column operations are realized geometrically by handle slides
and by the Whitney trick in the $`5`-dimensional middle level. The outcome is a Morse
function with exactly two critical points, and Reeb's theorem finishes.

# The h-cobordism toolbox

:::group "smale-machinery"
Gradient-like flows and their global existence on a compact manifold; regular level sets as
smooth hypersurfaces; a Hausdorff-dimension substitute for Sard's theorem; tubular
neighbourhoods through a Euclidean embedding; ambient isotopy and parametric
transversality; embedded Whitney disks in general position; the Whitney trick in an
explicit polynomial bigon model; the homology of attaching a single cell; and the
local-degree calculus that turns a geometric intersection into an integer sign.
:::

The first two constructions are the ones every later argument stands on: a vector field on
a compact manifold integrates to a global flow, and a regular level of a smooth function is
a manifold in its own right.

:::definition "def:flow-construction-compact-flow" (lean := "Mathoverflow1973.Smale.FlowConstruction.compactFlow") (parent := "smale-machinery")
*Definition.* A $`C^1` vector field $`v` on a compact Hausdorff manifold $`M` modeled on a
complete space $`E` generates a global flow. Compactness removes the escape-time problem,
so Mathlib's local integral curves patch into a genuine action of $`\R`: `compactFlow` is a
term of type `Flow ℝ M`, that is, a continuous map $`F : \R \times M \to M` with
$`F_0 = \mathrm{id}` and $`F_{s+t} = F_s \circ F_t`. The link back to the field is
`isMIntegralCurve_compactFlow`, which says each orbit $`t \mapsto F_t x` is an integral
curve of $`v`. Every flow in the chapter — descent flows, height-translating flows, the
flows carried inside the cancellation packages — is an instance of this one construction.
:::

:::definition "def:regular-level-charted-space" (lean := "Mathoverflow1973.Smale.RegularLevel.chartedSpace") (parent := "smale-machinery") (uses := "def:critical-points")
*Definition.* Let $`f : M \to \R` be smooth on an $`\infty`-smooth manifold modeled on
$`E`, and let $`b` be a regular value, in the sense that no point of $`\{f = b\}` is a
critical point of $`f`. The subtype $`\{x : M \mid f(x) = b\}` is given a charted-space
structure over $`\R^{\dim E - 1}` — Mathlib's `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))`.
The charts are built from *height charts*: charts of $`M` onto open subsets of
$`\R \times \R^{\dim E - 1}` whose first coordinate is literally $`f` itself, so that the
level set becomes the slice $`\{b\} \times \R^{\dim E - 1}`, and the level chart is that
slice read off in the remaining coordinates.
Regularity is what makes $`f` usable as a coordinate, and phrasing the atlas this way
means the inclusion into $`M` is smooth by construction rather than by a further argument.
:::

:::theorem "thm:regular-level-is-manifold" (lean := "Mathoverflow1973.Smale.RegularLevel.isManifold") (parent := "smale-machinery") (uses := "def:regular-level-charted-space")
*Theorem (implicit function theorem for level sets).* With the level-chart atlas, a regular
level set $`\{f = b\}` is an $`\infty`-smooth manifold modeled on $`\R^{\dim E - 1}`. The
companion `contMDiff_inclusion` makes the inclusion
$`\{f = b\} \hookrightarrow M` smooth for that structure. Because the atlas is
instance-level data attached to a proof of regularity, later statements about level sets
open with a `letI := chartedSpace hf hreg` and then quantify over diffeomorphisms of the
level — the smooth structure is a hypothesis-derived instance, not a global one.
:::

:::proof "thm:regular-level-is-manifold"
Smoothness of a charted space reduces to smoothness of the transition maps between charts
of the atlas, which is what `isManifold_of_contDiffOn` asks for. Each chart in the atlas is
a slice of a height chart, so a transition between two of them is the slice of a transition
between two charts of $`M`, restricted to the hyperplane where the height coordinate
vanishes. That restriction is smooth because the ambient transition is, and it maps the
hyperplane to itself because both height charts have $`f` as their first coordinate:
`contDiffOn_slice_transition` performs exactly this bookkeeping. No inverse function
theorem is invoked at this point; the work was done when the height charts were built.
$`\blacksquare`
:::

:::theorem "thm:exists-adapted-descent-flow" (lean := "Mathoverflow1973.Smale.FlowConstruction.exists_adaptedDescentFlow") (parent := "smale-machinery") (uses := "def:flow-construction-compact-flow, thm:exists-adapted-descent-field")
*Theorem.* A Morse function $`f` on a compact manifold admits a gradient-like field
together with its flow. There are a smooth vector field $`V` and a flow $`F` with: $`V`
vanishing exactly on $`\mathrm{crit}(f)`; $`df_x(V_x) < 0` at every non-critical $`x`;
near each critical point $`p`, agreement of $`V` with the standard descent field of some
signed Morse chart at $`p`; every orbit of $`F` an integral curve of $`V`; critical points
fixed by $`F`; $`t \mapsto f(F_t x)` strictly decreasing for non-critical $`x`, and
antitone for every $`x`. The last two clauses are what make the flow usable as a
substitute for a gradient: $`f` is a Lyapunov function whose only rest points are the
critical points. The local normal form near each critical point is the clause that later
lets the flow be computed in cubic model coordinates.
:::

Transversality arguments in the chapter never invoke Sard's theorem. Instead they use a
dimension count on Hausdorff measure: a smooth image cannot raise Hausdorff dimension, so
the image of a low-dimensional manifold is too thin to be an obstruction. The two forms in
which this is used are a density statement and a non-surjectivity statement.

:::theorem "thm:dense-compl-manifold-image" (lean := "Mathoverflow1973.Smale.GeneralPosition.dense_compl_manifold_image") (parent := "smale-machinery")
*Theorem (general position).* Let $`X` be an $`\infty`-smooth Lindelöf manifold modeled on
$`E`, let $`F` be a finite-dimensional real space with $`\dim E < \dim F`, let
$`s \subseteq X` be open and let $`f` be smooth on $`s`. Then $`(f(s))^{\complement}` is dense
in $`F`. The proof is a single application of `dimH_image_manifold_le`, the bound
$`\dim_H f(s) \le \dim E`, followed by the observation that a subset of Hausdorff dimension
strictly below $`\dim F` has dense complement. This is the workhorse behind every choice of
a generic perturbation vector in the chapter: one wants a small $`a` avoiding a bad set,
and the bad set is always the image of a parameter manifold of too small a dimension.
:::

:::theorem "thm:not-surjective-cont-mdiff-of-dim-lt" (lean := "Mathoverflow1973.NoExotic.not_surjective_contMDiff_of_dim_lt") (parent := "smale-machinery")
*Theorem (Sard substitute).* A smooth map $`f : M \to N` between boundaryless manifolds,
with $`M` Lindelöf modeled on $`E`, $`N` nonempty modeled on $`F`, and
$`\dim E < \dim F`, is never surjective. Taking a centred chart $`d` at any point of $`N`
and restricting to $`s = f^{-1}(d.\mathrm{source})`, surjectivity would force $`d \circ f`
to cover the open set $`d.\mathrm{target} \subseteq F`, contradicting the Hausdorff
dimension bound. Beyond its use in general position, this is the statement that drives the
from-scratch proof of $`\pi_m(S^n) = 0` for $`m < n`: a smooth representative omits a
point, and a map omitting a point contracts stereographically.
:::

:::definition "def:smooth-retraction" (lean := "Mathoverflow1973.Smale.NativeEuclideanEmbedding.SmoothRetraction") (parent := "smale-machinery")
*Definition (tubular neighbourhood).* Given a proper smooth embedding
$`e : M \hookrightarrow \R^N` with injective differential, a smooth retraction consists of
an open set $`\Omega \subseteq \R^N` containing $`e(M)`, together with a map
$`\rho : \R^N \to M`, smooth on $`\Omega`, with $`\rho(e(x)) = x` for all $`x`. On a
compact manifold one exists (`nonempty_smoothRetraction`), constructed from the normal
bundle: the displacement map $`(x, v) \mapsto e(x) + v` is a diffeomorphism from a
neighbourhood of the zero section onto a neighbourhood of $`e(M)`, and $`\rho` is its
inverse followed by the bundle projection. Everything in the file that needs to thicken a
submanifold — framed tubular neighbourhoods of embedded disks, collars of regular levels,
tubes along arcs — is built from a retraction of this kind.
:::

Away from the critical points the flow can be reparametrized to move at unit speed in the
height coordinate, which is the source of every product-structure statement about bands.

:::theorem "thm:exists-height-translating-flow" (lean := "Mathoverflow1973.Smale.FlowConstruction.exists_heightTranslatingFlow") (parent := "smale-machinery") (uses := "def:critical-points, def:flow-construction-compact-flow")
*Theorem.* If the band $`\{a \le f \le b\}` on a compact manifold contains no critical point
of $`f`, there is a flow $`F` on $`M` with

$$`f(F_t x) = f(x) + t`

whenever $`f(x)` and $`f(x) + t` both lie in $`[a, b]`. The field is the descent field
divided by $`-df(V)`, which is bounded away from zero on the compact band and cut off
outside it, so the height increases at unit rate for as long as the orbit stays in the
band; outside the band the flow is unconstrained and the statement says nothing. Both the
homotopy equivalence of sublevel sets and the homeomorphism of levels across a
critical-point-free band are immediate corollaries.
:::

Ambient isotopy is the currency in which every geometric move is stated. Rather than a
bundled isotopy type, the file uses a proposition about a diffeomorphism.

:::definition "def:isotopic-to-identity" (lean := "Mathoverflow1973.Smale.SupportedDiffeomorph.IsotopicToIdentity") (parent := "smale-machinery")
*Definition.* A diffeomorphism $`e` of $`M` is isotopic to the identity when there is a
smooth family $`A : \R \times M \to M` with $`A(0, \cdot) = \mathrm{id}`,
$`A(1, \cdot) = e`, and every time slice $`A(t, \cdot)` again a diffeomorphism. The
smoothness is joint in $`(t, y)`, so the family is a genuine smooth homotopy, and the
slice condition is existential — for each $`t` there is a diffeomorphism agreeing with
$`A(t, \cdot)` pointwise — which keeps the definition a `Prop`. The relation is closed
under composition (`trans`), and the constructions that produce isotopies (`bumpFamily`,
the graph motions of the Whitney model, the longitudinal tube motions) all deliver
compactly supported families, so the diffeomorphisms they produce are the identity outside
a compact set.
:::

:::theorem "thm:exists-ambient-transverse-plateau" (lean := "Mathoverflow1973.Smale.ChartMapPerturbation.exists_ambient_transverse_plateau") (parent := "smale-machinery") (uses := "def:isotopic-to-identity")
*Theorem (parametric transversality).* Let $`f : X \to N` and $`g : Y \to N` be smooth,
let $`c` be a chart of $`N` onto an open subset of $`F`, let $`\beta : F \to \R` be a
smooth compactly supported cutoff whose support lies in the chart's target, and suppose
$`\dim X + \dim Y = \dim F`. For every $`\varepsilon > 0`
there are a vector $`a` with $`\|a\| < \varepsilon` and a diffeomorphism $`e` of $`N` —
the bump translation $`y \mapsto c^{-1}(c(y) + \beta(c(y)) \cdot a)`, isotopic to the
identity and equal to the identity outside the chart — such that $`e \circ f` is transverse
to $`g` at every point $`x` at which $`\beta` is identically $`1` near $`c(f(x))`.
Transversality is stated as surjectivity of the coproduct
$`d(e \circ f)_x \oplus dg_y` (the predicate `NativeTransversality.At`), and the genericity
of $`a` comes from the density statement above applied to the collision parameter map. The
"plateau" is the region where the cutoff is flat, which is where the perturbation is an
honest translation and the dimension count applies.
:::

:::theorem "thm:exists-relative-embedded-avoidance-in-open" (lean := "Mathoverflow1973.Smale.ManifoldImmersion.exists_relative_embedded_avoidance_in_open") (parent := "smale-machinery") (uses := "def:smooth-retraction, thm:dense-compl-manifold-image")
*Theorem (embedded Whitney disks).* In a manifold $`N` of dimension at least $`5`, let
$`U \subseteq N` be open and $`f : E \to U` a smooth map of a plane ($`\dim E = 2`),
already injective and immersive on $`K \cap C` for a compact $`K` and a closed $`C`, and
already avoiding the image of a compact obstacle $`g : Y \to N` on
$`(K \cap C) \setminus B`, where $`B \subseteq \operatorname{int} C` and
$`2 + \dim Y < \dim N`. Then $`f` is
homotopic rel $`C` to a smooth $`f'` which is a closed embedding on $`K`, has injective
differential at every point of $`K`, and avoids $`\mathrm{range}\,g` on $`K \setminus B`.
The two hypotheses are the two classical dimension counts: $`2 \cdot 2 < \dim N` removes
self-intersections of the disk, and $`2 + \dim Y < \dim N` removes intersections with the
obstacle. This is the input that produces a Whitney disk in general position, and it is the
place where $`\dim N \ge 5` — hence the restriction to $`5`-dimensional regular levels of a
$`6`-manifold — first becomes essential.
:::

The Whitney trick itself is formalized on an explicit polynomial model, so that every
boundary germ and every normal frame is a formula rather than an existential.

:::definition "def:whitney-pair-model-bigon" (lean := "Mathoverflow1973.Smale.WhitneyPairModel.bigon") (parent := "smale-machinery")
*Definition (the model Whitney disk).* For a height $`h > 0`,

$$`\mathrm{bigon}(h) = \{(s,t) \in \R^2 : 0 \le t,\ h s^2 + t \le h\},`

the compact region between the parabolic arc $`t = h(1 - s^2)` and the $`s`-axis. Its two
corners are $`(\pm 1, 0)`, and they are the pair of intersection points to be cancelled.
Two model sheets pass through the boundary arcs: `firstSheet` carries $`(u, w)` to
$`((u, 0), (w, 0))` and `secondSheet` carries $`(u, w)` to
$`((u, h(1 - u^2)), (0, w))`, so the first sheet contains the axis and the second contains
the arc, and the two meet exactly at the corners. Hard-coding the disk as this polynomial
region — rather than positing an abstract embedded disk — is what makes the pushing
isotopy below an explicit finite composition.
:::

:::theorem "thm:exists-supported-native-bigon-cancellation" (lean := "Mathoverflow1973.Smale.RankThreeWhitneyModel.exists_supported_native_bigon_cancellation") (parent := "smale-machinery") (uses := "def:whitney-pair-model-bigon")
*Theorem (the model Whitney trick).* Let $`\Phi` be a chart of the rank-three model space
$`(\R \times \R) \times (\R^1 \times \R^2) \cong \R^5` into $`M` whose source contains the
zero section over $`\mathrm{bigon}(h)`, with $`h > 0`. Then there are a compact
$`K \subseteq \Phi.\mathrm{target}` and a smooth family $`A : \R \times M \to M` with
$`A(0, \cdot) = \mathrm{id}`, every slice a diffeomorphism, $`A(t, y) = y` for
$`y \notin K`, and $`A(1, \cdot)` carrying the image of the first sheet off the second sheet
entirely. The isotopy is assembled from finitely many `graphStep` moves, each a vertical
shear smoothed by `Real.smoothTransition`, which lift the second sheet over the bigon; the
splitting into a $`2`-dimensional and a $`3`-dimensional sheet inside $`\R^5` is the case
needed for $`2`- and $`3`-spheres in the middle level of a $`6`-manifold.
:::

:::theorem "thm:exists-rank-three-relative-cancellation" (lean := "Mathoverflow1973.Smale.TubularBigon.exists_rankThree_relative_cancellation") (parent := "smale-machinery") (uses := "def:smale-tubular-bigon, thm:exists-supported-native-bigon-cancellation")
*Theorem (the Whitney trick).* Let $`S, T \subseteq M` be closed sets carrying clean strip
patches along arcs $`a` and $`b`, let a rank-three tubular bigon between them be given, let
both sheets carry strip normal data, and suppose the two corners have opposite intersection
signs, expressed as $`\det_0 \cdot \det_1 < 0` for the pair of normal-frame determinants
`rankThreeSheetPairDet`. Then there is a compact $`K` disjoint from
$`(S \cap T) \setminus \{a(0), a(1)\}` and a smooth ambient isotopy $`A` from the identity,
supported in $`K`, with

$$`A(1, \cdot)(S) \cap T = (S \cap T) \setminus \{a(0), a(1)\}.`

Exactly one cancelling pair of intersection points is removed, and no other intersection is
disturbed. The opposite-sign hypothesis is not decorative: it is precisely what is needed
to build the chart carrying $`S` and $`T` onto the two model sheets, after which the model
cancellation applies and `image_inter_eq_diff` converts the disjointness statement into the
displayed equality of intersections.
:::

The homological half of the toolbox tracks what handle attachments do to homology, and
converts geometric intersections into integers.

:::theorem "thm:cell-exact-at-old" (lean := "Mathoverflow1973.Smale.EmbeddedCellAttachment.cell_exact_at_old") (parent := "smale-machinery") (uses := "thm:singular-mayer-vietoris-exact-at-pair")
*Theorem.* Let $`X` be presented as a closed set $`A` together with one embedded closed
cell $`D^n \hookrightarrow X` meeting $`A` exactly along its boundary sphere. For
$`k \ne 0`,

$$`\mathrm{range}\big(H_k(S^{n-1}) \to H_k(A)\big) = \ker\big(H_k(A) \to H_k(X)\big),`

the two maps being induced by the attaching map and by the inclusion. Together with
`cell_exact_at_ambient` and `cell_exact_at_sphere` this is the long exact sequence of a
single cell attachment, proved over the project's own singular homology and not over any
CW theory: the cover used is $`A^{\complement}` together with the complement of the inner
half of the cell, both open, and the Mayer–Vietoris exactness at the pair is what supplies
the argument. The restriction $`k \ne 0` is where the contractibility of the cell patch is
used.
:::

:::theorem "thm:exists-regular-sublevel-homotopy-equiv" (lean := "Mathoverflow1973.Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv") (parent := "smale-machinery") (uses := "thm:exists-height-translating-flow")
*Theorem.* If $`a \le b` and the band $`\{a \le f \le b\}` on a compact manifold contains no
critical point, the inclusion $`\{f \le a\} \hookrightarrow \{f \le b\}` is a homotopy
equivalence — and the equivalence produced satisfies $`(e\,x).1 = x.1`, so it *is* the
inclusion, not merely a map homotopic to it. The homotopy inverse is the explicit
deformation retraction that pushes a point down the height-translating flow until its
height reaches $`a` and leaves it alone if it is already there. Sublevel sets therefore
change homotopy type only when a critical value is crossed, which is the bookkeeping every
homological argument in the endgame relies on.
:::

:::theorem "thm:nonempty-regular-level-homeomorph" (lean := "Mathoverflow1973.Smale.FlowConstruction.nonempty_regularLevelHomeomorph") (parent := "smale-machinery") (uses := "thm:exists-height-translating-flow")
*Theorem.* Across a critical-point-free band, the regular levels are homeomorphic:
$`\{f = a\} \cong_{\mathrm{top}} \{f = b\}` whenever $`a \le b` and no critical point has
value in $`[a, b]`. Flowing for time $`b - a` is a homeomorphism, with the reverse flow as
inverse. Only a homeomorphism is claimed — the two levels carry smooth structures from
different height charts, and identifying those is never needed; what is needed downstream
is the transport of topological properties, such as the null-homotopy of every circle,
between the levels of a band.
:::

:::definition "def:sphere-connecting" (lean := "Mathoverflow1973.Smale.LocalDegree.NativeNeighborhood.sphereConnecting") (parent := "smale-machinery") (uses := "def:connecting-homomorphism, def:homotopy-equiv-homology-equiv")
*Definition (local connecting homomorphism).* At a nondegenerate zero $`x` of a map
$`f : M \to F`, quantified by neighbourhood data comparing $`f` to a linear equivalence
$`L` in the centred parametrization at $`x`, the local connecting map

$$`H_{k+1}(M;\Z) \longrightarrow H_k(S(E);\Z)`

is the Mayer–Vietoris connecting homomorphism of the open cover
$`\big(M \setminus \{x\},\ U_x\big)`, followed by the inverse of the homology isomorphism
induced by the homotopy equivalence between the punctured neighbourhood and the unit sphere
of $`E`. It is natural under diffeomorphisms (`pointConnecting_diffeomorph`) and under the
normalized linear sphere maps $`u \mapsto Au/\|Au\|`, and it is the device by which a
geometric intersection at a point becomes an element of a homology group of a sphere.
:::

:::definition "def:integer-presentation" (lean := "Mathoverflow1973.Smale.IntegerPresentation") (parent := "smale-machinery")
*Definition.* A presentation of a $`\Z`-module $`B` by $`r` generators and $`c` relations
consists of a surjection $`\Z^r \twoheadrightarrow B` whose kernel is the span of $`c`
given columns of $`\Z^r`. The theory attached to it is deliberately small: `ofEquiv` turns
an isomorphism $`\Z^r \cong B` into a presentation with no relations, `transport` carries a
presentation along an isomorphism of modules, and `adjoin` adds one relation across a
quotient whose kernel is cyclic. Injectivity criteria for the presentation matrix
accompany them. This stands in for Smith normal form and the structure theory of finitely
generated modules, neither of which is needed: the only thing the endgame asks of
$`H_2` of a sublevel set is that a basis coming from the index-$`2` handles be tracked
across the successive attachments of the index-$`3` handles.
:::

:::theorem "thm:local-boundary-homology-outward" (lean := "Mathoverflow1973.Smale.SphereNormalCoordinates.localBoundary_homology_outward") (parent := "smale-machinery") (uses := "def:singular-homology-map")
*Theorem (local degree is the Jacobian sign).* Let $`f` be a map from the unit sphere of a
space $`V` of dimension $`n + 3` into $`F`, differentiable with invertible differential at
$`c(0)` for a chart $`c`, and let boundary data compare $`f \circ c` with a linear
equivalence $`L`. Then, in degree $`k + 1`, the normalized map of the boundary data acts on
homology by

$$`\alpha \longmapsto \operatorname{sign}\big(J_{\mathrm{normal}}\big)\, \big(\text{reference linear sphere map}\big)_*\alpha,`

after twisting by the sign of the chart Jacobian. In words: the homological local degree of
$`f` at a nondegenerate zero equals the sign of an explicit determinant. This is the bridge
between the two languages of the endgame — geometric intersection points on one side,
integer entries of the middle matrix on the other — and it is what makes the Whitney
trick's opposite-signs hypothesis checkable, since no orientation or intersection theory is
developed anywhere in the file.
:::

# Cancelling critical points

:::group "cancellation"
The Morse-theoretic apparatus proper: adapted systems of surgery windows, the chart-free
Morse index and its counting function, the cubic birth-and-death model, the two
cancellation theorems, Smale's rearrangement theorem, the birth lemma, and the handle trade
that removes index $`1` from a homotopy $`6`-sphere.
:::

A Morse function is not by itself a workable object; what the arguments manipulate is a
Morse function together with a compatible system of local models and one global flow. That
package is the `AdaptedWindows` structure, and its existence is the first theorem of the
argument.

:::theorem "thm:nonempty-adapted-surgery-windows" (lean := "Mathoverflow1973.MorseCancel.nonempty_adaptedSurgeryWindows") (parent := "cancellation") (uses := "def:adapted-windows, def:flow-construction-compact-flow, thm:exists-adapted-descent-field, thm:exists-morse-surgery-data-lt")
*Theorem.* Every smooth Morse function with injective critical values on a compact manifold
admits an adapted system of surgery windows. The system supplies, for each critical point
$`p`, a Morse-model chart with a radius $`r_p` whose value window
$`[f(p) - r_p^2,\ f(p) + r_p^2]` contains no other critical value, and the windows are
pairwise separated: $`f(p) + r_p^2 < f(q) - r_q^2` whenever $`f(p) < f(q)`. Globally it
supplies a smooth vector field $`V` with its flow, vanishing exactly on
$`\mathrm{crit}(f)`, strictly decreasing $`f` elsewhere, and agreeing with the model
descent field of the chart near every point of the chart block of radius $`2 r_p`. The
separation of windows is what lets a construction be performed inside one window without
disturbing another, and the germ condition on the field is what lets the flow be computed
in model coordinates near a critical point.
:::

:::proof "thm:nonempty-adapted-surgery-windows"
Finiteness of the critical set and injectivity of $`f` on it give separated value radii
$`r_p`: an assignment of positive numbers with $`f(p) + r_p < f(q) - r_q` for consecutive
critical values. Shrinking each Morse-model chart to radius less than $`r_p / 3`
(`exists_morseSurgeryData_lt`, applied with the isolation requirement that no other
critical point has value in the window) makes $`9 r_p^2 < r_p^2 \cdot 9 < (r_p)^2 \cdot 9`
small enough that the enlarged windows are still pairwise disjoint — the arithmetic is a
`nlinarith` step from $`3 \cdot \mathrm{radius} < r_p`. With disjoint windows in hand, the
local descent fields of the individual charts are prescribed on disjoint closed blocks and
patched into a single global field by the partition-of-unity lemma
`exists_disjoint_surgery_block_field`, whose output is exactly the field, the flow, and the
three conditions (vanishing on the critical set, strict descent off it, model germ near
each critical point) required by the structure. $`\blacksquare`
:::

:::definition "def:morse-cancel-cubic" (lean := "Mathoverflow1973.MorseCancel.cubic") (parent := "cancellation")
*Definition (the birth-and-death model).* On the model space
$`\mathrm{Model}\,m = \R \times (\mathrm{Fin}\,m \to \R)`, with a sign vector
$`\sigma` and a parameter $`t`,

$$`\mathrm{cubic}\,\sigma\,t\,(x, y) = \frac{x^3}{3} + t x + \sum_i \sigma_i y_i^2.`

Its differential vanishes when $`x^2 + t = 0` and $`\sigma_i y_i = 0` for all $`i`, so for
$`t > 0` there are no critical points at all, and for $`t = -a^2 < 0` there are exactly two,
$`(\pm a, 0)`, whose indices differ by one — the index at $`-a` exceeds the index at $`+a`
by exactly the contribution of the $`x`-direction. The Hessian
$`2x\,dx^2 + \sum_i 2\sigma_i\,dy_i^2` is bijective off $`x = 0`, so the model is Morse
for every $`t \ne 0`
(`cubic_isMorse`). One polynomial thus does double duty: sweeping $`t` upward through zero
kills a cancelling pair, sweeping it downward creates one.
:::

:::definition "def:native-morse-index" (lean := "Mathoverflow1973.MorseCancel.nativeMorseIndex") (parent := "cancellation") (uses := "def:signed-morse-chart")
*Definition.* The Morse index of $`f` at $`p` is the real dimension of the negative
coordinate subspace of a signed Morse chart of $`f` at $`p`. In Lean the definition is
total: if some signed Morse chart at $`p` exists, the index is the finrank of the negative
coordinates of an arbitrary chosen one, and otherwise it is $`0`. Choice is harmless
because `signed_morse_chart_negative_finrank_eq` shows any two charts at the same point
have negative subspaces of equal dimension; the index is furthermore invariant under
changing $`f` to a function with the same germ at $`p`, and is bounded by $`\dim E`.
Defining it chart-freely, rather than carrying a chart everywhere, is what allows the
counting arguments below to be stated at all.
:::

The First Cancellation Theorem is the statement that a pair of critical points of adjacent
indices joined by a single transverse connecting orbit can be removed. Its hypotheses are
bundled into a structure so that the theorem itself can be stated in one line.

:::definition "def:native-connection-cancellation-data" (lean := "Mathoverflow1973.MorseCancel.NativeConnectionCancellationData") (parent := "cancellation") (uses := "def:critical-points, def:morse-cancel-cubic")
*Definition.* Cancellation data for a pair $`p, q` of critical points of $`f` consists of:
a sign vector $`\sigma` with entries $`\pm 1`; a smooth gradient-like field with its flow,
vanishing on $`\mathrm{crit}(f)` and strictly decreasing $`f` elsewhere; cubic model charts
$`\Phi_q, \Phi_p` with $`\Phi_q(-\tfrac12, 0) = q` and $`\Phi_p(\tfrac12, 0) = p`, on whose
targets the field is the cubic descent field $`\mathrm{cubic}\,\sigma\,(-\tfrac14)`
transported through the chart; a tube chart $`A` along the connecting orbit on which the
field is the constant vertical field and $`f` is affine in the tube coordinate,
$`f(A(z)) = \mathrm{height} - \mathrm{speed} \cdot z_2`; basin descriptions saying that a
point of $`\Phi_q.\mathrm{source}` flows backward to $`q` exactly when its positive
coordinates vanish, and dually at $`p`; and the uniqueness clause that any point flowing
backward to $`q` and forward to $`p` lies on the single orbit through $`A(0,0)`. A
transversality predicate on the endpoint slices completes the package.
:::

:::theorem "thm:native-connection-cancellation-data-cancel" (lean := "Mathoverflow1973.MorseCancel.NativeConnectionCancellationData.cancel") (parent := "cancellation") (uses := "def:flow-construction-compact-flow, def:morse-cancel-cubic, def:native-connection-cancellation-data, thm:exists-compact-isotopy-suspension, thm:remove-morse-band-pair")
*Theorem (First Cancellation Theorem).* Suppose transverse cancellation data is given for
$`p, q` with $`f(p) < f(q)`, and suppose $`c < f(p)`, $`f(q) < d` are such that $`p` and
$`q` are the only critical points with values in $`[c, d]`. Then there is a smooth Morse
function $`g` with

$$`\mathrm{crit}(g) = \mathrm{crit}(f) \setminus \{p, q\}, \qquad \#\mathrm{crit}(g) + 2 = \#\mathrm{crit}(f),`

and $`g` agreeing with $`f` on a neighbourhood of every point whose $`f`-value lies outside
$`(c, d)`. The new function is produced by removing the band: the flow is straightened by
the tube chart, the two cubic ends are joined into a single $`t > 0` cubic with no critical
points, and the modification is confined to the band by a cutoff. The statement is local in
value, not in space — nothing outside the value band $`(c, d)` moves at all.
:::

:::theorem "thm:cancel-of-transverse-level-isotopy" (lean := "Mathoverflow1973.MorseCancel.cancel_of_transverse_level_isotopy") (parent := "cancellation") (uses := "def:flow-construction-compact-flow, def:isotopic-to-identity, def:manifold-morse-is-morse, def:native-connection-cancellation-data, def:regular-level-charted-space, def:signed-morse-chart, thm:exists-native-level-flow-cylinder")
*Theorem (cancellation from a level isotopy).* The hypothesis of the previous theorem is
replaced by one that can be checked in a single regular level. Take signed Morse charts at
$`p` and $`q` with $`\operatorname{ind} q = \operatorname{ind} p + 1`, a gradient-like
field agreeing with the model descent fields near $`p` and $`q`, a regular value $`c` with
$`f(p) < c < f(q)` sitting inside a critical-point-free band $`[a, b]`, and a
diffeomorphism $`D` of the level $`\{f = c\}` that is isotopic to the identity. If the set
of level points that flow backward to $`q` and, after applying $`D`, forward to $`p`, is a
single point, and if the descending and ascending spheres meet transversally there, then
$`p` and $`q` cancel: a Morse function $`g` exists with
$`\mathrm{crit}(g) = \mathrm{crit}(f) \setminus \{p, q\}` and $`g = f` near every point
of value outside $`(l, u)`. The
isotopy $`D` is realized as a flow-preserving ambient motion of the band, which converts
"one transverse intersection after an isotopy" into the unique-orbit hypothesis of the
cancellation data.
:::

:::definition "def:native-morse-count" (lean := "Mathoverflow1973.MorseCancel.nativeMorseCount") (parent := "cancellation") (uses := "def:critical-points, def:native-morse-index")
*Definition.* $`c_k(f)` is the cardinality of the set
$`\{z \in \mathrm{crit}(f) : \operatorname{ind}(f, z) = k\}`, taken as `Set.ncard` and
finite because the critical set of
a Morse function on a compact manifold is finite. The entire endgame is a statement about
this sequence: starting from an arbitrary Morse function on a manifold homotopy equivalent
to $`S^6`, the profile $`(c_0, \dots, c_6)` is driven to $`(1, 0, 0, 0, 0, 0, 1)`. Duality
under $`f \mapsto -f`, which exchanges $`c_k` with $`c_{6-k}`, halves the work: index $`5`
and index $`4` are eliminated by applying the index $`1` and index $`2` arguments to
$`-f`.
:::

:::theorem "thm:exists-index-ordered-morse-system-preserving-critical-points" (lean := "Mathoverflow1973.MorseCancel.exists_index_ordered_morse_system_preserving_critical_points") (parent := "cancellation") (uses := "def:native-morse-count, thm:nonempty-adapted-surgery-windows")
*Theorem (Smale's rearrangement theorem).* Any adapted Morse system on a compact connected
manifold can be replaced by one with the same critical points, the same index at each of
them, and the same counts in every degree, whose critical values are ordered consistently
with the indices: $`f(p) < f(q)` implies $`\operatorname{ind} p \le \operatorname{ind} q`.
The proof is by minimality rather than induction. Let the index disorder of $`f` be the
number of inverted pairs among consecutive critical values; `Nat.find` selects a Morse
function, with the same critical points and indices as the given one, minimizing that
statistic. If its values were not index-ordered there would be an adjacent inversion, and a
pair of consecutive critical points with $`\operatorname{ind} q < \operatorname{ind} p`
admits no connecting orbit for dimension reasons, so their values may be exchanged; the
exchange strictly decreases the disorder, contradicting minimality.
:::

:::theorem "thm:exists-native-morse-birth" (lean := "Mathoverflow1973.MorseCancel.exists_native_morse_birth") (parent := "cancellation") (uses := "def:critical-points, def:manifold-morse-is-morse, def:morse-cancel-cubic")
*Theorem (birth lemma).* Let $`x` be a regular point of a Morse function $`f`, let
$`U \ni x` be open, and fix nonzero signs $`\sigma` with $`1 + m = \dim E`. There are
$`a, \delta > 0` and a chart $`\Phi` of $`\mathrm{Model}\,m` into $`U` with
$`(\pm a, 0) \in \Phi.\mathrm{source}`, on which $`f` reads as
$`f(x) + \delta \cdot \mathrm{cubic}\,\sigma\,(a^2)` — the critical-point-free branch — and
a new Morse function $`g` with $`\#\mathrm{crit}(g) = \#\mathrm{crit}(f) + 2`,

$$`\mathrm{crit}(g) = \mathrm{crit}(f) \cup \{\Phi(a, 0),\ \Phi(-a, 0)\},`

which agrees with $`f` outside $`U` and near every old critical point, and which reads as
$`f(x) + \delta \cdot \mathrm{cubic}\,\sigma\,(-a^2)` near each of the two new points. The
signs $`\sigma` are chosen freely, so a cancelling pair of any adjacent pair of indices can
be created inside any prescribed open set. This is what makes handle trading possible: one
manufactures a pair with the indices one wants, then cancels a different pair.
:::

:::theorem "thm:exists-one-to-three-handle-trade-of-ordered-indices" (lean := "Mathoverflow1973.MorseCancel.exists_one_to_three_handle_trade_of_ordered_indices") (parent := "cancellation") (uses := "def:native-connection-cancellation-data, def:native-morse-count, thm:dense-compl-manifold-image, thm:exists-embedded-disk-isotopy, thm:exists-morse-rearrangement-of-no-connection, thm:exists-native-descent-endpoints, thm:exists-native-morse-birth, thm:nonempty-adapted-surgery-windows, thm:nonempty-surgery-windows, thm:not-surjective-cont-mdiff-of-dim-lt")
*Theorem (handle trade).* On a compact $`6`-manifold $`M` homotopy equivalent to $`S^6`,
given an index-ordered adapted system with a unique index-$`0` point $`m` and some
index-$`1` point $`q`, there is a Morse function $`h` with distinct critical values, the
same total number of critical points as $`f`, and

$$`c_1(h) + 1 = c_1(f), \qquad c_3(h) = c_3(f) + 1, \qquad c_j(h) = c_j(f)\ (j \ne 1, 3).`

An index-$`1` point is traded for an index-$`3` point. The construction births a
cancelling $`2/3` pair just above a regular cut separating the low indices, slides the new
index-$`2` point's descending sphere across the level until it meets the ascending sphere
of $`q` in a single transverse point — general position in a $`5`-dimensional level makes
this possible, and the uniqueness of the minimum makes the ascending sphere of $`q`
connected — and then cancels $`q` against it. The count of index-$`1` points drops by one
and the newly born index-$`3` point survives. Applied to $`-f`, the same theorem removes
index $`5`.
:::

:::theorem "thm:exists-minimal-ordered-morse-system-without-outer-indices" (lean := "Mathoverflow1973.MorseCancel.exists_minimal_ordered_morse_system_without_outer_indices") (parent := "cancellation") (uses := "def:homotopy-equiv-homology-equiv, thm:exists-index-ordered-morse-system-preserving-critical-points, thm:exists-morse-function, thm:exists-one-to-three-handle-trade-of-ordered-indices, thm:exists-regular-sublevel-homotopy-equiv, thm:nonempty-signed-morse-chart, thm:singular-mayer-vietoris-exact-at-pair")
*Theorem.* On any compact $`6`-manifold $`M` homotopy equivalent to $`S^6` there is a
smooth Morse function $`f` with an adapted, index-ordered system of surgery windows,
counts

$$`c_0(f) = c_6(f) = 1, \qquad c_1(f) = c_5(f) = 0,`

and a total number of critical points minimal among all Morse functions on $`M` with
distinct critical values. The minimality is not an extra property to be arranged
afterwards; it is chosen first, by `Nat.find`, and every subsequent theorem in the chapter
is a proof that some configuration would allow a further cancellation and therefore cannot
occur.
:::

:::proof "thm:exists-minimal-ordered-morse-system-without-outer-indices"
Fix, by `Nat.find` applied to the set of achievable critical counts, a Morse function with
distinct critical values and minimal critical count, and rearrange it into index order —
rearrangement preserves the critical set and all counts, so minimality survives. Path
connectivity of $`M`, which follows from the homotopy equivalence with $`S^6`, and an
$`H_0`-argument identifying path components with classes in degree-zero homology force
$`c_0 = 1`: two distinct minima would give two components of the sublevel set below the
first index-$`1` value, and the $`0/1` cancellation theorem would remove a pair,
contradicting minimality. Dually $`c_6 = 1`. With a unique minimum in hand, any
index-$`1` point could be traded for an index-$`3` point without changing the total count,
and after the trade the resulting function is still minimal; iterating until no index-$`1`
point remains gives $`c_1 = 0`, and the same argument for $`-f` gives $`c_5 = 0`.
$`\blacksquare`
:::

# Middle indices and the two-critical-point theorem

:::group "cancellation-endgame"
What survives after the outer indices are gone is the middle block: index $`2`, $`3` and
$`4` critical points, whose interaction is recorded by an integer matrix. Its surjectivity
comes from the vanishing of the middle homology of a homotopy sphere, and the Whitney trick
converts an algebraic unit into a geometric cancellation. The counts collapse to two, and
Reeb's theorem produces the homeomorphism.
:::

At a regular cut between the index-$`2` block and the index-$`3` block, each index-$`3`
point contributes an embedded $`2`-sphere in the cut level — the set of level points that
flow backward into it — and each index-$`2` point contributes a generator of the second
homology of the sublevel set below the cut. The pairing between the two is an integer
matrix.

:::definition "def:canonical-middle-matrix" (lean := "Mathoverflow1973.MorseCancel.canonicalMiddleMatrix") (parent := "cancellation-endgame") (uses := "def:singular-homology-map, def:unit-sphere-homology-top-equiv")
*Definition.* Let $`a` be a regular value, let
$`B : \Z^r \xrightarrow{\ \sim\ } H_2(\{f \le a\};\Z)` be a basis coming from the
$`r` index-$`2` handles below the cut, and
let $`\gamma_1, \dots, \gamma_n` be continuous maps $`S^2 \to \{f = a\}`. The canonical
middle matrix is the $`r \times n` integer matrix whose $`j`-th column is the coordinate
vector of the class $`[\gamma_j] \in H_2(\{f \le a\})` in the basis $`B`, where
$`[\gamma_j]` is the image of the fundamental class of $`S^2` under $`\gamma_j` pushed into
the sublevel set. In the intended application the $`\gamma_j` are the descending
$`2`-spheres of the $`n` index-$`3` points, so the matrix is the algebraic shadow of how
the $`3`-handles are attached along the $`2`-handles. Surjectivity of
$`z \mapsto (\text{matrix}) z` is `canonical_middle_matrix_surjective`, and it holds
because $`H_2` and $`H_3` of a homotopy $`6`-sphere vanish, forcing the middle-section
classes to span.
:::

:::theorem "thm:cancel-from-complete-middle-family" (lean := "Mathoverflow1973.MorseCancel.cancel_from_complete_middle_family") (parent := "cancellation-endgame") (uses := "def:canonical-middle-matrix, def:homotopy-equiv-homology-equiv, def:isotopic-to-identity, def:native-morse-index, thm:nonempty-adapted-surgery-windows, thm:regular-level-is-manifold")
*Theorem (Whitney cancellation of a $`2/3` pair).* Let $`p` be an index-$`2` critical point
of an index-ordered adapted system on a compact $`6`-manifold, and write
$`c = f(p) + r_p^2` for the top of its window. Suppose the collapse coordinate
$`H_2(\{f \le c\}) \to \Z` attached to $`p`'s handle is surjective, every circle in the
lower level $`\{f = f(p) - r_p^2\}` is null-homotopic, and every critical point of index
below $`3` has value less than $`c`. Let $`\gamma_1, \dots, \gamma_n` be a complete family
of descending $`2`-spheres in $`\{f = c\}` for the index-$`3` points, whose windows all lie
above $`c`, and suppose the canonical middle matrix of that family against a basis
$`\Z^r \cong H_2(\{f \le c\})` is surjective. Then there is a Morse function $`v` with
distinct critical values and $`\#\mathrm{crit}(v) + 2 = \#\mathrm{crit}(f)`. Surjectivity
of the collapse coordinate is what makes the class of $`p` primitive, and the null-homotopy
of circles in the lower level is what leaves room for a Whitney disk in the middle level.
:::

:::theorem "thm:minimal-ordered-index-two-count-zero" (lean := "Mathoverflow1973.MorseCancel.minimal_ordered_index_two_count_zero") (parent := "cancellation-endgame") (uses := "def:canonical-middle-matrix, def:native-morse-count, thm:cancel-from-complete-middle-family, thm:exists-regular-sublevel-homotopy-equiv")
*Theorem.* A critical-count-minimal, index-ordered adapted system on a compact
$`6`-manifold homotopy equivalent to $`S^6`, with $`c_0 = 1` and $`c_1 = 0`, has
$`c_2 = 0`. The index-$`2` points form a prefix block of $`r` points followed by a block of
$`n` index-$`3` points; if $`r > 0` the machinery of the previous theorem produces a Morse
function with two fewer critical points, contradicting minimality.
:::

:::proof "thm:minimal-ordered-index-two-count-zero"
Index ordering splits the critical points into an index-$`2` prefix of length $`r` and an
index-$`3` block of length $`n`, with everything of index at least $`4` above them. Suppose
$`r > 0` and let $`q` be the topmost index-$`2` point, $`a` the top of its window. An
adapted system with smaller radii is chosen so that the descending spheres of the
index-$`3` points can be flowed down to the level $`\{f = a\}` as a disjoint embedded
family $`\gamma_j`, and the basis of $`H_2(\{f \le a\})` supplied by the index-$`2` handles
makes the canonical middle matrix defined. That matrix is surjective, because
$`H_2` and $`H_3` of $`M` vanish and the sublevel inclusions across critical-point-free
bands are homotopy equivalences, so the classes $`[\gamma_j]` must already span. A belt-cut
step then arranges the collapse coordinate of $`q` to be primitive and the circles in its
lower level to be null-homotopic, which are exactly the hypotheses of the Whitney
cancellation theorem; applying it produces $`v` with
$`\#\mathrm{crit}(v) + 2 = \#\mathrm{crit}(f)`, contradicting the minimality hypothesis.
Hence $`r = 0`, that is,
$`c_2 = 0`. Applying the same argument to $`-f` gives $`c_4 = 0`. $`\blacksquare`
:::

:::theorem "thm:ordered-no-middle-indices-count-two" (lean := "Mathoverflow1973.MorseCancel.ordered_no_middle_indices_count_two") (parent := "cancellation-endgame") (uses := "def:integer-presentation, def:native-morse-count, def:surgery-windows")
*Theorem.* An index-ordered system of surgery windows on a compact $`6`-manifold homotopy
equivalent to $`S^6` with

$$`c_0 = c_6 = 1, \qquad c_1 = c_2 = c_4 = c_5 = 0`

also has $`c_3 = 0`, and then exactly two windows: $`S.\mathrm{count} = 2`. The
index-$`3` points cannot be removed one at a time — there is nothing left to cancel them
against — so they are excluded by a rank count instead.
:::

:::proof "thm:ordered-no-middle-indices-count-two"
Write $`r` for the length of the index-$`2` prefix and $`n` for the length of the
index-$`3` block; the hypothesis $`c_2 = 0` gives $`r = 0` and the hypothesis
$`c_4 = c_5 = 0` together with $`c_6 = 1` shows the blocks are complete, so the total count
is $`r + n + 2`. The middle matrix of the system, built by adjoining one relation to an
integer presentation of $`H_2` of the sublevel set for each index-$`3` handle in turn, is
injective — each adjunction preserves injectivity of the presentation matrix because the
relevant $`H_3` of the intermediate sublevel set vanishes on a homotopy sphere — and it is
surjective for the same homological reason as before. A bijective map $`\Z^n \to \Z^r`
forces $`n = r` by rank, so $`n = r = 0`, that is, $`c_3 = 0` and the count is $`2`.
$`\blacksquare`
:::

:::theorem "thm:exists-two-critical-point-morse-of-homotopy-six-sphere" (lean := "Mathoverflow1973.MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere") (parent := "cancellation-endgame") (uses := "thm:exists-minimal-ordered-morse-system-without-outer-indices, thm:minimal-ordered-index-two-count-zero, thm:ordered-no-middle-indices-count-two, thm:simply-connected-space")
*Theorem (two-critical-point theorem).* Let $`M` be a compact smooth manifold modeled on a
real $`6`-dimensional space $`E`, and let $`e : M \simeq S^6` be a homotopy equivalence.
Then there is a smooth Morse function $`f : M \to \R` with exactly two critical points:
points $`p, q` with $`f(p) < f(q)` and $`\mathrm{crit}(f) = \{p, q\}`. The sphere here is
$`S^6 = \{v \in \R^7 : \|v\| = 1\}`, and no orientation, no smooth structure on the sphere,
and no comparison of smooth structures enters the statement.
:::

:::proof "thm:exists-two-critical-point-morse-of-homotopy-six-sphere"
The homotopy equivalence transports simple connectivity of $`S^6` to $`M`, hence path
connectivity, which is the standing hypothesis of the counting arguments. Choose a
critical-count-minimal index-ordered adapted system with $`c_0 = c_6 = 1` and
$`c_1 = c_5 = 0`. Minimality and the middle-matrix argument give $`c_2 = 0`, and the same
argument applied to $`-f` gives $`c_4 = 0`. The rank count then gives $`c_3 = 0` and shows
the system has exactly two windows. A system of two windows exhibits its critical set
directly: the two window centres $`p` and $`q` satisfy $`f(p) < f(q)` and
$`\mathrm{crit}(f) = \{p, q\}`, since every critical point is a window centre and there are
only two. $`\blacksquare`
:::

:::theorem "thm:nonempty-homeomorph-of-homotopy-six-sphere" (lean := "Mathoverflow1973.MorseCancel.nonempty_homeomorph_of_homotopySixSphere") (parent := "cancellation-endgame") (uses := "thm:exists-two-critical-point-morse-of-homotopy-six-sphere, thm:nonempty-homeomorph-sphere-of-two-critical-points")
*Theorem.* For a compact smooth manifold $`M` modeled on a real $`6`-dimensional space
$`E`, a homotopy equivalence $`M \simeq S^6` yields a homeomorphism
$`M \cong_{\mathrm{top}} S^6`. This is the result the cluster exports. The one-line wrapper
`Smale.homeomorphic_sixSphere_of_homotopySixSphere` restates it with the ambient hypotheses
the consumers carry, and the atlas-transport finale applies it to $`X`, the threefold of
the construction, along the homotopy equivalence supplied by the degree argument — after
which the complex atlas of $`X` is carried across the homeomorphism onto the unit
$`6`-sphere, answering {citep mathoverflow1973}[].
:::

:::proof "thm:nonempty-homeomorph-of-homotopy-six-sphere"
Take the Morse function $`f` with critical set $`\{p, q\}` and $`f(p) < f(q)`. Reeb's
theorem, in the form proved for this development, says that a compact manifold carrying a
Morse function with exactly two critical points is homeomorphic to the sphere of the
model's dimension: the sublevel set below a regular value between $`f(p)` and $`f(q)` is a
disk, since it deformation-retracts down the descent flow onto the minimum and the Morse
chart identifies a neighbourhood of the minimum with a ball; the superlevel set is a disk
for the same reason applied to $`-f`; and the manifold is the union of the two along their
common boundary level, which is the classical twisted-sphere presentation. Gluing two disks
along a homeomorphism of their boundary spheres gives a space homeomorphic to $`S^n`, and
no smooth structure on the result is claimed — this is exactly why the argument stops short
of a diffeomorphism, and why $`\Theta_6 = 0` is never needed. Rewriting the model dimension
$`\dim E = 6` turns the conclusion into $`M \cong_{\mathrm{top}} S^6`. $`\blacksquare`
:::

The gap between this and Theorem 8.1 of {citet alpoge.s6}[] is deliberate and is documented
in the formalization repository {citep alexeev.hopf}[]: the paper produces a
diffeomorphism, because {citep smale61}[] alone would leave open whether the complex
structure transported to $`S^6` lands on the *standard smooth* $`S^6`. What is formalized
here is the statement the rest of the development actually consumes — the underlying
topological identification, along which a complex atlas transports to a complex atlas on
the unit $`6`-sphere, with the resulting complex manifold biholomorphic to $`X`. The
classical inputs Section 8 cites for the smooth upgrade, the $`h`-cobordism theorem
{citep milnor65}[] and the vanishing of $`\Theta_6` {citep kervaire.milnor63}[], have no
counterpart in the file.
