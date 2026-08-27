/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — homotopy equivalence with the six-sphere chapter.

The smooth-flow and Morse toolbox of the `Degree` namespaces, and the endgame it serves:
a Hurewicz ladder, a hand-built finite cell structure on the threefold, and a single-map
lifting theorem that together produce `X ≃ₕ S⁶`.
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

#doc (Manual) "The homotopy equivalence with the six-sphere" =>

The paper reaches the six-sphere in one lemma. Lemma 8.2 of {citet alpoge.s6}[] says that a
closed smooth simply connected $`n`-manifold with the reduced integral homology of $`S^n`
is homotopy equivalent to $`S^n`, and its proof is three citations: the Hurewicz theorem
applied inductively in degrees $`2,\dots,n`; naturality of the Hurewicz map, so that a map
$`\varphi : S^n \to M` hitting a generator of $`\pi_n(M) \cong H_n(M;\Z) \cong \Z` induces
an isomorphism on all integral homology; and the homology Whitehead theorem, applicable
because both spaces are simply connected and of CW homotopy type {citep hatcher02}[]. Half a
page. None of the three is available off the shelf, and rebuilding exactly enough of each is
the business of this chapter.

What replaces them is narrower than the classical statements and correspondingly more
concrete. The Hurewicz isomorphisms in degrees $`2` through $`6` are built elsewhere in the
development; here they are run as a ladder on both sides — $`\pi_n(S^6) = 0` and
$`\pi_n(X) = 0` for $`0 < n < 6` — and then chased around a naturality square to make
$`\mathrm{sphereMap} : S^6 \to X` an isomorphism on $`\pi_6`. CW homotopy type is replaced by
an inductive predicate `Built d X`, which asserts that $`X` is reachable from the empty space
by homotopy equivalences and attachments of disks of dimension at most $`d`; Morse theory
supplies it for every compact smooth manifold, hence for $`X` with $`d = 6`. The Whitehead
theorem is replaced by exactly the lifting property the single map $`\mathrm{sphereMap}` has
to satisfy — every disk of dimension $`\le 6` mapped into $`X` lifts to $`S^6` rel its
boundary, up to homotopy — and an induction over the cell structure lifts $`\mathrm{id}_X`
through $`\mathrm{sphereMap}`. The resulting right homotopy inverse is a two-sided one
because a degree-one self-map of $`S^6` is homotopic to the identity, which is the
injectivity half of the same Hurewicz theorem. The output is
`Mathoverflow1973.Degree.threefoldHomotopyEquiv`, the hypothesis of Smale's theorem.

The `Degree` namespaces carry a second, larger cargo. They are also the shared smooth-flow
and Morse toolbox of the whole topological development: joint smoothness of the flow of a
smooth vector field, the qualitative theory of gradient-like flows and their level basins,
suspension of an isotopy into a flow so that a prescribed holonomy can be inserted at a
regular level, general position, the classical disk theorem, and the two operations —
rearrangement of critical values and cancellation of a pair of critical points — that drive
the $`h`-cobordism argument behind Smale's theorem {citep milnor65}[]. The two arcs sit in one
place because they share one engine: the analysis of what happens to a sublevel set as a
Morse function crosses a critical value is a handle attachment for the $`h`-cobordism
argument and a cell attachment for the homotopy argument, and the same charts, blocks and
flows serve both readings.

:::group "homotopy-equiv"
Smooth flows and Morse functions: joint smoothness of the flow of a smooth field, the
endpoint and cylinder structure of a gradient-like flow, suspension of isotopies into flows,
general position and the disk theorem, and the rearrangement and cancellation of critical
points. This is the machinery the $`h`-cobordism argument runs on; the cell-attachment
analysis it also supports is what the second half of the chapter consumes.
:::

Everything in this half is stated for a *compact* manifold $`M` charted on a
finite-dimensional real space $`E`, with vector fields written as sections
$`x \mapsto \langle x, V x\rangle` of the tangent bundle and smoothness measured by
`ContMDiff` at index $`\infty`. Flows are `Flow ℝ M`, that is, genuine global
$`\mathbb{R}`-actions; completeness is therefore a hypothesis rather than a conclusion, which
on a compact manifold costs nothing and buys the convenience of writing $`F_t` for every real
$`t`. The relation between a field and its flow is `IsMIntegralCurve`, applied orbit by
orbit.

:::definition "def:level-basin" (lean := "Mathoverflow1973.Degree.FlowCancellation.levelBasin") (parent := "homotopy-equiv")
For a flow $`F` on $`X` and a function $`f : X \to \mathbb{R}`, the *basin* of the level $`c`
is
$$`\mathrm{levelBasin}\,F\,f\,c \;=\; \{\, x \mid \exists\, t,\ f(F_t x) = c \,\},`
the union of the orbits that meet $`\{f = c\}`. It is flow-invariant by construction, and
when the flow crosses the level strictly downward the crossing time is unique, so
$`\mathrm{signedLevelTime}\,F\,f\,c` — defined by choice on the basin and by $`0` off it — is
a well-defined function there: the time at which the orbit through $`x` sits on the level,
negative when the crossing is in the past. The basin is the domain on which the level
behaves like the cross-section of a cylinder.
:::

:::theorem "thm:cont-mdiff-native-flow" (lean := "Mathoverflow1973.Degree.SmoothODE.contMDiff_native_flow") (parent := "homotopy-equiv")
Let $`V` be a $`C^\infty` vector field on a compact manifold $`M` modelled on a
finite-dimensional real space $`E`, and let $`F` be a flow on $`M` each of whose orbits is an
integral curve of $`V`. Then the joint map
$$`M \times \mathbb{R} \longrightarrow M, \qquad (x,t) \longmapsto F_t(x)`
is $`C^\infty`. Mathlib supplies existence and uniqueness of integral curves but not the
smooth dependence of the flow on its initial condition, so the development builds that theory
from scratch: Picard iteration is set up as a contraction on Banach spaces of continuous
paths, with quadratic remainder bounds and an induction on the order of differentiability,
giving smoothness at time zero in a chart and then, by the group law, everywhere. Every
time-$`t` map is in particular a diffeomorphism.
:::

:::theorem "thm:exists-native-descent-endpoints" (lean := "Mathoverflow1973.Degree.FlowCancellation.exists_native_descent_endpoints") (parent := "homotopy-equiv") (uses := "def:critical-points")
Let $`f` and $`V` be smooth on a compact Hausdorff manifold $`M`, let $`F` be a flow whose
orbits are integral curves of $`V`, and suppose $`V` vanishes on the critical set of $`f` and
that $`\mathrm{d}f(V) < 0` off it, with $`f` injective on the critical set. Then every orbit
runs from one critical point to another: for each $`x` there are critical points $`p, q` with
$$`F_t(x) \xrightarrow[t \to -\infty]{} p, \qquad F_t(x) \xrightarrow[t \to +\infty]{} q,`
and $`f(q) < f(x) < f(p)` whenever $`x` is not itself critical. The hypotheses are the exact
content of "gradient-like": $`V` vanishes precisely at the critical points, and $`f` strictly
decreases along every other orbit.
:::

:::proof "thm:exists-native-descent-endpoints"
Along any orbit $`t \mapsto f(F_t x)` is non-increasing, and strictly decreasing unless the
orbit is a fixed point. Compactness makes the forward limit set non-empty, and it is
connected and flow-invariant; $`f` is constant on it, because $`f(F_t x)` converges. A
flow-invariant set on which $`f` is constant consists of critical points, since $`f` strictly
decreases along non-constant orbits. Injectivity of $`f` on the critical set then collapses
that limit set to a single point: distinct critical points in it would share a critical
value. The same argument backwards gives $`p`, and the strict decrease between the two
endpoints gives the inequalities.
$`\blacksquare`
:::

:::theorem "thm:exists-native-level-flow-cylinder" (lean := "Mathoverflow1973.Degree.FlowCancellation.exists_native_level_flow_cylinder") (parent := "homotopy-equiv") (uses := "def:critical-points, def:level-basin, thm:cont-mdiff-native-flow, thm:regular-level-is-manifold")
Let $`c` be a regular value of $`f` that the flow crosses strictly downward, meaning
$`\mathrm{d}f(V) < 0` at every point of $`\{f = c\}`. Then the flow trivializes the basin of
the level: there is a surjective $`C^\infty` partial diffeomorphism
$$`\Phi : \{f = c\} \times \mathbb{R} \longrightarrow \mathrm{levelBasin}\,F\,f\,c, \quad \Phi(x,t) = F_t(x),`
with source all of $`\{f = c\} \times \mathbb{R}`, target exactly the basin, and inverse whose
second coordinate is $`-\,\mathrm{signedLevelTime}\,F\,f\,c`. The level carries the
charted-space and manifold structure that `Smale.RegularLevel` puts on a regular fibre, so
the statement is an honest diffeomorphism of manifolds and not merely a homeomorphism of
sets.
:::

:::proof "thm:exists-native-level-flow-cylinder"
Uniqueness of the crossing time is the strict descent: $`t \mapsto f(F_t x)` has negative
derivative wherever its value is $`c`, so it meets $`c` at most once. Smoothness of the
crossing time is the implicit function theorem applied to $`(x,t) \mapsto f(F_t x)`, whose
$`t`-derivative is $`\mathrm{d}f(V) < 0` on the level; the joint smoothness needed to apply
it is the previous theorem. The two maps $`(x,t) \mapsto F_t(x)` and
$`x \mapsto (r(x), -\theta(x))`, where $`\theta` is the crossing time and $`r` the point at
which the orbit meets the level, are then mutually inverse smooth maps, the flow-translation
identity $`\theta(F_t x) = \theta(x) - t` supplying both composites.
$`\blacksquare`
:::

The next two results are the geometric inputs to the Whitney-trick arguments of the
$`h`-cobordism development. They are classical, entirely absent from the paper, and
formalized here from nothing.

:::theorem "thm:exists-ambient-disjoint-diffeomorph-of-dimension" (lean := "Mathoverflow1973.Degree.MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension") (parent := "homotopy-equiv") (uses := "def:isotopic-to-identity, thm:exists-ambient-transverse-plateau")
General position. Let $`f : X \to N` and $`g : Y \to N` be smooth maps from compact manifolds
into a manifold $`N`, all boundaryless, with
$$`\dim X + \dim Y < \dim N.`
Then there is a diffeomorphism $`e` of $`N`, isotopic to the identity, with
$`e(f(X)) \cap g(Y) = \emptyset`. The proof does not perturb $`f` directly. It thickens the
source by a sphere of the deficient dimension $`d = \dim N - \dim X - \dim Y`, so that the
dimensions now add up exactly, applies the transversality theorem to the thickened map, and
observes that a transverse pair whose dimensions fall short of the target must have empty
intersection — the sphere factor is then discarded at a single point.
:::

:::theorem "thm:exists-embedded-disk-isotopy" (lean := "Mathoverflow1973.Degree.DiskShrinking.exists_embedded_disk_isotopy") (parent := "homotopy-equiv") (uses := "def:isotopic-to-identity")
The disk theorem. Let $`M` be a compact path-connected manifold of dimension at least $`2`,
and let $`f, g : D \to M` be smooth maps from a finite-dimensional inner-product space,
injective with injective differentials on the closed unit ball, with
$`\dim D + n = \dim M` for some $`n \ge 1`. Then there is a diffeomorphism $`P` of $`M`,
isotopic to the identity, with $`P \circ f = g` on the closed unit ball. Any two smoothly
embedded disks of positive codimension are ambient-isotopic: the embeddings are joined by
first joining their centres along a path, then transporting one disk onto the other along it
and shrinking the discrepancy into a chart.
:::

:::theorem "thm:radial-sphere-homology-relation" (lean := "Mathoverflow1973.Degree.PassageHomology.radial_sphere_homology_relation") (parent := "homotopy-equiv") (uses := "def:homotopy-equiv-homology-equiv, def:singular-homology-map, thm:exact-at-intersection")
The homological ledger of a passage. Fix $`b \ne 0` in a normed space $`E` and radii
$`0 < r < \|b\| < R` and $`0 < \varepsilon < \|b\|`. In the doubly punctured space
$`E \smallsetminus \{0, b\}`, the maps induced on $`H_n` for $`n \ne 0` by the three
parametrized spheres — the outer sphere of radius $`R` about $`0`, the inner sphere of radius
$`r` about $`0`, and the linking sphere of radius $`\varepsilon` about $`b` — satisfy
$$`(\text{outer})_* \;=\; (\text{inner})_* + (\text{linking})_*`
as maps out of $`H_n` of the unit sphere. This is what a descending sphere picks up when a
flow passage crosses a critical point: the large sphere is the small one plus a copy of the
link of the point that was crossed.
:::

The identity is proved by testing against the two inclusions that forget one puncture at a
time. Forgetting $`b`, the outer and inner spheres are radially homotopic and the linking
sphere is nullhomotopic; forgetting $`0`, the outer and linking spheres are homotopic through
a translate and the inner sphere is nullhomotopic. Mayer–Vietoris for the cover of
$`E \smallsetminus \{0,b\}` by the two once-punctured pieces makes those two readings
determine the class, which is where `SingularMayerVietoris.exact_at_intersection` enters.

Cancellation and rearrangement come next: the two operations on a Morse function that the
$`h`-cobordism argument performs, once the flow lines between critical points have been put
in the required position.

:::theorem "thm:exists-global-band-lyapunov" (lean := "Mathoverflow1973.Degree.FlowCancellation.exists_global_band_lyapunov") (parent := "homotopy-equiv")
Suppose the two boundary levels $`c < d` are crossed strictly downward —
$`\mathrm{d}f(V) < 0` at every point of $`\{f = c\}` and at every point of
$`\{f = d\}` — and that the flow crosses the band $`c \le f \le d` in uniformly
bounded time: there is $`T > 0` such that every point of $`\{f \le d\}` satisfies
$`f(F_T x) < c`, and every point of $`\{f \ge c\}` satisfies $`f(F_{-T} x) > d`.
Then there is a $`C^\infty` function $`b` with $`\mathrm{d}b(V) < 0` throughout the
closed band, agreeing with $`f` as a germ at every point outside the open band. The
uniform crossing hypothesis is exactly the statement that no orbit lingers in the band,
so no orbit can be trapped at a critical point there; the conclusion converts that
dynamical fact into a function with no critical behaviour inside the band at all, glued
to $`f` outside it.
:::

:::theorem "thm:remove-morse-band-pair" (lean := "Mathoverflow1973.Degree.FlowCancellation.remove_morse_band_pair") (parent := "homotopy-equiv") (uses := "def:critical-points, def:manifold-morse-is-morse, thm:cont-mdiff-native-flow, thm:exists-global-band-lyapunov")
Cancellation. Let $`f` be a Morse function with gradient-like flow $`F`, let $`[c,d]` be a
band whose two boundary levels are crossed strictly downward and which the flow crosses in
uniformly bounded time, and suppose the band contains exactly two critical points
$`p \ne q`. Then there is a Morse function $`g` agreeing with $`f` as a germ at every point
outside $`f^{-1}(c,d)`, whose critical set is
$$`\mathrm{crit}(g) \;=\; \mathrm{crit}(f) \smallsetminus \{p,q\},`
so that the number of critical points drops by exactly $`2`. Note what carries the geometric
content: the hypothesis is about the *flow*, and the conclusion is about the *function*. The
work of arranging that the flow crosses the band in bounded time — that the unique connecting
orbit between $`p` and $`q` has been normalized away — belongs to the cancellation chapter;
this theorem converts that arrangement into the deletion of the pair.
:::

:::proof "thm:remove-morse-band-pair"
The bounded-crossing hypothesis produces a global band Lyapunov function $`b`, smooth,
strictly decreasing along $`V` on the whole closed band, and equal to $`f` as a germ off the
open band. Take $`g = b`. Strict decrease along $`V` forbids critical points inside the band,
and germ equality transports both criticality and the Hessian condition at every point
outside it, so $`g` is Morse with critical set exactly $`\mathrm{crit}(f)` minus the points
whose values lie in $`[c,d]`, which by hypothesis are $`p` and $`q`. The count statement is
then the cardinality of a set difference along the two-element subset $`\{p,q\}`, using
finiteness of the critical set of a Morse function on a compact manifold.
$`\blacksquare`
:::

The other operation moves critical values rather than deleting critical points. Both rely on
being able to modify the flow in a controlled way, which is the subject of the suspension
theorems: an isotopy of a regular level is turned into a vector field, and that field is
grafted into the gradient-like flow so that orbits arrive at the level, are moved by the
isotopy, and continue.

:::theorem "thm:exists-compact-isotopy-suspension" (lean := "Mathoverflow1973.Degree.FlowSuspension.exists_compact_isotopy_suspension") (parent := "homotopy-equiv")
Let $`D` be a diffeomorphism of a finite-dimensional real space $`E` carried by an isotopy
supported in a compact set $`K` and fixing a set $`S`. Then $`D` is the time-one holonomy of
a flow on $`E \times \mathbb{R}` that is vertical translation outside a compact block: there
are a $`C^\infty` field $`W` with vertical component identically $`1` and
$`W - (0,1)` supported in $`K \times [\tfrac13, \tfrac23]`, and a flow $`F` whose orbits are
integral curves of $`W`, satisfying
$$`F_1(x, 0) = (Dx, 1), \qquad (F_t p)_2 = p_2 + t,`
with $`F_t(x,s) = (x, s+t)` for every $`x \notin K` and for every $`x \in S`. The
accompanying `SuspensionCoordinates` record exhibits $`W` and $`F` as the pushforward of the
plain vertical field along a height-preserving chart of $`E \times \mathbb{R}` that is the
identity below height $`0` and equal to $`D` above height $`1`.
:::

:::theorem "thm:exists-relative-regular-level-isotopy-realization" (lean := "Mathoverflow1973.Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization") (parent := "homotopy-equiv") (uses := "def:critical-points, def:flow-construction-compact-flow, def:regular-level-charted-space, thm:exists-native-level-flow-cylinder")
Insertion of a holonomy into a Morse flow. Let $`F` be a gradient-like flow for $`f` on a
compact manifold, let $`c` be a regular value inside a band $`[a,b]` free of critical points,
and let $`D` be a diffeomorphism of the level $`\{f = c\}` carried by an isotopy supported in
a compact $`K` and fixing $`T`. Then there are a reference field $`W` with flow $`H` having
the same orbits and the same forward and backward limits as $`F`, and a modified descending
field $`V'` with flow $`G`, such that $`V'` agrees with $`V` near every critical point and
with $`W` outside a compact set contained in $`f^{-1}(a,b)`, vanishes exactly where $`V`
does, still satisfies $`\mathrm{d}f(V') < 0` off the critical set, and realizes $`D` as
holonomy:
$$`G_1(x) = H_1(Dx) \quad \text{for } x \in \{f = c\}.`
Before the level the two flows agree — $`G_t = H_t` on $`\{f = c\}` for $`t \le 0` — and after
it they agree again, forward from the point $`H_1(x)`, which sits on the level $`c - r`; on
the fixed set $`T` they agree for all times. Orbits crossing the level are therefore rerouted
by exactly $`D` and by nothing else; this is Milnor's modification of the gradient field, and
it is the engine by which attaching spheres are repositioned.
:::

:::theorem "thm:exists-morse-rearrangement-of-no-connection" (lean := "Mathoverflow1973.Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection") (parent := "homotopy-equiv") (uses := "def:critical-points, def:flow-construction-compact-flow, def:manifold-morse-is-morse, def:native-morse-index, def:signed-morse-chart, thm:exists-native-level-flow-cylinder")
Rearrangement. Let $`p` and $`q`, with $`f(p) < f(q)`, be the only critical points with values
in $`[l,u]`, each equipped with a signed Morse chart whose descent field agrees with $`V` near
it, and suppose no flow line runs from $`q` down to $`p`. Then for any prescribed values
$`p', q' \in (l,u)` there is a Morse function $`g` with
$$`g = f \text{ off } f^{-1}(l,u), \quad \mathrm{crit}(g) = \mathrm{crit}(f), \quad g(p) = p', \quad g(q) = q',`
still strictly decreasing along $`V` off the critical set, equal to $`f` plus a constant near
each of $`p` and $`q`, equal to $`f` near every other critical point, and with the same Morse
index at every critical point. The absence of a connecting orbit is what makes the two values
independently movable — including past one another, which is how critical points are sorted
by index.
:::

:::group "homotopy-equiv-endgame"
The endgame: vanishing homotopy groups on both sides through degree $`5`, bijectivity on
$`\pi_6`, a finite cell structure on the threefold produced by Morse theory, the disk-lifting
property that replaces Whitehead's theorem, and the degree-one argument that upgrades a right
homotopy inverse to a two-sided one.
:::

The input from the rest of the development is a single based map. For a point $`x` of the
threefold $`X`, `SphereHomologyEquivalence.sphereMap x` is the map $`S^6 \to X` obtained by
factoring the generating cube of $`\pi_6(X)` through the quotient $`I^6 \to S^6`, and it
carries the fundamental class of $`S^6` to a generator of $`H_6(X;\Z) \cong \Z`; the homology
chapter shows it is an isomorphism on singular homology in every degree. Everything below
turns that homology statement into a homotopy statement.

:::theorem "thm:pi-subsingleton" (lean := "Mathoverflow1973.Degree.Sphere.pi_subsingleton") (parent := "homotopy-equiv-endgame") (uses := "def:hurewicz-pi2-equiv, def:hurewicz-pi3-equiv, def:hurewicz-pi4-equiv, def:hurewicz-pi5-equiv, thm:unit-sphere-homology-subsingleton")
The six-sphere is $`5`-connected: $`\pi_n(S^6)` is trivial for $`0 < n < 6`, where $`S^6` is
the unit sphere of $`\mathbb{R}^7` and triviality is expressed as `Subsingleton (π_ n S⁶ x)`
at an arbitrary basepoint. Degree $`1` is simple connectivity, transported from the
fundamental group along the standard identification. Degrees $`2` through $`5` climb a
Hurewicz ladder: each step feeds the vanishing of the previous groups into the Hurewicz
isomorphism of its own degree and reads off triviality from the vanishing of the
corresponding homology group of the sphere, which is where
`SphereHomology.unitSphere_homology_subsingleton` is consumed. The ladder is unavoidable —
the Hurewicz theorem in degree $`n` needs $`(n-1)`-connectivity as a hypothesis — and it is
run separately on $`S^6` and on $`X`.
:::

:::theorem "thm:sphere-map-pi-six-bijective" (lean := "Mathoverflow1973.Degree.sphereMap_piSix_bijective") (parent := "homotopy-equiv-endgame") (uses := "def:hurewicz-linear-equiv, def:sphere-homology-equivalence-homology-equiv, thm:hurewicz-linear-equiv-natural, thm:space-simply-connected")
The map induced by $`\mathrm{sphereMap}\,x : S^6 \to X` on $`\pi_6` at the base point of the
sphere is bijective. Both spaces are $`5`-connected — the sphere by the ladder above, the
threefold by simple connectivity together with its vanishing $`\pi_2, \dots, \pi_5` — so the
sixth Hurewicz maps $`h_{S^6} : \pi_6(S^6) \to H_6(S^6;\Z)` and
$`h_X : \pi_6(X) \to H_6(X;\Z)` are isomorphisms, and they intertwine the two induced maps:
$$`H_6(\mathrm{sphereMap}\,x) \circ h_{S^6} \;=\; h_X \circ \pi_6(\mathrm{sphereMap}\,x).`
The homology map on the left is an isomorphism because $`\mathrm{sphereMap}\,x` is a homology
equivalence, so the homotopy map on the right is one too.
:::

:::proof "thm:sphere-map-pi-six-bijective"
The four connectivity instances on each side are supplied as local instances so that
`SixthHurewicz.hurewiczLinearEquiv` is available at both base points, and the naturality
lemma `hurewiczLinearEquiv_natural` states precisely the identity above, after the
multiplicative $`\pi_6` has been transported to its additive form. Injectivity of
the $`\pi_6` map follows by applying the source Hurewicz equivalence, the homology
isomorphism and their injectivity in turn; surjectivity by pulling a class back through the
target Hurewicz equivalence, the inverse homology isomorphism and the source equivalence, and
checking with naturality that the resulting element has the required image.
$`\blacksquare`
:::

With the sphere and the threefold indistinguishable through dimension $`6`, what remains is a
Whitehead-type argument, and for that the threefold needs a cell structure. There is no CW
theory available, so one is defined.

:::definition "def:core-union-homotopy-equiv" (lean := "Mathoverflow1973.Degree.CoreAttachment.coreUnionHomotopyEquiv") (parent := "homotopy-equiv-endgame")
A handle deformation-retracts onto its core. For a handle $`D^\lambda \times D^{n-\lambda}`
attached to a compact set $`A` by an injective map $`h` whose preimage of $`A` is exactly the
attaching face $`\partial D^\lambda \times D^{n-\lambda}`, the inclusion
$$`A \cup (\text{core } D^\lambda \times \{0\}) \;\hookrightarrow\; A \cup \text{handle}`
is a homotopy equivalence. The retraction is written down explicitly rather than quoted:
a one-parameter family that fixes $`A` and the core throughout and slides the second factor
radially to the origin, with the interpolation formula supplying continuity at the seam.
Attaching a handle is, up to homotopy, attaching a cell of dimension equal to its index —
which is what lets the Morse-theoretic handle decomposition below be read as a cell
structure.
:::

:::definition "def:finite-cells-built" (lean := "Mathoverflow1973.Degree.FiniteCells.Built") (parent := "homotopy-equiv-endgame")
`Built d X` is an inductive predicate on topological spaces, the file's substitute for a
finite CW structure of dimension at most $`d`. Three constructors: the empty space is built;
if $`X` is built and $`e : X \simeq_h Y` then $`Y` is built; and if $`A \subseteq M` is built
and $`h` maps the closed unit disk of a space $`V` with $`\dim V \le d` into $`M`, carrying
the boundary sphere into $`A`, then the adjunction space $`A \cup_h D^V` is built. Note the
second constructor: homotopy equivalence, not homeomorphism, so `Built` is a statement about
homotopy type and the induction below never has to produce an actual cell decomposition — only
a chain of attachments and equivalences. The predicate lives on `Type`, not `Type*`, a
restriction inherited from the singular homology machinery it must interact with.
:::

:::definition "def:finite-cells-relative-disk-lifting" (lean := "Mathoverflow1973.Degree.FiniteCells.RelativeDiskLifting") (parent := "homotopy-equiv-endgame")
`RelativeDiskLifting F d` is the obstruction-theoretic condition that replaces the Whitehead
theorem, stated for one map $`F : X \to Y` and one range of dimensions. It says: for every
finite-dimensional $`V` with $`\dim V \le d`, every map $`a` of the boundary sphere into
$`X`, every map $`u` of the disk into $`Y`, and every homotopy $`H` in $`Y` from
$`F \circ a` to the restriction of $`u` to the boundary, there are a map $`v` of the disk into
$`X` restricting to $`a` and a homotopy $`G` from $`F \circ v` to $`u` restricting to $`H` on
the boundary. In words: a disk in $`Y` whose boundary has already been lifted, lifts, rel that
boundary data and up to a homotopy that extends the given one. It is exactly the induction
step of an obstruction argument, isolated so that only the one map that matters has to satisfy
it.
:::

:::theorem "thm:maps-lift-of-built" (lean := "Mathoverflow1973.Degree.FiniteCells.mapsLift_of_built") (parent := "homotopy-equiv-endgame") (uses := "def:finite-cells-built, def:finite-cells-relative-disk-lifting")
If $`F : X \to Y` has relative disk lifting in dimensions $`\le d` and $`Z` is `Built d`, then
every map $`Z \to Y` lifts through $`F` up to homotopy: there is $`v : Z \to X` with
$`F \circ v \simeq u`. The proof is the induction over the three constructors of `Built`. The
empty case is vacuous; the homotopy-equivalence case conjugates a lift by the equivalence and
composes the homotopies; the attachment case restricts $`u` to the old part, lifts it by the
inductive hypothesis, lifts the new cell by the disk-lifting property using the restriction of
the homotopy to the attaching sphere, and glues — which is where the homotopy extension
property of the pair (cylinder, boundary) is consumed, itself proved in the development by an
explicit retraction of $`I \times D` onto its bottom and sides.
:::

:::theorem "thm:sphere-map-relative-disk-lifting-six" (lean := "Mathoverflow1973.Degree.TopCellLifting.sphereMap_relativeDiskLifting_six") (parent := "homotopy-equiv-endgame") (uses := "def:finite-cells-relative-disk-lifting, thm:pi-subsingleton, thm:sphere-map-pi-six-bijective")
$`\mathrm{sphereMap}\,x : S^6 \to X` has relative disk lifting in dimensions $`\le 6`. Below
the top dimension the statement is soft: with both spaces $`5`-connected, a map of a sphere of
dimension $`\le 4` into $`S^6` is nullhomotopic, so the boundary data can be pushed to a
constant, and the cylinder over a disk of dimension $`\le 5` can be filled in $`X` by the
same vanishing. In dimension exactly $`6` softness runs out and the $`\pi_6`-bijectivity is
what does the work: after contracting the attaching sphere and transporting the base point
along a path, the disk becomes a based map of $`S^6` into $`X`, its class is pulled back
through the $`\pi_6` isomorphism, and the resulting lift is corrected on the side of the
cylinder so that the homotopy restricts to the prescribed one on the boundary.
:::

The cell structure itself comes from Morse theory, and this is the point at which the two
arcs of the chapter meet: the same passage analysis that the $`h`-cobordism argument reads as
a handle attachment is read here as a cell attachment.

:::theorem "thm:built-of-compact-smooth-manifold" (lean := "Mathoverflow1973.Degree.MorseCells.built_of_compact_smooth_manifold") (parent := "homotopy-equiv-endgame") (uses := "def:core-union-homotopy-equiv, def:finite-cells-built, thm:exists-adapted-descent-flow, thm:exists-morse-function, thm:exists-regular-sublevel-homotopy-equiv")
Every compact Hausdorff smooth manifold $`M` modelled on a finite-dimensional real space $`E`
is `Built (finrank ℝ E)`. Choose a Morse function with distinct critical values and induct
over the critical points in increasing order of value: between consecutive critical values the
sublevel sets are homotopy equivalent, and across a critical value the sublevel set is, up to
homotopy, the lower one with a single cell of dimension the Morse index attached. A point
where $`f` attains its maximum is critical, and the sublevel set just above it is all of
$`M`.
:::

:::proof "thm:built-of-compact-smooth-manifold"
The empty manifold is handled by the first constructor. Otherwise a Morse function $`f` with
pairwise distinct critical values exists, and around each critical point one extracts a
`Cell`: an isolating radius $`\rho`, a signed Morse chart whose $`2\rho`-block sits inside the
chart's target, and a homotopy equivalence between the sublevel set
$`\{f \le f(p) + \rho^2\}` and $`\{f \le f(p) - \rho^2\}` with the core cell of the handle
attached. The radii are shrunk so that the bands $`[f(p)-\rho^2, f(p)+\rho^2]` are pairwise
disjoint. Induction on the finite set of critical points, ordered by value, then builds every
upper sublevel set: below the lowest band the sublevel set is empty; between bands
`exists_regularSublevelHomotopyEquiv` supplies a homotopy equivalence, since a band free of
critical values is swept by the descending flow; and across a band the `Cell` comparison is
the attachment constructor. A point at which $`f` attains its maximum is critical, and the
sublevel set above its band is all of $`M`.
$`\blacksquare`
:::

:::theorem "thm:finite-homotopy-cells" (lean := "Mathoverflow1973.Degree.Threefold.finite_homotopy_cells") (parent := "homotopy-equiv-endgame") (uses := "def:finite-cells-built, def:threefold-charted-space, thm:built-of-compact-smooth-manifold, thm:complex-manifold-is-real-manifold, thm:threefold-space-compact")
The threefold is `Built 6`. The specialization supplies the four hypotheses as local
instances — the charted-space structure on $`X` with model $`\C \times \C^2`, compactness,
the Hausdorff property, and smoothness as a *real* manifold, obtained from the complex atlas
by the general bridge `complexManifold_isRealManifold` — and rewrites the dimension index
using $`\dim_{\mathbb{R}}(\C \times \C^2) = 6`. The homotopy-theoretic side of the argument
never sees the complex structure again after this line.
:::

:::theorem "thm:exists-right-homotopy-inverse" (lean := "Mathoverflow1973.Degree.exists_right_homotopy_inverse") (parent := "homotopy-equiv-endgame") (uses := "thm:finite-homotopy-cells, thm:maps-lift-of-built, thm:sphere-map-relative-disk-lifting-six")
There is a continuous $`g : X \to S^6` with
$$`\mathrm{sphereMap}\,x \circ g \;\simeq\; \mathrm{id}_X.`
This is the lifting theorem applied to the identity map of $`X`: the map to be lifted is
$`\mathrm{id}_X`, the map to lift through is $`\mathrm{sphereMap}\,x`, which has relative disk
lifting in dimensions $`\le 6`, and the source is `Built 6`. One inequality of dimensions
makes the whole argument close — the cell structure of $`X` stops at dimension $`6`, exactly
where the lifting property stops.
:::

A right homotopy inverse is not yet a homotopy equivalence. Upgrading it is the second use of
Hurewicz, in its injectivity form: a self-map of $`S^6` that fixes the fundamental homology
class is homotopic to the identity.

:::theorem "thm:sphere-homotopic-rel-of-top-class-eq" (lean := "Mathoverflow1973.Degree.sphere_homotopicRel_of_topClass_eq") (parent := "homotopy-equiv-endgame") (uses := "def:hurewicz-pi6-equiv, def:singular-homology-map")
Let $`X` be simply connected with trivial $`\pi_2, \dots, \pi_5`, and let $`f, g : S^6 \to X`
be based at $`x`. If $`f` and $`g` send the fundamental class of $`S^6` to the same element of
$`H_6(X;\Z)`, then they are homotopic rel the base point. This is the injectivity half of the
sixth Hurewicz theorem, made usable: the two maps are converted into based cubes, the sixth
Hurewicz equivalence identifies their classes in $`\pi_6(X)` because their cube homology
classes agree, and the identification of $`\pi_6` classes is unwound back into a homotopy of
maps of the sphere through the quotient $`I^6 \to S^6`.
:::

:::theorem "thm:homotopic-id-of-top-class" (lean := "Mathoverflow1973.Degree.Sphere.homotopic_id_of_topClass") (parent := "homotopy-equiv-endgame") (uses := "def:hurewicz-pi2-equiv, def:hurewicz-pi3-equiv, def:hurewicz-pi4-equiv, def:hurewicz-pi5-equiv, thm:sphere-homotopic-rel-of-top-class-eq, thm:unit-sphere-homology-subsingleton")
A self-map of $`S^6` fixing the fundamental class in $`H_6(S^6;\Z)` — a degree-one map — is
homotopic to the identity. The statement is the free one: no basepoint condition is imposed
on $`g`.
:::

:::proof "thm:homotopic-id-of-top-class"
The based case is the previous theorem applied with $`X = S^6`, whose hypotheses are met by
the Hurewicz ladder for the sphere, and with the identity as the second map; its homology
condition is exactly the hypothesis after the induced map of the identity has been simplified
away. The free case is reduced to the based one by moving the basepoint: a path from
$`g(\ast)` to $`\ast` produces a map $`v` that is based and homotopic to $`g`, homotopic maps
induce the same map on homology so $`v` still fixes the fundamental class, and the based
statement makes $`v` homotopic to the identity rel the base point. Composing the two
homotopies gives the free one.
$`\blacksquare`
:::

:::theorem "thm:right-inverse-is-left-inverse" (lean := "Mathoverflow1973.Degree.right_inverse_is_left_inverse") (parent := "homotopy-equiv-endgame") (uses := "def:sphere-homology-equivalence-homology-equiv, def:singular-homology-map, thm:homotopic-id-of-top-class")
If $`\mathrm{sphereMap}\,x \circ g \simeq \mathrm{id}_X` then
$`g \circ \mathrm{sphereMap}\,x \simeq \mathrm{id}_{S^6}`. Write $`F` for
$`\mathrm{sphereMap}\,x`. From the right-inverse homotopy, $`F \circ (g \circ F) \simeq F`, so
the composite $`g \circ F` and the identity of $`S^6` have the same image under
$`H_6(F)`. That map is injective — it is one of the homology isomorphisms induced by
$`\mathrm{sphereMap}` — so $`g \circ F` fixes the fundamental class of $`S^6`, and the
degree-one theorem makes it homotopic to the identity. The homology equivalence of the
threefold with the sphere is used here in the one direction the cell-lifting argument could
not supply.
:::

:::definition "def:sphere-homotopy-equiv" (lean := "Mathoverflow1973.Degree.sphereHomotopyEquiv") (parent := "homotopy-equiv-endgame") (uses := "def:homology-six-equiv, thm:exists-right-homotopy-inverse, thm:homology-subsingleton-of-lt, thm:right-inverse-is-left-inverse")
The homotopy equivalence $`S^6 \simeq_h X`, for each choice of base point $`x` of $`X`: its
forward map is $`\mathrm{sphereMap}\,x`, its inverse is the right homotopy inverse $`g`
extracted by choice, and its two coherence fields are the right-inverse homotopy itself and
the left-inverse homotopy obtained from it by the degree-one argument. The homological input
that makes it work is the computation of the previous chapters — $`H_6(X;\Z) \cong \Z` with a
distinguished generator, and $`H_n(X;\Z) = 0` in every other positive degree, including all
degrees above $`6`.
:::

:::definition "def:threefold-homotopy-equiv" (lean := "Mathoverflow1973.Degree.threefoldHomotopyEquiv") (parent := "homotopy-equiv-endgame") (uses := "def:sphere-homotopy-equiv, def:threefold-space")
The export:
$$`X \;\simeq_h\; \{\, v \in \mathbb{R}^7 \mid \|v\| = 1 \,\},`
a homotopy equivalence between the compact complex threefold and the standard six-sphere,
obtained by inverting the previous equivalence at a base point supplied by non-emptiness of
$`X`. The target is the metric sphere of radius $`1` about the origin in
`EuclideanSpace ℝ (Fin 7)` with its subspace topology — the standard sphere, not a
homeomorphic copy — because the six-sphere of the cell-lifting argument was defined as that
sphere throughout. This is Lemma 8.2 of {citet alpoge.s6}[] for the threefold, and it is the
hypothesis of Smale's theorem {citep smale61}[]: the next chapter turns it into a
homeomorphism, along which the complex atlas is finally transported.
:::
