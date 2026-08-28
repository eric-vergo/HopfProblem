/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — Analytic and quotient-manifold foundations chapter.

The complex-analysis engine of the formalization: the uniformization of the
(3,4,∞) triangle orbifold, the ∂̄/Cousin theory that produces the period functions,
the cusp log cover, and the generic quotient-manifold and covering-space machinery
that carries a holomorphic atlas across every quotient step of the construction.
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

#doc (Manual) "Analytic and quotient-manifold foundations" =>

The threefold of {citet alpoge.s6}[] is assembled out of analytic material that Mathlib
does not carry. Four separate classical theories are needed and none of them is
available: a uniformization of the $`(3,4,\infty)` orbifold identifying the base of the
fibration with the projective line; a solution of the additive Cousin problem on the
affine line, with a prescribed normalization at infinity; global analytic square roots
on simply connected domains; and an explicit realisation of a punctured neighbourhood of
the degenerate fibre as a quotient of an open set in $`\C^3`. Each is developed from
scratch inside the subject module, on top of one-variable complex analysis alone. This
chapter collects that development, together with the generic machinery it feeds — the
transport of a holomorphic atlas across a quotient covering map, and the two-chart
recognition principle for $`\PP^1`.

Two of these theories exist to produce the period functions. The paper's family of
$`2`-tori over the thrice-punctured line is built from three scalar functions
$`\tau, \mu, \beta` on the upper half-plane, equivariant for the triangle group in the
prescribed affine-fractional way; existence and uniqueness of $`\mu` and $`\beta` are
sheaf-theoretic statements, $`\mu` being the unique section of a torsor under an
invertible sheaf isomorphic to $`\mathcal{O}_{\PP^1}(-1)` and $`\beta` a section of a
torsor under $`\mathcal{O}`. The formalization never mentions sheaf cohomology. The
vanishing $`H^1(\PP^1, \mathcal{O}(-1)) = 0` is replaced by a hand-built Cousin theorem:
an additive analytic $`1`-cocycle on an open cover of $`\C`, one of whose members
contains a neighbourhood of infinity, splits into local holomorphic pieces whose
distinguished member is $`O(1/z)` at infinity. That is the exact form consumed by the
$`\mu`-torsor gluing. Likewise the modular square root $`E_6^{1/2}` that trivialises the
line bundle is produced by an étalé-space continuation principle rather than by an
appeal to analytic continuation.

The remaining theory is geometric. The base of the fibration is the quotient of the
upper half-plane by the $`(3,4,\infty)` triangle group, and the whole construction reads
that quotient as $`\PP^1`. The identification is proved by an explicit route: Riemann
map the open Ford half-triangle onto the unit disc, extend the map to the closed
triangle by Schwarz reflection along the sides with the two elliptic corners and the
ideal vertex straightened by root and logarithm charts, normalize by the cross-ratio
sending the two corner values and the cusp value to $`0, 1, \infty`, and descend. What
comes out is an analytic diffeomorphism from the compactified orbit space onto the
Riemann sphere.

:::group "analysis"
The complex-analysis engine: quotient-manifold transport, the cusp log cover, the
$`\bar\partial`-theory behind the period functions, and the uniformization of the
$`(3,4,\infty)` triangle orbifold.
:::

Simple connectivity is needed twice over, and in incomparable forms: as a hypothesis of
the monodromy and Riemann-mapping theorems below, and as the conclusion drawn about the
threefold itself. Both are proved in the module.

:::theorem "thm:simply-connected-space" (lean := "Mathoverflow1973.EuclideanSphere.simplyConnectedSpace") (parent := "analysis")
*Theorem.* The unit sphere in $`\R^{n+3}` is simply connected for every $`n \ge 0`.

The Lean statement evaluates the family $`n \mapsto S^n` at $`n+2`, so the hypothesis
"of dimension at least two" is carried by the index rather than by a side condition, and
the conclusion is the class-level `SimplyConnectedSpace`, path-connectedness included.
The argument avoids van Kampen entirely. A loop is first cut, along the two-set cover of
the sphere by the complements of a pair of antipodal points, into a concatenation of
loops each of which misses a point of the sphere; a loop into a sphere which is not
surjective lands in a contractible set and is therefore null-homotopic.
:::

:::theorem "thm:simply-connected-space-of-open-cover" (lean := "Mathoverflow1973.simplyConnectedSpace_of_open_cover") (parent := "analysis")
*Theorem (van Kampen for simple connectivity).* Let $`X` be covered by open sets
$`U_i`, each simply connected, all containing a common point $`o`, and suppose every
pairwise intersection $`U_i \cap U_j` is path-connected. Then $`X` is simply connected.

The index set is arbitrary rather than a two-element cover, which is what makes the
statement usable against the open covers the threefold is assembled from. The proof does
not go through a pushout of groups. It builds directly a coherent system
$`F : \prod_{x} \lbrack \mathrm{Path}\ o\ x \rbrack` of homotopy classes of paths from
the basepoint — one chart path per point, well defined because the overlaps are
path-connected — and shows that concatenating any path with $`F` at its source returns
$`F` at its target, so any two paths with the same endpoints are homotopic. The
Mathlib-directed version of this material is {citep kumar.vankampen}[].
:::

:::theorem "thm:covering-quotient-is-manifold" (lean := "Mathoverflow1973.CoveringQuotient.isManifold") (parent := "analysis")
*Theorem.* Let $`q : M \to Q` be a quotient covering map for an action of a group $`G`
on a complex manifold $`M` charted on a normed $`\C`-space $`E`, and suppose every
$`g \cdot (-)` is holomorphic of class $`n`. Then the transported atlas — charts
$`\varphi_M \circ \mathrm{loc}(q)^{-1}` at chosen orbit representatives — makes $`Q` a
complex manifold of class $`n` on the same model.

Mathlib has no holomorphic quotient construction, so the entire chart calculus is built
here over `IsQuotientCoveringMap`. The companions are what get used downstream: $`q` is
holomorphic and a local biholomorphism, and a map $`f : Q \to N` is holomorphic exactly
when $`f \circ q` is. That last equivalence is the universal property by which every
descended map in the construction — the cusp uniformization, the triangle orbit map, the
fibrewise torus quotients — is certified holomorphic without ever writing a chart.
:::

Near the cusp fibre the family degenerates, and the paper's §3.7 supplies the local form
of the periods that makes the degeneration explicit: on the distinguished cusp
neighbourhood the period matrix reads $`Z = s B_0 + C(t_c)`, with $`B_0` the integral
monodromy block and $`C` holomorphic across $`t_c = 0`. The formalization takes that
expression as its starting datum and builds a covering of a punctured neighbourhood of
the degenerate fibre by an open set of $`\C \times \C^2`.

:::definition "def:cusp-uniformization-exponential" (lean := "Mathoverflow1973.CuspUniformization.exponential") (parent := "analysis")
$`e(z) = \exp(2\pi i z)`, the exponential in the normalization under which the cusp
coordinate is $`t_c = e(s)`.

It is the most heavily used definition of the cusp development, and the calculus around
it is what carries the geometry: $`e(z+w) = e(z)e(w)`, $`e(z) \ne 0` everywhere,
$`e(z) = e(w)` exactly when $`z - w \in \Z`, and
$`\log \lVert e(s) \rVert = -2\pi\,\mathrm{Im}\,s`. The second identity is the deck
relation of the log cover in one line, and the third turns the height condition
$`\mathrm{Im}\,s \gg 0` into the punctured-disc condition $`\lVert e(s) \rVert < \varepsilon`.
:::

:::definition "def:logarithmic-period" (lean := "Mathoverflow1973.CuspUniformization.logarithmicPeriod") (parent := "analysis") (uses := "def:cusp-uniformization-exponential")
For an analytic drift $`C` on a disc, the logarithmic period matrix
$$`\Omega_C(s) \;=\; s\,B_0 \;+\; C(e(s)) \;\in\; M_2(\C), \qquad B_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}.`

This is the paper's $`Z(z) = s(z)B_0 + C(t_c \circ \pi(z))` transcribed, with the drift
reparametrized through $`t_c = e(s)` so that $`\Omega_C` is a function on the half-plane
rather than on the punctured disc. Its columns are the fibre periods, and its imaginary
part is nondegenerate whenever $`\log \lVert e(s) \rVert < 0` and the drift is small in
the sense of `ToricSpace.SmallDrift` — which is exactly the regime in which the fibres
are honest compact tori. The unbounded term $`sB_0` is the whole degeneration: it is
what makes the period lattice run off as $`s` goes up the half-plane.
:::

:::definition "def:punctured-cusp-cover" (lean := "Mathoverflow1973.CuspUniformization.puncturedCuspCover") (parent := "analysis") (uses := "def:cusp-quotient-quotient-space, def:cusp-uniformization-exponential")
The covering of the punctured cusp quotient by the log cover
$`\lbrace (s,z) \in \C \times \C^2 : \lVert e(s) \rVert < \varepsilon \rbrace`, sending
$`(s,z)` to the class of the toric point with coordinates $`(e(z_0), e(z_1), e(s))`.

Puncturing is imposed on both sides by the same function: the target is the locus of the
cusp quotient where the toric time coordinate is nonzero, and the source lands there
because $`e` never vanishes. The map is surjective, a local biholomorphism, and — the
statement the construction actually consumes — a quotient covering map, its deck group
being the log deck group below. Exponentiating all three coordinates at once is what
converts the additive period relations upstairs into the multiplicative toric relations
downstairs.
:::

:::definition "def:cusp-uniformization-log-deck" (lean := "Mathoverflow1973.CuspUniformization.LogDeck") (parent := "analysis") (uses := "def:logarithmic-period")
The deck group of the log cover: triples $`(k, m, n) \in \Z \times \Z^2 \times \Z^2`
with the twisted product
$$`(g \cdot h) = \bigl(g_k + h_k,\ \ g_m + h_m + h_k \cdot \mathrm{cuspVector}(g_n),\ \ g_n + h_n\bigr),`
acting on $`\C \times \C^2` by
$`(s, z) \mapsto (s + k,\ z + m + \Omega(s)\,n)`.

The twist in the middle coordinate is forced: translating $`s` by $`k` changes
$`\Omega(s)` by $`k B_0`, so the lattice vector picked up by $`n` shifts by
$`k \cdot \mathrm{cuspVector}(n)`. The triples with $`k = n = 0` are therefore central,
and what results is a central extension of the abelian $`\Z \times \Z^2` by that central
$`\Z^2` — a Heisenberg-like group whose axioms are verified by hand, Mathlib carrying no
presentation for it. Freeness and holomorphy of the action are the two facts that make
the quotient a manifold.
:::

:::definition "def:total-uniformization-biholomorph" (lean := "Mathoverflow1973.CuspUniformization.totalUniformizationBiholomorph") (parent := "analysis") (uses := "def:cusp-uniformization-log-deck, def:punctured-cusp-cover, thm:covering-quotient-is-manifold, thm:cusp-quotient-proper-action")
*Construction.* For $`0 < \varepsilon < 1`, with $`C` analytic on the $`\varepsilon`-ball and
of small drift, the quotient of the log cover by the period relation is analytically
diffeomorphic to the punctured cusp quotient.

The period relation identifies $`(s,z)` with $`(s + k,\ z + m + \Omega(s)n)`, so the
source is precisely the orbit space of the deck action; the map induced by
`puncturedCuspCover` is a bijection by construction and holomorphic in both directions
because both sides carry charts transported along local biholomorphisms. The content is
geometric: a punctured neighbourhood of the special fibre $`W` is
$`\lbrace \mathrm{Im}\,s \gg 0 \rbrace \times \C^2` modulo an explicit discrete group.
That description supplies the holomorphic charts of the threefold near $`W`, and it is
also where the generators and relations for the fundamental-group computation are read
off.
:::

The base of the fibration is $`\PP^1`, and rather than import a projective-space
construction the module recognizes it from a two-chart atlas.

:::definition "def:two-affine-charts" (lean := "Mathoverflow1973.TwoAffineCharts") (parent := "analysis")
*Definition.* A `TwoAffineCharts` structure on a space $`Y` is a pair of injective
continuous maps $`\mathrm{left}, \mathrm{right} : \C \to Y` which are jointly surjective,
have distinct origins, and satisfy $`\mathrm{left}(z) = \mathrm{right}(z^{-1})` for all
$`z \ne 0`.

The data is a recognition principle, not a construction: from it the module derives a
homeomorphism of $`Y` with the one-point compactification of $`\C`, a
$`\mathrm{ChartedSpace}\ \C\ Y`, the transition map $`z \mapsto 1/z` and its holomorphy,
and finally $`\mathrm{IsManifold}\ \mathcal{I}(\C)\ \omega\ Y`. Any space presented with
two affine charts glued by inversion is thereby the projective line, complex structure
included — which is how the base of the torus fibration acquires its analytic structure.
:::

:::definition "def:riemann-sphere" (lean := "Mathoverflow1973.RiemannSphere") (parent := "analysis") (uses := "def:two-affine-charts")
*Definition.* $`\PP^1(\C)`, realised as the one-point compactification `OnePoint ℂ`.

The two charts are the inclusion $`z \mapsto z` and `infinityParametrization`, the map
sending $`0` to the point at infinity and $`z \ne 0` to $`z^{-1}`; they assemble into a
`TwoAffineCharts` structure, and the derived charted-space and analytic-manifold
instances are the ones every later statement about the base uses. Presenting $`\PP^1` as
a one-point compactification rather than as a quotient of $`\C^2 \setminus 0` is what
makes the compactified triangle orbit space — also a one-point compactification —
comparable to it by a map that is visibly a homeomorphism away from a single point.
:::

Two of the three period functions are produced as sections of torsors, and both
constructions need an analytic input that Mathlib does not provide. The first is a global
square root, used to trivialise the line bundle attached to the $`\mu`-problem and again
to lift through the modular $`j`-function. It is obtained sheaf-theoretically, from a
monodromy principle stated for arbitrary local predicates.

:::theorem "thm:exists-global-section-with-germ-of-germ-bijective" (lean := "Mathoverflow1973.AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective") (parent := "analysis")
*Theorem (monodromy principle).* Let $`X` be simply connected and locally
path-connected, and let $`P` be a `LocalPredicate` on the constant presheaf with values
in a type $`Y`, whose germ maps are bijective on some neighbourhood of every point. Then
every element of every stalk is the germ of a global section.

The hypothesis says exactly that the étalé space of the associated presheaf is a
covering of $`X`; simple connectivity then lifts the identity map through it, and a
continuous section of the étalé space over all of $`X` is a global section of the
presheaf. Stating it for `TopCat.LocalPredicate` rather than for analytic functions is
what lets it be reused verbatim: once for square roots, once for lifting a map through
$`j` with prescribed order divisibility at the two elliptic points.
:::

:::theorem "thm:exists-analytic-square-root-on-of-even-zeros" (lean := "Mathoverflow1973.AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros") (parent := "analysis") (uses := "thm:exists-global-section-with-germ-of-germ-bijective")
*Theorem.* Let $`S \subseteq \C` be open and simply connected and let $`F` be analytic on
$`S` with every zero of even analytic order. Then there is an analytic $`r` on $`S` with
$`r^2 = F`, and $`\mathrm{ord}_a\,r = n` wherever $`\mathrm{ord}_a\,F = 2n`.

The local predicate is "analytic $`r` with $`r^2 = F`". Away from the zeros of $`F` its
germ map has exactly two values and the even-order condition makes it bijective on a
neighbourhood of every zero as well, so the monodromy principle applies and a germ at any
one point propagates to a global section. The order statement is not decoration: the
$`\mu`-torsor argument needs the square root of $`E_6 \circ \tau` to have a prescribed
divisor, and it is the halved orders that pin it down.
:::

:::theorem "thm:exists-holomorphic-square-root-upper-half-plane" (lean := "Mathoverflow1973.AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane") (parent := "analysis") (uses := "thm:exists-analytic-square-root-on-of-even-zeros")
*Theorem.* An `MDifferentiable` map $`f : \mathfrak{h} \to \C` all of whose zeros have
even analytic order admits a holomorphic $`r : \mathfrak{h} \to \C` with $`r^2 = f` and
halved vanishing orders.

The upper half-plane is a manifold in the development, not a subset of $`\C`, so the
statement is phrased with `ContMDiff` at smoothness $`\omega` and the orders are those of
$`f \circ \mathrm{ofComplex}` at the underlying complex point. Passing between the two
readings is the only work: analyticity on the open half-plane set and analyticity as a
map of complex manifolds agree there, and the previous theorem applies to the transported
function. This is the form in which the square root enters the construction of the period
$`\beta`.
:::

The second analytic input is the additive Cousin problem. Solving it needs the
$`\bar\partial`-operator, an elementary right inverse for it, and a partition-of-unity
argument; none of the three is imported.

:::definition "def:holomorphic-cousin-dbar" (lean := "Mathoverflow1973.HolomorphicCousin.dbar") (parent := "analysis")
*Definition.* The Wirtinger operator
$`\bar\partial f(z) = \tfrac12\bigl( Df(z)\,1 + i\,Df(z)\,i \bigr)`, where $`Df(z)` is the
real Fréchet derivative of $`f` at $`z`.

Defining $`\bar\partial` through the real derivative rather than through partial
derivatives in coordinates is what makes the characterization clean: $`f` is
complex-differentiable at $`z` precisely when it is real-differentiable there and
$`\bar\partial f(z) = 0`. That equivalence is the bridge used throughout the Cousin
argument, where a solution is first produced smoothly and then corrected until its
$`\bar\partial` vanishes, at which point it is holomorphic with no further work.
:::

:::definition "def:holomorphic-cousin-cauchy-green" (lean := "Mathoverflow1973.HolomorphicCousin.cauchyGreen") (parent := "analysis")
*Definition.* The Cauchy–Green transform
$`(Tf)(z) = \frac{1}{\pi}\int_{\C} w^{-1} f(z - w)\,dA(w)`.

The convolution form, rather than $`\int (z-w)^{-1} f(w)`, is chosen so that the
integrand's singularity sits at a fixed point and the integral is manifestly a
convolution with the locally integrable kernel $`w^{-1}`; smoothness of $`Tf` then
follows from smoothness of $`f` by differentiating under the integral. For compactly
supported $`f` of class $`C^1` the transform inverts $`\bar\partial`, and it preserves
$`C^\infty`. It is the entire solution theory for the inhomogeneous
$`\bar\partial`-equation used here — no elliptic regularity, no Hörmander estimates.
:::

:::theorem "thm:dbar-cauchy-green" (lean := "Mathoverflow1973.HolomorphicCousin.dbar_cauchyGreen") (parent := "analysis") (uses := "def:holomorphic-cousin-dbar, def:holomorphic-cousin-cauchy-green")
*Theorem.* For compactly supported $`f` of class $`C^1`, $`\bar\partial(Tf) = f`
everywhere.

The proof is by hand and stays elementary: $`\bar\partial` commutes with the transform on
$`C^1` functions, reducing the claim to $`T(\bar\partial f) = f`, which is the
Cauchy–Pompeiu formula for a compactly supported function and is established by explicit
radial and angular Green integrals in polar coordinates. The compact-support hypothesis is
not a technicality to be removed later — the cocycle data is cut off by a smooth partition
of unity precisely so that this hypothesis holds when the transform is applied.
:::

:::theorem "thm:exists-normalized-holomorphic-cocycle-solution" (lean := "Mathoverflow1973.HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution") (parent := "analysis") (uses := "def:holomorphic-cousin-dbar, thm:dbar-cauchy-green")
*Theorem (Cousin I, normalized at infinity).* Let $`(U_i)` be an open cover of $`\C` and
$`h_{ij}` an additive $`1`-cocycle of functions analytic on the overlaps, and suppose one
member $`U_{i_0}` contains $`\lbrace \lVert z \rVert > R \rbrace`. Then there are
$`u_i` holomorphic on $`U_i` with $`u_i - u_j = h_{ij}`, and an analytic $`g` near $`0`
with $`g(0) = 0` such that $`u_{i_0}(z) = g(1/z)` for $`\lVert z \rVert > R`.

Three steps. A smooth partition of unity subordinate to the cover splits the cocycle
smoothly, giving local potentials whose differences are the $`h_{ij}`; their common
$`\bar\partial` is a single globally defined smooth function, compactly supported once
the cutoff is arranged to be identically $`1` near infinity. Correcting each potential by
the Cauchy–Green transform of that forcing term kills the $`\bar\partial` and leaves the
differences unchanged, so the corrected pieces are holomorphic and still split the
cocycle. The normalization at infinity comes for free from the cutoff: outside the
support the distinguished potential vanishes, so the corrected piece there is the
transform alone, which extends analytically through $`\infty` with value $`0`.
:::

:::theorem "thm:exists-negative-one-holomorphic-cocycle-solution" (lean := "Mathoverflow1973.HolomorphicCousin.exists_negativeOne_holomorphic_cocycle_solution") (parent := "analysis") (uses := "thm:exists-normalized-holomorphic-cocycle-solution")
*Theorem.* The same cocycle splits with the sharper behaviour
$`u_{i_0}(z) = z^{-1} g(1/z)` at infinity, for $`g` analytic near $`0`.

Since the normalized solution already has $`g(0) = 0`, dividing by the variable is
legitimate, and `dslope` performs the division analytically: $`\mathrm{dslope}\ g\ 0` is
analytic on the same ball and agrees with $`g(z)/z` away from the origin. Read
cohomologically this is $`H^1(\PP^1, \mathcal{O}(-1)) = 0` — a splitting whose
distinguished piece is $`O(1/z)`, that is, a section of $`\mathcal{O}(-1)` on the chart at
infinity. It is this form, not the previous one, that the $`\mu`-torsor gluing consumes to
manufacture the global period $`\mu`.
:::

The remainder of the chapter uniformizes the $`(3,4,\infty)` orbit space. The descent
calculus is organized around a structure recording exactly what a candidate uniformizer
must satisfy on the fundamental half-domain.

:::definition "def:boundary-map" (lean := "Mathoverflow1973.TriangleUniformizationGluing.BoundaryMap") (parent := "analysis")
*Definition.* A `BoundaryMap` is a function $`D : \mathfrak{h} \to \C`, continuous on the
half Ford region, whose values are real at every point of that region which is not
interior.

The two conditions are what a Schwarz reflection needs. From $`D` the module builds the
folded map, defined on the left of the wall $`\mathrm{Re} = -1/2` as $`D` itself and on
the right as $`\overline{D(\rho z)}` for $`\rho` the reflection in that wall; the reality
condition on the boundary is exactly the compatibility making the two halves agree where
they meet. The folded map is then triangle-group invariant, descends to the orbit space,
and is the object all subsequent holomorphy and properness statements are made about.
:::

:::definition "def:signed-half-plane-map" (lean := "Mathoverflow1973.TriangleUniformizationGluing.SignedHalfPlaneMap") (parent := "analysis") (uses := "def:boundary-map")
*Definition.* A `SignedHalfPlaneMap` is a `BoundaryMap` together with an orientation
$`k \in \R` with $`k^2 = 1`, which is injective on the half Ford region, carries it onto
the closed half-plane $`\lbrace w : 0 \le k\,\mathrm{Im}\,w \rbrace`, and sends the
interior into the open half-plane.

The orientation is carried as data because it is never computed. The normalization step
produces a boundary homeomorphism whose image is one of the two closed half-planes, and
which one depends on a sign that the development does not determine; rather than settle
it, the entire gluing theory is developed for either sign at once. This is a
formalization-driven choice with no counterpart in the paper, and it costs only the extra
parameter $`k` threaded through every statement.
:::

Producing such a map requires the Riemann mapping theorem, which is itself proved here.
The extremal argument rests on Montel's theorem and on a Hurwitz dichotomy for locally
uniform limits.

:::theorem "thm:eq-on-zero-or-forall-ne-zero-of-tendsto-locally-uniformly-on" (lean := "Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn") (parent := "analysis")
*Theorem (Hurwitz).* Let $`U \subseteq \C` be open and preconnected and let $`F_i \to f`
locally uniformly on $`U`, where the $`F_i` are eventually holomorphic and eventually
nowhere zero on $`U`. Then either $`f` vanishes identically on $`U`, or $`f` has no zero
in $`U`.

The proof runs through the argument principle, also formalized here: for $`f` holomorphic
and nonvanishing on a circle, $`\frac{1}{2\pi i}\oint f'/f` counts the zeros inside with
multiplicity. If $`f` has an isolated zero, that integral is a positive integer for a
small circle around it, while the integrals for the $`F_i` all vanish and converge to it
— a contradiction. The companion statement, that a locally uniform limit of injective
holomorphic maps is constant or injective, is proved the same way and is what keeps
injectivity in the extremal family below.
:::

:::theorem "thm:exists-bij-on-unit-ball-deriv-ne-zero-map-eq-zero" (lean := "Mathoverflow1973.RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero") (parent := "analysis") (uses := "thm:eq-on-zero-or-forall-ne-zero-of-tendsto-locally-uniformly-on")
*Theorem (Riemann mapping theorem).* Every open simply connected $`U \subsetneq \C` and
every $`x_0 \in U` admit a holomorphic $`f` mapping $`U` bijectively onto the open unit
ball, with $`f' \ne 0` throughout $`U` and $`f(x_0) = 0`.

Both the properness of the inclusion $`U \ne \C` and simple connectivity are essential and
both appear as explicit hypotheses; the conclusion is stated as a bijection onto
`Metric.ball 0 1` together with the two normalizations, rather than as an abstract
biholomorphism, so that the packaged diffeomorphism can be built afterwards. The
formalization follows Kudryashov's Mathlib development {citep kudryashov.rmt}[], adapted
into the module.
:::

:::proof "thm:exists-bij-on-unit-ball-deriv-ne-zero-map-eq-zero"
Let $`\mathcal{N}` be the class of injective holomorphic maps $`U \to \mathbb{D}` with
$`f(x_0) = 0` and nonvanishing derivative. Simple connectivity makes $`\mathcal{N}`
nonempty: a square root of a Möbius-type function exists on $`U` because $`U` omits a
point, and composing with a disc automorphism normalizes it. Uniform convergence on
compact subsets of $`U` is realised as the `UniformOnFun` topology over the compact
subsets, and Montel's theorem — boundedness implies compact closure — makes the closure of
$`\mathcal{N}` compact. Hurwitz's dichotomy identifies the limit points: an element of the
closure is either constant or injective, and the normalization $`f'(x_0) \ne 0` rules out
the constants. So $`\lVert f'(x_0) \rVert` attains a maximum on $`\mathcal{N}`. A
maximizer is onto, by the Koebe square-root trick: if some $`a \in \mathbb{D}` were
omitted, composing with the automorphism moving $`a` to $`0`, extracting a square root
— again available because the composite is nonvanishing on a simply connected domain — and
renormalizing produces a member of $`\mathcal{N}` with strictly larger derivative at
$`x_0`, contradicting maximality. $`\blacksquare`
:::

:::definition "def:biholomorph-unit-disc" (lean := "Mathoverflow1973.RiemannMapping.biholomorphUnitDisc") (parent := "analysis") (uses := "thm:exists-bij-on-unit-ball-deriv-ne-zero-map-eq-zero")
*Definition.* The Riemann map of a simply connected proper open $`U \subseteq \C`,
packaged as an analytic diffeomorphism `Diffeomorph 𝓘(ℂ) 𝓘(ℂ) U unitDisc ω` onto the
open unit disc.

The upgrade from the bijection is not formal. Holomorphy of the inverse is supplied by the
nonvanishing of the derivative through the local inverse theorem, and the two sides are
then compared as complex manifolds rather than as subsets of the plane, which is the form
required wherever a chart is being built. Throughout the development "biholomorphism"
means an $`\omega`-`Diffeomorph` for the standard model with corners; there is no bespoke
biholomorphism type.
:::

Extending a Riemann map to the boundary of its domain is the technical heart of the
uniformization. Three ingredients are needed: a gluing theorem across the real axis, a
reflection principle producing the function to glue, and separate charts straightening the
corners and the ideal vertex of the Ford triangle.

:::theorem "thm:analytic-on-nhd-paste-upper" (lean := "Mathoverflow1973.SchwarzReflection.analyticOnNhd_pasteUpper") (parent := "analysis")
*Theorem.* Let $`U \subseteq \C` be open, $`f` continuous on
$`U \cap \lbrace \mathrm{Im} \ge 0 \rbrace` and holomorphic above the axis, $`g`
continuous on $`U \cap \lbrace \mathrm{Im} \le 0 \rbrace` and holomorphic below, and
$`f = g` on $`U \cap \R`. Then the pasted function is analytic on all of $`U`.

The point is that no hypothesis is imposed on the real axis beyond continuity and
agreement. The proof is a Morera argument, formalized as a standalone lemma: a function
continuous on $`U` and complex-differentiable off $`\R` is holomorphic on $`U`, proved by
showing its integral over every rectangle vanishes — rectangles meeting the axis being
handled by pushing the horizontal edge off it and passing to the limit. This is the
analytic-continuation engine for the whole triangle-group uniformization.
:::

:::theorem "thm:exists-analytic-extension-of-modulus-one" (lean := "Mathoverflow1973.RiemannBoundary.exists_analytic_extension_of_modulus_one") (parent := "analysis") (uses := "thm:analytic-on-nhd-paste-upper")
*Theorem (Schwarz reflection).* Let $`f` be holomorphic on
$`U \cap \lbrace \mathrm{Im} > 0 \rbrace` with $`\lVert f \rVert \to 1` on approach to each
real point of $`U`. Then for every real $`x \in U` there is $`r > 0` and an $`H` analytic
on the ball of radius $`r` about $`x` which agrees with $`f` above the axis, with
$`\overline{f(\bar z)}^{\,-1}` below it, and has $`\lVert H \rVert = 1` on the axis.

The reflected formula is inversion in the unit circle composed with conjugation, which is
the right reflection when the boundary values lie on the circle rather than on a line; the
modulus hypothesis is stated as a limit along the upper half-plane rather than as an
extension by continuity, since $`f` is not assumed to extend. Gluing the two halves is the
previous theorem, once the boundary values are shown to agree — an edge-of-the-wedge
argument on rectangles supplying the missing continuity along the axis.
:::

:::definition "def:riemann-mapping-triangle-map" (lean := "Mathoverflow1973.RiemannMapping.triangleMap") (parent := "analysis") (uses := "thm:exists-bij-on-unit-ball-deriv-ne-zero-map-eq-zero")
*Definition.* The chosen Riemann map of the open Ford triangle — the interior of the
fundamental half-domain of the $`(3,4,\infty)` triangle group in $`\mathfrak{h}` — onto
the unit disc, sending the triangle basepoint to $`0`.

The triangle interior is simply connected and proper in $`\C`, so the previous theorem
applies; `triangleMap` is the function extracted from it by choice, and every later
statement about the boundary behaviour of the uniformizer is a statement about this one
fixed map. Fixing it once matters, because the boundary germs at the two elliptic corners
and at the ideal vertex are each constructed by a separate argument and must all refer to
the same map for the resulting boundary correspondence to be consistent.
:::

:::theorem "thm:exists-conformal-extension-disc-homeomorph-at-ideal-vertex" (lean := "Mathoverflow1973.RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex") (parent := "analysis") (uses := "thm:exists-analytic-extension-of-modulus-one")
*Theorem.* Let $`D` be homeomorphic to the unit disc by $`e`, with $`f` the underlying
holomorphic map, and suppose $`D` contains a half-strip
$`\lbrace a < \mathrm{Re} < a + c\pi,\ \mathrm{Im} > B \rbrace` whose two vertical edges
above height $`B` lie outside $`D`. Then $`f \circ \mathrm{logHalfStrip}`, where
$`\mathrm{logHalfStrip}(q) = a - ic\log q`, extends to an analytic germ $`H` at $`q = 0`
with $`\lVert H \rVert = 1` on the real axis, $`H'(0) \ne 0`, and, near $`0`,
$`\lVert H \rVert < 1` exactly when $`\mathrm{Im}\,q > 0`.

The ideal vertex has no tangent to straighten, so the chart is logarithmic rather than a
root: $`q \mapsto a - ic\log q` maps a punctured half-disc onto the half-strip, converting
the cusp into an ordinary boundary point. The reflection theorem then applies at $`q = 0`,
and the two extra conclusions — nonvanishing derivative and the local characterization of
the interior — are what make the germ a genuine conformal boundary chart rather than a
mere analytic extension.
:::

:::definition "def:closed-disc-homeomorph" (lean := "Mathoverflow1973.RiemannBoundary.closedDiscHomeomorph") (parent := "analysis")
*Construction.* Let $`X` be compact Hausdorff with a dense
subset $`D` homeomorphic to the open unit disc, and suppose the `DiscBoundaryLimits`
condition holds: at every boundary point the homeomorphism has a limit on the unit circle
in both directions. Then $`X \simeq_{\mathrm{top}} \overline{\mathbb{D}}`.

Carathéodory's theorem is not proved in generality. The hypothesis is packaged as data —
for each boundary point, a prescribed unit-circle value together with the two limit
statements — and the conclusion follows formally: the boundary values extend the disc
homeomorphism to a continuous map on all of $`X`, injectivity and surjectivity onto the
closed ball are read off from the limits, and compactness upgrades the continuous
bijection to a homeomorphism. The work is entirely in verifying the hypothesis, which is
done point-type by point-type for the Ford triangle.
:::

:::definition "def:triangle-closed-disc-homeomorph" (lean := "Mathoverflow1973.RiemannMapping.triangleClosedDiscHomeomorph") (parent := "analysis") (uses := "def:biholomorph-unit-disc, def:closed-disc-homeomorph, def:riemann-mapping-triangle-map, thm:exists-analytic-extension-of-modulus-one, thm:exists-conformal-extension-disc-homeomorph-at-ideal-vertex")
*Construction.* The closed Ford triangle domain is homeomorphic to the closed unit disc,
extending the Riemann map of its interior: interior points go to the open disc, boundary
points to the unit circle.

Discharging `DiscBoundaryLimits` is a case analysis over the boundary. Along the three
sides the limit values come from the Schwarz reflection germs, which extend the map
analytically across each side and so produce two-sided limits of modulus one. At the two
elliptic corners, of angles $`\pi/3` and $`\pi/4`, the corner is first straightened by the
principal root $`z \mapsto z^{1/n}` — a rotated fourth root at the second — and the germ is
then supplied by the same reflection argument. The ideal vertex is straightened
logarithmically instead, by the previous theorem. Each case is packaged as a
`TriangleBoundaryGerm`: an analytic $`H` with $`\lVert H(0) \rVert = 1`, $`H'(0) \ne 0`,
and a correspondence identifying the source parameter with a triangle point.
:::

:::definition "def:triangle-signed-half-plane-map" (lean := "Mathoverflow1973.RiemannMapping.triangleSignedHalfPlaneMap") (parent := "analysis") (uses := "def:riemann-sphere, def:signed-half-plane-map, def:triangle-closed-disc-homeomorph")
*Definition.* The concrete uniformizer: the `SignedHalfPlaneMap` obtained from the closed
Ford triangle homeomorphism by post-composing with the Möbius cross-ratio that sends the
two elliptic corner values and the cusp value to $`0, 1, \infty`.

Three boundary values are computed from the germs of the previous step, and the cross-ratio
built on them carries the closed disc minus one boundary point onto a closed half-plane,
with the two elliptic centres landing at $`0` and $`1`. Which half-plane is not determined
— the orientation invariant $`-\,\mathrm{Im}\,\frac{b-c}{b-a}` is proved nonzero but its
sign is left open, which is precisely why the target structure carries a sign. The two
further facts the descent needs are proved separately: the map is proper on the half Ford
region, and it is holomorphic on the interior, where it equals the cross-ratio composed
with `triangleMap`.
:::

:::definition "def:quotient-biholomorph" (lean := "Mathoverflow1973.TriangleUniformizationGluing.SignedHalfPlaneMap.quotientBiholomorph") (parent := "analysis") (uses := "def:signed-half-plane-map, thm:triangle-compactified-is-manifold")
*Construction.* A `SignedHalfPlaneMap` which is proper on the half Ford region and holomorphic
on its interior descends to an analytic diffeomorphism
$`\mathfrak{h}/\Delta(3,4,\infty) \xrightarrow{\ \sim\ } \C`.

Properness turns the descended map into a closed continuous bijection, hence a
homeomorphism of the orbit space with $`\C`; the analytic content is that it and its
inverse are holomorphic. Holomorphy upstairs is propagated across the reflection walls by
a reusable removable-singularity predicate, verified for the real axis, for vertical lines,
for translated unit circles, and — since the predicate is stable under locally finite
unions — for the whole folded edge complex at once. The two elliptic orbit points, where
the quotient chart is branched, are handled by a manifold-level Riemann removable
singularity theorem, and the inverse is holomorphic because a holomorphic homeomorphism
between one-dimensional complex manifolds has holomorphic inverse.
:::

:::definition "def:compactified-biholomorph" (lean := "Mathoverflow1973.TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedBiholomorph") (parent := "analysis") (uses := "def:riemann-sphere, def:signed-half-plane-map, thm:triangle-compactified-is-manifold")
*Construction.* The same map, one-point compactified: an analytic diffeomorphism from the
compactified triangle orbit space onto the Riemann sphere.

Both sides are one-point compactifications — the orbit space plus its cusp on the left,
$`\C` plus $`\infty` on the right — so the homeomorphism extends by sending cusp to
$`\infty`, and holomorphy at that point is read in the chart $`z \mapsto 1/z` supplied by
`TwoAffineCharts`. This is the identification that gives the fibration its base: from here
on, the quotient of the upper half-plane by the $`(3,4,\infty)` triangle group,
compactified at the cusp, *is* $`\PP^1`, and the three special points $`p_0, p_1, p_2` of
the paper are three specified points of the Riemann sphere.
:::

Two results stand apart from the analytic development, both classical facts used in the
topological half of the argument and both absent from Mathlib.

:::theorem "thm:covering-comp-of-finite-fibres" (lean := "Mathoverflow1973.CoveringComposition.covering_comp_of_finite_fibres") (parent := "analysis")
*Theorem.* If $`f : E \to B` and $`g : B \to X` are covering maps and every fibre
$`g^{-1}(x)` is finite, then $`g \circ f` is a covering map.

The finiteness hypothesis cannot be dropped: without it the intersection of infinitely
many evenly-covered neighbourhoods need not be a neighbourhood, and composites of
coverings genuinely fail to be coverings. In the application $`g` is the finite-sheeted
covering coming from the elliptic points of the base, so the hypothesis is available.
:::

:::proof "thm:covering-comp-of-finite-fibres"
Fix $`x \in X` and let $`I = g^{-1}(x)`, a finite discrete set. A `SheetFamily` for $`g`
at $`x` is a choice, for each $`i \in I`, of an open sheet mapped homeomorphically onto a
fixed evenly-covered neighbourhood of $`x`; one exists because $`g` is a covering. Pick a
point $`b_i` over $`x` in each sheet, and a `SheetFamily` for $`f` at each $`b_i`.
Intersecting the finitely many base neighbourhoods obtained from the $`i \in I` leaves an
open neighbourhood of $`x`, and over it the sheets of $`f` above the sheets of $`g`, indexed
by the pairs, are pairwise disjoint opens each mapped homeomorphically by $`g \circ f`. The
finiteness of $`I` is used exactly once, for that intersection. $`\blacksquare`
:::

:::definition "def:twist-order" (lean := "Mathoverflow1973.twistOrder") (parent := "analysis")
*Definition.* $`\mathrm{twistOrder}(\ell_0, \ell_1, \ell_2) = 12\ell_0 - 4\ell_1 - 3\ell_2`.

This integer is the order of the cyclic fundamental group of the threefold as a function
of the three twist parameters, and it is the whole arithmetic content of the simple
connectivity of $`X`: the van Kampen presentation collapses to a cyclic group generated by
one central element $`c`, subject to $`c^{12\ell_0 - 4\ell_1 - 3\ell_2} = 1`. For the twist
data $`(0, 1, -1)` actually chosen in the construction, $`\mathrm{twistOrder} = -1`, so the
group has order one and is trivial. The evaluation is settled by `decide`.
:::
