/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — The toric filling at the cusp chapter.

Mumford's construction at the cusp point of the base: the infinite smooth toric
threefold over the fan on the A2 triangulation, the twisted lattice action, the
quotient N0 with its central fibre, and the diagonal-quotient fibration theory.
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

#doc (Manual) "The toric filling at the cusp" =>

Over the punctured base the family of complex two-tori is well behaved, but at the cusp
point $`p_0` the monodromy of the fibre lattice is the unipotent matrix $`M_0`, the period
matrix runs off to infinity, and there is no smooth torus to insert. Mumford's toric
construction supplies the replacement {citep mumford72}[]. One builds an infinite smooth
toric threefold $`Y` carrying a global holomorphic function $`t` whose zero divisor is a
reduced normal-crossings union of surfaces, one for each vertex $`v \in \Z^2`; a lattice
$`\Z^2` acts on the tube $`Y_\varepsilon = \{|t| < \varepsilon\}` by biholomorphisms
preserving $`t`, freely and properly discontinuously; and the quotient
$`N_0 = Y_\varepsilon/\Z^2` is a complex threefold fibred over a disc whose fibres over
$`t \ne 0` are exactly the tori of the family and whose fibre over $`0` is a compact
normal-crossings surface $`W`. This is the first of the three fillings that compactify
the family, and the only one that is toric; the two elliptic points are filled by
logarithmic transforms instead {citep alpoge.s6}[].

The fan is the cone over the $`A_2` triangulation of the plane: vertex set $`\Z^2`, edges
in the six directions $`\pm e_1, \pm e_2, \pm(e_1 - e_2)`, and the triangles
$`\{v, v + e_1, v + e_2\}` and $`\{v + e_1, v + e_2, v + e_1 + e_2\}`. Two features of it
carry the whole construction. Every cone is unimodular, so $`Y` is a smooth complex
threefold and each chart is a genuine copy of $`\C^3`. And every ray sits at height one,
so the monomial $`z_0 z_1 z_2` is the same function in every chart — that function is
$`t`, and its divisor is the sum of the toric prime divisors with all multiplicities one,
which is to say the central fibre is *reduced*.

The deck transformations twist the fan symmetry by the period data. Near the cusp the
period matrix reads $`Z = s B_0 + C(t)`, where $`B_0` is the quarter turn
$`B_0(v_0, v_1) = (v_1, -v_0)` and $`C` is holomorphic across $`t = 0`; the lattice shear
$`v \mapsto B_0 v` preserves the fan, and rescaling the fibre coordinates by
$`\exp(2\pi i\, C(t) v)` turns it into a $`t`-preserving biholomorphism of the tube. The
formalization keeps the shear but drops the surrounding period theory: $`B_0` is
hard-wired as the rotation `ToricSpace.cuspVector`, $`C` is an arbitrary matrix-valued
function holomorphic on a ball, and the analytic input the paper obtains from the
boundedness of $`\mathsf R = -2\pi \operatorname{Im} C` near the origin is isolated as an
explicit quantitative hypothesis, `SmallDrift`, which can always be arranged by shrinking
the disc.

Nothing in the development is abstract toric geometry. There are no fans, no cones, no
schemes: a triangle is a bare structure of two integers and a Boolean, its rays and their
inverse are written down as $`3 \times 3` integer matrices, unimodularity and the
adjacency combinatorics are decided by case analysis, and the space is glued from charts
by hand. The central fibre component is likewise handled through its nonnegative real
part — a hexagon in $`\R^2` cut out by three linear inequalities — rather than through
moment maps or the algebraic geometry of the degree-six del Pezzo surface. The chapter
closes with a self-contained theory of diagonal quotients $`(B \times F)/G`, a
general-purpose fibration package with no counterpart in the paper, which is what carries
the fundamental-group bookkeeping for the torus family over the orbifold base.

:::group "toric"
The infinite toric threefold over the $`A_2` triangulation, the twisted lattice action on
a tube around its central fibre, the quotient $`N_0`, and the hexagonal combinatorics of
the fibre over $`0`.
:::

# The fan

:::definition "def:toric-fan-triangle" (lean := "Mathoverflow1973.ToricFan.Triangle") (parent := "toric")
A triangle of the $`A_2` triangulation is recorded by two integers $`a, b` and a Boolean
flag: the *lower* triangle at $`(a,b)` has vertices $`(a,b)`, $`(a+1,b)`, $`(a,b+1)`, and
the *upper* one has $`(a+1,b)`, $`(a,b+1)`, $`(a+1,b+1)`. These exhaust the triangulation
of the plane with vertex set $`\Z^2` cut out by the three pencils $`y_1 \in \Z`,
$`y_2 \in \Z`, $`y_1 + y_2 \in \Z`.

The type is a plain structure with decidable equality, and countable. That is the entire
fan: there is no separate notion of cone, of support, or of the compatibility of two
cones along a face. Each triangle indexes one affine chart $`\C^3` of the toric threefold,
and the arithmetic that in the paper is a statement about cones over cells of the
triangulation becomes, here, a finite case analysis on $`a`, $`b` and the flag.
:::

:::definition "def:triangle-rays" (lean := "Mathoverflow1973.ToricFan.Triangle.rays") (parent := "toric") (uses := "def:toric-fan-triangle")
$`\mathrm{rays}(s)` is the $`3 \times 3` integer matrix whose columns are the three
vertices of $`s` lifted to height one — so its bottom row is $`(1,1,1)`, recorded
separately as `rays_height`. These are the primitive generators of the simplicial cone
over $`s`.

An explicit inverse $`\mathrm{dual}(s)`, again written out entry by entry, is verified in
both orders, and its rows give the character basis $`(z_0, z_1, z_2)` of the chart. The
transition matrix from $`s` to $`t` is $`\mathrm{dual}(t)\,\mathrm{rays}(s)`; it satisfies
the cocycle identity, is again of height one, and the Laurent-monomial map
$`z \mapsto \big(\prod_j z_j^{A_{ij}}\big)_i` it defines is an open partial homeomorphism
of $`\C^3` with holomorphic inverse. Negative exponents are harmless because they occur
only where the corresponding coordinate is invertible.
:::

:::theorem "thm:triangle-rays-det" (lean := "Mathoverflow1973.ToricFan.Triangle.rays_det") (parent := "toric") (uses := "def:triangle-rays, def:toric-fan-triangle")
$`\det \mathrm{rays}(s) = -1` when $`s` is upper and $`+1` when it is lower; in particular
$`\det \mathrm{rays}(s) = \pm 1` for every triangle $`s`.

Every cone of the fan is therefore unimodular, which is the smoothness of the toric
threefold: each chart is an honest $`\C^3` and each transition is invertible over $`\Z`,
so both directions of a chart change are Laurent-monomial. The sign records only the
orientation flip between the upper and lower triangles of a lattice square.
:::

:::proof "thm:triangle-rays-det"
Both matrices are explicit, and their determinants are polynomial identities in $`a` and
$`b`: expanding by `Matrix.det_fin_three` and clearing the brackets leaves the stated
constant, with no hypotheses on $`a, b` at all. The proof is a case split on the flag
followed by `ring`.
$`\blacksquare`
:::

# Gluing, the manifold structure, and the time function

The charts are glued along the monomial chart changes with mathlib's `TopCat.GlueData`,
which asks exactly for the cocycle identity already available from the transition
matrices. What comes out is a topological space; the complex structure, the global
function $`t`, and every later construction are then read off chart by chart, through a
`descend` idiom that defines a map on the glued space from a compatible family of maps on
the charts.

:::definition "def:toric-space-space" (lean := "Mathoverflow1973.ToricSpace.Space") (parent := "toric") (uses := "def:toric-fan-triangle")
$`Y := \mathrm{Space}` is the space obtained by gluing one copy of $`\C^3` per triangle
along the monomial chart changes. Each inclusion $`\iota_s : \C^3 \to Y` is an open
embedding; the inclusions are jointly surjective; and $`\iota_s(z) = \iota_t(w)` exactly
when $`z` lies in the source of the chart change from $`s` to $`t` and is carried to $`w`
by it. The space is Hausdorff and second countable.

This is the infinite-type toric variety $`Y_{\mathfrak F}` of the paper, produced without
any toric machinery. The charts and their overlaps are all there is; in particular no
claim is made, or needed, that $`Y` is a variety, that it is separated in the scheme sense,
or that it carries an algebraic torus action.
:::

:::definition "def:toric-space-is-manifold" (lean := "Mathoverflow1973.ToricSpace.isManifold") (parent := "toric") (uses := "def:toric-space-space, def:toric-fan-triangle")
$`Y`, with the atlas whose charts are the inverses of the parametrizations $`\iota_s`, is
an analytic complex manifold modelled on $`\C^3`: `IsManifold` for the model with corners
$`\mathcal{I}(\C, \C^3)` at smoothness $`\omega`.

The regularity is $`\omega` rather than $`1`, and the two are not interchangeable in this
development: the atlas transported all the way to the six-sphere is required to be
analytic, and the chart changes here — monomial maps of unimodular integer matrices —
supply that at no extra cost. Hausdorffness and second countability are separate
instances, so $`Y` is a manifold in the full sense and not merely a locally Euclidean
space.
:::

:::definition "def:toric-space-time" (lean := "Mathoverflow1973.ToricSpace.time") (parent := "toric") (uses := "def:toric-space-space, def:toric-fan-triangle")
$`t := \mathrm{time} : Y \to \C` is defined in each chart by $`z_0 z_1 z_2` and is well
defined globally: every ray has height one, so the monomial $`z_0z_1z_2` is fixed by every
transition matrix, and $`t \circ \iota_s = z_0z_1z_2` for all $`s`. It is holomorphic.

This is the paper's $`t = \chi^{(0,0,1)}`. The open torus $`\{t \ne 0\}` is the image of
the coordinate torus in any single chart and is dense in $`Y`; the fibre $`t^{-1}(0)` is
the union of the toric divisors, and the local normal forms $`z_0`, $`z_0z_1`,
$`z_0z_1z_2` at points lying on one, two or three of them are visible directly in the
chart formula. Height one is what makes all the multiplicities equal to one, so the
central fibre is reduced.
:::

# The twisted lattice action

:::definition "def:twisted-translate" (lean := "Mathoverflow1973.ToricSpace.twistedTranslate") (parent := "toric") (uses := "def:toric-space-time, def:toric-space-space")
For $`v \in \Z^2` and a matrix-valued function $`C : \C \to M_2(\C)`, the deck
transformation is
$$`\Psi_v = \mathrm{variableMultiplier}\big(\exp(2\pi i\, C(t) v)\big) \circ
\mathrm{translate}(\mathrm{cuspVector}\, v), \qquad \mathrm{cuspVector}(v) = (v_1, -v_0).`
Here $`\mathrm{translate}(w)` relabels the chart of a point from $`s` to $`s + w` without
touching its chart coordinates — the toric automorphism induced by the lattice shear — and
$`\mathrm{variableMultiplier}` rescales the first two chart coordinates by the unit vector
$`\exp(2\pi i\,(C(t)v)_j)`, leaving $`t` fixed.

The rotation $`\mathrm{cuspVector}` is the paper's $`B_0` applied to $`v`, hard-wired
rather than carried as data. The construction is additive in $`v`, satisfies
$`t \circ \Psi_v = t`, and is holomorphic on $`t^{-1}(D)` whenever the entries of $`C` are
holomorphic on $`D`; so it is an action of $`\Z^2` by biholomorphisms on every tube.
:::

:::definition "def:toric-space-small-drift" (lean := "Mathoverflow1973.ToricSpace.SmallDrift") (parent := "toric")
$`\mathrm{SmallDrift}\ C\ \varepsilon` asserts that for every $`t` with
$`0 < \|t\| < \varepsilon`,
$$`\|\mathsf R(t)\|_{\max} \le \frac{-\log\|t\|}{4}, \qquad
\mathsf R(t)_{ij} = -2\pi \operatorname{Im} C(t)_{ij},`
where $`\|\cdot\|_{\max}` is the largest absolute value of an entry.

This is the formal surrogate for the paper's normalization
$`|\log \varepsilon_0| \ge 2\|\mathsf R\|_\infty`. Its role is metric. In the normalized
logarithmic coordinates $`y(x) = \log|z(x)|/\log|t(x)|`, a twisted translate displaces a
point by $`\mathrm{cuspVector}(v)` plus a drift term whose norm the bound keeps below
$`\|v\|/2`; consequently $`\|v\| \le 2\,\|y(\Psi_v x) - y(x)\|`, so a lattice vector
cannot move a point far in $`Y` without being short.
:::

The quantitative statement above is what replaces the paper's asymptotic argument, and it
is the only place where an inequality on $`C` is used. Everything downstream —
discreteness of the orbits, the manifold structure on the quotient, the properness of the
fibration — is a formal consequence of it together with holomorphy of $`C` on the
$`\varepsilon`-ball.

:::theorem "thm:cusp-quotient-proper-action" (lean := "Mathoverflow1973.CuspQuotient.proper_action") (parent := "toric") (uses := "def:toric-space-small-drift, def:twisted-translate")
Let $`0 < \varepsilon < 1`, let the entries of $`C` be analytic on the ball
$`B(0,\varepsilon)`, and assume $`\mathrm{SmallDrift}\ C\ \varepsilon`. Then the action of
$`\Z^2` by twisted translation on the tube $`t^{-1}(D(0,\varepsilon))` is properly
discontinuous: for compact $`K, L` in the tube, only finitely many lattice elements $`g`
satisfy $`gK \cap L \ne \emptyset`.
:::

:::proof "thm:cusp-quotient-proper-action"
A compact subset of the tube has $`\|t\| < \varepsilon` throughout and meets only finitely
many of the truncated charts $`\{|z_j| < S\}`, so its normalized position
$`y = \log|z|/\log|t|` is bounded. If $`g = \Psi_v` carries a point of $`K` into $`L`, the
drift estimate of `SmallDrift` gives $`\|v\| \le 2\,\|y(\Psi_v x) - y(x)\|`, and the right
side is at most twice the diameter of the position image of $`K \cup L`. Only finitely
many integer vectors are that short, and the map $`v \mapsto \Psi_v` is injective on the
lattice, so the set of offending $`g` is finite. $`\blacksquare`
:::

:::theorem "thm:cusp-quotient-free-action" (lean := "Mathoverflow1973.CuspQuotient.free_action") (parent := "toric") (uses := "thm:cusp-quotient-proper-action, def:toric-space-small-drift, def:twisted-translate")
Under the same hypotheses the action is free: if $`\Psi_v x = x` for some point $`x` of
the tube then $`v = 0`. The Lean statement is `IsCancelSMul`, the cancellativity of the
scalar action, which for a group action is exactly freeness.

The argument is the cheap one available once proper discontinuity is known: a properly
discontinuous action has finite stabilizers, so any stabilizing $`v` has finite order in
$`\Z^2` and is therefore zero. The paper instead derives freeness directly from
$`|B_0 \bar\lambda| = |\bar\lambda|`; the formal route needs no such identity because it
already has the finiteness.
:::

# The quotient

:::definition "def:cusp-quotient-quotient-space" (lean := "Mathoverflow1973.CuspQuotient.QuotientSpace") (parent := "toric") (uses := "def:twisted-translate")
$`N_0 := \mathrm{QuotientSpace}\ C\ \varepsilon` is the quotient of the tube
$`t^{-1}(D(0,\varepsilon)) \subset Y` by the orbit relation of the twisted $`\Z^2`-action.

This is the local model of the threefold near the cusp point of the base: a family of
complex two-tori over the punctured disc, degenerating over $`0` to the cycle of toric
surfaces. Its hypotheses are carried explicitly rather than bundled into a structure, so
$`C` and $`\varepsilon` appear as parameters of the type itself; the quotient is formed
unconditionally, and the bounds $`0 < \varepsilon < 1`, holomorphy, and `SmallDrift` are
supplied one by one to the theorems that need them.
:::

:::definition "def:cusp-quotient-projection" (lean := "Mathoverflow1973.CuspQuotient.projection") (parent := "toric") (uses := "def:cusp-quotient-quotient-space, def:toric-space-time")
The twisted translations preserve $`t`, so $`t` descends to a continuous map
$`f_0 : N_0 \to \C` with image in $`D(0,\varepsilon)`; `baseMap` repackages it as a map
into the disc itself.

This is the fibration of the cusp piece over the disc. Its fibre over $`t_0 \ne 0` is the
quotient of $`(\C^*)^2` by the twisted Tate-type period action, which the paper identifies
with the compact torus $`\C^2/L`; its fibre over $`0` is the reduced normal-crossings
surface $`W`. Nothing in this development identifies the fibres with the tori of the
global family — that comparison is made where the pieces are glued together.
:::

:::theorem "thm:cusp-quotient-is-manifold" (lean := "Mathoverflow1973.CuspQuotient.isManifold") (parent := "toric") (uses := "def:cusp-quotient-quotient-space, thm:cusp-quotient-proper-action, thm:cusp-quotient-free-action, thm:covering-quotient-is-manifold")
For $`0 < \varepsilon < 1`, $`C` analytic on $`B(0,\varepsilon)` and satisfying
$`\mathrm{SmallDrift}`, the quotient $`N_0` carries the charted-space structure
`CuspQuotient.chartedSpace` over $`\C^3` and is an analytic complex manifold for
$`\mathcal{I}(\C, \C^3)` at smoothness $`\omega`.

The three hypotheses combine into the statement that the projection
$`\mathrm{pr} : t^{-1}(D(0,\varepsilon)) \to N_0` is a quotient covering map for $`\Z^2`,
and the generic covering-quotient machinery then transports the atlas: charts on $`N_0`
are the local inverses
of $`\mathrm{pr}` composed with charts upstairs, and the transitions stay analytic because
every deck transformation is a biholomorphism. Companion results record that
$`\mathrm{pr}` is itself analytic and a local biholomorphism, and that a map out of $`N_0`
is analytic exactly when its composite with $`\mathrm{pr}` is.
:::

:::theorem "thm:exists-admissible-radius" (lean := "Mathoverflow1973.CuspQuotient.exists_admissible_radius") (parent := "toric") (uses := "def:toric-space-small-drift")
If the entries of $`C` are analytic on a ball $`B(0,r)` with $`r > 0`, then there is an
$`\varepsilon` with $`0 < \varepsilon < r`, $`\varepsilon < 1`, satisfying
$`\mathrm{SmallDrift}\ C\ \varepsilon`, and with the entries of $`C` still analytic on
$`B(0,\varepsilon)`.

Every hypothesis of the construction can thus be arranged by shrinking the disc, which is
what makes the cusp piece usable: the twist matrix arrives from the period theory with a
radius of holomorphy and nothing else, and this statement converts that into a legitimate
$`\varepsilon`. The proof is the elementary one — $`C` is continuous at $`0`, so
$`\|\mathsf R(t)\|_{\max}` is bounded near the origin while $`-\log\|t\|/4` grows without
bound — and the witness is $`\min(\delta, r/2)`.
:::

:::theorem "thm:cusp-quotient-base-map-proper" (lean := "Mathoverflow1973.CuspQuotient.baseMap_proper") (parent := "toric") (uses := "def:cusp-quotient-projection, thm:cusp-quotient-proper-action")
Under the standing hypotheses the map $`f_0 : N_0 \to D(0,\varepsilon)` is proper:
preimages of compact subsets of the disc are compact.

In particular every fibre is compact — the tori over $`t_0 \ne 0` and the central fibre
$`W` alike — which is the point of the whole construction, since the family upstairs has
non-compact fibres $`(\C^*)^2`. The proof exhibits, over each closed subdisc
$`\{\|t\| \le \eta\}` with $`\eta < \varepsilon`, an explicit compact set of orbit
representatives: the union, over a finite set of triangles, of the images of the closed
polydisc $`\{|z_j| \le 1\}` intersected with $`\{|z_0z_1z_2| \le \eta\}`. Every orbit
meets it — for torus points by a lattice-translation argument in the position
coordinates, and for the rest by density of the torus — and a compact subset of the open
disc lies in some such closed subdisc.
:::

# The central fibre and the honeycomb

The fibre of $`f_0` over $`0` is a cycle of toric surfaces glued along the combinatorics of
the triangulation, and the quotient collapses that infinite cycle onto a single surface
with identifications. Two dual pictures are used. On the toric side the components are the
divisors $`E_v`, and their intersection pattern is the adjacency of the triangulation. On
the flat side the plane is tiled by hexagons, one per vertex, and the hexagon is
identified with the nonnegative real part of a component. The bridge between them is the
pair of results at the end of this section, and it is what the downstream homology
computation of $`W` actually consumes.

:::definition "def:cusp-honeycomb-tiling-base-cell" (lean := "Mathoverflow1973.CuspHoneycombTiling.baseCell") (parent := "toric")
$$`\mathrm{baseCell} = \{\, x \in \R^2 : |2x_0 + x_1| \le 1,\ |x_0 - x_1| \le 1,\
|x_0 + 2x_1| \le 1 \,\},`
a compact convex hexagon of area one, and $`\mathrm{cell}(v) = \mathrm{baseCell} + v` for
$`v \in \Z^2`.

The three linear forms are not independent — the third is the difference of the first two
— which is what makes the region a hexagon rather than a parallelogram, and its six sides
are indexed by the six edge directions of the triangulation. The translates form a locally
finite closed cover of the plane, and two cells meet exactly when their labels are equal
or adjacent, so the nerve of the tiling reproduces the triangulation: one cell for each
divisor component, meeting its six neighbours and nothing else.
:::

:::definition "def:toric-space-ray-divisor" (lean := "Mathoverflow1973.ToricSpace.rayDivisor") (parent := "toric") (uses := "def:toric-fan-triangle, def:toric-space-space")
Each point $`x \in Y` has a finite *branch-vertex* set: in any chart containing it, the
vertices labelling the vanishing coordinates, transported consistently across chart
changes. The set is nonempty precisely when $`t(x) = 0`. For $`v \in \Z^2` the toric
divisor is
$$`E_v = \{\, x \in Y : v \in \mathrm{branchVertices}(x) \,\},`
a closed subset of $`Y`, and $`t^{-1}(0) = \bigcup_{v} E_v`.

In the chart of a triangle $`s`, the divisor of the $`j`-th vertex of $`s` is cut out by
$`z_j = 0`, so the components meeting a chart are exactly the three vertices of its
triangle. The deck transformations permute the divisors by translation of the labels:
$`\Psi_v(x) \in E_w` if and only if $`x \in E_{w - \mathrm{cuspVector}(v)}`. Since
$`\mathrm{cuspVector}` is a bijection of $`\Z^2`, the lattice acts simply transitively on
the set of components, which is what will make the central fibre of the quotient
irreducible. The paper identifies $`E_v` with the degree-six del Pezzo surface; no such
identification is made or needed here.
:::

:::theorem "thm:toric-space-ray-divisor-inter-nonempty-iff" (lean := "Mathoverflow1973.ToricSpace.rayDivisor_inter_nonempty_iff") (parent := "toric") (uses := "def:toric-space-ray-divisor")
For $`v \ne w`, the divisors meet — $`E_v \cap E_w \ne \emptyset` — if and only if $`v`
and $`w` are adjacent in the triangulation, that is $`w - v` is one of
$`\pm e_1, \pm e_2, \pm(e_1 - e_2)`.

This is the normal-crossings combinatorics of the infinite central fibre: the dual graph of
$`t^{-1}(0)` is the one-skeleton of the $`A_2` triangulation, each component meets exactly
six others, and three components meet exactly when their vertices span a triangle. Together
with the local normal forms of $`t` it says that $`t^{-1}(0)` is a reduced
normal-crossings divisor with double curves along the edges and triple points at the
triangles.
:::

:::proof "thm:toric-space-ray-divisor-inter-nonempty-iff"
Two divisors meet if and only if some single chart contains both, because the branch
vertices at a point are exactly the vertices of a triangle containing it; so the condition
is that some triangle has both $`v` and $`w` among its vertices. Two distinct vertices of a
triangle are adjacent, by inspection of the two shapes; conversely each of the six edge
directions occurs in an explicit triangle, so an adjacent pair always spans one. Both
directions are finite case analyses on the flag and the vertex indices. $`\blacksquare`
:::

:::definition "def:compatible-cell-homeomorph" (lean := "Mathoverflow1973.CuspHoneycombHexagon.compatibleCellHomeomorph") (parent := "toric") (uses := "def:cusp-honeycomb-tiling-base-cell, def:toric-space-ray-divisor, def:cusp-positive-positive-twist")
Write $`E_0^{+}` for the nonnegative real part of the central component: the points of
$`E_0` fixed by the coordinatewise-modulus retraction of $`Y`. Then
$$`\mathrm{compatibleCellHomeomorph}(C_0) : \mathrm{baseCell} \;\xrightarrow{\ \sim\ }\;
E_0^{+}`
is a homeomorphism of the hexagonal cell onto $`E_0^{+}`, and it is compatible with the
labelling on both sides: a point of the cell is carried into $`E_v` exactly when its
cell coordinate lies in $`\mathrm{cell}(v)`.

The homeomorphism is assembled from a standard hexagon in between, with its six boundary
arcs prescribed one at a time over $`\mathrm{Fin}\ 6`. Three of the arcs are the
tautological boundary parametrizations; the other three are the reversed images of the
opposite arcs under the deck transformation of the *positive* twist
$`\mathrm{positiveTwist}(C_0)`, the constant matrix $`i\operatorname{Im} C_0` that has the
same drift as $`C_0` but acts by positive real scalings. Making that choice at the level of
arcs is what buys the equivariance of the next statement.
:::

:::theorem "thm:compatible-cell-homeomorph-opposite" (lean := "Mathoverflow1973.CuspHoneycombHexagon.compatibleCellHomeomorph_opposite") (parent := "toric") (uses := "def:compatible-cell-homeomorph, def:twisted-translate")
Let $`\rho_k` be one of the six hexagon rays and let $`x` lie in
$`\mathrm{baseCell} \cap \mathrm{cell}(\rho_k)`. Then
$$`\mathrm{compatibleCellHomeomorph}(C_0)(x - \rho_k) =
\Psi_{\mathrm{cuspVector}(\rho_k)}\big(\mathrm{compatibleCellHomeomorph}(C_0)(x)\big),`
the deck transformation being taken for the positive twist $`\mathrm{positiveTwist}(C_0)`.

Translating the cell by a hexagon ray corresponds, on $`E_0^{+}`, to applying a deck
transformation. In the quotient $`N_0`, therefore, the boundary arc indexed by $`k` and the
one indexed by $`k+3` become the same curve: the reduced central fibre $`W` is a single
hexagonal surface with its three pairs of opposite sides glued to one another. This is the
paper's description of $`W` as one copy of the del Pezzo surface with $`C_v` identified to
$`C_{-v}`, and it is the input to the cellular computation of $`H_*(W)`.
:::

:::proof "thm:compatible-cell-homeomorph-opposite"
Both sides are continuous in $`x`, and $`x` lies on the side of the cell indexed by $`k`,
so it suffices to check the identity along the parametrized boundary arc. Transporting
through the standard hexagon, the point $`x - \rho_k` is the image of the arc $`k+3` run
backwards, by the elementary fact that opposite sides of the hexagon differ by the lattice
translation $`\rho_k`. On arc $`k+3` the compatible parametrization was *defined* to be the
reversed image of arc $`k` under the deck map, and the orientation reversal cancels the one
just introduced. The six cases split into three where the arc is tautological and three
where it is the reversed opposite; each is the same computation read in one direction or the
other. $`\blacksquare`
:::

# The fundamental group of the cusp piece

:::theorem "thm:cusp-quotient-tube-simply-connected" (lean := "Mathoverflow1973.CuspQuotient.tube_simplyConnected") (parent := "toric") (uses := "def:toric-space-time, thm:simply-connected-space-of-open-cover")
For every $`\varepsilon > 0` the tube $`t^{-1}(D(0,\varepsilon)) \subset Y` is simply
connected.

The proof is by an open cover rather than by the paper's exhaustion of the fan by finite
subfans. The affine tube of a chart is $`\{z \in \C^3 : \|z_0z_1z_2\| < \varepsilon\}`,
which is star-convex about the origin and hence simply connected; its images under the
chart inclusions cover the tube, share a common point, and any two of them meet in a
path-connected set, since the intersection is the image of the affine tube intersected
with the domain of a monomial transition. The open-cover van Kampen criterion
`simplyConnectedSpace_of_open_cover` then applies.
:::

:::proof "thm:cusp-quotient-tube-simply-connected"
Fix a point of the tube lying in every one of the chart images at once: the point with
coordinates $`(\varepsilon/2, 1, 1)` in the reference chart will do, since it lies in the
open torus and every chart contains the whole torus. The four hypotheses of the open-cover
criterion are then discharged in turn: openness of each $`\iota_s(\text{affine tube})`,
jointness of the cover, simple connectivity of each member via star-convexity of
$`\{|z_0z_1z_2| < \varepsilon\}`, and path-connectedness of the pairwise intersections,
which reduces to path-connectedness of the intersection of the affine tube with the domain
of a transition monomial. $`\blacksquare`
:::

:::definition "def:fundamental-group-equiv" (lean := "Mathoverflow1973.CuspQuotient.fundamentalGroupEquiv") (parent := "toric") (uses := "def:cusp-quotient-quotient-space, thm:cusp-quotient-proper-action, thm:cusp-quotient-tube-simply-connected")
For every basepoint $`x \in N_0` there is a group isomorphism
$$`\pi_1(N_0, x) \;\cong\; \Z^2`
onto the lattice, written multiplicatively. The covering
$`\mathrm{pr} : t^{-1}(D(0,\varepsilon)) \to N_0` has simply connected total space, so it
is the universal cover and its deck group is the fundamental group.

The isomorphism is explicitly the monodromy: `fundamentalGroupEquivAt_monodromy` states
that for a basepoint of the form $`\mathrm{pr}(e)`, the class of a loop $`\gamma` is sent
to the unique lattice vector $`v` with $`\Psi_v(e)` equal to the endpoint of the lift of
$`\gamma` starting at $`e`. Passing through the file's first-Hurewicz interface,
`singularH1Equiv` upgrades this to $`H_1(N_0;\Z) \cong \Z^2` as $`\Z`-modules. These are
the two facts the Seifert–van Kampen and Mayer–Vietoris computations near the cusp
consume. In the paper's reading the fibre lattice surjects onto $`\Z^2` with the vanishing
cycles in its kernel, so those cycles die in $`\pi_1(N_0)`; that comparison is made where
the cusp piece is glued into the family, not here.
:::

:::group "diagonal-quotient"
A self-contained theory of fibre bundles arising as diagonal quotients $`(B \times F)/G`,
including the exact sequence of the fibration at $`\pi_1` — the general machinery behind
the torus family over the orbifold base.
:::

The last block of this chapter is not a piece of the paper's §4 at all. Mathlib has no
theory of fibrations and no exact homotopy sequence, so the development builds, from
scratch, the special case it needs: a group $`G` acting on a base $`B` and on a fibre
$`F`, the diagonal quotient of the product, and the fibration of that quotient over
$`B/G`. It is instantiated with $`G` the $`(3,4,\infty)` triangle group and $`F` the real
four-torus when the fundamental group of the family away from the cusp is computed.

:::definition "def:diagonal-quotient-space" (lean := "Mathoverflow1973.DiagonalQuotient.Space") (parent := "diagonal-quotient")
For a group $`G` acting on spaces $`B` and $`F`, the diagonal quotient is
$`\mathrm{Space}\ G\ B\ F = (B \times F)/G` for the diagonal action, fibred by
$`[b, f] \mapsto [b]` over the base quotient $`\mathrm{BaseSpace}\ G\ B = B/G`.

Two points of $`B \times F` have the same image exactly when some $`g \in G` carries one
to the other, and the projection is well defined because the action commutes with the
first projection. Nothing is assumed about $`G` at this stage; the hypotheses that make
the projection a fibre bundle — that $`B \to B/G` is a quotient covering map and that
$`G` acts continuously on $`F` — are supplied to the individual theorems.
:::

:::definition "def:diagonal-quotient-fibre-homeomorph-over" (lean := "Mathoverflow1973.DiagonalQuotient.fibreHomeomorphOver") (parent := "diagonal-quotient") (uses := "def:diagonal-quotient-space")
Assume $`B \to B/G` is a quotient covering map and $`G` acts continuously on $`F`. For
each $`b \in B` there is a homeomorphism
$$`\mathrm{projection}^{-1}\{[b]\} \;\xrightarrow{\ \sim\ }\; F.`

It comes from local trivializations: over an evenly-covered patch $`U \subset B/G` around
$`[b]`, choosing the sheet through $`b` identifies $`\mathrm{projection}^{-1}(U)` with
$`U \times F` compatibly with the projection, and the fibre homeomorphism is the
restriction of that identification. The same trivializations give properness of the
projection when $`F` is compact, and transfer Hausdorffness and second countability from
$`B/G` and $`F` to the total space.
:::

:::theorem "thm:fibre-fundamental-group-hom-range-eq-ker" (lean := "Mathoverflow1973.DiagonalQuotient.fibreFundamentalGroupHom_range_eq_ker") (parent := "diagonal-quotient") (uses := "def:diagonal-quotient-space")
Assume $`B \to B/G` is a quotient covering map and $`G` acts continuously on $`F`, and fix
$`b \in B`, $`c \in F`. Then the fundamental-group sequence of the fibration is exact at
the middle term:
$$`\mathrm{range}\big(\pi_1(F, c) \to \pi_1((B \times F)/G)\big) \;=\;
\ker\big(\pi_1((B \times F)/G) \to \pi_1(B/G)\big).`
The fibre map is moreover injective, and any section of the base splits the sequence.
:::

:::proof "thm:fibre-fundamental-group-hom-range-eq-ker"
One inclusion is formal: a loop that lies in a fibre projects to a constant loop. For the
other, let $`\gamma` be a loop in $`(B \times F)/G` whose image in $`B/G` is
null-homotopic. The quotient $`B \times F \to (B \times F)/G` is itself a covering map, so
$`\gamma` lifts to a loop $`\alpha` at $`(b,c)`. Its first component is a loop in $`B`
whose image in $`B/G` is null-homotopic; since $`B \to B/G` is a covering, the induced map
on fundamental groups is injective, and the first component is null-homotopic in $`B`. A
loop in a product whose first component is trivial is homotopic to its vertical part, and
pushing that homotopy down through the quotient exhibits $`\gamma` in the image of
$`\pi_1(F)`. Injectivity of the fibre map is the same lifting argument run backwards:
two vertical loops with homotopic images downstairs have homotopic lifts, hence are
homotopic in the fibre. No fibration theory is invoked anywhere — every step is an explicit
path lift. $`\blacksquare`
:::
