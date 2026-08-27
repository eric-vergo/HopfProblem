/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — Assembling the threefold chapter.

Sections 5 and 6 of Alpöge's paper together with the endgame: the two logarithmic
fillings, the star-shaped gluing that produces the compact complex threefold X, its
simple connectivity, and the transport of its atlas onto the standard six-sphere.
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

#doc (Manual) "Assembling the threefold" =>

The threefold of {citet alpoge.s6}[] is assembled rather than found. Over the complement
of three points in the base — the compactified orbit space of the $`(3,4,\infty)`
triangle group, which is the Riemann sphere — one already has a holomorphic family of
complex $`2`-tori $`\C^2/\Lambda(\tau(z),\mu(z),\beta(z))`, its period lattice built
from three covariant functions $`\tau,\mu,\beta` on the upper half-plane $`\mathbb{H}`.
That family does not extend across the three special points. At the cusp the local
monodromy is unipotent of infinite order; at the two elliptic points it has finite
orders $`3` and $`4`. Each puncture is filled by a surgery adapted to its monodromy, and
the three fillings are then glued to the regular family along the punctured coordinate
discs.

At the cusp the filling is a Mumford-style toroidal degeneration {citep mumford72}[]
whose central fibre is a reduced normal-crossings surface $`W`; at the elliptic point of
order $`m_j \in \{3,4\}` it is a Kodaira logarithmic transform {citep kodaira64}[] of
multiplicity $`m_j`, obtained by quotienting the local torus family by the logarithmic
deck transformation $`\tilde g_j^{\log}`, which in flat coordinates is
$$`(z,x) \;\longmapsto\; (g_j z,\; A_j x + v_j/m_j).`
The twist vectors are $`v_1 = \varepsilon` and $`v_2 = -\varepsilon'`, with
$`\gamma(v_1) = 1` and $`\gamma(v_2) = -1`; the reduced central fibre of the filling is
then a bielliptic surface $`S_j` and the fibre of the completed fibration over $`p_j` is
$`m_j S_j`. Together with the untwisted regluing at the cusp these choices give the
discrete gluing data $`(\ell_0,\ell_1,\ell_2) = (0,1,-1)`, which is the entire
combinatorial content of the construction — and, as the fundamental-group computation
below shows, exactly the content that forces $`\pi_1(X) = 1`.

The formalization departs from the paper in one structural respect. Where the paper
glues a disjoint union $`\mathcal{Z} = J \sqcup N_0 \sqcup N_1 \sqcup N_2` by an
equivalence relation, the Lean development isolates a *star-shaped* gluing datum: the
three filling patches are pairwise disjoint, so every transition map factors through the
regular piece and no cocycle condition survives to be checked. The abstract theory then
delivers the total space, its atlas on the common model $`\C \times \C^2`, properness of
the projection to the base, and — since all transitions are holomorphic — the
$`\omega`-manifold structure. What remains is topology: $`X` is simply connected, its
homology agrees with that of $`S^6`, and a Whitehead argument followed by Smale's
theorem produces a homeomorphism $`X \simeq_t S^6`. The last step is cheaper than one
might expect. Transporting a charted space and a manifold structure along a bare
homeomorphism preserves the transition maps *on the nose*, so no identification of
smooth structures — no computation in $`\Theta_6` {citep kervaire.milnor63}[] — is
needed anywhere.

:::group "threefold"
The analytic data at the cusp, the period triple for the $`(3,4,\infty)` triangle group,
the three local pieces and the star-shaped gluing that assembles them into the compact
complex threefold $`X`, the proof that $`X` is simply connected, and the transport of its
holomorphic atlas onto the unit six-sphere.
:::


The cusp filling is driven by an explicit $`2 \times 2` matrix of holomorphic functions
on a disc, together with a growth bound that keeps the associated toric degeneration
under control. Everything about the cusp — the period map, the toroidal quotient, and
the gluing to the regular family — is derived from that package.

:::definition "def:cusp-family-log-base" (lean := "Mathoverflow1973.SpecialPeriods.CuspFamily.LogBase") (parent := "threefold") (uses := "def:cusp-uniformization-exponential")
For $`\varepsilon > 0`, the open set
$$`\mathrm{LogBase}\,\varepsilon \;=\; \{\, s \in \C \;:\; \|e(s)\| < \varepsilon \,\},`
where $`e` is the cusp exponential. It is the preimage of the $`\varepsilon`-disc under
$`e`, hence the $`\Z`-cover of the punctured $`\varepsilon`-disc with deck
transformations $`s \mapsto s - k`. Working over $`\mathrm{LogBase}\,\varepsilon` rather
than the punctured disc itself is what makes the period map single-valued: the
logarithmic ambiguity of the periods at the cusp becomes an honest deck action, and the
monodromy is recovered afterwards as the induced action on fibres.
:::

:::definition "def:cusp-family-data" (lean := "Mathoverflow1973.SpecialPeriods.CuspFamily.Data") (parent := "threefold") (uses := "def:cusp-family-log-base, def:toric-space-small-drift")
Cusp-degeneration data: three functions $`\mu, b, h : \C \to \C` and a radius
$`0 < r < 1` such that every entry of the correction matrix
$$`\mathrm{cuspCorrection}\,\mu\,b\,h\,(t) \;=\; \begin{pmatrix} 6\mu(t) & h(t) \\ b(t) - h(t) & \mu(t)\end{pmatrix}`
is complex-analytic on the ball $`B(0,r)`, and such that the *small-drift* bound holds:
for $`0 < \|t\| < r` the entry norm of the associated drift matrix is at most
$`-\log\|t\|/4`. The bound is what confines the degeneration to the toric model — it
forces the fibre lattice to stretch strictly more slowly than the logarithmic scale of
the base coordinate. From this data one obtains a holomorphic period map over
$`\mathrm{LogBase}\,r`, whose fibre $`2`-tori degenerate as $`t \to 0`.
:::


The period triple $`(\tau,\mu,\beta)` is the analytic heart of the construction: $`\tau`
is the uniformizing modulus, $`\mu` and $`\beta` the two further coordinates of the
period lattice, and all three must transform correctly under the two generators of the
triangle group while remaining regular at the cusp.

:::definition "def:period-functions" (lean := "Mathoverflow1973.SpecialPeriods.Construction.PeriodFunctions") (parent := "threefold") (uses := "def:beta-torsor-data, def:triangle-compactified-charted-space")
A period triple for the $`(3,4,\infty)` triangle group: a `BetaTorsor.Data` — which
carries $`\tau` and $`\mu` with their holomorphy and their covariance under the two
generators — together with a holomorphic $`\beta : \mathbb{H} \to \C` satisfying the
generator laws for $`\beta`, subject to three cusp-regularity conditions. First, $`\tau`
has the expansion
$$`\tau(z) \;=\; \frac{z}{\mathrm{width}} \;+\; h(q(z))`
eventually as $`\mathrm{Im}\,z \to \infty`, with $`h` analytic at $`0` and $`q` the cusp
parameter. Second, $`\mu` is cusp-regular. Third, $`\beta + \tau` is cusp-regular. The
third condition, rather than regularity of $`\beta` itself, is what the logarithmic
growth of $`\beta` at the cusp permits.
:::

:::theorem "thm:exists-period-functions-of-sphere" (lean := "Mathoverflow1973.SpecialPeriods.Construction.exists_periodFunctions_of_sphere") (parent := "threefold") (uses := "def:period-functions, thm:exists-covariant-tau-of-triangle-source, thm:exists-unique-solution")
*Theorem.* Let $`\pi` be a biholomorphism from the compactified triangle orbit space to
the Riemann sphere, normalized by $`\pi(\mathrm{cusp}) = \infty`, $`\pi(c_1) = 0` and
$`\pi(c_2) = 1`. Then there is a `PeriodFunctions` whose $`\tau` is precisely the modulus
$`\mathrm{tauOfSphere}\,\pi` induced by $`\pi`.

The normalization is not cosmetic: fixing the images of the cusp and the two elliptic
centres pins the uniformizing coordinate, hence pins $`\tau`, and the remaining data is
then produced in order — $`\mu` as the unique solution of its torsor equation, $`\beta`
from the $`\beta`-torsor together with the analytic $`q`-expansion at the cusp that
supplies the last two regularity conditions.
:::

Specializing $`\pi` to the fixed uniformization `triangleSphereUniformization` freezes the
construction: `specialPeriodMap` is the resulting holomorphic period map on
$`\mathbb{H}`, and `specialCuspData` the cusp datum extracted from it by shrinking the
radius until the small-drift bound holds. Every piece below is built from these two
constants, so the threefold produced is a single space rather than a family of choices —
which is what makes the closing statement a statement about *the* six-sphere.


:::definition "def:threefold-puncture" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.Puncture") (parent := "threefold") (uses := "def:elliptic-kind")
The index type of the special base points, $`\mathrm{Puncture} = \mathrm{Option}\ \mathrm{Elliptic.Kind}`:
the cusp $`p_0` is `none`, and the elliptic points $`p_1, p_2` are `some .three` and
`some .four`. Each puncture carries a preferred holomorphic chart centred at it — the
full cusp chart at $`p_0` and the compactified elliptic chart at $`p_j` — together with
the radius up to which that chart is defined. Encoding the three points as one option
type is what lets the gluing below be stated once, with the regular piece as the extra
`none` index of a second option layer.
:::

:::definition "def:threefold-base-cover" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.BaseCover") (parent := "threefold") (uses := "def:threefold-puncture, def:triangle-compactified-charted-space, thm:covering-quotient-is-manifold, thm:shimizu-leutbecher, thm:triangle-geometric-representation-injective")
A choice of radius $`\varrho_i > 0` for each puncture $`i`, smaller than that puncture's
chart radius, such that the coordinate discs $`D_i` around distinct punctures are
pairwise disjoint. This is the combinatorial cover datum of the base: the three filling
patches $`D_0, D_1, D_2` are the coordinate discs so determined, and the regular patch is
the complement of the three puncture points. Disjointness is the hypothesis that later
makes the gluing star-shaped — with it, no two filling pieces ever meet, so the only
transitions to construct are those between each filling piece and the regular family.
:::


The regular family, the toric cusp piece and the two logarithmic-transform elliptic
pieces are built independently and given atlases on the common model $`\C \times \C^2`.
Only then are they glued.

:::definition "def:special-regular-family" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.SpecialRegularFamily") (parent := "threefold") (uses := "def:period-family-regular-data, def:special-period-map, thm:special-period-map-generator")
The regular piece: the total space of the period-family quotient built from
`specialPeriodMap` over the triangle-regular locus. Concretely it is the family of
complex $`2`-tori $`\C^2/\Lambda(\tau(z),\mu(z),\beta(z))` over the complement of the
three special base points, formed as the quotient of $`\mathbb{H} \times \C^2` by the
combined action of the lattice and of the triangle group, the latter acting on the fibres
through the two generator laws $`P(g_1 z) = P(z).\mathrm{step}_1` and
$`P(g_2 z) = P(z).\mathrm{step}_2`. It is charted on $`\C \times \C^2`, Hausdorff, second
countable, an $`\omega`-manifold, and its projection to the regular patch is proper.
:::

:::definition "def:elliptic-filling-filling-space" (lean := "Mathoverflow1973.SpecialPeriods.EllipticFilling.fillingSpace") (parent := "threefold") (uses := "def:equivariant-data, def:triangle-orbit-space, thm:main-twist-admissible, thm:triangle-geometric-representation-injective")
For an equivariant holomorphic period map $`P` on $`\mathbb{H}` satisfying the two
generator step laws, and $`j \in \{3,4\}`, the filled elliptic family: the space of the
local equivariant data at $`j`, built with the twist vector $`j.\mathrm{twist}` — that is,
$`\varepsilon` for $`j = 3` and $`-\varepsilon'` for $`j = 4`. This is Kodaira's
logarithmic transform of multiplicity $`j.\mathrm{order}` over the disc: the quotient of
the local torus family by the order-$`m_j` group generated by the logarithmic deck
transformation. That the twist is admissible — $`3 \nmid \gamma(v)` when $`m_j = 3`,
$`\gamma(v)` odd when $`m_j = 4` — is exactly what makes the action free, so the quotient
map is an unramified $`m_j`-sheeted covering and the filling is a complex manifold with a
proper projection to the disc.
:::

:::definition "def:special-elliptic-piece" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.SpecialEllipticPiece") (parent := "threefold") (uses := "def:elliptic-filling-filling-space, def:special-period-map, def:threefold-base-cover, thm:special-period-map-generator")
The elliptic local piece at $`p_j`: the open subspace of the special filled elliptic
family lying over the base-cover disc $`D_j`, i.e. the points whose projection to the
disc has norm less than the chosen radius $`\varrho_j`. The multiple fibre $`m_j S_j`
sits over the centre of that disc, $`S_j` being the bielliptic quotient
$`A_0^{(j)}/\langle x \mapsto A_j x + v_j/m_j\rangle` of the central abelian surface; the
whole piece strong-deformation-retracts onto $`S_j`. Its charted structure on
$`\C \times \C^2` is inherited from the filling.
:::

:::definition "def:threefold-cusp-model-equiv" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.cuspModelEquiv") (parent := "threefold")
The continuous $`\C`-linear equivalence
$$`\C^3 \;=\; \mathrm{ToricCharts.CoordinateSpace}\ 3 \;\xrightarrow{\ \sim\ }\; \C \times \C^2,\qquad x \longmapsto (x_0, (x_1,x_2)),`
splitting off the base coordinate. It is the model change that reconciles the toric atlas
native to the cusp piece with the common model used by every other piece, and it is
reused at the very end of the development to rewrite $`\C \times \C^2` as
`EuclideanSpace ℂ (Fin 3)`. Nothing analytic happens here — the map is linear, so it
transports charted spaces and manifold structures at every regularity, $`\omega`
included.
:::

:::definition "def:star-input" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.Star.Input") (parent := "threefold") (uses := "def:threefold-gluing-data")
A star-shaped gluing datum over a base $`B` with index type $`I`: an open cover of $`B`
indexed by $`\mathrm{Option}\ I` whose filling patches (the `some` indices) are pairwise
disjoint; a piece over each patch, with a continuous base map landing in that patch; and,
for each $`i \in I`, a partial homeomorphism from piece $`i` to the distinguished
`none` piece whose source and target are the preimages of the two patches' overlap and
which commutes with the base maps. From this `toData` derives a full `ThreefoldGluing.Data`
by declaring every transition to factor through the `none` piece: the transition from
$`i` to $`j` is the composite of the overlap at $`i` with the inverse of the overlap at
$`j`. Disjointness of the filling patches makes the cocycle condition vacuous where it
would otherwise have content, so it is discharged once and for all here rather than
verified for the concrete pieces.
:::

:::definition "def:special-cusp-piece" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.SpecialCuspPiece") (parent := "threefold") (uses := "def:cusp-family-data, def:cusp-quotient-quotient-space, def:threefold-base-cover, def:threefold-cusp-model-equiv, def:triangle-sphere-uniformization, thm:exists-period-functions-of-sphere")
The cusp local piece: the toroidal quotient space of the correction matrix of
`specialCuspData` over the disc of radius $`\varrho_0`. This is the Mumford-style
degeneration of the torus family at the cusp; its central fibre is the reduced
normal-crossings surface $`W`, and away from the centre it is the family of $`2`-tori
again. It is charted natively on the toric coordinate space $`\C^3`, and re-charted onto
the common model $`\C \times \C^2` through `cuspModelEquiv`. Both atlases are kept in the
development — the native one is where the toric geometry is legible, the common one is
what the gluing needs — and the identity map between them is recorded as an
$`\omega`-diffeomorphism.
:::

:::definition "def:threefold-local-piece" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.localPiece") (parent := "threefold") (uses := "def:special-cusp-piece, def:special-elliptic-piece, def:special-regular-family")
The assignment from the index type $`\mathrm{Option}\ \mathrm{Puncture}` to spaces: the
regular torus family at the outer `none`, the toric cusp piece at the cusp index, and the
elliptic pieces of multiplicities $`3` and $`4` at the two elliptic indices. Uniformly
across the four indices the piece is nonempty, Hausdorff, second countable, charted on
$`\C \times \C^2`, an $`\omega`-manifold, and its projection to the corresponding base
patch is proper. Those six properties are exactly the input the abstract gluing theory
consumes; establishing them index by index is what the preceding definitions were for.
:::


Two things must be true for the gluing to be more than formal bookkeeping. The overlap
maps must be biholomorphisms, so that the glued atlas is holomorphic; and over each
punctured disc the filling's torus family must be the *same* family as the regular one,
not merely an isomorphic one. The second point is settled at the cusp by an identity
between period points.

:::theorem "thm:cusp-global-overlap-sphere-period-agreement" (lean := "Mathoverflow1973.SpecialPeriods.CuspGlobalOverlap.spherePeriod_agreement") (parent := "threefold") (uses := "def:cusp-family-data, def:cusp-family-log-base, thm:exists-period-functions-of-sphere")
*Theorem.* Fix a normalized uniformization $`\pi` and a radius $`r` small enough for both
the cusp datum and the cusp chart. For every $`s \in \mathrm{LogBase}\,r`, the period
point of the regular family at $`\mathrm{logBaseToRegular}(s) \in \mathbb{H}` equals the
period point of the cusp family at $`s`.

This is the analytic compatibility that makes the cusp gluing canonical: the two torus
families over the punctured disc are not merely isomorphic, they have literally the same
period lattice once the disc is passed to its logarithmic cover. The overlap
biholomorphism is then induced by the identity on fibres, and no choice enters.
:::

:::definition "def:threefold-local-overlap" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.localOverlap") (parent := "threefold") (uses := "def:a, def:diagonal-quotient-space, def:elliptic-flat-affine, def:flat-torus-affine, def:m, def:main-filling-to-tautological-biholomorph, def:punctured-cusp-cover, def:threefold-local-piece, def:triangle-torus-action, thm:cusp-global-overlap-sphere-period-agreement, thm:cusp-quotient-proper-action")
For each puncture $`i`, an $`\omega` partial diffeomorphism from the filling piece at
$`i` to the regular family, with source and target the preimages of the punctured disc
$`D_i^{\ast}` on the two sides, commuting with the projections to the base. At the cusp
it is the composite of the native-to-common model change with the toroidal comparison
map supplied by the period agreement above. At an elliptic point it is the descent of
the fibrewise translation by the logarithmic section $`\sigma_j`, which conjugates the
logarithmic deck transformation $`\tilde g_j^{\log}` into the tautological one
$`\tilde g_j^{0}` and therefore identifies the punctured filling with the restricted
regular family. These are the gluing maps of the threefold, and the fact that they are
complex-analytic in both directions is what makes the glued atlas holomorphic.
:::

:::definition "def:threefold-space" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.Space") (parent := "threefold") (uses := "def:star-input, def:threefold-local-overlap, def:threefold-local-piece, thm:cusp-quotient-is-manifold")
The threefold $`X`: the space of the gluing datum assembled from the four pieces, their
base maps and the three overlap maps, viewed as a star-shaped input and converted to a
full gluing datum. Concretely, $`X` is the quotient of the disjoint union of the regular
torus family, the toric cusp piece and the two logarithmic-transform elliptic pieces by
the identifications made over the three punctured discs. The four pieces include into it
as open subspaces whose images cover $`X`, and the preimage of each base patch is exactly
the corresponding piece.
:::

:::definition "def:threefold-charted-space" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.chartedSpace") (parent := "threefold") (uses := "def:threefold-space")
The atlas of $`X` on the model $`\C \times \C^2`, inherited from the pieces through the
gluing: a chart at a point of $`X` is the chart of whichever piece contains it,
transported along that piece's open embedding. Because the pieces already carry
$`\C \times \C^2`-atlases with holomorphic transitions among themselves, all that the
glued atlas adds is the transitions coming from the overlap maps.
:::

:::definition "def:threefold-projection" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.projection") (parent := "threefold") (uses := "def:threefold-charted-space, def:triangle-sphere-uniformization")
The projection $`f : X \to B` to the compactified triangle orbit space, given on each
piece by that piece's base map. It is a proper map, and composing it with the
uniformization $`B \cong \PP^1` gives $`\mathrm{projectionSphere} : X \to \PP^1` — the
elliptic fibration of the paper. Its fibres are the complex $`2`-tori over the regular
locus, the reduced normal-crossings surface $`W` over the cusp, and the multiple fibres
$`m_j S_j` over the two elliptic points.
:::

:::theorem "thm:threefold-space-compact" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.space_compact") (parent := "threefold") (uses := "def:threefold-charted-space, def:threefold-projection")
*Theorem.* $`X` is compact.

Properness of $`f` is checked patch by patch — each piece projects properly onto its own
base patch, and properness is local on the base — after which compactness of $`X` follows
from compactness of $`B \cong \PP^1`. The companion results record that $`X` is Hausdorff,
second countable, nonempty and connected; second countability comes from the compactness
of the base together with second countability of the four pieces.
:::

:::theorem "thm:space-is-manifold" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.space_isManifold") (parent := "threefold") (uses := "def:threefold-charted-space, def:threefold-local-overlap")
*Theorem.* $`X` is a complex-analytic manifold: with the glued atlas on
$`\C \times \C^2`, it satisfies `IsManifold 𝓘(ℂ, ℂ × ℂ²) ω`.

The smoothness index is $`\omega`, not $`\infty` and not $`1`: the transition maps are
genuinely analytic, and the stronger statement is what later gets weakened, never
strengthened.
:::

:::proof "thm:space-is-manifold"
The abstract gluing theory reduces the claim to holomorphy of every transition map of the
gluing datum. By construction the datum is star-shaped, so each transition is either the
identity, one of the three overlap maps, one of their inverses, or a composite of two of
them; all four cases are $`\omega` because each overlap is an $`\omega` partial
diffeomorphism in both directions. At the cusp that holomorphy comes from the toric
comparison map together with the linear model change; at an elliptic point it comes from
holomorphy of the logarithmic section $`\sigma_j(z) = \frac{\log s_j(z)}{2\pi i}\,\Pi(z)v_j`
on the punctured disc, whose branch ambiguity is a lattice period and therefore invisible
in the quotient. The charts of $`X` are the charts of the pieces transported along open
embeddings, so compatibility of two charts drawn from the same piece is inherited, and
compatibility of charts drawn from different pieces is exactly the transition holomorphy
just established. $`\blacksquare`
:::

:::theorem "thm:threefold-real-dimension" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.real_dimension") (parent := "threefold") (uses := "def:threefold-charted-space")
*Theorem.* $`\dim_{\R}(\C \times \C^2) = 6`.

Trivial as arithmetic, and load-bearing as bookkeeping: it is the hypothesis under which
$`X`, with its complex structure restricted along $`\R \to \C`, counts as a smooth real
six-manifold. That restriction of scalars is a general fact about the analytic groupoid —
a $`\C`-manifold on a model $`E` is an $`\R`-manifold on the same $`E` at the same
regularity — and it is the only place the argument leaves complex geometry.
:::


The twist data $`(\ell_0,\ell_1,\ell_2) = (0,1,-1)` enters $`\pi_1(X)` through two
relations satisfied by the meridians of the elliptic points. Throughout, $`\pi_1(X)` is
taken at the marked basepoint on the zero section, $`c` denotes the image of the lattice
generator $`\varepsilon`, and $`m_0, m_1` are the meridians of the order-$`3` and
order-$`4` points.

:::theorem "thm:trivial-of-oriented-elliptic-power-relations" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.PiOne.trivial_of_oriented_elliptic_power_relations") (parent := "threefold") (uses := "def:fundamental-group-van-kampen-two-open-cover, def:marked-regular-fundamental-group-equiv, def:threefold-local-overlap, def:threefold-projection, thm:main-group-trivial, thm:simply-connected-space-of-open-cover")
*Theorem.* Let $`c^{\pm}` denote $`c` or $`c^{-1}` according to an orientation flag. If
$`m_0^3 = c^{\pm}` and $`m_1^4 = (c^{\pm})^{-1}`, then every element of $`\pi_1(X)` is
trivial.

The group is generated by the image of the fibre lattice together with the two meridians;
the lattice image is central and is itself a power of $`c`, so $`\pi_1(X)` is a quotient
of the presented twist group on $`c, x, y` with $`c` central, $`xy = c^{\ell_0}`,
$`x^3 = c^{\ell_1}` and $`y^4 = c^{\ell_2}`. Such a presentation collapses when
$`|12\ell_0 - 4\ell_1 - 3\ell_2| = 1`, and the twist data $`(0,1,-1)` gives
$`12\cdot 0 - 4 + 3 = -1`. The orientation flag is carried explicitly because the sign of the
meridian classes depends on a normalization made much earlier, and the argument must not
depend on which way it went.
:::

:::theorem "thm:pi-one-meridian-first-cube" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.PiOne.meridian_first_cube") (parent := "threefold") (uses := "def:elliptic-kind")
*Theorem.* $`m_0^3 = c^{\pm}`, with the same orientation flag throughout.

This is the order-$`3` instance of the general relation: the clockwise-oriented meridian
of the elliptic point of order $`m_j`, raised to the power $`m_j`, equals the image of the
twist vector $`j.\mathrm{twist}` under the lattice homomorphism, and that image is
$`c^{\gamma(j.\mathrm{twist})}`. For $`j = 3` the twist is $`\varepsilon` with
$`\gamma(\varepsilon) = 1`, so the exponent is $`1` — the value $`\ell_1` of the discrete
gluing data.
:::

:::theorem "thm:pi-one-meridian-second-fourth" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.PiOne.meridian_second_fourth") (parent := "threefold") (uses := "def:elliptic-kind")
*Theorem.* $`m_1^4 = (c^{\pm})^{-1}`.

The order-$`4` instance of the same relation. Here the twist is $`-\varepsilon'` with
$`\gamma(-\varepsilon') = -1`, so the exponent is $`\ell_2 = -1`. Choosing
$`v_2 = +\varepsilon'` instead is equally admissible as a logarithmic transform and
yields a different threefold — the comparison space $`X'` of the paper, with twist data
$`(0,1,1)` and $`12\cdot 0 - 4 - 3 = -7`, reserved there as the contrasting case. This
sign is the whole difference between the two constructions, and it is what the
collapse of the twist group turns on.
:::

:::theorem "thm:space-simply-connected" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.space_simplyConnected") (parent := "threefold") (uses := "def:diagonal-quotient-space, def:elliptic-filling, def:main-filling-to-tautological-biholomorph, def:triangle-torus-action, thm:pi-one-meridian-first-cube, thm:pi-one-meridian-second-fourth, thm:space-is-manifold, thm:trivial-of-oriented-elliptic-power-relations")
*Theorem.* $`X` is simply connected.
:::

:::proof "thm:space-simply-connected"
Path-connectedness first: $`X` is connected, because its base is connected and its fibres
are, and it is locally path-connected as a charted space over a normed space, so it is
path-connected. Triviality of the fundamental group at the marked basepoint is then the
combination of the two meridian relations with the twist-group collapse. Producing the
relations is the long part of the development. The regular family's fundamental group is
computed from the period lattice and the two generator meridians; van Kampen against the
filling pieces {citep kumar.vankampen}[] shows that the map from the regular piece to
$`X` is surjective on $`\pi_1`, so the global group is generated by the images of those
classes. The class of a meridian encircling an elliptic point is then identified inside
the filling: the filling deformation-retracts onto its bielliptic central surface, whose
fundamental group is the crystallographic extension
$`1 \to \Lambda \to \Gamma \to \Z/m_j \to 1` with $`\tilde\sigma^{m_j} = t_{v_j}`, and
tracking a small clockwise loop through the log-gauge identification gives
$`m_j`-th power equal to the lattice element $`v_j`. Passing to $`\pi_1(X)`, where the
lattice image is $`c^{\gamma(\cdot)}`, yields $`m_0^3 = c^{\pm}` and
$`m_1^4 = (c^{\pm})^{-1}`. Since a path-connected space whose fundamental group at one
point is trivial is simply connected, the theorem follows. $`\blacksquare`
:::


With $`X` simply connected, the Hurewicz ladder against the homology of $`X` — which is
that of $`S^6` — kills $`\pi_2` through $`\pi_5` and identifies $`\pi_6(X) \cong \Z`. A
generator of $`\pi_6` is a $`6`-cube whose cubical homology class is the top class, and
factoring that cube through the sphere turns it into a map $`S^6 \to X`.

:::definition "def:sphere-homology-equivalence-homology-equiv" (lean := "Mathoverflow1973.SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyEquiv") (parent := "threefold") (uses := "def:homology-six-equiv, def:hurewicz-linear-equiv, def:hurewicz-pi2-equiv, def:hurewicz-pi3-equiv, def:hurewicz-pi4-equiv, def:hurewicz-pi5-equiv, def:top-degree-top-class, thm:homology-five-subsingleton, thm:homology-four-subsingleton, thm:homology-subsingleton-of-lt, thm:homology-three-subsingleton, thm:homology-two-subsingleton, thm:unit-sphere-homology-subsingleton")
For a basepoint $`x \in X` and every degree $`n`, a $`\Z`-linear isomorphism
$$`H_n(S^6;\Z) \;\xrightarrow{\ \sim\ }\; H_n(X;\Z)`
induced by the continuous map $`\mathrm{sphereMap}\,x : S^6 \to X` that factors the
generating $`6`-cube of $`\pi_6(X,x)`. The map is an isomorphism in every degree at once
for a structural reason: it carries the top class of $`S^6` to the top class of $`X`, and
both spaces have $`\Z` in degrees $`0` and $`6` and vanishing homology in every other
degree. This is the input the Whitehead argument turns into a homotopy equivalence
$`X \simeq_h S^6`.
:::

:::definition "def:manifold-atlas-transport-charted-space" (lean := "Mathoverflow1973.ManifoldAtlasTransport.chartedSpace") (parent := "threefold")
Transport of a charted space along a homeomorphism. Given $`h : M \simeq_t N` and a
`ChartedSpace H M`, the collection $`\{\,e \circ h^{-1} : e \in \mathrm{atlas}\,H\,M\,\}`
— each chart lifted through the open embedding $`h` — is an atlas making $`N` a charted
space over the *same* model $`H`, with the chart at $`y \in N` being the lift of the
chart at $`h^{-1}(y)`. Note that only a homeomorphism is required; no differentiable
structure on $`N` is presupposed, because there is none to presuppose.
:::

:::theorem "thm:manifold-atlas-transport-is-manifold" (lean := "Mathoverflow1973.ManifoldAtlasTransport.isManifold") (parent := "threefold") (uses := "def:manifold-atlas-transport-charted-space")
*Theorem.* If $`M` is a manifold for a model with corners $`I` at smoothness $`n`, then
so is $`N` with the transported atlas, for any $`I` and any $`n` — $`\omega` included.

The proof is a rewriting rather than an argument. Lifting two charts $`e, e'` through the
open embedding $`h` and forming their transition gives back
$`e^{-1} \circ e'` *on the nose*, so compatibility in the $`n`-smooth groupoid is
inherited verbatim from $`M`. This is the formal content of the paper's closing remark:
moving a complex structure from $`X` onto the standard sphere requires a homeomorphism
and nothing more, so no identification of smooth structures — in particular no appeal to
the group of exotic $`6`-spheres — is needed.
:::

:::definition "def:threefold-homeomorph" (lean := "Mathoverflow1973.SixSphereComplexAtlas.threefoldHomeomorph") (parent := "threefold") (uses := "def:threefold-homotopy-equiv, thm:complex-manifold-is-real-manifold, thm:homeomorphic-six-sphere-of-homotopy-six-sphere, thm:threefold-real-dimension, thm:threefold-space-compact")
A homeomorphism $`X \simeq_t S^6`, where $`S^6` is the unit sphere about the origin in
$`\R^7`. It is extracted by choice from Smale's theorem applied to $`X`: the complex
structure is restricted along $`\R \to \C` to make $`X` a smooth real manifold, whose
model has real dimension $`6`; $`X` is compact, Hausdorff and second countable; and
$`\mathrm{threefoldHomotopyEquiv}` supplies the homotopy equivalence $`X \simeq_h S^6`.
The choice is genuine — the theorem produces nonemptiness of the space of such
homeomorphisms, not a preferred one — and it is one of the points at which
`Classical.choice` enters the final result, the other being the generating $`6`-cube of
$`\pi_6(X)`.
:::

:::theorem "thm:exists-complex-analytic-atlas" (lean := "Mathoverflow1973.SixSphereComplexAtlas.exists_complex_analytic_atlas") (parent := "threefold") (uses := "def:threefold-cusp-model-equiv, def:threefold-homeomorph, thm:manifold-atlas-transport-is-manifold")
*Theorem.* There is a `ChartedSpace (EuclideanSpace ℂ (Fin 3))` structure on the unit
six-sphere making it a manifold for $`\mathcal{I}(\C, \C^3)` at smoothness $`\omega`: the
six-sphere carries a complex-analytic atlas.
:::

:::proof "thm:exists-complex-analytic-atlas"
Transport the atlas of $`X` along the homeomorphism $`X \simeq_t S^6`. The transported
charted space is over the model $`\C \times \C^2`, and by the transport theorem it is an
$`\omega`-manifold for $`\mathcal{I}(\C, \C \times \C^2)`, since the transported
transitions are the transitions of $`X` unchanged. It remains to rewrite the model. The
composite of `cuspModelEquiv` inverted with the standard identification
$`\C^3 \cong \mathrm{EuclideanSpace}\ \C\ (\mathrm{Fin}\ 3)` is a continuous
$`\C`-linear equivalence, and re-charting a manifold along such an equivalence changes
neither the transitions' regularity nor the underlying space. The result is an
$`\omega`-atlas of $`\mathrm{EuclideanSpace}\ \C\ (\mathrm{Fin}\ 3)`-charts on the sphere.
$`\blacksquare`
:::


