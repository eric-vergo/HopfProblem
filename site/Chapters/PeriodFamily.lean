/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — period family chapter.

The holomorphic family of complex 2-tori over the thrice-punctured line: the period
formalism, the triangle-group quotient carrying its complex structure, and the complete
computation of its fundamental group, its integral homology, and its boundary interface.
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

#doc (Manual) "The period family over the thrice-punctured line" =>

The threefold whose underlying space is the six-sphere is assembled from an open piece and
three fillings. The open piece is a holomorphic family $`J \to B^\circ` of compact complex
two-dimensional tori over the thrice-punctured projective line
$`B^\circ = B \setminus \{p_0, p_1, p_2\}`, and it carries almost all of the topology: the
fillings at $`p_0, p_1, p_2` are local, and what they contribute to $`\pi_1(X)` and
$`H_*(X)` is measured against $`J` through its boundary tori. $`J` is explicit at every
level: its complex structure comes from a quotient construction, its fundamental group and
its integral homology are computed in closed form, and the classes carried by its three
boundary tori are determined inside that homology.

Everything rests on three scalar holomorphic functions $`\tau, \mu, \beta` on the upper
half-plane, the period functions of {citet alpoge.s6}[] §3. They are pinned down by
functional equations under the $`(3,4,\infty)` triangle group
$`\Delta = \langle g_1, g_2 \mid g_1^3 = g_2^4 = 1\rangle \cong \Z/3 * \Z/4`, which
uniformises the orbifold $`(\PP^1; 3, 4, \infty)`, and they assemble into a $`2\times 4`
period matrix whose columns span a rank-four lattice in $`\C^2`. No Hodge theory is
available and none is used: the invariant Hermitian form on the Hodge filtration has
signature $`(1,1)` for every choice of the additive constant in $`\beta`, so the fibres of
$`J` carry no monodromy-compatible polarisation, which is the structural reason the
completed threefold can fail to be Kähler.

The formal development mirrors this austerity. There is no algebraic geometry in the
construction of $`J`: the family is the quotient of $`B \times \R^4/\Z^4` by a diagonal
action of the triangle group — geometric on the base, and on the torus factor through the
integral dual representation $`g \mapsto A_g` — and its complex structure arrives by
transporting charts along that quotient covering map, with the fibrewise complex structure
supplied by the period matrix alone. The homology is computed against a from-scratch
singular theory with its own Mayer–Vietoris machinery, since none is available upstream.
One artifact of the formalization is visible throughout: the identification of the base
quotient with the twice-punctured plane is only determined up to orientation, so every
meridian, path and difference map is defined by a case split on the sign of the
normalisation, and lemmas about them come in upper and lower pairs.

:::group "period-family"
The period formalism — admissible triples $`(\tau,\mu,\beta)`, the lattices they span, and
holomorphic families of them — together with the triangle-group datum that turns such a
family into a complex threefold fibred by tori.
:::

The period functions enter as a plain triple of complex numbers subject to an open
nondegeneracy condition. The triangle group never appears abstractly at this level: its two
generators act by explicit fractional-linear substitutions on $`(\tau,\mu,\beta)`, of orders
three and four, and the whole construction turns on the fact that these substitutions
intertwine the period matrix with the integral matrices $`T_1, T_2` of the monodromy
representation.

:::definition "def:period-point" (lean := "Mathoverflow1973.PeriodPoint") (parent := "period-family") (uses := "def:t")
A *period point* is a triple $`(\tau, \mu, \beta) \in \C^3`. Its *discriminant* is
$`D = \operatorname{Im}\beta - 6(\operatorname{Im}\mu)^2/\operatorname{Im}\tau`, and it is
*admissible* when $`\operatorname{Im}\tau > 0` and $`D < 0`. Its period matrix is

$$`\Pi = \begin{pmatrix} 6\mu & \tau & 1 & 0 \\ \beta & \mu & 0 & 1\end{pmatrix},`

a $`\C`-linear map $`\Z^4 \otimes \C \to \C^2` whose four columns are indexed by the
distinguished basis of the lattice $`\Lambda`. Realified as a $`4\times4` matrix over
$`\R` in the real and imaginary coordinates of $`\C^2`, its determinant is
$`\operatorname{Im}\tau \cdot D`, hence strictly negative on the admissible locus. The generator substitutions

$$`\mathrm{step}_1(\tau,\mu,\beta) = \Big(\tfrac{\tau-1}{\tau},\ \tfrac{1-\mu}{\tau},\ \beta + 2 - \tfrac{6(1-\mu)^2}{\tau}\Big), \qquad \mathrm{step}_2(\tau,\mu,\beta) = \Big(\tfrac{-1}{\tau},\ 1 + \tfrac{\mu}{\tau},\ \beta - 3 - \tfrac{6\mu^2}{\tau}\Big)`

have orders three and four and satisfy
$`\Pi(\mathrm{step}_j\, p) = R_j(p)\,\Pi(p)\,T_j^{\mathsf T}` for $`\tau \neq 0`, with
$`R_1 = \begin{pmatrix}-1/\tau & 0\\ (1-\mu)/\tau & 1\end{pmatrix}` and
$`R_2 = \begin{pmatrix}1/\tau & 0\\ -\mu/\tau & 1\end{pmatrix}`. Admissibility and the
discriminant are invariant under both.
:::

:::definition "def:period-domain" (lean := "Mathoverflow1973.PeriodDomain") (parent := "period-family") (uses := "def:period-point")
The *period domain* is the subtype of admissible period points. For $`p` in it, the
invertibility of the realified period matrix makes the four columns of $`\Pi` an
$`\R`-basis of $`\C^2`, so their $`\Z`-span $`\Lambda_p = \Pi\Lambda \subset \C^2` is a
genuine lattice: discrete, closed, and cocompact, recorded as an `IsZLattice` instance. The
quotient $`\C^2/\Lambda_p` is therefore a compact, path-connected complex torus of
dimension two — the fibre attached to $`p`. Negativity of the discriminant is exactly the
condition that makes this work, and it is the only place the condition $`(\beta 3)` of
{citet alpoge.s6}[] is used.
:::

:::definition "def:holomorphic-period-map" (lean := "Mathoverflow1973.HolomorphicPeriodMap") (parent := "period-family") (uses := "def:period-domain")
A *holomorphic period map* over a base $`B` charted on a complex normed space $`V` is a map
$`b \mapsto p(b)` into the period domain whose three components $`\tau, \mu, \beta` are
analytic as maps of complex manifolds — smoothness index $`\omega` for the model with
corners $`\mathcal{I}(\C,V)`, which over $`\C` is holomorphy. This single datum generates
the entire twisted torus family: the fixed topological fibre is the standard flat torus
$`\R^4/\Z^4`, the total space is $`B \times \R^4/\Z^4` with a complex chart at each point
obtained by pushing the fibre coordinate through the real isomorphism
$`\R^4 \xrightarrow{\ \Pi\ } \C^2` attached to $`p(b)`, and the projection to $`B` is proper
and holomorphic with holomorphic fibre inclusions. The complex structure of each fibre is
read off the period matrix and from nothing else.
:::

The datum that makes such a family into the family of {citet alpoge.s6}[] is the
equivariance. It is imposed only on the two generators, where it is a statement about
explicit fractional-linear substitutions; that it propagates to the whole group is a
consequence, and the resulting cocycle is what allows the diagonal action to be holomorphic
on the total space.

:::definition "def:period-family-data" (lean := "Mathoverflow1973.PeriodFamily.Data") (parent := "period-family") (uses := "def:holomorphic-period-map, def:special-periods-triangle-group")
A *period family datum* over a base $`B` charted on $`V` and carrying an action of the
triangle group consists of a holomorphic period map $`P` on $`B`, holomorphy of every
translation $`b \mapsto g \cdot b`, and the two covariance laws
$`P(g_1 \cdot b) = \mathrm{step}_1\,P(b)` and $`P(g_2 \cdot b) = \mathrm{step}_2\,P(b)`.
Nothing further is assumed — in particular the action need not be free, and the base is not
required to be a quotient of the half-plane. From a datum $`D` one builds the total space
$`B \times \R^4/\Z^4`, the diagonal action of the triangle group (geometric on $`B`, through
the integral dual representation on the torus), the orbit quotient $`D.\mathrm{Space}`, and
the projection of that quotient to the base orbit space.
:::

:::theorem "thm:data-matrix-covariance" (lean := "Mathoverflow1973.PeriodFamily.Data.matrix_covariance") (parent := "period-family") (uses := "def:period-family-data")
The two generator covariances propagate to the whole triangle group as a cocycle law: for
every $`g` and every $`b`,

$$`\Pi\big(P(g\cdot b)\big)\, D(g) \;=\; R(g,b)\, \Pi\big(P(b)\big),`

where $`D(g)` is the complexification of the integral dual representation of $`g` and
$`R(g,b)`, the *right block*, is the $`2\times2` submatrix formed by the last two columns of
the left-hand side. Equivalently $`\Pi(g\cdot b) = R(g,b)\Pi(b)M_g` in the notation of
{citet alpoge.s6}[] Proposition 3.16. The right block is the cocycle by which monodromy acts
on the fibres: under the period trivialisation, transport along $`g` is multiplication by
$`R(g,b)`, matching the action of $`D(g)` on the lattice.
:::

:::theorem "thm:data-is-manifold-3" (lean := "Mathoverflow1973.PeriodFamily.Data.isManifold") (parent := "period-family") (uses := "def:period-family-data, thm:covering-quotient-is-manifold")
Let $`D` be a period family datum whose base quotient $`B \to B/\Delta` is a quotient
covering map, and let $`B` be an analytic complex manifold. Then the orbit quotient
$`J = (B \times \R^4/\Z^4)/\Delta` is an analytic complex manifold modelled on
$`V \times \C^2` — for the regular family, on $`\C \times \C^2`, so a complex threefold. The
statement is conditional on the covering hypothesis rather than on freeness of the action,
which is the form in which the regular locus supplies it. Along with the manifold structure
come the facts that the quotient map is a local biholomorphism, that the projection to the
base is proper, and that each fibre is homeomorphic to the polarisation-free complex torus
$`\C^2/\Lambda_{P(b)}`.
:::

:::proof "thm:data-is-manifold-3"
The total space $`B\times\R^4/\Z^4` is a complex manifold: charts are products of a chart of
$`B` with the fibre coordinate pushed through the period isomorphism, and analyticity of the
transition maps is analyticity of $`\tau,\mu,\beta`. The diagonal action is holomorphic
because its base component is holomorphic by hypothesis and its fibre component is, in
period coordinates, multiplication by the right block $`R(g,b)`, which depends
holomorphically on $`b` by the cocycle law. When the base quotient is a quotient covering
map, so is the quotient map of the total space, since the torus factor is acted on through
a discrete group of homeomorphisms. The generic transport principle for covering quotients
then carries the charted-space structure and the manifold structure across, the quotient
map becoming a local biholomorphism. $`\blacksquare`
:::

:::definition "def:period-family-regular-data" (lean := "Mathoverflow1973.PeriodFamily.regularData") (parent := "period-family") (uses := "def:period-family-data, thm:triangle-geometric-action-properly-discontinuous")
Any holomorphic period map $`P` on the upper half-plane satisfying the two generator
covariances restricts to a period family datum on the *regular locus* — the points of the
half-plane whose triangle-group orbit is free, that is, the complement of the orbits of the
two elliptic fixed points. The action there is free and properly discontinuous, and its
quotient map is a quotient covering map, so the previous theorem applies: the resulting
space is a complex threefold. Its base orbit space is the thrice-punctured line
$`B^\circ`, identified with $`\C \setminus \{0,1\}` through the Riemann-mapping
uniformisation, and the threefold is the family $`J` of $`2`-tori over it. Substituting the
actual period map of the construction yields the canonical instance.
:::

:::group "period-family-topology"
The topology of $`J`: the marked presentation
$`\pi_1(J) \cong \Z^4 \rtimes F_2` of its fundamental group, the Wang-type short exact
sequence computing $`H_*(J;\Z)`, and the boundary compatibility statements that hand the
result to the three fillings.
:::

The base $`B^\circ` is homotopy equivalent to a wedge of two circles and the family is
locally trivial, so both $`\pi_1(J)` and $`H_*(J)` are determined by the fibre together with
the two monodromy operators. Making that precise requires marking the fibre, marking the
base, and choosing a cover. The fibre is marked by the lattice; the base by two explicit
meridians; the cover by two slit planes, whose intersection has three components — the
bookkeeping that this forces is the bulk of the formal work.

:::definition "def:singular-h1-equiv" (lean := "Mathoverflow1973.PeriodFamily.FlatTorus.singularH1Equiv") (parent := "period-family-topology") (uses := "def:lattice, def:singular-h1-equiv-of-pi1")
$`H_1(\R^4/\Z^4;\Z) \cong \Lambda = \Z^4`, the isomorphism sending the homology class of the
straight-line loop of a lattice vector $`c` to $`c` itself. It is obtained by composing the
computation $`\pi_1(\R^4/\Z^4, 0) \cong \Z^4` — by lifting loops to the universal cover —
with the first Hurewicz isomorphism, both developed from scratch against the site's own
singular theory. A triangle-group element $`g` acts on $`H_1` by the integral matrix
$`A_g` of the dual representation; the corresponding statements in degrees two and three
identify $`H_2 \cong \Lambda^2\Z^4 \cong \Z^6` and $`H_3 \cong \Lambda^3\Z^4 \cong \Z^4`
with the group acting by exterior powers.
:::

:::definition "def:compatible-regular-meridian-class" (lean := "Mathoverflow1973.PeriodFamily.Meridians.compatibleRegularMeridianClass") (parent := "period-family-topology") (uses := "def:triangle-signed-half-plane-map, def:twice-punctured-fundamental-group-free-equiv")
The two marked meridians of the base, as elements of $`\pi_1(B^\circ)` at the basepoint
$`1/2`. Each is the projection of an explicit path in the regular locus running from a fixed
lift of the basepoint to its translate by the inverse of the corresponding generator; its
deck monodromy is therefore $`g_1^{-1}`, respectively $`g_2^{-1}`, and the two classes
freely generate $`\pi_1(B^\circ) \cong F_2`. The definition is genuinely two-sided: the
identification of the base quotient with the plane is supplied by a Riemann map whose
orientation is only known through the sign of a normalisation constant, so the semicircular
paths around $`0` and $`1` are chosen by a case split on that sign, and each downstream
statement about them carries the same split.
:::

:::definition "def:fundamental-group-free-semidirect-equiv" (lean := "Mathoverflow1973.PeriodFamily.Data.fundamentalGroupFreeSemidirectEquiv") (parent := "period-family-topology") (uses := "def:period-family-data, def:lattice")
For any period family datum with covering base quotient, any basepoint, and any marking
$`\pi_1(\mathrm{base}) \cong F_2` of the base, the fundamental group of the total space
splits: $`\pi_1(J) \cong \Z^4 \rtimes_\varphi F_2`, the lattice included as the fibre loops
and the free group by the zero section. The splitting is not an assumption but a
construction — the fibration $`J \to B^\circ` has a holomorphic zero section, so the
homotopy exact sequence splits, and the free group is precisely the section's image. The
twisting $`\varphi` is the composite of the marking with the action of the deck
transformations on the lattice.
:::

:::definition "def:marked-regular-fundamental-group-equiv" (lean := "Mathoverflow1973.PeriodFamily.markedRegularFundamentalGroupEquiv") (parent := "period-family-topology") (uses := "def:lattice, def:period-family-regular-data, def:t, def:triangle-compactified-charted-space, def:triangle-signed-half-plane-map, def:twice-punctured-fundamental-group-free-equiv, def:fundamental-group-free-semidirect-equiv, def:compatible-regular-meridian-class")
Feeding the meridian marking into the splitting gives the presentation of
{citet alpoge.s6}[] in normalised form:
$`\pi_1(J) \cong \Z^4 \rtimes_\varphi F_2`, where the two free generators are the marked
meridians and act on the lattice by the integral matrices $`A_1` and $`A_2`. The
reparametrisation step is what makes the statement usable: the twisting produced by the
general construction is rewritten so that the first free generator acts by $`A_1` and the
second by $`A_2`, on the nose, independently of the orientation branch. Companion simp
lemmas locate the lattice generators and the two meridian sections inside the semidirect
product, and an extensionality principle states that a homomorphism out of
$`\pi_1(J)` is determined by its values on them. This presentation is the input to the van
Kampen computation of $`\pi_1(X) = 1` {citep kumar.vankampen}[].
:::

The homology of $`J` is computed by covering the base with two slit planes. Each is
contractible and its preimage is trivialised by a section lift, so it is homotopy equivalent
to the fibre; their intersection has three components, each again pulling back to a copy of
the fibre. Mayer–Vietoris then reduces everything to the difference of the two monodromy
operators, and the sequence degenerates into a Wang-type short exact sequence
{citep hatcher02}[].

:::definition "def:source-difference" (lean := "Mathoverflow1973.PeriodFamily.Homology.sourceDifference") (parent := "period-family-topology") (uses := "def:homeomorph-homology-equiv, def:lattice, def:special-periods-triangle-group, def:t")
The difference operator of the family in degree $`n`,

$$`\delta_n : H_n(T^4)^2 \to H_n(T^4), \qquad \delta_n(x,y) = \big((A_1)_* - 1\big)x + \big((A_2)_* - 1\big)y,`

where $`(A_j)_*` is the automorphism of $`H_n(\R^4/\Z^4;\Z)` induced by the torus
homeomorphism of the $`j`-th generator. This is the *normalised* form: the Mayer–Vietoris
difference map of the slit-plane cover is defined with the transition operators of the
overlap strips, and a separate coordinate change conjugates it to $`\delta_n`, absorbing
both the three-component bookkeeping of the intersection and the orientation branch. In
degree one $`(A_j)_*` is the matrix $`A_j` itself, in degree two its exterior square on
$`\Z^6`, in degree three its exterior cube on $`\Z^4`, and in degree four the identity.
:::

:::definition "def:source-kernel-projection" (lean := "Mathoverflow1973.PeriodFamily.Homology.sourceKernelProjection") (parent := "period-family-topology") (uses := "def:diagonal-quotient-space, def:period-family-data, def:source-difference, def:triangle-orbit-space, def:triangle-signed-half-plane-map, def:triangle-torus-action, thm:exact-at-intersection")
The connecting map of the family's Wang-type sequence: a surjection
$`H_{n+1}(J) \to \ker \delta_n`. It is the Mayer–Vietoris boundary of the slit-plane cover,
landing in the kernel because a class in the image of the boundary is annihilated by the
difference of the two inclusions, and transported to the normalised coordinates by the same
conjugation that defines $`\delta_n`. Surjectivity comes from exactness at the intersection
term of the Mayer–Vietoris sequence together with the identification of the preimages of the
three overlap components. Every boundary computation of the three fillings is ultimately a
computation of the image of a boundary class under this map.
:::

:::theorem "thm:source-coinvariant-inclusion-kernel-projection-exact" (lean := "Mathoverflow1973.PeriodFamily.Homology.sourceCoinvariantInclusion_kernelProjection_exact") (parent := "period-family-topology") (uses := "def:source-kernel-projection, thm:exact-at-ambient, thm:singular-mayer-vietoris-exact-at-pair")
For every regular period family and every $`n`, the sequence

$$`0 \longrightarrow \operatorname{coker}\delta_{n+1} \longrightarrow H_{n+1}(J;\Z) \longrightarrow \ker \delta_n \longrightarrow 0`

is exact: the coinvariant inclusion is injective, the kernel projection is surjective, and
the image of the first is the kernel of the second. The coinvariant inclusion sends the
class of $`a \in H_{n+1}(T^4)` to the image of $`a` under a fibre inclusion, which is
well defined on $`\operatorname{coker}\delta_{n+1}` precisely because the difference operator
measures the failure of a fibre class to be monodromy-invariant. The homology of the family
is therefore an extension of the monodromy-invariants in degree $`n` by the coinvariants in
degree $`n+1`.
:::

:::proof "thm:source-coinvariant-inclusion-kernel-projection-exact"
Cover $`B^\circ` by two slit planes, each contractible, each with contractible intersection
components — three of them. Monodromy-controlled section lifts trivialise the family over
each piece, so the preimage of a slit plane is homotopy equivalent to the fibre $`T^4` and
the preimage of the intersection to three copies of it. In the resulting Mayer–Vietoris
sequence the difference of the two inclusion maps is, after the orientation normalisation
and the placement of each intersection component into its meridian slot, exactly
$`\delta_n` on $`H_n(T^4)^2`; the two outer terms are $`H_n(T^4)^2` and $`H_n(T^4)^3`
collapsed accordingly. Exactness at the pair term yields injectivity of the coinvariant
inclusion and identifies its image; exactness at the ambient term yields surjectivity of the
connecting map onto $`\ker\delta_n` and exactness in the middle. $`\blacksquare`
:::

:::theorem "thm:family-fibre-inclusion-kernel" (lean := "Mathoverflow1973.PeriodFamily.Homology.familyFibreInclusion_kernel") (parent := "period-family-topology") (uses := "def:source-difference, def:period-family-data")
The kernel of the map $`H_n(T^4;\Z) \to H_n(J;\Z)` induced by a fibre inclusion is exactly
the image of $`\delta_n`. Fibre homology therefore injects into the homology of the family
precisely modulo monodromy coboundaries, and the coinvariant inclusion of the exact sequence
above is the induced injection on the quotient. This is the statement that determines which
fibre classes survive in the family, and it is used in both directions: to produce classes
in $`H_*(J)` from fibre classes, and to prove that a given class dies.
:::

:::definition "def:kernel-two-equiv" (lean := "Mathoverflow1973.PeriodFamily.HomologyDifference.kernelTwoEquiv") (parent := "period-family-topology") (uses := "def:source-difference")
$`\ker \delta_2 \cong \Z^7`. With the fibre homology in coordinates, $`\delta_2` becomes the
integer map $`(x,y) \mapsto (\Lambda^2A_1 - 1)x + (\Lambda^2A_2 - 1)y` on $`\Z^6`, and the
kernel and cokernel of each $`\delta_n` are computed as explicit free modules by integer
linear algebra: $`\ker\delta_0 \cong \Z^2`, $`\ker\delta_1 \cong \Z^5`,
$`\operatorname{coker}\delta_1 \cong \Z`, $`\ker\delta_2 \cong \Z^7`,
$`\operatorname{coker}\delta_2 \cong \Z` through the functional $`a \mapsto 6a_2 + a_3`,
$`\ker\delta_3 \cong \Z^5`, $`\operatorname{coker}\delta_3 \cong \Z`. The transport from the
homological difference operator to the matrix one is a general conjugation principle for
kernels and cokernels of commuting squares, which keeps the linear algebra separate from the
topology.
:::

:::definition "def:homology-family-betti" (lean := "Mathoverflow1973.PeriodFamily.Homology.familyBetti") (parent := "period-family-topology")
The Betti numbers of the family, $`b = (1, 3, 6, 8, 6, 2, 0, 0, \dots)`, defined by cases as
a function $`\mathbb{N} \to \mathbb{N}` and vanishing in degrees above five. The total rank is $`26`, and the
Euler characteristic $`1 - 3 + 6 - 8 + 6 - 2 = 0`, as it must be for a space fibred by tori.
:::

:::definition "def:family-homology-equiv" (lean := "Mathoverflow1973.PeriodFamily.Homology.familyHomologyEquiv") (parent := "period-family-topology") (uses := "def:flat-torus-circle-homeomorph, def:homology-family-betti, def:product-torus-homology-equiv, thm:source-coinvariant-inclusion-kernel-projection-exact, def:kernel-two-equiv")
For every regular period family and every $`n`, $`H_n(J;\Z) \cong \Z^{b_n}` with
$`b = (1,3,6,8,6,2,0,\dots)`: the complete integral homology of the open part of the
threefold, free in every degree. Each degree is assembled from the short exact sequence,
whose two ends are the explicitly computed cokernel of $`\delta_n` and kernel of
$`\delta_{n-1}`; both are free, so the extension splits and the ranks add. Freeness,
finiteness and the rank statement $`\operatorname{rank} H_n(J) = b_n` follow as corollaries,
and the homology vanishes in degrees above five — as it must, $`J` being an open
$`6`-manifold.
:::

What the fillings need is not the homology of $`J` in the abstract but the position of the
three boundary tori inside it. Near each puncture the family over a small circle is a
mapping torus of the corresponding monodromy: the unipotent cusp matrix $`M_0` at $`p_0`, and
finite-order affine maps of orders three and four at $`p_1` and $`p_2`. Each carries a Wang
boundary map, and the content of the interface is the comparison of that map with the
family's connecting map.

:::definition "def:boundary-cap-kernel-equiv" (lean := "Mathoverflow1973.PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv") (parent := "period-family-topology") (uses := "def:circle-product-homology-equiv, def:cross-product-homology, def:elliptic-surface, def:homeomorph-homology-equiv, def:piece-mapping-torus-homotopy-equiv, def:threefold-projection, def:torus-matrix-map")
For each elliptic kind $`j \in \{3,4\}` and each $`n`, the kernel of the filling map
$`H_{n+1}(\partial_j) \to H_{n+1}(\text{filling}_j)` on the boundary of the multiple-fibre
neighbourhood is isomorphic to $`H_n` of the central bielliptic surface of the log
transform. The boundary is homeomorphic to the product of the positive boundary circle with that
surface, so its homology splits by the Künneth formula into a summand mapping isomorphically onto
the filling and a summand crossed with the circle; the second summand is the kernel, and the
isomorphism above is inverse to crossing with the circle class. This is what converts a homology
class of the elliptic boundary that dies in the filling into a class of the surface, where it can
be evaluated.
:::

:::definition "def:unit-cap-section-class" (lean := "Mathoverflow1973.PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass") (parent := "period-family-topology") (uses := "def:boundary-cap-kernel-equiv, def:elliptic-surface")
A distinguished class in $`H_4` of the elliptic boundary: the image, under the section of the
cap product decomposition, of the fundamental class of the central surface. Its coordinates in the
splitting are $`(1,0)`, so it generates the summand carried isomorphically onto $`H_4` of the
filling, and its Wang boundary in $`H_3(T^4) \cong \Z^4` is $`-e_3` — the negative of the fourth
basis vector, the coordinate that the monodromy fixes. Having a named class with both of these
values computed is what makes the degree-three elimination argument quantitative rather than
existential.
:::

:::theorem "thm:elliptic-boundary-source-kernel-projection" (lean := "Mathoverflow1973.PeriodFamily.Boundary.ellipticBoundary_sourceKernelProjection") (parent := "period-family-topology") (uses := "def:main-filling-to-tautological-biholomorph, def:mapping-torus-homology-wang-boundary, def:piece-mapping-torus-homotopy-equiv, def:source-kernel-projection, def:threefold-projection, thm:intersection-to-v-twisted-fold")
Let $`j \in \{3,4\}` and let $`a \in H_{n+1}` of the mapping torus of the order-$`j` affine
monodromy, with Wang boundary $`w \in H_n(T^4)`. Then the image of $`a` in $`H_{n+1}(J)`
projects under the family's connecting map to $`(w, 0)` when $`j = 3` and to $`(0, w)` when
$`j = 4`. Each multiple fibre therefore feeds exactly one meridian coordinate of
$`\ker\delta_n`, the one belonging to the elliptic point it lies over — and it feeds the
Wang boundary of the class unchanged, with no correction and no sign.
:::

:::proof "thm:elliptic-boundary-source-kernel-projection"
The boundary of the multiple-fibre neighbourhood sits over a small circle around $`p_j`,
which lies inside one of the two slit planes and crosses exactly one of the three
intersection strips. Comparing the mapping-torus cover with the slit-plane cover identifies
the two connecting maps: the upper and lower columns of the mapping torus map to the two
inclusions of the strip, so the Mayer–Vietoris boundary of the family agrees with the
mapping-torus Wang boundary on the nose. Placing the result into the correct meridian slot is
the content of the attaching-meridian index, which records that the order-three point sits on
the first meridian and the order-four point on the second. For $`j = 4` one extra step is
needed: the raw computation produces $`(g_2^{-1})_* w`, and the boundary class is fixed by
that operator, so the two agree. $`\blacksquare`
:::

:::theorem "thm:boundary-source-kernel-projection" (lean := "Mathoverflow1973.PeriodFamily.Boundary.Cusp.boundary_sourceKernelProjection") (parent := "period-family-topology") (uses := "def:m, def:main-filling-to-tautological-biholomorph, def:mapping-torus-homology-wang-boundary, def:piece-mapping-torus-homotopy-equiv, def:punctured-cusp-cover, def:source-kernel-projection, def:threefold-projection, thm:intersection-to-v-twisted-fold")
Let $`a \in H_{n+1}` of the mapping torus of the cusp monodromy $`M_0`, with Wang boundary
$`w`. Then the image of $`a` in $`H_{n+1}(J)` projects under the family's connecting map to

$$`\big({-}(g_1^{-1})_* w,\ -w\big) \in \ker\delta_n.`

Unlike the elliptic points, the cusp contributes to *both* meridian coordinates, and with a
sign. This is forced by the relation $`g_1g_2g_0 = 1`: the meridian of $`p_0` is the inverse
of the product of the other two, so a class supported near the cusp is seen by both slits.
:::

:::proof "thm:boundary-source-kernel-projection"
The cusp collar is parametrised in the reciprocal coordinate, in which the distinguished
neighbourhood is a half-plane and the family over it is the mapping torus of $`M_0`. The
loop around $`p_0` crosses both slits, so the boundary class contributes to two of the three
intersection strips rather than one, and the two contributions must be computed separately.
A refined quarter-column technique splits each contribution into the part carried by the
upper column of the mapping-torus cover and the part carried by the lower, and evaluates each
against the corresponding slit inclusion. Rewriting the cusp generator as the inverse word in
the two elliptic generators converts the second contribution into $`-w` and the first into
$`-(g_1^{-1})_*w`. The pair does lie in $`\ker\delta_n`: the Wang boundary of a mapping-torus
class is invariant under its monodromy, so $`(M_0)_*w = w`, and $`g_1g_2 = g_0^{-1}` turns
that invariance into $`(g_1^{-1})_*w = (g_2)_*w`, which is exactly the vanishing of
$`\delta_n(-(g_1^{-1})_*w,\, -w)`. $`\blacksquare`
:::

:::theorem "thm:reference-classes-regular" (lean := "Mathoverflow1973.PeriodFamily.Boundary.ThirdRelation.referenceClasses_regular") (parent := "period-family-topology") (uses := "def:boundary-cap-kernel-equiv, def:central-singular-homology-equiv, def:circle-homology-one-equiv, def:native-cap-kernel, def:singular-h1-equiv, def:surface-mapping-torus-homeomorph, thm:boundary-source-kernel-projection, thm:boundary-to-filling-neg, thm:elliptic-boundary-source-kernel-projection, thm:exists-actual-specialization-homology, thm:exists-controlled-retraction-all-levels, thm:source-coinvariant-inclusion-kernel-projection-exact, thm:wang-exact-at-fibre")
The third relation: the degree-three reference classes of the three boundary pieces are sent
by the cap-kernel regular map to the third fibre cyclic class evaluated at $`1`. Equivalently
the reference coefficient in degree three equals $`1`, hence is a unit — which is exactly
what forces $`H_3(X;\Z) = 0`. The three relations among the reference classes, of which this
is the last and the only one not visible from the Wang boundaries alone, are what close the
Mayer–Vietoris assembly of the threefold's homology.
:::

:::proof "thm:reference-classes-regular"
Fibrewise negation $`x \mapsto -x` is well defined on $`J` because the monodromy acts by
integral matrices, which commute with it, and it acts on the fibre homology in degree $`k` by
$`(-1)^k`. On the cusp piece it is compatible with the filling — the boundary-to-filling map
intertwines negation with the corresponding involution of the toric model — so the degree
three cusp reference class is fixed by the induced map on $`H_3(J)`. Being fixed by an
involution that acts by $`-1` on the odd fibre classes pins the class down to the part
coming from the base, and the cusp Wang computation identifies that part. The remaining
input is the central homology of the cusp: controlled retractions at all levels, together
with the actual specialisation of the central fibre, evaluate the cap-kernel regular map on
the reference classes, and the value is the third fibre cyclic class at $`1`.
$`\blacksquare`
:::

Taken together these results deliver the open part of the threefold as a fully computed
object: a complex manifold of dimension three with $`\pi_1 = \Z^4 \rtimes F_2` presented on
named generators, integral homology free of ranks $`(1,3,6,8,6,2)`, and three boundary tori
whose classes are known in the family's connecting map. The fillings supply the rest, and
what they must supply is now a finite list of comparisons rather than an open-ended
geometric problem.
