/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — homology of the threefold chapter.

The star Mayer–Vietoris sequence of the two-set cover of the threefold by its regular
part and its three fillings, and the degree-by-degree computation it drives: the middle
homology vanishes and the top group is infinite cyclic.
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

#doc (Manual) "The homology of the threefold" =>

Recognizing the compact complex threefold $`X` as the six-sphere consumes exactly two
topological facts: $`\pi_1(X) = 1`, and $`H_*(X;\Z) \cong H_*(S^6;\Z)`. The first is
settled by van Kampen together with a presented-group computation whose entire arithmetic
content is that a certain cyclic group has order one. The second is the subject here.
What must be proved is that $`H_n(X;\Z) = 0` for $`1 \le n \le 5` and for $`n > 6`, and
that $`H_6(X;\Z) \cong \Z` — that is, $`X` is an integral homology six-sphere.

The geometry that organizes the computation is the elliptic fibration $`f : X \to B`
over the projective line. Away from three points $`p_0, p_1, p_2` the fibres are real
four-tori, and $`X` is assembled from four patches: the regular part $`J`, a torus bundle
over the thrice-punctured base, and three fillings — a neighbourhood of the cusp fibre
over $`p_0`, and neighbourhoods of the two multiple fibres over $`p_1` and $`p_2`, of
multiplicities $`3` and $`4` {citep kodaira64}[]. In the formalization the punctures are
indexed by `Mathoverflow1973.SpecialPeriods.Threefold.Puncture`, which is
$`\mathrm{Option}` of the two elliptic kinds, so that `none` names the cusp and
`some .three`, `some .four` the two multiple fibres. The four patches are regrouped into
a *two-set* cover: $`U` is the regular patch and $`V` the union of the three fillings.
Since the fillings are pairwise disjoint, $`U \cap V` is the disjoint union of three
overlaps, each of them homotopy equivalent to the mapping torus of the monodromy acting on
the four-torus fibre — $`M_0` at the cusp, $`A_1` and $`A_2` at the elliptic points. The
Mayer–Vietoris sequence of this cover is what the development calls the *star sequence*,
and every group below is extracted from it.

The paper computes $`H_*(X;\Z)` twice by logically independent routes: once from an
explicit collapse of the general fibre onto the cusp fibre followed by Mayer–Vietoris
(Theorem 7.22), and once from the Leray spectral sequence of $`f` (Corollary 7.29)
{citep alpoge.s6}[]. Both isolate the same integer $`p = 12\ell_0 - 4\ell_1 - 3\ell_2`,
with $`H_1 \cong \cdots \cong H_4 \cong \Z/p`, and both give $`p = -1` for the gluing data
$`(\ell_0,\ell_1,\ell_2) = (0,1,-1)` of this threefold. The formalization follows neither
route verbatim. The star sequence replaces both, and degrees $`3`, $`4` and $`5` are
reached directly from it rather than through the Poincaré-duality-and-universal-coefficients
shortcut that Theorem 7.22 takes: each middle degree is killed by explicit integer linear
algebra on the Wang boundary maps of the three overlaps. The arithmetic that the paper
packages as $`|p| = 1` reappears in two concrete places: in degree $`2` as the Bézout
identity $`1 = 2 + 2 - 3` applied to a cyclic generator, and in degrees $`3` and $`4` as a
single integer coefficient that turns out to equal $`1`.

One further constraint shapes everything. There is no singular homology theory in
mathlib at this scale, so the development carries its own, built from the singular chain
complex in `ModuleCat ℤ` {citep hatcher02}[]. Consequences that would ordinarily be quoted
— additivity over disjoint unions, the Mayer–Vietoris sequence, the Wang sequence of a
mapping torus, homotopy invariance — are proved in the file, and the first of them is the
entry point below.

:::group "homology-x"
The apparatus: finite additivity for the from-scratch singular homology, the holomorphic
gluing framework that produces $`X` and its patches, the star Mayer–Vietoris sequence of
the two-set cover, and the cap-kernel bookkeeping that converts exactness into vanishing.
:::

:::definition "def:sigma-homology-equiv" (lean := "Mathoverflow1973.ThreefoldHomologyStarCoproduct.sigmaHomologyEquiv") (parent := "homology-x") (uses := "def:singular-homology")
For a finite index type $`\iota` and a family of topological spaces $`X_i`, singular
homology is additive:
$$`H_n\Bigl(\coprod_{i} X_i;\Z\Bigr) \;\cong\; \prod_i H_n(X_i;\Z).`
The isomorphism is constructed at chain level rather than quoted: a singular simplex has
connected domain, so it factors through exactly one summand, and the singular chain
complex of the disjoint union is therefore isomorphic to the biproduct of the summands'
complexes in $`\mathrm{Ch}(\mathrm{Mod}_\Z)`. Homology is an additive functor, so it
commutes with that finite biproduct. The inverse is the sum of the maps induced by the
inclusions, which is what later arguments actually use.
:::

The gluing framework comes next, because $`X` itself is an instance of it and because the
patches whose homology is compared below are the pieces of that instance.

:::definition "def:threefold-gluing-data" (lean := "Mathoverflow1973.ThreefoldGluing.Data") (parent := "homology-x")
Gluing data over a base $`B` consists of an index type $`J`, an open cover
$`\{U_i\}_{i \in J}` of $`B`, a space $`P_i` over each $`U_i` — a topological space with a
continuous map $`P_i \to B` landing in $`U_i` — and transition maps
$`t_{ij} : P_i \rightharpoonup P_j`, each an open partial homeomorphism whose source is the
part of $`P_i` lying over $`U_j`. The transitions are required to be the identity when
$`i = j`, to be inverse to one another under $`t_{ij}^{-1} = t_{ji}`, to commute with the
maps to $`B`, and to satisfy the cocycle condition $`t_{jk} \circ t_{ij} = t_{ik}` wherever
both sides are defined. The glued space is the colimit taken through mathlib's
`TopCat.GlueData`; the threefold is the instance whose four pieces are the regular family
and the three fillings.
:::

:::theorem "thm:data-is-manifold" (lean := "Mathoverflow1973.ThreefoldGluing.Data.isManifold") (parent := "homology-x") (uses := "def:threefold-gluing-data")
Let $`D` be gluing data over $`B` whose pieces are all nonempty, each charted on a complex
normed space $`E` and each a complex analytic manifold for the model
$`\mathcal{I}(\C, E)`. If every transition $`t_{ij}` is holomorphic on its source, then
the glued space, equipped with the glued atlas, is again a complex analytic manifold for
$`\mathcal{I}(\C, E)`. The smoothness index is $`\omega`, not $`1` or $`\infty`: the
charts of the glued space are the pieces' charts transported along the open embeddings,
and the compatibility condition on any two of them reduces, after unfolding, exactly to
analyticity of a transition map on its source.
:::

:::definition "def:star-fillings" (lean := "Mathoverflow1973.ThreefoldHomology.starFillings") (parent := "homology-x") (uses := "def:threefold-space")
The open set $`V \subseteq X` obtained as the union of the three filling patches, one for
each puncture. Together with the regular patch $`U`, which is the lifted patch indexed by
`none`, it covers $`X`. The two facts about this cover that the sequence below rests on
are proved separately: that $`U \cup V = X`, and that the three fillings are pairwise
disjoint, so that $`U \cap V` decomposes as the disjoint union of the three regular
overlaps $`\mathrm{RegularOverlap}\ i = U \cap V_i`.
:::

Writing $`\mathrm{ov}_i` for the three overlaps, $`J` for the regular part and $`W_i` for
the fillings, and applying finite additivity to the intersection term, the abstract
two-set Mayer–Vietoris sequence takes the concrete shape
$$`\cdots \to \prod_i H_n(\mathrm{ov}_i) \to H_n(J) \times \prod_i H_n(W_i) \to H_n(X) \to \prod_i H_{n-1}(\mathrm{ov}_i) \to \cdots`
whose three maps are the next three declarations.

:::definition "def:star-left-homology-map" (lean := "Mathoverflow1973.ThreefoldHomology.starLeftHomologyMap") (parent := "homology-x") (uses := "def:singular-homology-map, def:threefold-charted-space")
The difference map of the star sequence,
$$`\prod_i H_n(\mathrm{ov}_i;\Z) \longrightarrow H_n(J;\Z) \times \prod_i H_n(W_i;\Z), \qquad (a_i) \longmapsto \Bigl(\sum_i (\iota_J)_* a_i,\ -\bigl((\iota_{W_i})_* a_i\bigr)_i\Bigr),`
where $`\iota_J` and $`\iota_{W_i}` are the inclusions of the overlap into the regular part
and into its filling. The two components are separate declarations —
`starOverlapToRegularHomologyMap`, which sums over the punctures, and
`starOverlapToFillingsHomologyMap`, which acts componentwise — and the sign is carried on
the second, matching the usual Mayer–Vietoris convention. Both are $`\Z`-linear.
:::

:::definition "def:star-connecting-homomorphism" (lean := "Mathoverflow1973.ThreefoldHomology.starConnectingHomomorphism") (parent := "homology-x") (uses := "def:connecting-homomorphism, def:homeomorph-homology-equiv, def:sigma-homology-equiv, def:star-fillings, def:threefold-projection")
The connecting homomorphism
$`\partial : H_{n+1}(X;\Z) \to \prod_i H_n(\mathrm{ov}_i;\Z)` of the star sequence. It is
the abstract two-set connecting map for the cover $`\{U, V\}`, whose target is
$`H_n(U \cap V;\Z)`, composed with the isomorphism that splits that group as a product
over the three punctures. The splitting is the disjointness of the fillings run through
the additivity isomorphism of the first declaration, together with the homeomorphism
identifying $`U \cap V` with the coproduct of the three overlaps.
:::

:::theorem "thm:star-exact-at-pair" (lean := "Mathoverflow1973.ThreefoldHomology.star_exact_at_pair") (parent := "homology-x") (uses := "def:homeomorph-homology-equiv, def:sigma-homology-equiv, def:star-fillings, def:star-left-homology-map, def:threefold-projection, thm:singular-mayer-vietoris-exact-at-pair")
The star sequence is exact at the pair term: the image of the difference map
$`\prod_i H_n(\mathrm{ov}_i) \to H_n(J) \times \prod_i H_n(W_i)` is the kernel of the sum
map into $`H_n(X)`. In Lean the statement is `Function.Exact`, which is exactly the
equality of range and kernel. It is obtained by transporting the abstract exactness for
the cover $`\{U, V\}` across the two splitting isomorphisms — of the overlap term and of
the pair term — which is why those isomorphisms occur in the statement's dependencies
rather than only in its proof.
:::

:::theorem "thm:star-exact-at-ambient" (lean := "Mathoverflow1973.ThreefoldHomology.star_exact_at_ambient") (parent := "homology-x") (uses := "def:star-connecting-homomorphism, def:star-fillings, thm:star-exact-at-pair")
Exactness at the ambient term: the image of the sum map
$`H_{n+1}(J) \times \prod_i H_{n+1}(W_i) \to H_{n+1}(X)` is the kernel of the connecting
homomorphism $`\partial`. With the companion `star_exact_at_intersection`, which gives
exactness at the overlap term, the three statements together constitute the long exact
sequence. Every vanishing theorem below is an application of one of them: a group is
squeezed to zero by naming its two neighbours in the sequence and showing the maps into
and out of it are respectively surjective and zero.
:::

The sequence alone does not compute anything until the homology of the pieces and of the
overlaps is known, and until one can say which regular classes die when the fillings are
glued in. The overlaps are handled by the Wang sequences of their mapping tori, and the
fillings by deformation retractions onto their central fibres. The one comparison that is
genuinely delicate is at the cusp.

:::theorem "thm:boundary-filling-homology-map-surjective" (lean := "Mathoverflow1973.ThreefoldHomologyCuspFibre.boundaryFillingHomologyMap_surjective") (parent := "homology-x") (uses := "def:piece-mapping-torus-homotopy-equiv, def:punctured-cusp-cover, def:threefold-projection, thm:exists-actual-specialization-homology, thm:exists-controlled-retraction-all-levels")
The map $`H_n(\partial_{\mathrm{cusp}};\Z) \to H_n(W_0;\Z)` induced by the inclusion of
the cusp boundary into the cusp filling is surjective in every degree. This is the
analogue at $`p_0` of Lemma 7.18 of {citet alpoge.s6}[], and the proof is a limit
argument: the map factors through the inclusion of a single four-torus fibre sitting at
height $`h` over a base point of norm $`e^{-2\pi h}`, all heights are homotopic to one
another inside the boundary, and fibres at large height — hence over base points
arbitrarily close to the puncture — already surject onto the filling's homology. The
elliptic punctures are easier and are handled uniformly with this case in
`CapElimination.boundaryFillingHomologyMap_surjective`.
:::

:::theorem "thm:regular-inclusion-kernel" (lean := "Mathoverflow1973.ThreefoldHomology.CapElimination.regularInclusion_kernel") (parent := "homology-x") (uses := "def:star-left-homology-map, thm:star-exact-at-pair")
A regular class dies globally exactly when it comes from overlap classes that the fillings
kill:
$$`\ker\bigl(H_n(J;\Z) \to H_n(X;\Z)\bigr) \;=\; \Bigl\{\textstyle\sum_i (\iota_J)_* a_i \;:\; (a_i) \in \prod_i H_n(\mathrm{ov}_i),\ (\iota_{W_i})_* a_i = 0 \ \text{for all } i\Bigr\}.`
Both inclusions are exactness at the pair term, read in the two directions: a class with
$`(a, 0)` in the kernel of the sum map lifts to an overlap tuple, and the second component
of the resulting equation says the tuple is annihilated by every filling. This identity is
what turns the qualitative sequence into a computation, since it replaces a statement
about $`X` by a statement about the three boundary five-manifolds.
:::

:::definition "def:native-cap-kernel" (lean := "Mathoverflow1973.ThreefoldHomology.CapElimination.NativeCapKernel") (parent := "homology-x") (uses := "def:piece-mapping-torus-homotopy-equiv, def:singular-homology-map, def:threefold-projection")
The *cap kernel* at the puncture $`i` in degree $`n`:
$$`\mathcal{K}_i^{\,n} \;=\; \ker\bigl(H_n(\partial_i;\Z) \to H_n(W_i;\Z)\bigr),`
the classes on the boundary five-manifold that die when the filling is capped in. These
are the vanishing cycles of the local degeneration, and tuples
$`(a_i) \in \prod_i \mathcal{K}_i^{\,n}` are the central bookkeeping object of the whole
computation: by the previous theorem their images under the overlap-to-regular map are
exactly the regular classes that die in $`X`, so surjectivity of that map in degree $`n`
gives surjectivity of the difference map in degree $`n`; the sum map in that degree is then
zero, and exactness at the ambient term makes the connecting map out of $`H_n(X;\Z)`
injective. Every vanishing below is reached this way.
:::

Each overlap is a mapping torus over the circle with fibre the four-torus, so its homology
sits in a Wang exact sequence relating $`H_*(T^4)` to $`H_*(\mathrm{ov}_i)` through
$`f_* - 1`. Reading a cap-kernel tuple through the three Wang boundary maps produces three
classes in $`H_n(T^4;\Z)`, and the constraint that ties them together is the following.

:::theorem "thm:wang-cancellation" (lean := "Mathoverflow1973.ThreefoldHomology.FourthWang.wang_cancellation") (parent := "homology-x") (uses := "def:mapping-torus-homology-wang-boundary, def:star-left-homology-map")
Let $`(a_i)` be a tuple of overlap classes in degree $`n+1` whose image in $`H_{n+1}(J;\Z)`
vanishes, and let $`w_0, w_3, w_4 \in H_n(T^4;\Z)` be the Wang boundaries of its cusp,
multiplicity-$`3` and multiplicity-$`4` components. Then all three coincide,
$`w_3 = w_4 = w_0`, and the common value is fixed by both monodromy generators of the
triangle group. The proof is the pair of relations that the vanishing in the regular part
imposes — $`w_3` is the inverse of the first triangle generator applied to $`w_0`, and
$`w_4 = w_0` — combined with the fact that each elliptic Wang boundary is already fixed by
its own generator; the two statements collapse into one another. This is the compatibility
condition that every degree-by-degree elimination below feeds on.
:::

:::theorem "thm:homology-subsingleton-of-lt" (lean := "Mathoverflow1973.ThreefoldHomology.Finiteness.homology_subsingleton_of_lt") (parent := "homology-x") (uses := "def:actual-quotient-fibre, def:central-boundary-suspension-homeomorph, def:contractible-cover-homology-higher-equiv, def:overlap-phase-homeomorph, def:piece-mapping-torus-homotopy-equiv, def:star-connecting-homomorphism, def:surface-homology-coordinates, thm:exists-closed-quotient-strong-deformation-retraction, thm:source-coinvariant-inclusion-kernel-projection-exact, thm:star-exact-at-ambient")
$`H_n(X;\Z) = 0` for every $`n > 6`. Each filling is homotopy equivalent to a compact object
of real dimension $`4` — the cusp filling retracts onto the quotient central fibre, each
elliptic filling onto its bielliptic central surface — so filling homology vanishes above
degree $`4`; the regular part, which retracts onto a torus bundle over a wedge of two
circles, and the overlaps, being mapping tori of a four-torus, vanish above degree $`5`
instead. Exactness at the ambient term then squeezes $`H_n(X)` between a group that is
already zero and a connecting target that is also zero. In Lean the conclusion is
`Subsingleton`, which for a $`\Z`-module is the vanishing statement.
:::

:::group "homology-x-degrees"
The computation itself, degree by degree: the first difference map is bijective, the
generator of $`H_2` is killed by a Bézout identity in the multiplicities, degrees $`3` and
$`4` reduce to a single integer coefficient, degree $`5` to a single Wang coordinate, and
degree $`6` produces the fundamental class.
:::

Degree $`1` is imported: $`X` is simply connected, so $`H_1(X;\Z) = 0`. That input enters
the star sequence at exactly one place.

:::theorem "thm:star-left-one-bijective" (lean := "Mathoverflow1973.ThreefoldHomology.SecondDegree.starLeft_one_bijective") (parent := "homology-x-degrees") (uses := "def:star-left-homology-map, thm:space-simply-connected")
The difference map in degree $`1` is bijective. Surjectivity is exactness at the pair term
together with $`H_1(X;\Z) = 0`, which comes from simple connectivity through the first
Hurewicz map. Injectivity is not proved by a determinant computation: source and target are
finite free $`\Z`-modules of the same rank $`9` — three overlaps of first Betti number $`3`
each, against $`H_1(J) \cong \Z^3` and $`\prod_i H_1(W_i) \cong \Z^6` — and mathlib's
`OrzechProperty` upgrades a surjection to a bijection as soon as the source's rank is at
most the target's, which the equality of the two ranks supplies. Bijectivity forces the
degree-$`1` connecting map to vanish, hence the degree-$`2` sum map to be surjective.
:::

With $`\partial_1 = 0`, exactness makes $`H_2(X;\Z)` a quotient of the regular part's
degree-$`2` homology modulo the cap kernels, and that quotient is cyclic: it is generated
by the image of the fibre class through the monodromy coinvariants
$`\mathrm{coker}\bigl(f_* - 1 \text{ on } H_2(T^4)\bigr) \cong \Z`. Killing $`H_2` is
therefore killing one generator, and the mechanism is the circle action supplied by the
logarithmic transform at each multiple fibre: sweeping a class along the transform's
circle direction produces relations, and the two multiple fibres produce two of them.

:::theorem "thm:homology-two-generator-eq-zero" (lean := "Mathoverflow1973.ThreefoldHomology.SecondDegree.homologyTwoGenerator_eq_zero") (parent := "homology-x-degrees") (uses := "def:elliptic-kind, thm:star-left-one-bijective")
The generator of $`H_2(X;\Z)` is zero. Sweeping in the multiplicity-$`3` fibre, whose
twist vector is $`\varepsilon`, kills $`2 \cdot \mathrm{gen}`; sweeping in the
multiplicity-$`4` fibre, whose twist vector is $`-\varepsilon'`, kills
$`(-3) \cdot \mathrm{gen}`. The conclusion is then the identity $`1 = 2 + 2 - 3` applied to
the cyclic map $`z \mapsto z \cdot \mathrm{gen}`. This is the coprimality of the
multiplicities $`3` and $`4` in Bézout form, and it is the concrete shadow of the paper's
condition $`|p| = 1`: the same choice of twist data that makes $`\pi_1(X)` trivial makes
the two sweep relations generate the full group of integers.
:::

:::theorem "thm:homology-two-subsingleton" (lean := "Mathoverflow1973.ThreefoldHomology.SecondDegree.homologyTwo_subsingleton") (parent := "homology-x-degrees") (uses := "def:circle-homology-one-equiv, def:coordinate-torus-h2-exterior-equiv, def:flat-torus-circle-homeomorph, def:mapping-torus-homology-wang-boundary, def:period-torus-higher-homology-pontryagin-product, def:product-torus-top-class, def:punctured-product-homeomorph, def:singular-h1-equiv, def:source-difference, def:surface-mapping-torus-homeomorph, def:threefold-projection, thm:homology-two-generator-eq-zero, thm:intersection-to-v-twisted-fold, thm:singular-mayer-vietoris-exact-at-pair, thm:space-simply-connected")
$`H_2(X;\Z) = 0`.
:::

:::proof "thm:homology-two-subsingleton"
The group is cyclic, generated by the image of the four-torus fibre class under the
composite $`\Z \cong \mathrm{coker}(f_* - 1 \text{ on } H_2(T^4)) \to H_2(X;\Z)`, and this
surjection exists because the degree-$`2` sum map is surjective and the degree-$`2` cap
kernels exhaust the kernel of the regular inclusion. So it suffices to kill the generator.
Each multiple fibre carries a free circle action — free precisely because the twist
parameter is coprime to the multiplicity — and crossing a class with the positive circle
class and pushing forward along the action gives a sweeping operator that raises degree by
one. Explicit coordinate computations on the bielliptic central surfaces evaluate the two
sweeps: the multiplicity-$`3` fibre yields the relation $`2\cdot \mathrm{gen} = 0`, the
multiplicity-$`4` fibre yields $`-3 \cdot \mathrm{gen} = 0`, and $`1 = 2 + 2 - 3` finishes.
$`\blacksquare`
:::

Degrees $`3` and $`4` are governed by one integer. An explicit degree-$`3` cap-kernel
tuple, the *reference classes*, is written down puncture by puncture with hand-computed
lattice coordinates; the tuple is arranged so that its three Wang values agree and its
obstruction in the regular family's source lattice vanishes, which by the cancellation
theorem is exactly the condition for it to survive. Its image in the regular part is then
an integer multiple of the fibre class, and that integer decides both degrees.

:::theorem "thm:reference-fibre-coefficient-eq-one" (lean := "Mathoverflow1973.ThreefoldHomology.ThirdDegree.referenceFibreCoefficient_eq_one") (parent := "homology-x-degrees") (uses := "thm:reference-classes-regular, thm:wang-cancellation")
The reference fibre coefficient equals $`1`. It is defined as the unique integer $`z` with
$`z \cdot [\text{fibre}] = \sum_i (\iota_J)_* r_i` for the reference cap-kernel tuple
$`(r_i)`, so the claim is the single equation `referenceClasses_regular`, supplied by the
period-family computation of the third relation. Uniqueness of $`z` is part of the
definition, obtained by a choice principle from an existence-and-uniqueness lemma, so the
value is pinned rather than merely constrained.
:::

:::theorem "thm:homology-three-subsingleton" (lean := "Mathoverflow1973.ThreefoldHomology.ThirdDegree.homologyThree_subsingleton") (parent := "homology-x-degrees") (uses := "thm:reference-classes-regular, thm:reference-fibre-coefficient-eq-one")
$`H_3(X;\Z) = 0`.
:::

:::proof "thm:homology-three-subsingleton"
Write $`c` for the reference fibre coefficient. The group $`H_3(X;\Z)` is cyclic: a
surjection $`\Z \to H_3(X;\Z)` is built from the degree-$`3` fibre class, exactly as in
degree $`2`. The kernel of that surjection is computed to be the ideal $`(c)`: a multiple
$`z` of the fibre class dies in $`X` precisely when the corresponding regular class lies in
the image of the degree-$`3` cap kernels, and by the source-map analysis the reachable
multiples are exactly $`\{k c : k \in \Z\}` — the reference tuple realizes $`c` and nothing
smaller is available. Hence $`H_3(X;\Z) \cong \Z/(c)`, which vanishes if and only if $`c`
is a unit. Since $`c = 1`, it does. $`\blacksquare`
:::

:::theorem "thm:homology-four-subsingleton" (lean := "Mathoverflow1973.ThreefoldHomology.FourthDegree.homologyFour_subsingleton") (parent := "homology-x-degrees") (uses := "def:singular-homology, def:threefold-space, thm:reference-fibre-coefficient-eq-one")
$`H_4(X;\Z) = 0`.
:::

:::proof "thm:homology-four-subsingleton"
The same coefficient $`c` controls degree $`4`, but through its annihilator rather than its
ideal. A chain of three isomorphisms identifies $`H_4(X;\Z)` with the kernel of
multiplication by $`c` on $`\Z`: the connecting map identifies $`H_4(X)` with the kernel of
the degree-$`3` difference map, that kernel with the kernel of the degree-$`3`
cap-kernel-to-regular map, and the latter — through the reference tuple, which realizes
$`c` there — with $`\{z \in \Z : zc = 0\}`. So $`H_4(X;\Z) = 0` if and only if $`c \ne 0`,
which is weaker than the unit condition degree $`3` needs. Since $`c = 1`, both conditions
hold and both degrees vanish. $`\blacksquare`
:::

Degree $`5` is detected by a single integer coordinate. Given a class in $`H_5(X;\Z)`, its
connecting image is a cap-kernel tuple in degree $`4`; taking the Wang boundary of the cusp
component lands in $`H_3(T^4;\Z) \cong \Z^4`, and one of those four coordinates already
determines the class.

:::definition "def:fifth-wang-coordinate" (lean := "Mathoverflow1973.ThreefoldHomology.FourthWang.fifthWangCoordinate") (parent := "homology-x-degrees") (uses := "def:mapping-torus-homology-wang-boundary, def:star-connecting-homomorphism")
The linear functional $`H_5(X;\Z) \to \Z` sending $`a` to the top coordinate, in the
standard basis of $`H_3(T^4;\Z)`, of the Wang boundary of the cusp component of
$`\partial a`. Its usefulness is that it is faithful: `fifthWangCoordinate_eq_zero` shows
that a class on which it vanishes is zero, because the cancellation theorem forces the three
Wang boundaries of $`\partial a` to be equal and monodromy-invariant, invariance confines
them to a rank-one subgroup detected by this one coordinate, and a class with
$`\partial a = 0` lies in the image of the degree-$`5` sum map, which is identically zero
because the degree-$`5` difference map is surjective.
:::

:::theorem "thm:homology-five-subsingleton" (lean := "Mathoverflow1973.ThreefoldHomology.FifthDegree.homologyFive_subsingleton") (parent := "homology-x-degrees") (uses := "def:central-singular-homology-equiv, def:cusp-boundary-gamma-zero-native-class, def:fifth-wang-coordinate, def:real-torus-h4-equiv, def:star-connecting-homomorphism, def:surface-homology-coordinates, thm:boundary-source-kernel-projection, thm:elliptic-boundary-source-kernel-projection, thm:exists-actual-specialization-homology, thm:exists-controlled-retraction-all-levels, thm:period-cover-h1-ker-eq-deck-difference-range, thm:source-coinvariant-inclusion-kernel-projection-exact, thm:star-exact-at-pair, thm:wang-exact-at-fibre")
$`H_5(X;\Z) = 0`.
:::

:::proof "thm:homology-five-subsingleton"
It is enough to show the fifth Wang coordinate vanishes identically, since it detects the
whole group. Fix a class $`a \in H_5(X;\Z)`. Its connecting image is a degree-$`4`
cap-kernel tuple, and each component decomposes as a boundary contribution together with a
fibre class in $`H_4(T^4;\Z) \cong \Z`: the cusp component through the controlled
retraction of the cusp neighbourhood onto its central fibre, the two elliptic components
through the period-cover description of the bielliptic surfaces. Write $`k` for the fifth
Wang coordinate of $`a`, $`u` and $`v` for the fibre coefficients at the
multiplicity-$`3` and multiplicity-$`4` punctures, and $`d` for the cusp residual
coefficient. Each elliptic puncture contributes one equation, with its multiplicity as the
factor and the sign of its twist vector: $`3u = k` and $`-4v = k`. Subtracting the cusp
equation from the vanishing sum of all three boundary contributions gives the third,
$`u + v = dk`. Eliminating $`u` and $`v` by $`4(3u) - 3(-4v) - 12(u+v)` leaves
$`(12d - 1)k = 0`, and $`12d - 1` is never zero for an integer $`d`. So $`k = 0`. That
$`12d - 1 \not\equiv 0 \pmod{12}` is the same obstruction the paper records as
$`\gcd(p,12) = 1`, which is likewise how it knows $`p \ne 0`. $`\blacksquare`
:::

What survives in degree $`6` is the cusp overlap. The degree-$`5` difference map is
surjective, so the connecting map $`H_6(X) \to \prod_i H_5(\mathrm{ov}_i)` is injective
onto the kernel of that map; the two elliptic columns of the kernel cancel against one
another under an explicit column isomorphism; and what is left is the cusp overlap's fifth
homology.

:::definition "def:homology-six-equiv" (lean := "Mathoverflow1973.ThreefoldHomology.TopDegree.homologySixEquiv") (parent := "homology-x-degrees") (uses := "def:m, def:mapping-torus-homology-wang-boundary, def:period-torus-higher-homology-pontryagin-product, def:piece-mapping-torus-homotopy-equiv, def:product-torus-top-class, def:real-torus-h4-equiv, def:star-connecting-homomorphism, def:threefold-projection, def:torus-matrix-map, def:triangle-torus-action, thm:intersection-to-v-twisted-fold")
An isomorphism $`H_6(X;\Z) \cong \Z`, realized as the composite of the connecting map into
the cusp overlap's fifth homology with the identification $`H_5(\mathrm{ov}_0;\Z) \cong \Z`.
The latter is the Wang sequence of the cusp mapping torus in its top range: the four-torus
fibre has no homology in degree $`5`, so $`H_5(\mathrm{ov}_0)` reduces to
$`\ker\bigl((M_0)_* - 1 \text{ on } H_4(T^4;\Z)\bigr)`, and $`M_0` is unipotent of
determinant $`1`, so it acts trivially on the top exterior power and the kernel is all of
$`H_4(T^4;\Z) \cong \Z`. The simp lemma `homologySixEquiv_apply` records the formula: a
class is sent to the cusp coordinate of its connecting image.
:::

:::definition "def:top-degree-top-class" (lean := "Mathoverflow1973.ThreefoldHomology.TopDegree.topClass") (parent := "homology-x-degrees") (uses := "def:homology-six-equiv, def:singular-homology, def:threefold-space")
The fundamental class of $`X`: the element of $`H_6(X;\Z)` corresponding to $`1` under the
isomorphism above. The companion `eq_smul_topClass` states that every degree-$`6` class is
the integer multiple of it named by the isomorphism, so the class is a generator and the
group is infinite cyclic with a preferred orientation. This is the last piece of data the
recognition argument needs: together with the vanishing in degrees $`1` through $`5` and
above $`6`, it says that $`X` is an integral homology six-sphere, and the generator is what
the Hurewicz ladder uses to produce a map $`X \to S^6` carrying it onto the sphere's own
top class.
:::

Assembled immediately downstream, these results give
$`H_n(X;\Z) = 0` for $`n \ne 0, 6` and $`H_0(X;\Z) \cong H_6(X;\Z) \cong \Z`, which is the
homology of the six-sphere. Combined with simple connectivity, the Hurewicz theorem
upgrades this to a homotopy equivalence $`X \simeq S^6`, and Smale's theorem then makes it
a homeomorphism onto the standard sphere — at which point the complex atlas of $`X`
transports and the Hopf problem is settled.
