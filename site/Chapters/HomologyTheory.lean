/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — singular homology chapter.

The homological engine room of the development: the singular chain complex over the
integers, the Mayer–Vietoris sequence of a two-set open cover proved through barycentric
subdivision, the degree-one Hurewicz isomorphism, and the homology of spheres.
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

#doc (Manual) "Singular homology from scratch" =>

Section 7 of {citet alpoge.s6}[] computes the two invariants of the threefold $`X` that
the recognition argument consumes: $`\pi_1(X) = 1` and $`H_*(X;\Z) \cong H_*(S^6;\Z)`.
Both computations are ordinary algebraic topology — Mayer–Vietoris over the decomposition
$`X = N_0' \cup X^\circ`, Wang sequences of mapping tori, Hurewicz comparisons between
$`\pi_1` and $`H_1` of each piece — and the paper treats that apparatus as standard,
citing {citep hatcher02}[]. Mathlib does not supply it. Mathlib has the singular
simplicial set of a topological space, the Moore complex of a simplicial object in a
module category, and the homological algebra that takes homology of a chain complex; it
has essentially nothing between those and the theorems the paper uses. The missing layer
is built here, and it is the largest self-contained block of classical mathematics in the
subject.

The division is worth stating precisely, because "from scratch" would otherwise
overclaim. Imported from Mathlib: $`\mathrm{Sing}(X)` as `TopCat.toSSet`, its chain
complex with coefficients in $`\Z`, `HomologicalComplex.homology`, the long exact homology
sequence of a short exact sequence of complexes (`ShortComplex.ShortExact.δ` together with
`homology_exact₁`, `homology_exact₂`, `homology_exact₃`), the metric Lebesgue number
lemma, `FundamentalGroup`, and `Abelianization`. Built here: the free-basis interface that
makes a chain group usable as the free $`\Z`-module on singular simplices, the small
simplices theorem with barycentric subdivision and its mesh estimate, Mayer–Vietoris as
explicit equalities of $`\Z`-linear maps, the degree-one Hurewicz theorem with a
hand-constructed inverse, and the homology of every sphere by suspension induction.

The interface that leaves this chapter is deliberately elementary. A consumer sees a
$`\Z`-module $`H_n(Y;\Z)`, a $`\Z`-linear map $`f_*` for each continuous $`f`, a
connecting map $`\partial`, and three equalities of the form
$`\mathrm{range} = \mathrm{ker}`; the category theory that produced them does not appear
in any statement. That shielding is what makes the rest of the development legible at its
scale — `SingularHomology` is referenced 1366 times in the file and `singularHomologyMap`
903 times, more than any other pair of declarations.

:::group "homology-theory"
The singular chain complex over $`\Z` and its free basis of singular simplices, the
homology functor, the Mayer–Vietoris sequence of a two-set open cover obtained from the
small simplices theorem, and the degree-one Hurewicz isomorphism.
:::

:::definition "def:first-hurewicz-simplex" (lean := "Mathoverflow1973.FirstHurewicz.Simplex") (parent := "homology-theory")
*Definition.* The standard $`n`-simplex is Mathlib's
$`\Delta^n = \{t : \mathrm{Fin}(n{+}1) \to \R \mid t_i \ge 0,\ \sum_i t_i = 1\}`, with its
subspace topology. A singular $`n`-simplex of a space $`X` is a continuous map
$`\sigma : \Delta^n \to X`, recorded as the bundled type `SingularSimplex X n`. The face
inclusions are induced from the simplex category: `simplexFace n i` is
$`\Delta^n \to \Delta^{n+1}` obtained from the coface map
$`\delta_i : [n] \to [n{+}1]`, so the combinatorics of faces is Mathlib's rather than
hand-rolled, and the $`i`-th face of $`\sigma` is the composite
$`\sigma \circ \delta_i`.
:::

:::definition "def:singular-complex" (lean := "Mathoverflow1973.FirstHurewicz.singularComplex") (parent := "homology-theory")
*Definition.* The singular chain complex $`C_\bullet(X;\Z)` is the Moore complex of
Mathlib's singular simplicial set with coefficients in $`\Z`: an object of
$`\mathrm{ChainComplex}(\mathrm{Mod}_\Z, \mathbb{N})`, with $`C_n(X)` written
`Chains X n`. Nothing about it is defined by hand — the differential is the one Mathlib
attaches to a simplicial object — and the bridge back to topology is
`boundary_simplex`, which identifies that differential on a generator with the classical
alternating sum
$`\partial\sigma = \sum_{i=0}^{n+1} (-1)^i\, \sigma \circ \delta_i`. Degree $`1` gets its
own abbreviation `SingularH1 X` for the homology in that degree, which is the target of
the Hurewicz map below.
:::

:::definition "def:first-hurewicz-chain-lift" (lean := "Mathoverflow1973.FirstHurewicz.chainLift") (parent := "homology-theory") (uses := "def:singular-complex, def:first-hurewicz-simplex")
*Definition.* Every function $`f` from singular $`n`-simplices of $`X` to a
$`\Z`-module $`M` extends to a $`\Z`-linear map $`C_n(X) \to M` taking the generator
$`\sigma` to $`f(\sigma)`. Together with `chainMap_ext`, which says two linear maps out of
$`C_n(X)` agreeing on generators are equal, this is the statement that $`C_n(X)` is the
free $`\Z`-module on the set of continuous maps $`\Delta^n \to X` — a fact that the Moore
complex definition does not hand over directly. Every operator constructed later in the
chapter, the subdivision operator, its chain homotopy, and the cochain inverting the
Hurewicz map, is defined by this universal property and its extensionality companion.
:::

:::definition "def:singular-homology" (lean := "Mathoverflow1973.SingularMayerVietoris.SingularHomology") (parent := "homology-theory") (uses := "def:singular-complex")
*Definition.* Singular homology $`H_n(Y;\Z)` is the degree-$`n` homology of the singular
chain complex, computed by Mathlib's `HomologicalComplex.homology`. It is an object of
$`\mathrm{Mod}_\Z` and is used throughout as a $`\Z`-module: linear equivalences
$`\simeq_\Z` into $`\Z`, $`\Z^k`, or $`\Z/p` are the form every downstream homology
computation takes. This is the central object of the homological half of the proof.
:::

:::definition "def:singular-homology-map" (lean := "Mathoverflow1973.SingularMayerVietoris.singularHomologyMap") (parent := "homology-theory") (uses := "def:singular-homology")
*Definition.* A continuous map $`f : Y \to Z` induces
$`f_* : H_n(Y;\Z) \to H_n(Z;\Z)`, a $`\Z`-linear map in every degree, obtained as the
underlying linear map of the categorical homology map of the chain map
$`\sigma \mapsto f \circ \sigma`. Functoriality is available in the form consumers need it —
$`(\mathrm{id})_* = \mathrm{id}` and $`(g \circ f)_* = g_* \circ f_*` as linear maps —
and every comparison of pieces of $`X` downstream, every collapse map, every inclusion of
a fibre, is expressed through this one map.
:::

:::definition "def:module-homology-cycle-class" (lean := "Mathoverflow1973.SingularMayerVietoris.ModuleHomology.cycleClass") (parent := "homology-theory")
*Definition.* For a chain complex $`K` of $`\Z`-modules, $`Z_n(K) = \ker \partial_n` and
the class map $`Z_n(K) \to H_n(K)` is $`\Z`-linear and surjective, with
$`[c] = 0` if and only if $`c = \partial b` for some $`b`, and with $`[c] = [d]` if and
only if $`c - d` bounds. Categorical homology is a limit-and-quotient construction whose
elements are not literally cycles; this layer restores the classical calculus, and it is
the only interface later chapters use when they need to name an element of a homology
group. The chapter's quasi-isomorphism criterion is phrased entirely in its terms: a chain
map inducing isomorphisms is recognized by lifting cycles and boundaries, with no spectral
or derived machinery.
:::

The Mayer–Vietoris sequence is obtained by Hatcher's route rather than by an excision
axiom. For subsets $`U, V \subseteq X` the chains supported in $`U` or in $`V` form a
subcomplex, and the sequence relating it to the pieces is short exact for purely formal
reasons; the topological content is entirely in the comparison between that subcomplex and
the full complex, which is where subdivision enters.

:::definition "def:singular-mayer-vietoris-small-complex" (lean := "Mathoverflow1973.SingularMayerVietoris.smallComplex") (parent := "homology-theory") (uses := "def:singular-complex")
*Definition.* For subsets $`U, V \subseteq X`, the small chains
$`C_n^{U+V}(X) \subseteq C_n(X)` are the span of the singular simplices whose image lies
entirely in $`U` together with those whose image lies entirely in $`V`. The boundary
carries small chains to small chains — a face of a simplex has image inside the image of
the simplex — so these submodules form a subcomplex $`C^{U+V}_\bullet(X)`, with
`smallInclusion` its degreewise injective, hence monomorphic, inclusion into
$`C_\bullet(X)`. No hypothesis on $`U` and $`V` is used.
:::

:::theorem "thm:chain-sequence-short-exact" (lean := "Mathoverflow1973.SingularMayerVietoris.chainSequence_shortExact") (parent := "homology-theory") (uses := "def:singular-mayer-vietoris-small-complex")
*Theorem.* For arbitrary subsets $`U, V \subseteq X`, the sequence of chain complexes

$$`0 \to C_\bullet(U \cap V) \xrightarrow{\ (i_U,\, -i_V)\ } C_\bullet(U) \oplus C_\bullet(V) \xrightarrow{\ j_U + j_V\ } C^{U+V}_\bullet(X) \to 0`

is short exact. Here $`C_\bullet(U)` is the singular complex of the subspace $`U`, the
middle term is the biproduct in $`\mathrm{ChainComplex}(\mathrm{Mod}_\Z, \mathbb{N})`, and
the two maps are the biproduct lift of the inclusions of $`U \cap V` with a sign on the
second, and the biproduct description of the two pushforwards into small chains. Openness
of $`U` and $`V` plays no part.
:::

:::proof "thm:chain-sequence-short-exact"
Short exactness of a sequence of complexes is short exactness in each degree, and in each
degree all three modules are free on explicit bases of singular simplices. Injectivity of
the left map holds because a simplex with image in $`U \cap V` is recovered from its
composite into $`U`. Joint surjectivity is the definition of the small chains: a small
chain is by construction a sum of a chain supported in $`U` and a chain supported in
$`V`, which is the image of the corresponding pair. Exactness in the middle is the
overlap computation — a pair $`(a,b)` with $`j_U a + j_V b = 0` has, on each basis
simplex, cancelling coefficients, so the simplex is supported in both $`U` and $`V` and
the pair is the image of the corresponding chain on $`U \cap V`. These ingredients
are assembled by the degreewise helper `SmallChainBiprod.shortExactOfComplexes`, which
takes exactly the injectivity, joint surjectivity, and overlap-lifting hypotheses and
returns short exactness of the biproduct sequence. $`\blacksquare`
:::

:::definition "def:formal-subdivision" (lean := "Mathoverflow1973.SingularMayerVietoris.formalSubdivision") (parent := "homology-theory")
*Definition.* Barycentric subdivision is defined on a combinatorial model rather than on
singular chains. Formal chains on a vertex set $`V` in degree $`n` are the finitely
supported functions from $`n`-tuples of vertices to $`\Z` — so a tuple of $`n{+}1`
vertices stands for an $`n`-simplex — carrying an alternating-face boundary $`\partial`
and a cone operator $`\mathrm{Cone}_a` prepending an apex $`a`. Given a choice of centre for every tuple,
subdivision is the recursion $`\mathrm{Sd} = \mathrm{id}` in degree $`0` and
$`\mathrm{Sd}(v) = \mathrm{Cone}_{c(v)}\big(\mathrm{Sd}(\partial v)\big)` on a generator.
It commutes with the boundary, and `formalSubdivisionIteratedHomotopy` supplies an
explicit $`T` with $`\partial T + T\partial = \mathrm{id} - \mathrm{Sd}^k`. All of this is
finite bookkeeping in a free module, with no topology; the operators on actual singular
chains, `subdivision` and `subdivisionHomotopy`, are then obtained by realizing the
subdivided standard simplex through affine maps and pushing forward along each
$`\sigma`, which makes their naturality in $`X` immediate.
:::

:::theorem "thm:formal-subdivision-iterate-mesh" (lean := "Mathoverflow1973.SingularMayerVietoris.formalSubdivision_iterate_mesh") (parent := "homology-theory") (uses := "def:formal-subdivision")
*Theorem.* Subdivision shrinks simplices. Measure the vertices of a formal chain through
a coordinate map $`V \to E` into a normed space, and require the chosen centres to map to
barycentres of the corresponding vertex families. If every tuple in the support of a chain
in degree $`n{+}1` has all pairwise vertex distances at most $`D`, then after $`k`
subdivisions every tuple in the support has pairwise vertex distances at most
$`\big(\tfrac{n}{n+1}\big)^k D`. The contraction factor $`\tfrac{n}{n+1}` is dimensional
and is what makes iteration effective: applied to the standard simplex, whose diameter is
at most $`1`, it drives the mesh of $`\mathrm{Sd}^k` to zero.
:::

:::theorem "thm:small-inclusion-quasi-iso" (lean := "Mathoverflow1973.SingularMayerVietoris.smallInclusion_quasiIso") (parent := "homology-theory") (uses := "def:formal-subdivision, thm:formal-subdivision-iterate-mesh, def:singular-mayer-vietoris-small-complex, def:module-homology-cycle-class, def:first-hurewicz-chain-lift")
*Theorem (small simplices).* If $`U` and $`V` are open and $`U \cup V = X`, the inclusion
$`C^{U+V}_\bullet(X) \hookrightarrow C_\bullet(X)` is a quasi-isomorphism. The companion
`smallHomologyEquiv` packages the conclusion as the $`\Z`-linear isomorphism
$`H_n^{U+V}(X) \cong H_n(X)` in every degree, and it is this isomorphism, not the abstract
`QuasiIso` statement, that the Mayer–Vietoris maps are transported along.
:::

:::proof "thm:small-inclusion-quasi-iso"
The proof is the classical one, arranged so that the only homological input is an
elementary lifting criterion. A chain map that is degreewise injective induces
isomorphisms on homology as soon as every cycle of the target agrees, modulo boundaries,
with a cycle carried by the source, and every source cycle bounding in the target already
bounds in the source; this is `ModuleHomology.quasiIso_of_injective_chain_conditions`,
proved directly from the cycle-class interface. Both conditions are supplied by iterated
subdivision. Given a chain $`c`, each of its finitely many simplices is uniformly
continuous on the compact simplex, so the two-set Lebesgue number lemma
`exists_lebesgue_number_two` produces a $`\delta > 0` such that any subset of $`\Delta^n`
of diameter at most $`\delta` maps into $`U` or into $`V`; the mesh estimate then gives a
$`k` with $`\mathrm{Sd}^k c` small, and the same $`k` works for the finitely many
simplices at once. The homotopy $`T` with
$`\partial T + T\partial = \mathrm{id} - \mathrm{Sd}^k` converts that into the two lifting
conditions, and it preserves small chains, which is what makes the second condition hold
in the subcomplex rather than only in $`C_\bullet(X)`. Openness is used exactly once, in
the Lebesgue number lemma.
$`\blacksquare`
:::

:::definition "def:connecting-homomorphism" (lean := "Mathoverflow1973.SingularMayerVietoris.connectingHomomorphism") (parent := "homology-theory") (uses := "def:singular-homology, thm:chain-sequence-short-exact, thm:small-inclusion-quasi-iso")
*Definition.* For an open cover $`U \cup V = X`, the Mayer–Vietoris connecting
homomorphism is the $`\Z`-linear map
$`\partial : H_{n+1}(X) \to H_n(U \cap V)`. It is the snake map of the short exact
sequence of complexes, whose right-hand term computes $`H_{n+1}^{U+V}(X)`, precomposed
with the inverse of the small-simplices isomorphism. The hypotheses that $`U` and $`V` are
open and cover $`X` enter only through that isomorphism, and they are carried as explicit
arguments, so the map depends on the cover data as well as on the two sets.
:::

The three exactness statements below are the Mayer–Vietoris sequence

$$`\cdots \to H_{n+1}(X) \xrightarrow{\ \partial\ } H_n(U \cap V) \to H_n(U) \oplus H_n(V) \to H_n(X) \to \cdots`

written out one node at a time. Each is a literal equality
$`\mathrm{range}\, f = \ker g` between submodules of an explicit $`\Z`-module, which is
the form a consumer wants: to conclude that a class dies one exhibits a preimage, and to
conclude that a class lifts one checks it is killed. With `rightHomologyMap_zero_surjective`
supplying surjectivity onto $`H_0(X)` at the bottom, and `connectingHomomorphism_naturality`
supplying commutativity of the squares relating covers of different spaces, this is the
whole sequence in the form the threefold computations use.

:::theorem "thm:exact-at-intersection" (lean := "Mathoverflow1973.SingularMayerVietoris.exact_at_intersection") (parent := "homology-theory") (uses := "def:connecting-homomorphism")
*Theorem.* Exactness at $`H_n(U \cap V)`: the range of
$`\partial : H_{n+1}(X) \to H_n(U \cap V)` equals the kernel of
$`a \mapsto (i_{U*}a,\ -i_{V*}a)`, the map $`H_n(U \cap V) \to H_n(U) \oplus H_n(V)`
induced by the two inclusions with a sign on the second.
:::

:::proof "thm:exact-at-intersection"
Mathlib's `homology_exact₁` gives exactness of the long sequence of the short exact
sequence of complexes at the first spot, in the categorical form of a `ShortComplex` being
exact; unwinding it through the identification of the homology of a biproduct of complexes
with the product of homologies yields the statement with the small complex in place of
$`C_\bullet(X)`. The connecting map here is that snake map composed with a linear
equivalence, and composing with an equivalence on the source does not change the range, so
the range of $`\partial` is the range of the snake map. The kernel side does not involve
the ambient complex at all. $`\blacksquare`
:::

:::theorem "thm:singular-mayer-vietoris-exact-at-pair" (lean := "Mathoverflow1973.SingularMayerVietoris.exact_at_pair") (parent := "homology-theory") (uses := "def:singular-homology-map, thm:chain-sequence-short-exact, thm:small-inclusion-quasi-iso")
*Theorem.* Let $`U` and $`V` be open with $`U \cup V = X`. Exactness at $`H_n(U) \oplus H_n(V)`: the range of
$`a \mapsto (i_{U*}a, -i_{V*}a)` equals the kernel of
$`(a,b) \mapsto j_{U*}a + j_{V*}b`, the map $`H_n(U) \oplus H_n(V) \to H_n(X)` given by
the sum of the two pushforwards along the inclusions of $`U` and $`V` into $`X`. Neither
of the two maps refers to the small complex, but unlike the short exact sequence of
complexes the statement itself carries the cover hypotheses.
:::

:::proof "thm:singular-mayer-vietoris-exact-at-pair"
The sum-of-pushforwards map into $`H_n(X)` factors as the corresponding map into
$`H_n^{U+V}(X)` followed by the small-simplices isomorphism. That isomorphism is
injective, so the two maps have the same kernel, and the kernel of the small version is
exactly the range of the left map by `homology_exact₂` for the short exact sequence of
complexes. This is the step where the small simplices theorem is doing genuine work: the
sequence of complexes only ever sees $`C^{U+V}_\bullet(X)`, and without the comparison one
would have a Mayer–Vietoris sequence for small homology and no statement about $`X`.
$`\blacksquare`
:::

:::theorem "thm:exact-at-ambient" (lean := "Mathoverflow1973.SingularMayerVietoris.exact_at_ambient") (parent := "homology-theory") (uses := "def:connecting-homomorphism, def:singular-homology-map")
*Theorem.* Exactness at $`H_{n+1}(X)`: the range of
$`H_{n+1}(U) \oplus H_{n+1}(V) \to H_{n+1}(X)` equals the kernel of
$`\partial : H_{n+1}(X) \to H_n(U \cap V)`.
:::

:::proof "thm:exact-at-ambient"
Both sides are transported along the same isomorphism. The sum-of-pushforwards map into
$`H_{n+1}(X)` is the small version followed by `smallHomologyEquiv`, so its range is the
image under that equivalence of the range of the small version; the connecting map is the
small snake map precomposed with the inverse equivalence, so its kernel is the image under
the equivalence of the kernel of the snake map. Exactness of the small sequence at that
spot is `homology_exact₃`, and applying a bijection to both sides of an equality of
submodules preserves it. $`\blacksquare`
:::

Homology alone does not identify the fundamental groups the paper computes, and the route
from $`\pi_1` to $`H_1` is needed for every piece of $`X`: the general fibre, the fibres
over the multiple points, the cusp fibre, and $`X` itself. The degree-one Hurewicz theorem
is therefore proved in full, including an explicitly constructed inverse — the abstract
argument by transversality is not available, and the concrete one turns out to be a
cochain built with the free-basis interface.

:::definition "def:first-hurewicz-hurewicz-map" (lean := "Mathoverflow1973.FirstHurewicz.hurewiczMap") (parent := "homology-theory") (uses := "def:singular-complex")
*Definition.* A loop $`p` at $`b` is a singular $`1`-simplex whose two faces agree, hence
a cycle, and its class in $`H_1(X;\Z)` depends only on the path-homotopy class of $`p`:
the witness is an explicit $`2`-chain with boundary $`p - q` built from a path homotopy.
A second explicit $`2`-chain, with boundary $`q - p\cdot q + p`, shows the assignment is
additive on concatenation, so it is a group homomorphism into
$`H_1(X;\Z)` written multiplicatively, and since the target is abelian it factors through
the abelianization. The Hurewicz map is the resulting $`\Z`-linear map
$`h : \pi_1(X,b)^{\mathrm{ab}} \to H_1(X;\Z)`, where $`\pi_1(X,b)^{\mathrm{ab}}` is the
abelianized fundamental group written additively.
:::

:::definition "def:first-hurewicz-equiv" (lean := "Mathoverflow1973.FirstHurewicz.firstHurewiczEquiv") (parent := "homology-theory") (uses := "def:first-hurewicz-hurewicz-map, def:first-hurewicz-chain-lift")
*Definition.* For a path-connected $`X` with basepoint $`b`, the Hurewicz map is a
$`\Z`-linear isomorphism
$`\pi_1(X,b)^{\mathrm{ab}} \cong H_1(X;\Z)`. The inverse is constructed, not merely shown
to exist. Fix a path $`r_x` from $`b` to each point $`x` — path-connectedness supplies the
choice, and the underlying construction `firstHurewiczEquivOfPaths` takes the family as an
argument. The cochain sending a singular $`1`-simplex $`\sigma` to the class of the loop
$`r_{\sigma(0)} \cdot \sigma \cdot r_{\sigma(1)}^{-1}` extends linearly to
$`C_1(X) \to \pi_1(X,b)^{\mathrm{ab}}` by the free-basis property, kills the boundaries of
$`2`-simplices, and so descends to $`H_1(X;\Z)`. Both composites are the identity, checked
on loop classes in one direction and on cycle classes in the other.
:::

:::definition "def:singular-h1-equiv-of-pi1" (lean := "Mathoverflow1973.FirstHurewicz.singularH1EquivOfPi1") (parent := "homology-theory") (uses := "def:first-hurewicz-equiv")
*Definition.* The corollary that the rest of the development actually calls. If $`X` is
path-connected and its fundamental group at $`b` is isomorphic to an abelian group $`A`
— as a group isomorphism onto $`A` written multiplicatively — then
$`H_1(X;\Z) \cong_\Z A`, compatibly with the Hurewicz function on loops: the class of a
loop $`g` maps to the element of $`A` corresponding to $`g`. Every first-homology
computation downstream has this shape, because the fundamental groups of the fibres and
pieces of $`X` are computed first, by covering-space and van Kampen arguments, and are
abelian when they need to be transported.
:::

:::group "homology-theory-spheres"
The homology of spheres, computed by suspension induction from the circle: the
identification of $`\Sigma S^n` with $`S^{n+1}`, the resulting suspension isomorphism,
$`H_{n+1}(S^{n+1};\Z) \cong \Z` with its fundamental class, and the vanishing of
everything in between.
:::

The comparison target for the whole proof is $`H_*(S^6;\Z)`, so the homology of spheres
has to be available as a theorem about the same object the final statement names: the
metric unit sphere in Euclidean space. It is computed by suspension induction. The base
case is not proved here — $`H_1(S^1) \cong \Z` comes from the circle computation in the
period-torus development, and is transported across three models of the circle: the metric
sphere in $`\R^2`, the unit circle in $`\C`, and $`\R/\Z`.

:::definition "def:sphere-homology-unit-sphere" (lean := "Mathoverflow1973.SphereHomology.UnitSphere") (parent := "homology-theory-spheres")
*Definition.* $`S^n` is the metric sphere of radius $`1` about the origin in
$`\mathrm{EuclideanSpace}\ \R\ (\mathrm{Fin}\ (n{+}1))`, with its subspace topology,
together with a basepoint (the first standard vector), nonemptiness, and compactness. This
is the same model whose case $`n = 6` appears in the final theorem, which is what makes
the sphere computations here usable as statements about the six-sphere rather than about a
homeomorphic copy of it.
:::

:::definition "def:suspension-sphere-homeomorph" (lean := "Mathoverflow1973.SphereHomology.suspensionSphereHomeomorph") (parent := "homology-theory-spheres") (uses := "def:cusp-central-homology-suspension, def:sphere-homology-unit-sphere")
*Definition.* The unreduced suspension of $`S^n` is homeomorphic to $`S^{n+1}`. The map is
latitude coordinates: a point of the suspension is a pair $`(t,x)` with $`t \in [0,1]` and
$`x \in S^n`, modulo collapsing the two ends, and it is sent to the point of $`S^{n+1}`
with height $`h(t) = 2t - 1` in the new coordinate and $`\sqrt{1 - h(t)^2}\, x` in the
remaining ones. This is well defined on the quotient because the radius vanishes at both
ends, continuous, and bijective; the upgrade to a homeomorphism is the compact-to-Hausdorff
principle rather than an explicit inverse.
:::

:::definition "def:unit-sphere-homology-suspension-equiv" (lean := "Mathoverflow1973.SphereHomology.unitSphereHomologySuspensionEquiv") (parent := "homology-theory-spheres") (uses := "def:contractible-cover-homology-higher-equiv, def:homeomorph-homology-equiv, def:suspension-sphere-homeomorph")
*Definition.* The suspension isomorphism for spheres:
$`H_{k+2}(S^{n+1};\Z) \cong H_{k+1}(S^n;\Z)`, $`\Z`-linearly. It is the composite of the
homology equivalence induced by the homeomorphism $`S^{n+1} \cong \Sigma S^n` with the
suspension isomorphism for an arbitrary nonempty space. The latter is Mayer–Vietoris for
the cover of $`\Sigma X` by the two open cones: both are contractible, so above degree one
the connecting map is an isomorphism onto the homology of the intersection, and the
intersection — the open band around the equator — deformation retracts to $`X`. The
indices start at $`k+2` and $`k+1` because exactness makes the connecting map bijective
only where the neighbouring terms $`H_*(U) \oplus H_*(V)` vanish, which for contractible
pieces means positive degrees; degree one is handled separately, and there the connecting
map identifies $`H_1(\Sigma X)` with a kernel rather than with a whole homology group.
:::

:::definition "def:unit-sphere-homology-top-equiv" (lean := "Mathoverflow1973.SphereHomology.unitSphereHomologyTopEquiv") (parent := "homology-theory-spheres") (uses := "def:circle-homology-one-equiv, def:unit-sphere-homology-suspension-equiv")
*Definition.* Top homology of spheres: $`H_{n+1}(S^{n+1};\Z) \cong \Z` for every $`n`,
defined by recursion on $`n`. The base case $`n = 0` is $`H_1(S^1) \cong \Z`, imported
from the circle computation and moved onto the metric circle in $`\R^2` through the
isometry with $`\C` and the identification of the unit circle with $`\R/\Z`. The step is
one application of the suspension isomorphism, which lowers both the space and the degree
by one. The recursion is a definition rather than a theorem because the isomorphism itself,
not merely its existence, is used downstream.
:::

:::definition "def:unit-sphere-top-class" (lean := "Mathoverflow1973.SphereHomology.unitSphereTopClass") (parent := "homology-theory-spheres") (uses := "def:unit-sphere-homology-top-equiv")
*Definition.* The fundamental class $`[S^{n+1}] \in H_{n+1}(S^{n+1};\Z)` is the preimage
of $`1` under the top homology isomorphism. Fixing a generator rather than quantifying
over the two possible ones is what makes degree theory statable: a self-map of the sphere
has a degree, defined by its effect on this class, and the recognition of $`X` as a
homotopy six-sphere ultimately compares a map's action on it with the identity's.
:::

:::theorem "thm:unit-sphere-homology-subsingleton" (lean := "Mathoverflow1973.SphereHomology.unitSphere_homology_subsingleton") (parent := "homology-theory-spheres") (uses := "def:circle-product-homology-equiv, def:unit-sphere-homology-suspension-equiv")
*Theorem.* $`H_k(S^{n+1};\Z) = 0` for every $`k \ne 0` and $`k \ne n+1`. The vanishing is
stated as `Subsingleton`, which for a module is equivalent to being trivial and is the form
that transports along injections without choosing an isomorphism. With
$`H_0(S^{n+1};\Z) \cong \Z` for the path-connected sphere and
$`H_{n+1}(S^{n+1};\Z) \cong \Z` above, this completes the homology of every sphere — the
comparison table against which $`H_*(X;\Z)` is checked.
:::

:::proof "thm:unit-sphere-homology-subsingleton"
Induction on $`n`, with the degree split into three cases at each stage. For $`n = 0` the
claim is that $`H_k(S^1) = 0` for $`k \ge 2`, which is the circle computation transported
across the models of the circle; there it is proved by writing $`S^1` as $`S^1 \times \{*\}`
and applying the splitting
$`H_{n+1}(S^1 \times Y;\Z) \cong H_{n+1}(Y;\Z) \oplus H_n(Y;\Z)`, both of whose summands
vanish for a one-point $`Y` in positive degrees. For the step, degree $`1` is separate: the
suspension of a path-connected space has $`H_1 = 0`, because the connecting map identifies
$`H_1(\Sigma X)` with the kernel of
$`H_0(N \cap S;\Z) \to H_0(N;\Z) \oplus H_0(S;\Z)` for the cone cover, and that kernel
vanishes because the equatorial band is path-connected. In degrees
$`k+2` the suspension isomorphism reduces the claim for $`S^{n+2}` to the claim for
$`S^{n+1}` in degree $`k+1`, where the inductive hypothesis applies since $`k+1 \ne 0` and
$`k+1 \ne n+2` exactly when $`k+2 \ne n+3`. $`\blacksquare`
:::

:::theorem "thm:unit-sphere-simply-connected-space" (lean := "Mathoverflow1973.SphereHomology.unitSphere_simplyConnectedSpace") (parent := "homology-theory-spheres") (uses := "def:suspension-sphere-homeomorph, def:fundamental-group-van-kampen-two-open-cover")
*Theorem.* $`S^{n+2}` is simply connected, as an instance rather than a plain theorem, so
that the simple-connectivity hypothesis of every later statement about spheres is
discharged by instance search. The proof is van Kampen for the cone cover of the
suspension: both cones are contractible and their intersection is path-connected, so the
pushout of trivial groups is trivial, and the conclusion transports along
$`\Sigma S^{n+1} \cong S^{n+2}`. The van Kampen development it uses was adapted from
Mathlib work of Sebastian Kumar {citep kumar.vankampen}[] that had not landed upstream.
The companion statement $`\pi_2(S^{n+3}) = 0` follows from this one through the degree-two
Hurewicz theorem.
:::

The dependency on this chapter is one-directional and heavy. The torus fibres, the cusp
fibre $`W`, the multiple fibres, the Mayer–Vietoris assembly of $`H_*(X;\Z)`, the Hurewicz
ladder that upgrades homology equivalence to homotopy equivalence, and the Morse-theoretic
recognition of $`X` as a topological six-sphere all consume the same four exports:
`SingularHomology`, `singularHomologyMap`, the connecting map with its three exactness
statements, and the sphere computations. Nothing in this chapter refers to the threefold,
and nothing in it is specific to dimension six.
