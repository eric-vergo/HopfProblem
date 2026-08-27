/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — Homology of tori chapter.

The integral singular homology of the fibre tori, built from scratch: homotopy
invariance, a one-circle-factor Künneth equivalence, hand-made chain cross products,
$H_n(T^r) \cong \Z^{\binom{r}{n}}$, and the exterior-power identification on which the
monodromy of the period local system acts by minors.
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

#doc (Manual) "Homology of tori" =>

The general fibre of $`f : X \to \PP^1` is a real four-torus, and everything §7 of
{citet alpoge.s6}[] asks of it is homological: $`H_1(F) = \Lambda`, then
$`H_q(F) = \bigwedge^q \Lambda`, and the monodromy $`A_j` of the period local system
acts on $`H_q(F)` by $`\bigwedge^q A_j`. The paper quotes these as standard, as one
does — Künneth for a product of circles, the Pontryagin product on a topological
group, and the resulting isomorphism $`H_*(T^r) \cong \bigwedge^* H_1(T^r)`
{citep hatcher02}[]. A formalization has no such option, and the development supplies
all of it, on top of its own hand-rolled singular homology rather than on top of a
library theory.

The route taken is deliberately narrow. There is no Eilenberg–Zilber theorem here and
no general Künneth formula; instead there is a single-circle-factor splitting
$`H_{n+1}(S^1 \times X) \cong H_{n+1}(X) \times H_n(X)`, proved by Mayer–Vietoris on
the cover of $`S^1 = \R/\Z` by the two punctured arcs, and iterated against Pascal's
rule $`\binom{r+1}{n+1} = \binom{r}{n+1} + \binom{r}{n}` to reach
$`H_n(T^r) \cong \Z^{\binom{r}{n}}` for all $`r` and $`n`. Chain-level cross products
are constructed by hand, and only in left-degrees $`0`, $`1` and $`2` — the exact
fragment a four-torus requires, and nothing beyond it. The chain homotopies that make
the resulting partial product graded-anticommutative and associative are each a long
explicit boundary computation.

What leaves this chapter is the interface the topological half of the proof consumes:
the model torus $`T^4` with its identification of every flat fibre torus, the marking
$`\Z^4 \cong H_1(T^4)` by winding loops, the fundamental classes, the isomorphism
$`H_4 \cong \Z` that orients a fibre, and — the point of the whole exercise — the
identifications $`H_2(T^4) \cong \bigwedge^2\Z^4` and $`H_3(T^4) \cong \bigwedge^3\Z^4`
made *equivariant* for integer-matrix self-maps of the torus, so that the monodromy
generators act on the fibre homology of the family by their exterior squares and cubes.

:::group "torus-homology"
Integral singular homology of the model tori $`T^r = (\R/\Z)^r`, from homotopy
invariance through the exterior-power description of $`H_2` and $`H_3` of the
four-torus on which the period monodromy acts by minors.
:::

# Homotopy invariance

Functoriality of the file's singular homology and its invariance under homotopy are
the two facts that are *not* reproved: they are imported from Mathlib's
`AlgebraicTopology.singularHomologyFunctor` and `TopCat.Homotopy`, and adapted by
`congrArg ModuleCat.Hom.hom` shims to the concrete `SingularHomology` of this
development. Everything downstream in the chapter is stated for the concrete theory,
so the packaging matters.

:::definition "def:homotopy-equiv-homology-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.homotopyEquivHomologyEquiv") (parent := "torus-homology") (uses := "def:singular-homology-map")
*Definition.* A homotopy equivalence $`e : X \simeq_h Y` induces, in each degree $`n`,
a $`\Z`-linear isomorphism $`H_n(X;\Z) \cong H_n(Y;\Z)` of singular homology.

The isomorphism is not abstract: its forward map is literally the pushforward
`singularHomologyMap e.toFun n` and its inverse the pushforward along `e.invFun`. Both
inverse identities come from the theorem that homotopic maps induce equal maps on
homology, applied to the two homotopies $`e^{-1}e \simeq \mathrm{id}` and
$`e e^{-1} \simeq \mathrm{id}` carried by the Lean structure `X ≃ₕ Y`, together with
functoriality of the pushforward.
:::

:::definition "def:homeomorph-homology-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.homeomorphHomologyEquiv") (parent := "torus-homology") (uses := "def:homotopy-equiv-homology-equiv")
*Definition.* A homeomorphism $`e : X \simeq_t Y` induces a $`\Z`-linear isomorphism
$`H_n(X;\Z) \cong H_n(Y;\Z)` for every $`n`, whose forward map is the pushforward along
$`e` viewed as a continuous map.

Formally it is the previous construction applied to `e.toHomotopyEquiv`. This is the
workhorse of the whole file — over a hundred call sites — because the development
computes homology only for the model spaces $`S^1`, $`T^r` and their products, and
transports the answer to every space that arises geometrically by exhibiting a
homeomorphism to a model.
:::

:::definition "def:connected-homology-zero-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.connectedHomologyZeroEquiv") (parent := "torus-homology") (uses := "def:singular-homology")
*Definition.* For a path-connected space $`X`, the augmentation is an isomorphism
$`H_0(X;\Z) \cong \Z`.

The hypothesis enters as the instance `PathConnectedSpace X`, and the map is Mathlib's
degree-zero augmentation comparison `singularHomology₀ε`, turned into a linear
equivalence by `asIso`. Specialized at the one-point space this is
`pointHomologyZeroEquiv`, which is the base case of every homology computation in the
chapter; its companion facts are that a totally disconnected space has vanishing
homology in positive degrees, and hence so does a contractible one.
:::

# One circle factor

The circle used throughout is $`\R/\Z` rather than the unit circle in $`\C`, and it is
covered by two arcs, each obtained by deleting a point. Both arcs are contractible and
their intersection has two contractible components; crossing this cover with an
arbitrary space $`X` and feeding it to the Mayer–Vietoris sequence of the development
produces a splitting of $`H_*(S^1 \times X)` that needs only one piece of pure algebra.

:::definition "def:split-exact-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.splitExactEquiv") (parent := "torus-homology")
*Definition.* Given $`\Z`-linear maps $`i : A \to B`, $`p : B \to A` and
$`d : B \to C` with $`p \circ i = \mathrm{id}_A`, $`\mathrm{range}\,i = \ker d`, and
$`d` surjective, the map $`b \mapsto (p\,b,\, d\,b)` is an isomorphism
$`B \cong A \times C`.

This is the split-exactness lemma in exactly the form the Mayer–Vietoris output
presents itself: a retraction and a boundary map, with exactness stated as the single
equality $`\mathrm{range}\,i = \ker d`. Nothing is assumed about $`A`, $`B`, $`C`
beyond being $`\Z`-modules, and no long exact sequence is invoked — the isomorphism is
built directly from the bijectivity of $`b \mapsto (p\,b, d\,b)`.
:::

:::definition "def:circle-topology-circle" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.CircleTopology.Circle") (parent := "torus-homology")
*Definition.* The model circle is $`S^1 := \R/\Z`, in Lean the additive circle
`AddCircle (1 : ℝ)`, covered by the arcs $`\mathrm{arcU} = S^1 \setminus \{0\}` and
$`\mathrm{arcV} = S^1 \setminus \{1/2\}`.

Both arcs are contractible, their union is $`S^1`, and their intersection has exactly
two contractible components — the data every Mayer–Vietoris argument in the file
consumes, in over two hundred places. Taking the quotient of $`\R` rather than the unit
circle in $`\C` is what makes the coordinate description of $`T^r` below immediate; it
does duplicate Mathlib's own `Circle`, and the two are reconciled only later, by an
explicit homeomorphism used when the sphere enters the argument.
:::

:::definition "def:circle-boundary" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.circleBoundary") (parent := "torus-homology") (uses := "def:circle-topology-circle, def:connecting-homomorphism, thm:exact-at-ambient")
*Definition.* The Mayer–Vietoris connecting map of the cover
$`\{\mathrm{arcU} \times X,\ \mathrm{arcV} \times X\}` of $`S^1 \times X`, followed by
the identification of the homology of the two-component intersection with
$`H_n(X) \times H_n(X)` and projection to the first factor, is a surjection
$`\partial : H_{n+1}(S^1 \times X) \to H_n(X)`.

The sign is explicit — `circleBoundary` is *minus* the first coordinate — chosen so
that the boundary of the positive loop crossed with a class is that class rather than
its negative. Its kernel is exactly the image of the section $`x \mapsto (0,x)`, which
is where exactness of the Mayer–Vietoris sequence at the ambient space is used.
:::

:::definition "def:circle-product-homology-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.circleProductHomologyEquiv") (parent := "torus-homology") (uses := "def:circle-topology-circle, def:circle-boundary, def:split-exact-equiv, def:homotopy-equiv-homology-equiv, thm:exact-at-ambient, thm:exact-at-intersection")
*Definition.* Künneth for one circle factor: for every space $`X` and every $`n`,
$$`H_{n+1}(S^1 \times X;\Z) \;\cong\; H_{n+1}(X;\Z) \times H_n(X;\Z),`
by the map sending a class to its pushforward along the projection $`S^1 \times X \to X`
together with its Mayer–Vietoris boundary.

The proof is the split-exactness lemma applied to the section $`x \mapsto (0,x)`, the
projection, and the boundary: the section splits the projection, the boundary is
surjective, and exactness at the intersection and at the ambient space of the
Mayer–Vietoris sequence identifies the range of the section with the kernel of the
boundary. Contractibility of the arcs enters through homotopy invariance, which is what
collapses the homology of the cover to copies of $`H_*(X)`. Every homology computation
in the chapter is an iteration of this one equivalence.
:::

:::definition "def:circle-homology-one-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.circleHomologyOneEquiv") (parent := "torus-homology") (uses := "def:circle-product-homology-equiv, def:homeomorph-homology-equiv, def:connected-homology-zero-equiv")
*Definition.* $`H_1(S^1;\Z) \cong \Z`.

Taking $`X` to be a point in the previous equivalence gives
$`H_1(S^1) \cong H_1(\mathrm{pt}) \times H_0(\mathrm{pt})`; the first factor vanishes
because a point is totally disconnected, the second is $`\Z` by the augmentation, and
the homeomorphism $`S^1 \cong S^1 \times \mathrm{pt}` supplies the comparison. The same
argument in degrees $`\ge 2` gives $`H_{n+2}(S^1) = 0`. A companion identity records
the normalization that matters later: the class of the degree-one loop
$`t \mapsto t \bmod 1` goes to $`1`.
:::

# Cross products by hand

Multiplicative structure on homology cannot be borrowed here, so it is built at chain
level. Two locally-scoped instances — $`\Z`-module structures on spaces of linear maps
and on tensor products — carry the bilinear algebra; they are attached declaration by
declaration with `attribute [local instance] … in` rather than made global, which is
why they end up the two most-referenced declarations in the entire file. The
construction itself is a recursive cone on formal simplices, transported to singular
chains by naturality.

:::definition "def:cross-product-edge" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.crossProductEdge") (parent := "torus-homology") (uses := "def:singular-complex")
*Definition.* A bilinear chain-level cross product
$`C_1(X) \times C_n(Y) \to C_{n+1}(X \times Y)`, determined on singular simplices
$`\sigma : \Delta^1 \to X` and $`\tau : \Delta^n \to Y` by pushing a universal chain on
$`\Delta^1 \times \Delta^n` forward along $`\sigma \times \tau`.

The universal chain is a formal triangulation of the prism $`\Delta^1 \times \Delta^n`,
built by an explicit recursive cone construction on vertex tuples and carried into
singular chains by the affine comparison map. The Leibniz rule
$`\partial(a \times b) = (\partial a) \times b - a \times (\partial b)` is proved for it
directly, so a cycle crossed with a cycle is a cycle. A degree-two analogue
$`C_2(X) \times C_n(Y) \to C_{n+2}(X \times Y)` is constructed the same way; those two
degrees, with the trivial degree-zero case, are all the file ever needs.
:::

:::definition "def:cross-product-homology" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.crossProductHomology") (parent := "torus-homology") (uses := "def:singular-complex, def:cross-product-edge")
*Definition.* The homology cross product
$`H_1(X;\Z) \otimes H_n(Y;\Z) \to H_{n+1}(X \times Y;\Z)`, obtained by descending the
chain-level product to homology classes.

In Lean the map is *curried* — a $`\Z`-linear map
$`H_1(X) \to (H_n(Y) \to H_{n+1}(X\times Y))` — rather than a map out of a tensor
product; the tensor notation here is the informal reading. Descent is by the universal property of homology in the
first variable, using that the chain product of a boundary with a cycle is a boundary.
The product is natural in both variables, and explicit swap, mixed-swap and associator
chain homotopies — each a long boundary computation with its own defect term — give
graded anticommutativity after pushforward along the swap of factors, associativity,
and cyclic invariance.
:::

:::definition "def:positive-circle-cross" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.positiveCircleCross") (parent := "torus-homology") (uses := "def:cross-product-homology, def:circle-topology-circle, def:circle-boundary")
*Definition.* Crossing with the class of the positive degree-one loop is a map
$`H_n(X) \to H_{n+1}(S^1 \times X)`, $`b \mapsto [\,t \mapsto t \bmod 1\,] \times b`.

It is a section of the Mayer–Vietoris boundary: the composite
$`\partial \circ (\text{cross})` is the identity, proved by writing the loop's class as
an explicit small cycle adapted to the two-arc cover and running it through the
connecting map. Consequently the inverse of the circle Künneth equivalence is the sum
of the obvious section and this cross product, which is what makes the splitting
canonical rather than merely existent, and natural in $`X`.
:::

# The homology of the model torus

:::definition "def:period-torus-higher-homology-product-torus" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.ProductTorus") (parent := "torus-homology") (uses := "def:circle-topology-circle")
*Definition.* The model $`n`-torus $`T^n := (\R/\Z)^n`, in Lean the function type
`Fin n → AddCircle (1 : ℝ)` with its product topology and its coordinatewise group
structure.

Splitting off the zeroth coordinate is a homeomorphism $`T^{n+1} \cong S^1 \times T^n`,
and $`T^0` is a point; those two facts, with the circle Künneth equivalence, are the
whole induction. The type is an `abbrev`, so the group and topology instances on
function types apply to it without transport — a small choice with large consequences,
since $`T^n` is then literally a topological abelian group and the Pontryagin product
applies to it directly.
:::

:::definition "def:flat-torus-circle-homeomorph" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.flatTorusCircleHomeomorph") (parent := "torus-homology") (uses := "def:lattice, def:period-torus-higher-homology-product-torus")
*Definition.* The flat torus $`\R^4/L` of the period family, where $`L` is the standard
lattice $`\Z^4 \subset \R^4`, is homeomorphic to the model torus $`T^4` by the map
induced from coordinatewise reduction modulo $`\Z`.

The map is a group isomorphism, and the homeomorphism is obtained the compact way — a
continuous closed bijection — rather than by exhibiting a continuous inverse. Composed
with the identification of a period fibre with the flat torus, it gives
$`p.\mathrm{Torus} \simeq_t T^4` for every point $`p` of the period domain, so a single
computation on the model torus serves every fibre of the family at once.
:::

:::definition "def:product-torus-homology-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.productTorusHomologyEquiv") (parent := "torus-homology") (uses := "def:circle-product-homology-equiv, def:homeomorph-homology-equiv, def:period-torus-higher-homology-product-torus, def:connected-homology-zero-equiv")
*Definition.* For all $`r` and $`n`,
$$`H_n(T^r;\Z) \;\cong\; \Z^{\binom{r}{n}},`
the right-hand side being `Fin (r.choose n) → ℤ`.

The definition is a recursion on both indices with three clauses. In degree $`0` the
torus is path-connected and the augmentation gives $`\Z \cong \Z^{\binom{r}{0}}`; over
$`T^0`, a point, all positive degrees vanish; and in the general case
$`H_{n+1}(T^{r+1})` is carried by $`T^{r+1} \cong S^1 \times T^r` and the circle
Künneth equivalence to $`H_{n+1}(T^r) \times H_n(T^r)`, which the recursion identifies
with $`\Z^{\binom{r}{n+1}} \times \Z^{\binom{r}{n}}`, and Pascal's rule
$`\binom{r+1}{n+1} = \binom{r}{n+1} + \binom{r}{n}` — realized as an explicit
re-indexing bijection on `Fin` — closes the induction. The composite is assembled as
additive equivalences and upgraded to $`\Z`-linear at the end.
:::

:::theorem "thm:product-torus-homology-finrank" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.productTorus_homology_finrank") (parent := "torus-homology") (uses := "def:product-torus-homology-equiv")
*Theorem.* $`\mathrm{rank}_{\Z}\, H_n(T^r;\Z) = \binom{r}{n}`.

The companion statements record the rest of the structure transported along the same
equivalence: $`H_n(T^r;\Z)` is free and finitely generated, hence torsion-free, and it
vanishes for $`n > r` because $`\binom{r}{n} = 0` there. Torsion-freeness is not a
decoration — it is the hypothesis under which the Pontryagin pairing below is
alternating rather than merely skew, and therefore the hypothesis under which the
exterior-power description exists at all.
:::

:::proof "thm:product-torus-homology-finrank"
Immediate from the isomorphism $`H_n(T^r;\Z) \cong \Z^{\binom{r}{n}}`, whose target has
rank $`\binom{r}{n}` by the standard rank of a finite free module.

The content is in the isomorphism. Cover the circle factor of
$`T^{r+1} \cong S^1 \times T^r` by the two punctured arcs; both are contractible and
their intersection has two contractible components, so the Mayer–Vietoris sequence
degenerates into a short exact sequence split by the section $`x \mapsto (0,x)`, giving
$`H_{n+1}(S^1 \times T^r) \cong H_{n+1}(T^r) \times H_n(T^r)`. Induct on $`r`: the base
$`T^0` is a point, degree $`0` is the augmentation on a path-connected space, and the
inductive step matches the splitting against Pascal's rule. The bookkeeping that makes
this a definition rather than a rank count is the re-indexing bijection
$`\mathrm{Fin}\binom{r+1}{n+1} \cong \mathrm{Fin}\binom{r}{n+1} \sqcup \mathrm{Fin}\binom{r}{n}`,
which is where the eventual identification of the summands with subsets of coordinates
is fixed. $`\blacksquare`
:::

# Multiplicative structure

:::definition "def:torus-matrix-map" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.torusMatrixMap") (parent := "torus-homology") (uses := "def:period-torus-higher-homology-product-torus")
*Definition.* An integer matrix $`A \in M_{m \times n}(\Z)` induces a continuous
homomorphism $`T^n \to T^m`, $`x \mapsto Ax`, the $`i`-th coordinate of the image being
$`\sum_j A_{ij}\, x_j` computed in $`\R/\Z`.

The identity matrix gives the identity map and a matrix product gives the composite, so
the assignment is functorial; and reduction modulo $`\Z` intertwines it with ordinary
matrix–vector multiplication on $`\R^n`. This is how the monodromy of the period local
system acts on fibres: the generators are integer matrices, and the induced self-maps
of $`T^4` are the objects whose pushforwards on $`H_2` and $`H_3` the last section of
this chapter computes.
:::

:::definition "def:period-torus-higher-homology-pontryagin-product" (lean := "Mathoverflow1973.PeriodTorusHigherHomologyPontryagin.product") (parent := "torus-homology") (uses := "def:cross-product-homology, def:singular-homology-map")
*Definition.* For a topological abelian group $`G`, the Pontryagin product
$`H_1(G;\Z) \otimes H_n(G;\Z) \to H_{n+1}(G;\Z)` is the homology cross product followed
by the pushforward along the addition map $`G \times G \to G`.

As with the cross product, the Lean form is curried and bilinear rather than defined on
a tensor product. It is natural for continuous additive maps: a map of topological
abelian groups intertwines the products, because it intertwines the addition maps.
Iterating gives a triple product $`H_1^{\otimes 3} \to H_3`, cyclically invariant with no
hypothesis at all, and — once $`H_2(G)` is torsion-free — vanishing whenever two of its
three arguments agree.
:::

:::definition "def:product-torus-top-class" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.productTorusTopClass") (parent := "torus-homology") (uses := "def:product-torus-homology-equiv")
*Definition.* The fundamental class $`[T^n] \in H_n(T^n;\Z)`, defined as the preimage
of $`1` under the isomorphism $`H_n(T^n;\Z) \cong \Z^{\binom{n}{n}} = \Z`.

It is worth being precise about what this is and is not: no orientation of $`T^n` is
constructed, and no top-degree duality is invoked — the class is *defined* by the
computed isomorphism, and its properties are read off from that definition. The
identity that makes it usable is
$`[T^{n+1}] = [\text{coordinate loop}] \cdot [\,\text{tail}_*[T^n]\,]` for the
Pontryagin product, so that in low degrees $`[T^2]` and $`[T^3]` are products of
classes of coordinate loops; that is the form in which pushforwards of fundamental
classes are recognized inside the images of the lattice wedge maps later.
:::

:::theorem "thm:product11-skew" (lean := "Mathoverflow1973.PeriodTorusHigherHomologyPontryagin.product11_skew") (parent := "torus-homology") (uses := "def:period-torus-higher-homology-pontryagin-product, def:cross-product-homology")
*Theorem.* The Pontryagin pairing $`H_1(G) \times H_1(G) \to H_2(G)` of a topological
abelian group is antisymmetric: $`a \cdot b = -\,b \cdot a`.

When $`H_2(G)` is torsion-free — which for the tori of this chapter is one of the
corollaries of the rank computation — antisymmetry upgrades to alternating,
$`a \cdot a = 0`, and the pairing therefore factors through $`\bigwedge^2 H_1(G)`.
That factorization, together with its degree-three analogue through
$`\bigwedge^3`, is what turns a marking $`\Z^4 \cong H_1` into candidate maps
$`\bigwedge^2\Z^4 \to H_2` and $`\bigwedge^3\Z^4 \to H_3`.
:::

:::proof "thm:product11-skew"
Anticommutativity is inherited from the cross product. Pushing a cross product forward
along a map that swaps the two factors reverses the sign in these degrees, by the
explicit swap chain homotopy constructed for the chain-level product. The addition map
of an abelian group is invariant under the swap of $`G \times G` — this is exactly
`add_comm`, and it is discharged as such — so the two composites
$`a \times b \mapsto \mathrm{add}_*(a \times b)` and
$`b \times a \mapsto \mathrm{add}_*(b \times a)` differ by that sign alone. Skewness
plus torsion-freeness of the target gives $`a \cdot a = 0` by the usual argument
$`2(a\cdot a) = 0`. $`\blacksquare`
:::

# Exterior powers and the monodromy action

The remaining step converts the abstract rank count into the description the period
local system needs. The coordinate loops mark $`H_1(T^4)` by $`\Z^4`; the Pontryagin
product carries wedges of those markings into $`H_2` and $`H_3`; and both wedge maps
turn out to be isomorphisms, checked by surjectivity onto the coordinate-subtorus basis
together with equality of ranks. Equivariance for `torusMatrixMap` then reduces the
monodromy action on fibre homology to exterior powers of integer matrices.

:::definition "def:real-torus-h4-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.realTorusH4Equiv") (parent := "torus-homology") (uses := "def:flat-torus-circle-homeomorph, def:product-torus-homology-equiv")
*Definition.* $`H_4(\R^4/L;\Z) \cong \Z` for the flat four-torus.

Transport the model computation along the homeomorphism $`\R^4/L \simeq_t T^4` and then
along $`\binom{4}{4} = 1`. The Lean composite reuses the degree-zero comparison
$`\Z \cong \Z^{\binom{4}{0}}` in the last step, which typechecks because
$`\binom{4}{4}` and $`\binom{4}{0}` both reduce to $`1` and the two index types are
definitionally `Fin 1`. This is the isomorphism that orients a torus fibre, and the
degree-four analogue for the period fibres $`p.\mathrm{Torus}` follows the same route.
:::

:::theorem "thm:standard-exterior-map-coefficient" (lean := "Mathoverflow1973.PeriodTorusHigherHomologyExterior.standardExterior_map_coefficient") (parent := "torus-homology")
*Theorem.* In the basis of $`\bigwedge^n(\Z^m)` indexed by $`n`-element subsets of
$`\{1,\dots,m\}`, the matrix coefficient of $`\bigwedge^n A` at a pair of subsets
$`(s,t)` is $`\det A_{s,t}`, the minor of $`A` on rows $`s` and columns $`t`.

Exterior powers act by minors — the classical statement, in the form a machine can use.
It is what makes the monodromy action computable: the exterior square of a
$`4 \times 4` integer matrix is an explicit $`6 \times 6` integer matrix of
two-by-two minors and its exterior cube an explicit $`4 \times 4` matrix of
three-by-three minors, so the exterior squares and cubes of the monodromy generators
$`A_1`, $`A_2` and $`M_0` are settled by `decide` on concrete integer matrices rather
than by an argument.
:::

:::definition "def:coordinate-h1-four-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.coordinateH1FourEquiv") (parent := "torus-homology") (uses := "def:lattice, def:flat-torus-circle-homeomorph, def:homeomorph-homology-equiv, def:period-domain, def:singular-complex")
*Definition.* The marking $`\Lambda = \Z^4 \cong H_1(T^4;\Z)`, sending a winding vector
$`v` to the class of the loop $`t \mapsto (t v_i \bmod 1)_i`.

The underlying map is defined for every $`n` as the linear extension of
$`e_i \mapsto [\,i\text{-th coordinate loop}\,]`, and in dimension $`4` it sends $`v` to
the class of the single winding-$`v` loop. Bijectivity is what needs an argument, and
it is obtained by comparison: the marking agrees with the period marking of any fibre
under the identification $`p.\mathrm{Torus} \simeq_t T^4`. That is why the Lean
declaration carries a point $`p` of the period domain as an argument even though the
map itself does not depend on it — $`p` supplies the proof, not the data. The marking
is equivariant for integer matrices: pushforward along `torusMatrixMap A` corresponds
to $`v \mapsto Av`.
:::

:::definition "def:coordinate-torus-h2-exterior-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv") (parent := "torus-homology") (uses := "def:lattice, def:singular-homology, def:coordinate-h1-four-equiv, def:period-torus-higher-homology-pontryagin-product, thm:product11-skew, def:product-torus-top-class, def:torus-matrix-map, thm:standard-exterior-map-coefficient")
*Definition.* $`H_2(T^4;\Z) \cong \bigwedge^2 \Z^4`, as the inverse of the wedge map
$`\bigwedge^2\Lambda \to H_2(T^4)` sending $`v \wedge w` to
$`[\text{loop } v] \cdot [\text{loop } w]`.

The wedge map exists because the Pontryagin pairing on $`H_1` is alternating once
$`H_2(T^4)` is known to be torsion-free. It is surjective because the classes of the
coordinate two-subtori — pushforwards of the fundamental class $`[T^2]` along the
coordinate inclusions — form a basis of $`H_2(T^4)`, and each is the wedge of two
coordinate markings; surjectivity plus the equality of ranks $`\binom{4}{2} = 6`
forces bijectivity. The identification is equivariant: pushforward along
`torusMatrixMap A` corresponds to $`\bigwedge^2 A`, which in coordinates
$`H_2(T^4) \cong \Z^6` is the $`6 \times 6` matrix of two-by-two minors of $`A`.
:::

:::definition "def:coordinate-torus-h3-exterior-equiv" (lean := "Mathoverflow1973.PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv") (parent := "torus-homology") (uses := "def:lattice, def:period-torus-higher-homology-product-torus, def:coordinate-h1-four-equiv, def:period-torus-higher-homology-pontryagin-product, def:product-torus-top-class, thm:product-torus-homology-finrank, def:torus-matrix-map, thm:standard-exterior-map-coefficient")
*Definition.* $`H_3(T^4;\Z) \cong \bigwedge^3 \Z^4`, inverse to the triple-product map
$`u \wedge v \wedge w \mapsto [\text{loop } u]\cdot[\text{loop } v]\cdot[\text{loop } w]`.

The argument is the degree-three repetition of the previous one, against the basis of
coordinate three-subtori and the rank $`\binom{4}{3} = 4`; the inverse of the
identification sends a decomposable wedge to the iterated Pontryagin product of the
three corresponding loop classes. Equivariance again reads
$`(\text{torusMatrixMap } A)_* \leftrightarrow \bigwedge^3 A`, so in the coordinates
$`H_2(T^4) \cong \Z^6` and $`H_3(T^4) \cong \Z^4` the monodromy generators
$`A_1, A_2, M_0` act by the explicit integer matrices $`\bigwedge^2 A_j`,
$`\bigwedge^3 A_j` of the local-system data. That is precisely the input the twisted
Mayer–Vietoris and Leray computations of $`H_*(X)` consume: the fibre homology in
degrees $`1`, $`2`, $`3` with its monodromy, as concrete integer matrices.
:::
