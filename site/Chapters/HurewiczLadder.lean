/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — Hurewicz ladder chapter.

The from-scratch Hurewicz theorem in degrees two through six, built over the chapter's own
singular homology, together with the naturality square that powers the Whitehead step.
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

#doc (Manual) "The Hurewicz ladder" =>

Lemma 8.2 of {citet alpoge.s6}[] is the recognition principle that turns the homological
output of Section 7 into a homotopy sphere: a closed smooth simply connected $`n`-manifold
with the reduced integral homology of $`S^n` is homotopy equivalent to $`S^n`. Its proof is
three lines of classical citation — the Hurewicz theorem applied inductively in degrees
$`2, \dots, n`, naturality of the Hurewicz map, and the homology Whitehead theorem, all
from {citep hatcher02}[]. Mathlib supplies none of it above degree one. This chapter is the
missing induction, carried out one degree at a time.

What is proved is the Hurewicz isomorphism in exactly the range the argument needs, for an
arbitrary topological space. For each $`n` between $`2` and $`6`, given
`[SimplyConnectedSpace X]`, a point $`x \in X`, and `[Subsingleton (π_ k X x)]` for every
$`2 \le k < n`, there is an isomorphism $`\pi_n(X,x) \cong H_n(X;\Z)`. It appears in two
forms, because Mathlib writes homotopy groups multiplicatively and homology as a
$`\Z`-module: a linear equivalence `hurewiczLinearEquiv` from `Additive (π_ n X x)` to
$`H_n(X;\Z)`, and a multiplicative equivalence `hurewiczPiNEquiv` from $`\pi_n(X,x)` to
`Multiplicative` of $`H_n(X;\Z)`. The vanishing hypotheses are instance arguments phrased
as `Subsingleton` rather than as equations, so the rungs stack by instance resolution: once
a space is known to have subsingleton $`\pi_2, \pi_3, \pi_4, \pi_5` at $`x`, the sixth rung
applies with no further bookkeeping.

The ladder is five hand-instantiated copies of one schema rather than a single theorem
parametric in $`n`, and it is the largest single cluster in the subject: 2192
declarations, 594 of them definitions and 1553 theorems, with no docstrings. Each rung
builds a forward map explicitly at chain level and an inverse by a straightening program
whose tower grows one storey taller with each degree, which is why the parametric statement
was never attempted; the parts that are genuinely uniform in $`n` — based simplices, the
staircase triangulation of the cube, the null-homotopy engine, the cube subdivision
identity — are factored into a shared toolbox. Two consumers wait at the top. For the
standard six-sphere and for the threefold alike, the lower rungs convert vanishing homology
into vanishing homotopy in degrees two through five, and the sixth rung then gives
$`\pi_6(X) \cong H_6(X;\Z) \cong \Z`; naturality of that isomorphism turns an
$`H_6`-isomorphism $`S^6 \to X` into a bijection on $`\pi_6`, and its injectivity makes two
based maps out of $`S^6` with equal top homology classes based homotopic. Those are the two
Whitehead-step inputs to the homotopy equivalence $`X \simeq S^6`.

:::group "hurewicz"
Degree two, where the whole method is visible: the Hurewicz homomorphism as an explicit
pushforward of the fundamental chain of the square, the face-coherence predicate that lets
simplex-wise homotopies assemble into chain maps, a hand-built homotopy extension property
for the pair $`(\Delta^n, \partial\Delta^n)`, the tetrahedron relation that makes the
inverse kill boundaries, and the resulting isomorphism $`\pi_2(X,x) \cong H_2(X;\Z)` for
simply connected $`X`.
:::

:::definition "def:based-simplex" (lean := "Mathoverflow1973.HigherHurewicz.BasedSimplex") (parent := "hurewicz")
*Definition.* A based $`n`-simplex at $`x \in X` is a continuous map
$`\tau : \Delta^n \to X` that is constant equal to $`x` on the boundary
$`\partial\Delta^n = \{s \in \Delta^n : s_i = 0 \text{ for some } i\}`, the union of the
closed faces. It is recorded as a subtype of $`C(\Delta^n, X)`, so the basing condition
travels with the map rather than as a side hypothesis. Every such $`\tau` determines an
element of $`\pi_n(X,x)`: precomposing with the quotient $`I^n \to \Delta^n` that collapses
the boundary cube onto the boundary simplex turns $`\tau` into a cube loop in Mathlib's
sense. This subtype is the currency in which every inverse map of the ladder is written —
the straightening programs all produce based simplices, and the class operators all read
their classes.
:::

:::definition "def:square-chain" (lean := "Mathoverflow1973.SecondHurewicz.squareChain") (parent := "hurewicz") (uses := "def:singular-complex")
*Definition.* For a cube loop $`p \in \mathrm{GenLoop}(\mathrm{Fin}\,2, X, x)`, the singular
$`2`-chain $`\mathrm{squareChain}(p) \in C_2(X)` is the suspension of the path chain of
$`p` regarded as a path in the based loop space: `GenLoop.toLoop 0 p` is that path of loops,
`pathChain` is its fundamental $`1`-chain, and `suspensionOne` sweeps a $`1`-chain of loops
into a $`2`-chain by the loop-space evaluation map. Concretely it is the image of the
fundamental $`2`-chain of the square under $`p`, the fundamental chain being the
Eilenberg–Zilber cross product of the fundamental $`1`-chain of $`[0,1]` with itself,
transported through the identification $`I \times I \cong (\mathrm{Fin}\,2 \to I)`. Its
boundary vanishes, since the boundary of the path chain of a loop vanishes, so it is a
cycle `squareCycle p`.
:::

:::definition "def:second-hurewicz-hurewicz-map" (lean := "Mathoverflow1973.SecondHurewicz.hurewiczMap") (parent := "hurewicz") (uses := "def:singular-homology, def:square-chain")
*Definition.* The degree-two Hurewicz homomorphism is the $`\Z`-linear map
$$`h_2 : \mathrm{Additive}\,\pi_2(X,x) \longrightarrow H_2(X;\Z), \qquad
[p] \longmapsto [\mathrm{squareCycle}(p)].`
No hypothesis is placed on $`X` beyond being a topological space; simple connectivity
enters only when the inverse is built. Well-definedness is homotopy invariance of the
square cycle class, and additivity is the statement that concatenating two cube loops in
the zeroth coordinate adds their square classes, proved from an explicit prism chain
subdividing the product square into four triangles. Linearity over $`\Z` is then automatic,
since the source is the abelian group $`\pi_2(X,x)` written additively and any additive map
between $`\Z`-modules is $`\Z`-linear.
:::

The remainder of degree two is the inverse, and it occupies more than three thousand lines.
The obstruction is that a singular $`2`-simplex of $`X` is not a based map, so it has no
class in $`\pi_2(X,x)`; it must first be deformed until its vertices, and then its edges,
sit at the basepoint. Doing that for one simplex is easy. Doing it for all simplices at
once, compatibly with taking faces, so that the resulting assignment respects the boundary
operator and descends to homology, is the entire difficulty, and it is managed by a single
predicate.

:::definition "def:face-compatible-homotopies" (lean := "Mathoverflow1973.SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies") (parent := "hurewicz")
*Definition.* Let $`H` assign to each singular $`n`-simplex $`\sigma` of $`X` a homotopy
$`H(\sigma) : I \times \Delta^n \to X`, and let $`H'` do the same in dimension $`n+1`. The
pair is face compatible when
$$`H'(\sigma) \circ (\mathrm{id}_I \times \delta_i) = H(\sigma \circ \delta_i)`
for every $`(n{+}1)`-simplex $`\sigma` and every coface $`\delta_i`. In words: deforming a
simplex and then restricting to a face gives the same result as restricting first and
deforming the face. This is the coherence that makes a simplex-wise family of deformations
behave like a chain-level construction, and it is the workhorse of the cluster, with 63
declarations referring to it. It is stated as a `Prop` on the pair of families, so a
straightening tower carries its coherence as a proof term propagated from stage to stage.
:::

:::definition "def:extend-coherent-simplex-homotopy" (lean := "Mathoverflow1973.SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy") (parent := "hurewicz") (uses := "def:face-compatible-homotopies")
*Definition.* Given a face-compatible pair $`(H, H')` in dimensions $`n` and $`n+1` with
$`H'(\sigma)(0, \cdot) = \sigma`, the construction produces for each $`(n{+}2)`-simplex
$`\sigma` a homotopy $`I \times \Delta^{n+2} \to X` extending the deformations already
chosen on the faces of $`\sigma`. The faces of $`\sigma` are $`(n{+}1)`-simplices, so
$`H'` deforms each of them; face compatibility is exactly what makes those deformations
agree on shared $`n`-faces, so they glue to a continuous map on
$`(\{0\} \times \Delta^{n+2}) \cup (I \times \partial\Delta^{n+2})` that starts at
$`\sigma`. `cylinderRetraction` is a hand-built continuous retraction of the whole cylinder
onto that subspace, written from explicit minimum-coordinate and denominator formulas, and
composing with it extends the glued map. The companion lemmas say the result again starts
at the identity and is again face compatible, so the construction can be iterated. This is
the homotopy extension property of $`(\Delta^{n+2}, \partial\Delta^{n+2})`, proved by hand
because no such retraction is available off the shelf.
:::

:::theorem "thm:normalized-triangle-boundary-relation" (lean := "Mathoverflow1973.SecondHurewicz.SimplyConnected.normalizedTriangle_boundary_relation") (parent := "hurewicz") (uses := "def:extend-coherent-simplex-homotopy")
*Theorem.* Let $`X` be simply connected, $`x \in X`, and $`\sigma` a singular
$`3`-simplex of $`X`. Then
$$`\sum_{i=0}^{3} (-1)^i \, \big[\mathrm{normalizedTriangle}(\sigma \circ \delta_i)\big] = 0
\quad\text{in } \mathrm{Additive}\,\pi_2(X,x).`
Here $`\mathrm{normalizedTriangle}` is the based triangle obtained from an arbitrary
singular $`2`-simplex by two stages of straightening: first the three vertices are dragged
to $`x` along chosen paths supplied by path connectivity, then the three edges are pulled
onto the constant loop along chosen null-homotopies supplied by simple connectivity. The
class of a based triangle is read in $`\pi_2(X,x)` through the quotient
$`I^2 \to \Delta^2`. The alternating sum is the image of the boundary of $`\sigma`, so the
theorem is the assertion that straightening followed by taking classes annihilates
boundaries.
:::

:::proof "thm:normalized-triangle-boundary-relation"
The straightening tower is run one dimension up: $`\sigma` itself is normalized to a based
tetrahedron $`T`, and `normalizedTetrahedron_face` identifies the $`i`-th face of $`T` with
the normalized $`i`-th face of $`\sigma`, so the claim reduces to the signed relation among
the four faces of an arbitrary based tetrahedron. That relation is proved by concrete
homotopies on $`\partial\Delta^3`. The four faces of a based tetrahedron are based
triangles; pairing them along shared edges produces quadrilateral loops on the
$`1`-skeleton, all of which are null since $`X` is simply connected. The square is then
manipulated directly: `quarterTurn` is a literal rotation homotopy showing that rotating a
square loop by a quarter turn does not change its class, cyclic permutation of the vertices
of a triangle is realized by an explicit homotopy of the corresponding cube loop, and the
diagonal subdivision `squareChain_two_triangles` splits a square into two triangles with
matching signs. Assembling these identifications around the tetrahedron cancels the four
face classes in pairs. $`\blacksquare`
:::

:::definition "def:triangle-class-operator" (lean := "Mathoverflow1973.SecondHurewicz.SimplyConnected.triangleClassOperator") (parent := "hurewicz") (uses := "def:extend-coherent-simplex-homotopy, def:singular-complex")
*Definition.* For simply connected $`X` and $`x \in X`, the triangle class operator is the
$`\Z`-linear map
$$`C_2(X) \longrightarrow \mathrm{Additive}\,\pi_2(X,x), \qquad
\sigma \longmapsto \big[\mathrm{normalizedTriangle}(\sigma)\big],`
defined by the universal property of $`C_2(X)` as the free $`\Z`-module on singular
$`2`-simplices. Its defining property is that it kills boundaries: the composite with
$`\partial : C_3(X) \to C_2(X)` is zero, which follows from the tetrahedron relation after
checking on generators. It is not a chain map in any useful sense and is not natural; it is
exactly a cocycle on $`C_2` with values in $`\pi_2`, which is all that is needed.
:::

:::definition "def:hurewicz-inverse" (lean := "Mathoverflow1973.SecondHurewicz.SimplyConnected.hurewiczInverse") (parent := "hurewicz") (uses := "def:triangle-class-operator, thm:normalized-triangle-boundary-relation, def:singular-homology")
*Definition.* Since the triangle class operator vanishes on boundaries, it descends to
$$`H_2(X;\Z) \longrightarrow \mathrm{Additive}\,\pi_2(X,x)`
by the universal property `secondHomologyDesc`, whose content is that a linear map on
$`2`-chains killing boundaries induces a linear map on homology taking the class of a cycle
$`c` to the value on $`c`. That last identity, `hurewiczInverse_cycleClass`, is the only
form in which the descended map is ever used, and the two round-trip computations that
follow — that straightening the square chain of a cube loop recovers its class, and that
the Hurewicz map of a straightened cycle recovers its class — are both proved on cycle
representatives.
:::

:::definition "def:hurewicz-pi2-equiv" (lean := "Mathoverflow1973.SecondHurewicz.SimplyConnected.hurewiczPi2Equiv") (parent := "hurewicz") (uses := "def:second-hurewicz-hurewicz-map, def:hurewicz-inverse")
The Hurewicz theorem in degree two. For a simply connected space $`X` and any
$`x \in X`, the Hurewicz map and its inverse are mutually inverse, giving
$$`\pi_2(X,x) \;\cong\; H_2(X;\Z).`
The isomorphism is produced in both idioms: `hurewiczLinearEquiv` is the $`\Z`-linear
equivalence from `Additive (π_ 2 X x)` to $`H_2(X;\Z)`, and `hurewiczPi2Equiv` is the
multiplicative equivalence from $`\pi_2(X,x)` to `Multiplicative` of $`H_2(X;\Z)`, sharing
the forward map and inheriting the inverse. The only hypothesis is
`[SimplyConnectedSpace X]`; no manifold, finiteness, or CW condition appears. Its first use
is immediate: since $`H_2(S^{n+3};\Z)` is trivial, $`\pi_2` of every sphere of dimension at
least three is trivial, which is the first hypothesis the next rung asks for.
:::

:::group "hurewicz-higher"
Degrees three through six. A generic toolbox replaces the hand-made degree-two
constructions — a null-homotopy engine for based simplices, based simplex classes, the
staircase triangulation of the cube indexed by permutations, an axiomatized evaluator on
cube loops, and the subdivision identity it proves — after which each rung is the same
argument with one more straightening layer. The chapter ends with the degree-six
isomorphism and the naturality square that the recognition argument consumes.
:::

:::definition "def:hurewicz-pi3-equiv" (lean := "Mathoverflow1973.ThirdHurewicz.hurewiczPi3Equiv") (parent := "hurewicz-higher") (uses := "def:extend-coherent-simplex-homotopy, def:singular-homology")
The Hurewicz theorem in degree three. For $`X` simply connected and $`x \in X` with
$`\pi_2(X,x)` trivial, $`\pi_3(X,x) \cong H_3(X;\Z)`, again in both the linear and the
multiplicative form. The forward map is the pushforward of the fundamental $`3`-chain of
$`I^3`, defined recursively as the cross product of the fundamental chain of the interval
with the fundamental chain of the square; every rung repeats this recursion one dimension
up. The inverse chain-lifts a singular $`3`-simplex to the class of its normalized based
replacement, where the normalization tower is the degree-two vertex and edge straightening
followed by a triangle straightening stage — the stage that consumes the hypothesis
$`\pi_2 = 0`, since it must null-homotope based triangles — and `composeSimplexHomotopies`
concatenates the stages in time while `extendCoherentSimplexHomotopy` pushes the resulting
family up to dimension four so that the boundary relation can be stated.
:::

:::definition "def:simplex-straightening-homotopy" (lean := "Mathoverflow1973.HigherHurewicz.simplexStraighteningHomotopy") (parent := "hurewicz-higher") (uses := "def:based-simplex")
*Definition.* Fix $`n` and $`x` with $`\pi_n(X,x)` trivial. For each singular
$`n`-simplex $`\sigma`, the straightening homotopy is a map $`I \times \Delta^n \to X`
defined by a case split: if $`\sigma` is already based, that is constant equal to $`x` on
$`\partial\Delta^n`, it is the null-homotopy of the based simplex $`\sigma` rel boundary
whose existence is exactly triviality of $`\pi_n(X,x)`; otherwise it is the stationary
homotopy $`(t,s) \mapsto \sigma(s)`. The split is classical and its two branches are
reconciled by the companion lemmas: the family starts at the identity, is stationary on the
boundary, and — the point of the stationary branch — is face compatible with the stationary
family one dimension down. Each higher rung uses it once, as the top layer of its
normalization tower, which is what makes rungs four through six near-verbatim copies of one
another.
:::

:::definition "def:based-simplex-class" (lean := "Mathoverflow1973.HigherHurewicz.SimplexGeometry.basedSimplexClass") (parent := "hurewicz-higher") (uses := "def:based-simplex")
*Definition.* The class of a based $`n`-simplex $`\tau` at $`x` is the element of
$`\mathrm{Additive}\,\pi_n(X,x)` obtained by precomposing $`\tau` with the quotient
$`I^n \to \Delta^n` and taking the homotopy class of the resulting cube loop. The companion
`basedSimplex_face` records the fact this construction depends on: every face of a based
$`(n{+}1)`-simplex is the constant map at $`x`, since a point of a face has a vanishing
barycentric coordinate and therefore lies in $`\partial\Delta^{n+1}`. This is the degree-$`n`
replacement for the degree-two based triangle class, and it is the value taken by every
higher class operator on a generator.
:::

:::definition "def:cube-simplex" (lean := "Mathoverflow1973.HigherHurewicz.CubeTriangulation.cubeSimplex") (parent := "hurewicz-higher")
*Definition.* For a permutation $`e` of $`\{1, \dots, n\}`, the chamber simplex
$`\mathrm{cubeSimplex}(e) : \Delta^n \to I^n` is the affine map determined by the staircase
of vertices $`v_k = \mathbf{1}_{\{i \,:\, e^{-1}(i) < k\}}`, so that in coordinates
$$`\big(\mathrm{cubeSimplex}(e)\,s\big)_{e(i)} = \sum_{k > i} s_k .`
Its image is the closed chamber $`u_{e(1)} \ge \cdots \ge u_{e(n)}`, and these $`n!`
chambers are the simplices of the staircase, or Freudenthal–Kuhn, triangulation of the
cube. The orientation `cubeOrientation e` is the sign of $`e`, and the two facts the
subdivision argument needs are that the coordinates of a chamber point are antitone along
$`e` — proved directly from the coordinate formula — and that a transposition flips the
sign.
:::

:::definition "def:cubical-evaluator" (lean := "Mathoverflow1973.HigherHurewicz.CubicalBoundary.CubicalEvaluator") (parent := "hurewicz-higher")
*Definition.* A cubical evaluator of degree $`n` at $`x` with values in an abelian group
$`A` is a function $`E` on cube loops $`\mathrm{GenLoop}(\mathrm{Fin}\,n, X, x)` satisfying
five axioms: $`E` vanishes on the constant loop, is invariant under homotopy of cube loops,
is additive under concatenation in every coordinate, is negated by reflection in every
coordinate, and is negated by transposing two coordinates. From the last axiom alone,
$`E(p \circ e) = \mathrm{sgn}(e)\,E(p)` for every permutation $`e`, by induction on
transpositions. The motivating instance sends a cube loop to its own class in
$`\mathrm{Additive}\,\pi_n(X,x)`, so packaging the axioms as a structure lets the long
subdivision bookkeeping be carried out once for an abstract $`E` and then specialized. This
is one of only three structures in the entire cluster.
:::

:::theorem "thm:native-cube-subdivision-class" (lean := "Mathoverflow1973.HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class") (parent := "hurewicz-higher") (uses := "def:cube-simplex, def:based-simplex-class, def:cubical-evaluator")
*Theorem (cube subdivision at the level of homotopy).* Let $`n \ge 2` and let
$`p` be a cube loop in $`X` at $`x` that is internally based: $`p(u) = x` whenever two
coordinates of $`u` agree. Then
$$`[p] \;=\; \sum_{e \in S_n} \mathrm{sgn}(e) \cdot
\big[\, p \circ \mathrm{cubeSimplex}(e) \,\big] \quad\text{in }
\mathrm{Additive}\,\pi_n(X,x),`
where each $`p \circ \mathrm{cubeSimplex}(e)` is a based $`n`-simplex and the bracket is its
based simplex class. The internal basing hypothesis is what makes each restriction based:
the boundary of a chamber lies either in $`\partial I^n` or on a wall $`u_i = u_j`, and
$`p` is $`x` on both. This identity is the homotopy-level counterpart of the chain-level
fact that the fundamental chain of the cube is the signed sum of its chambers, and it is
precisely what makes the simplex class operators invert the Hurewicz map in degrees above
two.
:::

:::proof "thm:native-cube-subdivision-class"
The class assignment $`p \mapsto [p]` is first shown to be a cubical evaluator, which
supplies constancy, homotopy invariance, additivity under concatenation in each coordinate,
and the sign rule for permutations of the coordinates. The decomposition is then proved by
induction on how much of the ordering has been imposed: `nativeClass_eq_sum_partialChambers`
expresses the class of $`p` as a signed sum over the permutations that order the first $`k`
coordinates, the inductive step splitting one remaining coordinate pair by a concatenation
in which the two halves are related by the transposition axiom, so their contributions
appear with opposite signs. When all $`n` coordinates are ordered, each summand is the class
of a loop supported on a single closed chamber. Composing with the ordered Duffy chart of
that chamber identifies it with the class of the corresponding based simplex
$`p \circ \mathrm{cubeSimplex}(e)`, up to the sign of $`e`, which is the stated identity.
$`\blacksquare`
:::

:::definition "def:hurewicz-pi4-equiv" (lean := "Mathoverflow1973.FourthHurewicz.hurewiczPi4Equiv") (parent := "hurewicz-higher") (uses := "def:extend-coherent-simplex-homotopy, def:simplex-straightening-homotopy, def:singular-homology, thm:native-cube-subdivision-class")
The Hurewicz theorem in degree four. For $`X` simply connected and $`x \in X` with
$`\pi_2(X,x)` and $`\pi_3(X,x)` trivial, $`\pi_4(X,x) \cong H_4(X;\Z)`. This is the first
rung assembled entirely from generic parts. Its normalization tower has two storeys, each
raised one dimension by the extension step and then concatenated in time: the degree-three
tower lifted from dimension three to dimension four, followed by the straightening homotopy
in dimension three lifted the same way against the stationary family. The whole tower is
built once more in dimension five, which is what lets the boundary relation for the class
operator be stated at all. The identity making the inverse a left inverse,
`fourSimplexClassOperator_cubeChain`, says the class operator applied to the fundamental
chain of a cube loop returns that loop's class, and it is deduced from the subdivision
theorem together with the chain-level decomposition of the fundamental cube chain into
chambers.
:::

:::definition "def:hurewicz-pi5-equiv" (lean := "Mathoverflow1973.FifthHurewicz.hurewiczPi5Equiv") (parent := "hurewicz-higher") (uses := "def:extend-coherent-simplex-homotopy, def:simplex-straightening-homotopy, def:singular-homology, thm:native-cube-subdivision-class")
The Hurewicz theorem in degree five. For $`X` simply connected and $`x \in X` with
$`\pi_2(X,x)`, $`\pi_3(X,x)` and $`\pi_4(X,x)` trivial,
$`\pi_5(X,x) \cong H_5(X;\Z)`. The rung is the degree-four argument with one more layer,
and it is the first to use a further generic tool: `normalizedCycleAssignment` turns a
choice of based replacement for each $`(n{+}1)`-simplex into a linear map from chains to
cycles, subtracting a constant-simplex correction term so that the result really is a cycle,
and proves that on a cycle it does not change the homology class. The correction term is
governed by the augmentation, and its treatment requires a case split on the parity of the
degree, which is the one place where the schema is not uniform in $`n`.
:::

The sixth rung is stated in the same generality as the others but is placed much later in
the file, immediately before the material that consumes it. It also carries the naturality
theorems, which no lower rung needs and which the recognition argument cannot do without.

:::definition "def:cube-homology-class" (lean := "Mathoverflow1973.SixthHurewicz.cubeHomologyClass") (parent := "hurewicz-higher") (uses := "def:singular-homology")
*Definition.* For a cube loop $`p` of degree six at $`x`, the chain
$`\mathrm{cubeChain}(p) \in C_6(X)` is the pushforward along $`p` of the fundamental
$`6`-chain of $`I^6`, built by six iterated cross products starting from the fundamental
chain of the interval; the identity `cubeChain_eq_induced` records that the suspension
description used in the definition agrees with the pushforward description. Its boundary
vanishes, giving `cubeCycle p`, and $`\mathrm{cubeHomologyClass}(p) \in H_6(X;\Z)` is the
class of that cycle. Naturality holds at every stage: a continuous $`f : X \to Y` carries
the chain, the cycle, and the class of $`p` to those of $`f \circ p`, because the induced
chain map is functorial in $`f`. This class is also how the top class of $`S^6` is
presented downstream.
:::

:::definition "def:homotopy-map" (lean := "Mathoverflow1973.SixthHurewicz.homotopyMap") (parent := "hurewicz-higher")
*Definition.* A continuous map $`f : X \to Y` induces a group homomorphism
$`f_* : \pi_6(X,x) \to \pi_6(Y,f(x))` by post-composition on representatives. It is well
defined because post-composing a homotopy of cube loops with $`f` is again a homotopy, it
sends the constant loop to the constant loop, and it commutes with concatenation, which is
performed coordinatewise on representatives. It is defined here rather than transported
from an abstract functoriality statement precisely so that it is literally post-composition
on the cube loops the Hurewicz map consumes, which is what reduces the naturality proof
below to a chain-level computation instead of a comparison of two constructions.
:::

:::definition "def:hurewicz-linear-equiv" (lean := "Mathoverflow1973.SixthHurewicz.hurewiczLinearEquiv") (parent := "hurewicz-higher") (uses := "def:extend-coherent-simplex-homotopy, def:simplex-straightening-homotopy, def:singular-homology, thm:native-cube-subdivision-class, def:cube-homology-class")
The Hurewicz theorem in degree six, linear form. For $`X` simply connected and $`x \in X`
with $`\pi_2(X,x)`, $`\pi_3(X,x)`, $`\pi_4(X,x)` and $`\pi_5(X,x)` all trivial, there is a
$`\Z`-linear equivalence
$$`\mathrm{Additive}\,\pi_6(X,x) \;\simeq_{\Z}\; H_6(X;\Z),`
with forward map $`[p] \mapsto \mathrm{cubeHomologyClass}(p)` and inverse the descent of the
six-simplex class operator through homology. Instantiated on the threefold, with the four
vanishing hypotheses supplied by its own homotopy computations and simple connectivity by
the fundamental group chapter, it becomes `HomotopySix.hurewiczEquiv`, an isomorphism
$`\pi_6(X) \cong H_6(X;\Z) \cong \Z`. The linear form, rather than the multiplicative one,
is what the naturality statement is phrased in.
:::

:::definition "def:hurewicz-pi6-equiv" (lean := "Mathoverflow1973.SixthHurewicz.hurewiczPi6Equiv") (parent := "hurewicz-higher") (uses := "def:extend-coherent-simplex-homotopy, def:simplex-straightening-homotopy, def:singular-homology, thm:native-cube-subdivision-class")
The Hurewicz theorem in degree six. Under the same hypotheses, $`\pi_6(X,x)` is isomorphic
as a group to $`H_6(X;\Z)`, written as a multiplicative equivalence onto
`Multiplicative` of $`H_6(X;\Z)`. This is the summit of the ladder. Its injectivity is what
the recognition argument invokes directly: two based maps out of $`S^6` with the same top
homology class have the same class in $`\pi_6`, hence are based homotopic, which is the
uniqueness half of the argument. Surjectivity of the linear form is what produces, on the
threefold, a cube loop whose homology class is the chosen generator of $`H_6(X;\Z)`, and
that loop is the one factored through $`S^6` to build the comparison map.
:::

:::theorem "thm:hurewicz-linear-equiv-natural" (lean := "Mathoverflow1973.SixthHurewicz.hurewiczLinearEquiv_natural") (parent := "hurewicz-higher") (uses := "def:hurewicz-linear-equiv, def:singular-homology-map, def:homotopy-map")
*Theorem (naturality).* Let $`f : X \to Y` be continuous, let $`x \in X`, and suppose both
$`X` and $`Y` are simply connected with $`\pi_2, \pi_3, \pi_4, \pi_5` trivial at $`x` and at
$`f(x)` respectively, so that both degree-six Hurewicz isomorphisms are available. Then for
every $`a \in \mathrm{Additive}\,\pi_6(X,x)`,
$$`f_*\big(h_X(a)\big) \;=\; h_Y\big(f_*(a)\big),`
where the outer $`f_*` on the left is the induced map on $`H_6` and the inner $`f_*` on the
right is the induced map on $`\pi_6`. The square commutes for arbitrary $`f`; the vanishing
hypotheses are needed only to have the two isomorphisms to compare.
:::

:::proof "thm:hurewicz-linear-equiv-natural"
Both equivalences have the Hurewicz map as their forward map, so the statement is
naturality of that linear map, and linearity lets it be checked on the underlying function
of homotopy classes. A class in $`\pi_6(X,x)` is represented by a cube loop $`p`, and
quotient induction reduces the claim to the identity
$`f_*(\mathrm{cubeHomologyClass}(p)) = \mathrm{cubeHomologyClass}(f \circ p)`. That is a
statement about cycle classes, so it reduces further to the chain level, where it is the
functoriality of the induced chain map: the pushforward of the fundamental $`6`-chain of
the cube along $`p` and then along $`f` is its pushforward along $`f \circ p`. No property
of $`f` beyond continuity is used, and no property of $`X` or $`Y` at all — the hypotheses
in the statement only name the two isomorphisms. $`\blacksquare`
:::

The ladder is climbed twice. For the standard six-sphere, the sphere homology computation
gives trivial $`H_k(S^6;\Z)` for $`1 \le k \le 5`, and rungs two through five convert that,
degree by degree, into triviality of $`\pi_k(S^6)` for $`2 \le k \le 5`; with simple
connectivity supplying the remaining degree, this is packaged as one statement for
$`0 < k < 6`. For the threefold, the corresponding vanishing statements are fed by the
Section 7 homology computation of the previous chapters, and the sixth rung then delivers
$`\pi_6(X) \cong \Z`.

What the recognition argument takes away is the pair of consequences of degree six. A map
$`S^6 \to X` that is an isomorphism on $`H_6` is, by the commuting square, a bijection on
$`\pi_6`; and two based maps out of $`S^6` with equal top homology classes are based
homotopic, by injectivity of the degree-six isomorphism. Those are the Hurewicz and
Whitehead inputs to Lemma 8.2 of {citep alpoge.s6}[], and in the formalization they are the
inputs to the homotopy equivalence $`X \simeq S^6` constructed in the degree chapter. The
CW hypothesis that the classical homology Whitehead theorem needs, and that the paper
discharges by citing the CW homotopy type of a closed topological manifold, is not
available here; the formalization replaces that route with a Morse-theoretic cell structure
on the threefold, which is why the recognition step in this development is longer than its
three-line counterpart in the paper.
