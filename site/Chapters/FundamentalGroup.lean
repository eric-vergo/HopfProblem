/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — The fundamental group chapter.

The two from-scratch topological engines behind §7: a Seifert–van Kampen theorem for a
path-connected two-open cover, and a mapping-torus theory with its Wang exact sequence,
together with the identification of each punctured special fibre neighbourhood of the
threefold with the mapping torus of its local monodromy.
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

#doc (Manual) "The fundamental group" =>

Recognising the threefold $`X` as the six-sphere consumes exactly two topological facts
about it: $`\pi_1(X) = 1` and $`H_*(X;\Z) \cong H_*(S^6;\Z)`. Both are decided at the
three special fibres of $`f : X \to \PP^1` — the cusp fibre over $`p_0` and the two
multiple fibres $`3S_1` and $`4S_2` over the elliptic points — and both rest on the same
local picture. Away from a special fibre the map $`f` is a locally trivial bundle of real
four-tori, so a punctured neighbourhood of the fibre is the mapping torus of the local
monodromy acting on the general fibre $`F \cong T^4`. This chapter holds the two engines
that turn that picture into invariants: a Seifert–van Kampen theorem, applied to the
decomposition $`X = J \cup N_0 \cup N_1 \cup N_2` one filling piece at a time, and a Wang
exact sequence for mapping tori, which feeds the Mayer–Vietoris computation of
$`H_*(X;\Z)`.

The arithmetic that emerges is small and sharp. Theorem 7.17 of {citet alpoge.s6}[]
presents $`\pi_1(X)` as
$`\langle c, x, y \mid c \text{ central},\ xy = c^{\ell_0},\ x^3 = c^{\ell_1},\ y^4 = c^{\ell_2}\rangle`, where $`c` is the image of the fibre lattice, $`x` and $`y` are lifts of the clockwise
meridians of the two elliptic points, and $`(\ell_0, \ell_1, \ell_2)` are the discrete
gluing parameters. The group is abelian and cyclic of order $`|p|` with
$`p = 12\ell_0 - 4\ell_1 - 3\ell_2`. The threefold of the construction has
$`(\ell_0, \ell_1, \ell_2) = (0, 1, -1)`, whence $`p = -1` and $`\pi_1(X) = 1`; the
comparison threefold built with $`v_2 = +\varepsilon'` instead of $`-\varepsilon'` has
$`p = -7` and fails. The whole of that computation is isolated in the formalization as a
statement about one finitely presented group, with no topology in it at all.

Nothing in this chapter is imported. Mathlib has no van Kampen theorem, no mapping torus,
and no Wang sequence, so all three are built here. The van Kampen proof is not the
groupoid or covering-space argument but a nonabelian analytic continuation: a group-valued
"path value" defined on paths that fit inside a single chart is continued along an
arbitrary path by Lebesgue-number subdivision, and shown homotopy-invariant by chopping
the homotopy square into chart-small rectangles. The two charts are indexed by `Bool`
purely so that mathlib's indexed amalgamated product `Monoid.PushoutI` can serve as the
pushout. The Wang sequence is derived from the development's own singular Mayer–Vietoris
theory, with the linear algebra of the two-arc pattern factored out into an abstract
layer.

:::group "pi1"
The Seifert–van Kampen theorem for a two-open cover, proved from scratch by continuing a
locally defined group-valued path invariant along arbitrary paths, together with the
presented-group arithmetic that the stage-by-stage application of it produces.
:::

:::definition "def:local-path-value" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.LocalPathValue") (parent := "pi1")
*Definition.* Let $`X` be a space, $`\{U_i\}_{i \in \iota}` a family of subsets and $`G` a
group. A *local path value* assigns to each index $`i` and each path $`p` whose image lies
entirely in $`U_i` an element $`\mathrm{val}_i(p) \in G`, subject to four laws: constant
paths get $`1`; concatenation is multiplicative,
$`\mathrm{val}_i(p \cdot q) = \mathrm{val}_i(p)\,\mathrm{val}_i(q)` whenever all three
paths lie in $`U_i`; restriction splits,
$`\mathrm{val}_i(p|_{[a,c]}) = \mathrm{val}_i(p|_{[a,b]})\,\mathrm{val}_i(p|_{[b,c]})` for
$`a \le b \le c`; and the value is independent of the chart,
$`\mathrm{val}_i(p) = \mathrm{val}_j(p)` when $`p` lies in both $`U_i` and $`U_j`. In
Lean the membership hypothesis is an explicit argument of `value`, so the last law is
what makes the notation $`\mathrm{val}(p)` legitimate. This is the local datum from which
the van Kampen lift is continued.
:::

:::theorem "thm:exists-path-subdivision" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.exists_path_subdivision") (parent := "pi1")
*Theorem.* Let $`\{U_i\}` be an open cover of $`X` and $`p` a path in $`X`. There is a
monotone sequence $`0 = t_0 \le t_1 \le \cdots` in $`[0,1]` attaining the value $`1` at
some index, such that for every $`n` the segment $`p([t_n, t_{n+1}])` is contained in a
single member of the cover. This is the Lebesgue-number lemma in the form the continuation
argument uses: the sequence is indexed by $`\mathbb{N}` and eventually constant at $`1`
rather than being a finite partition, which lets the primitive be built by induction on
$`n` without carrying a length.
:::

:::theorem "thm:local-path-value-exists-primitive" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.LocalPathValue.exists_primitive") (parent := "pi1") (uses := "def:local-path-value, thm:exists-path-subdivision")
*Theorem.* Let $`L` be a local path value over an open cover of $`X` and let $`p` be any
path. There is $`F : [0,1] \to G` with $`F(0) = 1` which is a *primitive* of $`L` along
$`p`: whenever $`a \le b` and the restriction $`p|_{[a,b]}` lies in a single chart $`U_i`, $`F(b) = F(a) \cdot L.\mathrm{val}_i(p|_{[a,b]})`. The function $`F` is the nonabelian
analogue of an antiderivative of a locally exact form, and $`F(1)` is the value assigned
to $`p` by the extension of $`L` to all paths. It is constructed by subdividing $`p` as
above and extending the primitive one segment at a time; the subpath law of $`L` is
exactly what makes the extension consistent on overlaps, and it forces $`F` to be unique
given $`F(0)`.
:::

:::theorem "thm:value-eq-of-homotopy-of-open-cover" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.PathValue.value_eq_of_homotopy_of_open_cover") (parent := "pi1") (uses := "def:local-path-value")
*Theorem.* Let $`V` be a globally defined path value on $`X` extending a local path value
$`L` over an open cover, and suppose $`L` is homotopy-invariant within each chart. Then
$`V` is homotopy-invariant: paths $`p, q` with the same endpoints admitting a homotopy
$`H` rel endpoints satisfy $`V(p) = V(q)`. The proof subdivides the square $`[0,1]^2` by
a single monotone sequence in both coordinates so that every closed rectangle of the grid
maps into one chart, shows the value is unchanged across each individual cell, and then
across each horizontal strip. Homotopy invariance is what lets the extended path value
descend from paths to $`\pi_1`.
:::

:::definition "def:fundamental-group-van-kampen-two-open-cover" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.TwoOpenCover") (parent := "pi1")
*Definition.* A *two-open cover* of $`X` is a pair of opens $`U, V \subseteq X` with
$`U \cup V = X`, with $`U`, $`V` and $`U \cap V` all path-connected, together with a
basepoint $`x_0` lying in both — hence in $`U \cap V`. The structure carries the derived
data the theorem is stated in: the chart family
$`\mathrm{chart} : \mathrm{Bool} \to \mathcal{O}(X)` sending `false` to $`U` and `true` to
$`V`, the three groups $`\pi_1(U, x_0)`, $`\pi_1(V, x_0)`, $`\pi_1(U \cap V, x_0)`,
the two overlap maps and the two inclusion maps between them, and the commutation
$`(\iota_U)_* \circ (\jmath_U)_* = (\iota_V)_* \circ (\jmath_V)_*` in $`\pi_1(X, x_0)`.
Path-connectivity of $`U \cap V` is the hypothesis that makes the pushout description
correct; without it the theorem is false.
:::

:::definition "def:two-open-cover-lift" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.TwoOpenCover.lift") (parent := "pi1") (uses := "def:fundamental-group-van-kampen-two-open-cover, def:local-path-value, thm:local-path-value-exists-primitive, thm:value-eq-of-homotopy-of-open-cover")
*Definition.* The existence half of van Kampen. Given homomorphisms
$`f_U : \pi_1(U) \to G` and $`f_V : \pi_1(V) \to G` that agree on $`\pi_1(U \cap V)`,
there is a homomorphism $`\mathrm{lift} : \pi_1(X, x_0) \to G` with
$`\mathrm{lift} \circ (\iota_U)_* = f_U` and $`\mathrm{lift} \circ (\iota_V)_* = f_V`. It
is assembled from the material above: a chart-contained path is closed into a based loop
using chosen access paths from $`x_0`, and $`f_U` or $`f_V` is applied to the resulting
class; compatibility of the pair makes this a local path value, the primitive extends it
to every path, and homotopy invariance lets it descend to homotopy classes. The Lean
construction records the value of a chart-contained based loop as the *inverse* of the
local value, an orientation convention that keeps the extension a homomorphism rather than
an antihomomorphism.
:::

:::theorem "thm:two-open-cover-hom-ext" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.TwoOpenCover.hom_ext") (parent := "pi1") (uses := "def:fundamental-group-van-kampen-two-open-cover")
*Theorem.* The uniqueness half. Two homomorphisms $`f, g : \pi_1(X, x_0) \to G` that agree
after composition with $`(\iota_U)_*` and with $`(\iota_V)_*` are equal. Equivalently,
$`\pi_1(X, x_0)` is generated by the images of $`\pi_1(U)` and $`\pi_1(V)`. The proof is
a path induction over the cover: a chart-contained path from $`x` to $`y` is closed into a
based loop by the chosen access paths, on which $`f` and $`g` agree by hypothesis, and an
arbitrary loop is a product of such pieces by subdivision. Together with the lift this
says the pair $`((\iota_U)_*, (\iota_V)_*)` has the universal property of a pushout.
:::

:::definition "def:two-open-cover-pushout-equiv" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv") (parent := "pi1") (uses := "def:fundamental-group-van-kampen-two-open-cover, def:two-open-cover-lift, thm:two-open-cover-hom-ext")
*Definition.* The Seifert–van Kampen theorem: the amalgamated free product
$`\pi_1(U) \ast_{\pi_1(U \cap V)} \pi_1(V)` is isomorphic to $`\pi_1(X, x_0)`, compatibly
with the inclusions — under the isomorphism, the canonical map of the $`i`-th factor is
$`(\iota_i)_*`. The amalgamated product is realised as mathlib's `Monoid.PushoutI` over
the `Bool`-indexed family of overlap homomorphisms, which is why the cover was indexed by
`Bool` in the first place. The isomorphism is the map out of the pushout induced by the two
inclusions, with inverse the lift of the two canonical maps into the pushout; the two round
trips are checked by the pushout's own extensionality principle in one direction and by
the uniqueness half in the other.
:::

:::theorem "thm:inclusion-hom-u-surjective-of-overlap-hom-v-surjective" (lean := "Mathoverflow1973.FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective") (parent := "pi1") (uses := "def:two-open-cover-pushout-equiv")
*Theorem.* If $`\pi_1(U \cap V) \to \pi_1(V)` is surjective, then $`\pi_1(U) \to \pi_1(X)`
is surjective. This is the transfer lemma that carries the fundamental group across an
attachment stage. Each filling piece of $`X` is glued to the rest along a punctured
neighbourhood whose $`\pi_1` already surjects onto that of the piece, so attaching a piece
adds relations but no generators, and the fundamental group of every stage stays generated
by the regular part. The proof reads the conclusion off the pushout: every element of
$`\pi_1(X)` is a product of images of the two factors and of the base, and the hypothesis
rewrites each $`\pi_1(V)`-factor as the image of an overlap class, hence of a $`\pi_1(U)`-class.
:::

The stage-by-stage application of the pushout to $`X = J \cup N_0 \cup N_1 \cup N_2`
produces generators $`c`, $`x`, $`y` — the image of the fibre lattice, and the lifts of
the two elliptic meridians — subject to the relations that each filling imposes: filling
the cusp neighbourhood kills the toric part of the lattice and the toric meridian, filling
$`N_j` imposes $`\hat\rho_j^{m_j} = t_{\varepsilon_j v_j}` with $`m_1 = 3`, $`m_2 = 4`.
The delicate point of the paper's argument is that the two signs
$`\varepsilon_1, \varepsilon_2` agree, which is what makes $`|p|` independent of
orientation conventions. Once that is settled, everything remaining is a question about
one presented group.

:::theorem "thm:main-group-trivial" (lean := "Mathoverflow1973.TwistGroup.main_group_trivial") (parent := "pi1") (uses := "def:twist-order")
*Theorem.* Let $`T(a,b,d)` be the group presented on three generators $`c, x, y` by the
relators $`[c,x]`, $`[c,y]`, $`xy\,c^{-a}`, $`x^3c^{-b}`, $`y^4c^{-d}`. Then
$`T(a,b,d)` is cyclic, generated by $`c`, and $`c^{12a-4b-3d} = 1`. For
$`(a,b,d) = (0,1,-1)` the exponent is $`-1`, and every element of $`T(0,1,-1)` equals
$`1`. This is the whole arithmetic of $`\pi_1(X) \cong \Z/|12\ell_0 - 4\ell_1 - 3\ell_2|`
extracted as pure group theory: the topology enters only in producing three elements of
$`\pi_1(X)` satisfying the five relations, after which the presented group maps onto it.
:::

:::proof "thm:main-group-trivial"
Since $`c` is central and $`xy = c^a`, conjugating by $`x` gives $`x(xy) = (xy)x`, so
$`x` and $`y` commute. Hence $`x^4 = (xy)^4 (y^4)^{-1} = c^{4a}c^{-d} = c^{4a-d}`, and
therefore $`x = x^4(x^3)^{-1} = c^{4a-b-d}` and $`y = x^{-1}(xy) = c^{-3a+b+d}`. Both
generators are powers of $`c`, so $`T(a,b,d) = \langle c \rangle`. Substituting the
expression for $`x` back into $`x^3 = c^b` gives $`c^{3(4a-b-d)-b} = 1`, that is
$`c^{12a-4b-3d} = 1`. For $`(a,b,d) = (0,1,-1)` the exponent $`12a-4b-3d` equals $`-1`,
so $`c^{-1} = 1`, hence $`c = 1` and, $`c` generating, the group is trivial. The applied
form of the statement takes any group containing $`c_0, x_0, y_0` with $`c_0` central,
$`x_0y_0 = 1`, $`x_0^3 = c_0` and $`y_0^4 = c_0^{-1}`, and concludes
$`c_0 = x_0 = y_0 = 1`; fed the van Kampen generators of $`\pi_1(X)`, it gives simple
connectivity. $`\blacksquare`
:::

:::group "mapping-torus"
Mapping tori of a self-homeomorphism, their two-arc cover and the Wang exact sequence it
produces, and the identification of the punctured neighbourhood of each special fibre of
the threefold with the mapping torus of its local monodromy.
:::

:::definition "def:mapping-torus-torus" (lean := "Mathoverflow1973.MappingTorus.Torus") (parent := "mapping-torus")
*Definition.* For a homeomorphism $`f : X \to X`, the mapping torus $`T_f` is the
quotient of $`\R \times X` by the $`\Z`-action $`n \cdot (t, x) = (t + n, f^{-n}(x))`.
Explicitly, $`[t, x] = [t', x']` in $`T_f` if and only if $`t' = t + n` and
$`x' = f^{-n}(x)` for some $`n \in \Z`. The quotient map is open, the projection
$`\mathrm{base} : T_f \to \R/\Z`, $`[t,x] \mapsto t \bmod 1`, is continuous, and $`T_f`
is compact whenever $`X` is, being the image of $`[0,1] \times X`. The sign in the action
is the one that makes $`f` the monodromy of the fibration $`\mathrm{base}` in the positive
direction; the general fibre over $`0` is $`X` itself.
:::

:::definition "def:homology-cover-intersection-homotopy-equiv" (lean := "Mathoverflow1973.MappingTorus.HomologyCover.intersectionHomotopyEquiv") (parent := "mapping-torus") (uses := "def:circle-topology-circle, def:mapping-torus-torus")
*Definition.* Cut the circle at two points. The opens $`U = \{\mathrm{base} \ne 0\}` and
$`V = \{\mathrm{base} \ne -1/2\}` cover $`T_f`; each is homeomorphic to a product,
$`U \cong (0,1) \times X` and $`V \cong (-1/2, 1/2) \times X`, and the interval factor is
contractible, so both are homotopy equivalent to the fibre $`X`. Their intersection is
two slabs, $`(0, 1/2) \times X` and $`(1/2, 1) \times X`, whence a homotopy equivalence
$`U \cap V \simeq_h X \sqcup X`. These identifications turn the Mayer–Vietoris sequence
of the cover into a sequence relating $`H_*(X)^2` to $`H_*(X)^2` and $`H_*(T_f)`; what
remains is to say what the two inclusions do in these coordinates.
:::

:::theorem "thm:intersection-to-v-twisted-fold" (lean := "Mathoverflow1973.MappingTorus.HomologyCover.intersectionToV_twistedFold") (parent := "mapping-torus") (uses := "def:circle-topology-circle, def:homology-cover-intersection-homotopy-equiv, def:mapping-torus-torus")
*Theorem.* Under the identifications above, the inclusion $`U \cap V \hookrightarrow V`
followed by $`V \simeq_h X` is the *twisted* fold map
$`(\mathrm{id}, f) : X \sqcup X \to X`, while the corresponding composite on the $`U`-side is the untwisted fold $`(\mathrm{id}, \mathrm{id})`. Both statements are equalities
of continuous maps, not merely of homotopy classes. This asymmetry is the entire content
of the mapping-torus construction as far as homology is concerned: one of the two slabs is
glued back to the fibre through $`f`, and the monodromy enters at exactly this one point.
It is what turns the Mayer–Vietoris sequence of the two-arc cover into the Wang sequence.
:::

:::definition "def:mapping-torus-homology-wang-boundary" (lean := "Mathoverflow1973.MappingTorusHomology.wangBoundary") (parent := "mapping-torus") (uses := "def:circle-topology-circle, def:connecting-homomorphism, def:homology-cover-intersection-homotopy-equiv, def:homotopy-equiv-homology-equiv, def:mapping-torus-torus")
*Definition.* The Wang boundary $`\partial : H_{n+1}(T_f) \to H_n(X)`. Transporting the
Mayer–Vietoris connecting homomorphism $`H_{n+1}(T_f) \to H_n(U \cap V)` along
$`H_n(U \cap V) \cong H_n(X) \oplus H_n(X)` gives a pair of classes, and $`\partial` is
minus the first coordinate. The choice of coordinate is not arbitrary: the connecting map
lands on the antidiagonal, its value being $`(-\partial a, \partial a)`, so either
coordinate determines the other and the sign is fixed by making $`\partial` agree with the
classical Wang boundary. All homology here is singular with $`\Z` coefficients, in the
development's own from-scratch construction.
:::

:::theorem "thm:wang-exact-at-fibre" (lean := "Mathoverflow1973.MappingTorusHomology.wang_exact_at_fibre") (parent := "mapping-torus") (uses := "def:homotopy-equiv-homology-equiv, thm:intersection-to-v-twisted-fold, thm:singular-mayer-vietoris-exact-at-pair")
*Theorem.* Exactness of the Wang sequence at the fibre: the range of $`1 - f_*` on
$`H_n(X)` equals the kernel of the map $`H_n(X) \to H_n(T_f)` induced by the fibre
inclusion. With the two companion statements — the range of $`H_{n+1}(X) \to H_{n+1}(T_f)`
is the kernel of $`\partial`, and the range of $`\partial` is the kernel of $`1 - f_*` —
this is the Wang exact sequence
$$`\cdots \to H_{n+1}(T_f) \xrightarrow{\ \partial\ } H_n(X) \xrightarrow{\ 1 - f_*\ } H_n(X) \to H_n(T_f) \to \cdots`
The three statements split into short exact sequences
$`0 \to \mathrm{coker}(1-f_*)_n \to H_n(T_f) \to \ker(1-f_*)_{n-1} \to 0`, which is the
form the fibre-by-fibre homology computations use.
:::

:::proof "thm:wang-exact-at-fibre"
Run Mayer–Vietoris on the two-arc cover. In the coordinates supplied by the homotopy
equivalences $`U \simeq_h X`, $`V \simeq_h X` and $`U \cap V \simeq_h X \sqcup X`, the
map $`H_n(U \cap V) \to H_n(U) \oplus H_n(V)` becomes
$`(a, b) \mapsto (a + b, -(a + f_*b))`, because the $`U`-side fold is untwisted and the
$`V`-side fold is $`(\mathrm{id}, f)`. That pattern is pure linear algebra, and the
development isolates it: for an endomorphism $`F` of an abelian group $`M` and a map $`i`
out of $`M`, if the range of $`(a,b) \mapsto (a+b, -(a+Fb))` equals the kernel of
$`i \circ \mathrm{sum}` on $`M \times M`, then the range of $`1 - F` equals $`\ker i`.
One direction is the computation $`i((1-F)m) = (i \circ \mathrm{sum})(\,(m, -Fm)\,) = 0`,
the pair $`(m, -Fm)` being the two-arc image of $`(0, m)`; the other takes
$`m \in \ker i`, writes $`(m, 0)` — which lies in $`\ker(i \circ \mathrm{sum})` — as a
two-arc image $`(a + b, -(a + Fb))`, whence $`a = -Fb` and $`m = b - Fb`. Instantiating
$`F = f_*` and $`i` the map induced by the fibre inclusion, the hypothesis is exactly
exactness of Mayer–Vietoris at the pair — the range of the map from the intersection is
the kernel of the map to the ambient space — for the two-arc cover. $`\blacksquare`
:::

:::definition "def:covering-homology-norm" (lean := "Mathoverflow1973.MappingTorusHomology.Covering.homologyNorm") (parent := "mapping-torus") (uses := "def:singular-homology-map")
*Definition.* For $`B : X \to X` a homeomorphism and $`m \in \mathbb{N}`, the homology
norm is $$`N = \sum_{k < m} (B^k)_* : H_n(X) \to H_n(X).` When $`B^m = 1` it is the
norm element of the cyclic group $`\langle B \rangle` acting on $`H_n(X)`: its image lies
in the invariants of $`B_*`, and it annihilates every class of the form $`c - B_*c`.
Symmetry under $`B \mapsto B^{-1}` holds when $`B^m = 1`,
since the powers $`B^{-k}` for $`k < m` are a permutation of the powers $`B^k`. The
elliptic monodromies of the threefold have order $`3` and $`4`, so this is the object
that appears in their boundary homology.
:::

:::theorem "thm:wang-boundary-product-cover" (lean := "Mathoverflow1973.MappingTorusHomology.Covering.wangBoundary_productCover") (parent := "mapping-torus") (uses := "def:covering-homology-norm, def:cross-product-homology, def:mapping-torus-homology-wang-boundary, thm:exact-at-ambient, thm:exact-at-intersection, thm:intersection-to-v-twisted-fold")
*Theorem.* Let $`X` be compact Hausdorff, $`m \ne 0`, and $`B : X \to X` a homeomorphism
with $`B^m = 1`. The $`m`-fold unrolling $`S^1 \times X \to T_{B^{-1}}`,
$`(t, x) \mapsto [tm, x]`, is a covering, and on homology
$$`\partial \circ (\mathrm{productCover})_* \ = \ N \circ \beta \quad\text{on } H_{n+1}(S^1 \times X),`
where $`\partial` is the Wang boundary of $`T_{B^{-1}}`, $`N` the homology norm of $`B`,
and $`\beta : H_{n+1}(S^1 \times X) \to H_n(X)` the circle slant boundary. For a
finite-order monodromy the mapping torus is thus computed from a product, and the twisting
survives only as the norm — the computational engine behind the homology of the
multiple-fibre boundaries.
:::

:::proof "thm:wang-boundary-product-cover"
Both sides are homomorphisms out of $`H_{n+1}(S^1 \times X)`, and that group is generated
by the cross products $`[S^1] \times b` together with the image of the section
$`H_{n+1}(X) \to H_{n+1}(S^1 \times X)`: every class $`a` differs from
$`[S^1] \times \beta(a)` by a class from the section. The slant boundary annihilates the
section, and so does the left-hand side, so it suffices to evaluate both sides on a cross
product $`[S^1] \times b`. There the computation is explicit at chain level: a cycle
representing $`b` is pushed around the circle, its image under the unrolling is cut by the
two arcs of the cover of $`T_{B^{-1}}`, and the resulting arc sum telescopes into the
$`m` translates $`(B^k)_*b`. Exactness of Mayer–Vietoris at the intersection and at the
ambient space identifies the difference cycle with a boundary, and the twisted fold
supplies the single $`B` that shifts each successive translate. Summing gives
$`\sum_{k<m}(B^k)_*b = N b`. $`\blacksquare`
:::

The three punctured neighbourhoods of $`X` are now identified with mapping tori, one
puncture at a time, and by different coordinates in the cusp and elliptic cases. At the
cusp the monodromy is parabolic and has infinite order, so no finite cover is available
and the identification runs through logarithmic coordinates; at an elliptic point the
monodromy is a finite-order affine map of the four-torus and polar coordinates on the disc
of $`m_j`-th roots do the work.

:::definition "def:punctured-mapping-torus-homotopy-equiv" (lean := "Mathoverflow1973.ThreefoldOverlapMappingTorus.Cusp.puncturedMappingTorusHomotopyEquiv") (parent := "mapping-torus") (uses := "def:cusp-family-data, def:cusp-quotient-quotient-space, def:cusp-uniformization-exponential, def:lattice, def:mapping-torus-torus, thm:cusp-quotient-proper-action")
*Definition.* The punctured cusp neighbourhood is homotopy equivalent to the mapping torus
of the parabolic monodromy. For a cusp family datum $`D`, the punctured quotient — the
total space over the punctured disc — is homeomorphic to
$`\mathrm{Height}(r) \times \mathrm{Boundary}`, where
$`\mathrm{Boundary} = T_{\,\mathrm{cuspTorusHomeomorph}\,1}` is the mapping torus of the
parabolic homeomorphism of $`\R^4/\Z^4` and
$`\mathrm{Height}(r) = \big(\tfrac{-\log r}{2\pi}, \infty\big)` is the range of the
imaginary part in logarithmic coordinates on the base. The height factor is a convex
subset of $`\R`, hence contractible, and contracting it gives the homotopy equivalence.
The choice of a height $`h` is a choice of radius at which to read the boundary; different
choices give homotopic inclusions.
:::

:::theorem "thm:elliptic-affine-pow-order" (lean := "Mathoverflow1973.ThreefoldOverlapMappingTorus.Elliptic.affine_pow_order") (parent := "mapping-torus") (uses := "def:a, def:admissible-twist, def:flat-torus-affine")
*Theorem.* Let $`j` be an elliptic point, of order $`3` or $`4`, with monodromy matrix
$`A_1` resp. $`A_2` on the lattice $`\Lambda = \Z^4`, and let $`v \in \Lambda` satisfy
$`A_j v = v`. The affine homeomorphism of $`\R^4/\Z^4` given by
$`x \mapsto A_j x + v/\mathrm{ord}(j)` has order dividing $`\mathrm{ord}(j)`: its
$`\mathrm{ord}(j)`-th power is the identity. The translation part accumulates to
$`(1 + A_j + \cdots + A_j^{\mathrm{ord}(j)-1})v/\mathrm{ord}(j) = v`, which is trivial
modulo $`\Lambda`, and the linear part is trivial because $`A_j^{\mathrm{ord}(j)} = 1`.
Finiteness of the order is what makes the elliptic boundaries accessible to the
product-cover computation; the cusp monodromy, being unipotent and non-trivial, has no
such power.
:::

:::definition "def:punctured-product-homeomorph" (lean := "Mathoverflow1973.ThreefoldOverlapMappingTorus.Elliptic.puncturedProductHomeomorph") (parent := "mapping-torus") (uses := "def:cusp-uniformization-exponential, def:elliptic-filling, def:flat-torus-affine, def:mapping-torus-torus, thm:elliptic-affine-pow-order, thm:flat-affine-free-iff")
*Definition.* The punctured logarithmic-transform filling at an elliptic point $`j` with
admissible twist $`v` is homeomorphic to a product,
$$`\mathrm{PuncturedFilling}(j, v, r) \ \cong\ \mathrm{Radius}(\mathrm{ord}(j), r) \times T_{\,\mathrm{flatTorusAffine}(j,v)},`
with $`\mathrm{Radius}(n, r) = \{a \in \R : 0 < a < 1,\ a^n < r\}` the radial factor. The
filling is built upstairs on the disc of $`\mathrm{ord}(j)`-th roots crossed with the
four-torus, modulo the cyclic group of deck rotations; writing the punctured root disc in
polar coordinates $`(a, \theta)` splits off the radius, and what is left is the quotient
of $`S^1 \times T^4` by the rotation of $`\theta` by $`1/\mathrm{ord}(j)` coupled with the
affine twist. That quotient is exactly the mapping torus, the identity matching a rotation
by $`1/\mathrm{ord}(j)` with one application of the twist. Admissibility of $`v` makes the
action free, so the quotients are manifolds and the two descriptions agree.
:::

:::definition "def:threefold-overlap-mapping-torus-monodromy" (lean := "Mathoverflow1973.ThreefoldOverlapMappingTorus.monodromy") (parent := "mapping-torus") (uses := "def:flat-torus-affine, def:triangle-compactified-charted-space")
*Definition.* The local monodromy at each puncture of the base. The punctures are indexed
by `Option Elliptic.Kind`: the value `none` is the cusp $`p_0` of the
compactified triangle orbit space, and `some j` is the elliptic point of order $`3` or
$`4`. At the cusp the monodromy is the parabolic homeomorphism
$`\mathrm{cuspTorusHomeomorph}\,1` of the real four-torus; at an elliptic point $`j` it is
the finite-order affine homeomorphism $`\mathrm{flatTorusAffine}(j, v_j)`, where
$`v_1 = \varepsilon` and $`v_2 = -\varepsilon'` are the twist vectors fixed by $`A_1` and
$`A_2`. The sign in $`v_2` is the one that makes $`(\ell_0, \ell_1, \ell_2) = (0, 1, -1)`; the opposite choice gives the comparison threefold with $`\pi_1 \cong \Z/7`. The
boundary model at puncture $`i` is the mapping torus of the monodromy there.
:::

:::definition "def:piece-mapping-torus-homotopy-equiv" (lean := "Mathoverflow1973.ThreefoldOverlapMappingTorus.pieceMappingTorusHomotopyEquiv") (parent := "mapping-torus") (uses := "def:punctured-mapping-torus-homotopy-equiv, def:punctured-product-homeomorph, def:threefold-local-piece, def:threefold-overlap-mapping-torus-monodromy")
*Definition.* Uniformly over all three punctures: the punctured local piece — the filling
piece at $`i` minus its special fibre, that is the part of it lying over the regular patch
of the base — is homotopy equivalent to $`\mathrm{Boundary}(i)`, the mapping torus of the
monodromy at $`i`. The cusp case is the height contraction and the elliptic case the
polar product; the two are packaged by cases on the puncture into one statement. Composed
with the homeomorphism between the punctured piece and the overlap of the piece with the
regular family, it also identifies
$`\mathrm{RegularOverlap}(i) \simeq_h \mathrm{Boundary}(i)`. These are the arrows the
Mayer–Vietoris ladder for $`H_*(X)` plugs into: each special fibre contributes its filling
piece and its boundary, and the boundary is a mapping torus whose homology the Wang
sequence computes.
:::
