/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
Hopf problem blueprint — the lattice and monodromy data chapter.

Section 2 of Alpöge's paper: the rank-four lattice, the three local monodromy matrices
of the (3,4,∞) pattern, the contragredient action with its twist vectors and invariant
functional, and the induced action on the exterior powers of the fibre lattice.
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

#doc (Manual) "The lattice and monodromy data" =>

Two integer matrices generate the entire construction. The threefold of {citet alpoge.s6}[]
is a family of complex two-tori over $`\PP^1`, and a family of tori over a punctured base
is, up to the analytic work of realizing it, a lattice together with a monodromy
representation of the fundamental group of the base. Alpöge's base is the orbifold
$`(\PP^1; 3, 4, \infty)`: two cone points of orders $`3` and $`4` at $`t = 0` and $`t = 1`,
and a puncture at $`t = \infty`. Its orbifold fundamental group is the $`(3,4,\infty)`
triangle group $`\Delta \cong \Z/3 * \Z/4`, so a representation of it into $`\mathrm{GL}_4(\Z)`
is exactly a pair of matrices of orders $`3` and $`4` — and those two matrices, written out
in coordinates, are the whole discrete input to the paper.

The formalization takes that description literally. The fibre lattice is `Fin 4 → ℤ`, the
matrices are `!![…]` literals over $`\Z`, and every identity among them — determinants,
orders, duality, fixed vectors, kernels and images — is closed by `decide` on the literal
entries. Nothing here is abstract representation theory; it is a page of finite integer
linear algebra, and the Lean development treats it as such. The one place the encoding
departs from the paper's notation is worth naming at the outset: Alpöge distinguishes the
rank-four module $`V` with ordered basis $`(\gamma, u, w, \delta)` from its dual
$`\Lambda = V^*` with dual basis $`(\hat\gamma, \hat u, \hat w, \hat\delta)`, and the
monodromy acts on $`V` tautologically and on $`\Lambda` through the contragredient
$`\mathfrak{A}(T) = (T^{-1})^{\mathsf T}`. The Lean file carries a single type for both and
distinguishes the two actions by which matrix acts: $`T_1, T_2, T_0` for $`V`, and
$`A_1, A_2, M_0` for $`\Lambda`. Since $`T_1` and $`T_2` have finite order, the
contragredient never requires inverting a matrix — $`A_1 = (T_1^2)^{\mathsf T}` and
$`A_2 = (T_2^3)^{\mathsf T}` are transposes of powers, which is what makes the duality
`decide`-checkable.

Everything downstream consumes this data. The period map of the family is equivariant along
the dual representation; the toric filling over the cusp is governed by the unipotent part
of $`M_0`; the twisting that trivializes $`\pi_1` is indexed by two fixed vectors of
$`A_1` and $`A_2` and by a single $`\Delta`-invariant functional $`\gamma`; and the homology
of the total space is computed from the induced action on $`\Lambda^2` and $`\Lambda^3` of
the fibre lattice. $`M_0` and $`A_1` are, by inbound reference count, the two most heavily
used definitions in the whole development.

:::group "lattice"
The fibre lattice $`\Lambda = \Z^4` and the three local monodromy matrices: $`T_1` and
$`T_2` of orders $`3` and $`4` at the two cone points, and the unipotent $`T_0 = (T_1T_2)^{-1}`
at the cusp.
:::

:::definition "def:lattice" (lean := "Mathoverflow1973.Lattice") (parent := "lattice")
$`\Lambda := \Z^4`, realized as `Fin 4 → ℤ`: the first homology of the complex two-torus
fibre, and the ambient module every monodromy matrix acts on. The companion abbreviation
`LatticeMatrix` is $`M_4(\Z)`, and matrices act on the left by `Matrix.mulVec` (`*ᵥ`), so
the columns of a matrix are the images of the basis vectors. Coordinates are indexed by
`Fin 4`, and index $`0,1,2,3` corresponds to the paper's dual basis
$`\hat\gamma, \hat u, \hat w, \hat\delta` — a fact used silently throughout, since the
fixed-vector and kernel
computations below are stated as conditions on `v 0`, `v 1`, `v 2`. Both `Lattice` and
`LatticeMatrix` are `abbrev`s, hence reducible, so the elaborator sees through them to the
underlying function and matrix types and `decide` can evaluate on them.
:::

:::definition "def:t" (lean := "Mathoverflow1973.T₁") (parent := "lattice") (uses := "def:lattice")
The monodromy at the first cone point, the order-three element of the pattern:

$$`T_1 = \begin{pmatrix} 1 & 0 & -6 & 2 \\ 0 & -1 & 1 & 1 \\ 0 & -1 & 0 & 1 \\ 0 & 0 & 0 & 1 \end{pmatrix}`

Read by columns, $`T_1\gamma = \gamma`, $`T_1u = -u - w`, $`T_1w = -6\gamma + u`, and
$`T_1\delta = 2\gamma + u + w + \delta`. The first column is $`(1,0,0,0)^{\mathsf T}` and the
last row is $`(0,0,0,1)`, so $`T_1` fixes $`\gamma` and acts trivially on the quotient by
$`\langle \gamma, u, w\rangle`; the same holds for $`T_2`, and it is the structural reason
the coinvariant lattice of the monodromy group is free of rank one. Its determinant is
$`1` (`det_T₁`), so it lies in $`\mathrm{SL}_4(\Z)`.
:::

:::definition "def:t-two" (lean := "Mathoverflow1973.T₂") (parent := "lattice") (uses := "def:lattice")
The monodromy at the second cone point, of order four:

$$`T_2 = \begin{pmatrix} 1 & 6 & 0 & -3 \\ 0 & 0 & -1 & 1 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix}`

By columns, $`T_2\gamma = \gamma`, $`T_2u = 6\gamma + w`, $`T_2w = -u`, and
$`T_2\delta = -3\gamma + u + \delta`. Like $`T_1` it has determinant $`1` (`det_T₂`) and
fixes $`\gamma`. The pair $`(T_1, T_2)` is the entire input: the subgroup
$`G = \langle T_1, T_2\rangle \subset \mathrm{SL}_4(\Z)` is the image of the monodromy
representation, and the sixes in $`T_1w = -6\gamma + u` and $`T_2u = 6\gamma + w` are what
eventually produce the value $`6` taken on the pair $`(u, w)` by the essentially unique
invariant alternating form, the discriminant $`-6` attached to it, and the hexagonal toric
geometry over the cusp.
:::

:::definition "def:t-zero" (lean := "Mathoverflow1973.T₀") (parent := "lattice") (uses := "def:lattice")
The cusp monodromy, unipotent:

$$`T_0 = \begin{pmatrix} 1 & 0 & 0 & 1 \\ 0 & 1 & -1 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix}`

Equivalently $`T_0 = I + N` with $`N\gamma = Nu = 0`, $`Nw = -u`, $`N\delta = \gamma`, so
$`N^2 = 0` and $`\ker N = \operatorname{im} N = \langle \gamma, u\rangle`. The paper defines
$`T_0 := (T_1T_2)^{-1}`, matching the triangle-group relation $`g_1g_2g_0 = 1`; the Lean
file gives $`T_0` as a literal and verifies the relation where it is used, in
`SpecialPeriods.triangleLatticeRepresentation_cusp_matrix`, which evaluates the monodromy
representation at the cusp generator $`(g_1g_2)^{-1}` and closes the resulting matrix
identity by `decide`. Rank-two nilpotent monodromy at the puncture is what forces the fibre
to degenerate there, and $`N` drives the whole cusp analysis.
:::

The order relations are the hinge between the geometry and the algebra: they are exactly
what the universal property of a free product of cyclic groups needs. Because
$`\Delta = \langle g_1\rangle * \langle g_2\rangle` with $`g_j` of order $`m_j`, giving a
representation $`\rho_V \colon \Delta \to \mathrm{GL}(V)` amounts to giving matrices
satisfying $`T_1^3 = T_2^4 = I` and nothing more. In the Lean development the two identities
below are restated for the corresponding elements of $`\mathrm{SL}_4(\Z)`, as
`SpecialPeriods.triangleLatticeT₁_cube` and `triangleLatticeT₂_fourth`, and fed to the lift
`SpecialPeriods.triangleLatticeRepresentation` out of the free product.

:::theorem "thm:t-cube" (lean := "Mathoverflow1973.T₁_cube") (parent := "lattice") (uses := "def:t")
*Theorem.* $`T_1^3 = I`.

The order of $`T_1` is exactly $`3`, since $`T_1 \ne I` is visible from the literal. Both
this and the determinant statement `det_T₁` are proved by `decide`: `Matrix (Fin 4) (Fin 4) ℤ`
with `!![…]` entries is a decidable-equality type on which the kernel can evaluate the cube
and compare entrywise, so the proof term is a reflexivity check rather than a tactic script.
The same style closes every matrix identity in this chapter.
:::

:::theorem "thm:t-fourth" (lean := "Mathoverflow1973.T₂_fourth") (parent := "lattice") (uses := "def:t-two")
*Theorem.* $`T_2^4 = I`.

Again exact: $`T_2^2 \ne I`, so $`T_2` has order precisely $`4`. Together with
$`T_1^3 = I` this is the $`(3,4,\infty)` pattern in its entirety — finite orders $`3` and
$`4` at the two cone points, and, since $`T_0 = (T_1T_2)^{-1}` is unipotent rather than of
finite order, infinite order at the puncture.
:::

Dualizing is where the arithmetic that the rest of the paper actually uses lives. The
contragredient $`\mathfrak{A}(T) = (T^{-1})^{\mathsf T}` is the unique automorphism of
$`\Lambda = V^*` with $`\langle \mathfrak{A}(T)\lambda, Tx\rangle = \langle\lambda, x\rangle`;
it is a group homomorphism, so the relation $`T_1T_2T_0 = I` transports to
$`A_1A_2M_0 = I`. The Lean file builds it as `SpecialPeriods.latticeContragredient` on
$`\mathrm{SL}_4(\Z)` and composes to get the dual representation, but the three matrices
themselves are given by literals and matched to the abstract description by `decide`.

:::group "lattice-dual"
The contragredient action on $`\Lambda`: the dual matrices $`A_1, A_2, M_0`, the invariant
functional $`\gamma` and the twist vectors it measures, the kernel–image coincidence at the
cusp, and the induced action on the exterior powers of the fibre lattice.
:::

:::definition "def:a" (lean := "Mathoverflow1973.A₁") (parent := "lattice-dual") (uses := "def:lattice, def:t")
The dual of $`T_1`:

$$`A_1 = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 6 & 0 & 1 & 0 \\ -6 & -1 & -1 & 0 \\ -2 & 1 & 0 & 1 \end{pmatrix}`

so $`A_1\hat\gamma = \hat\gamma + 6\hat u - 6\hat w - 2\hat\delta`,
$`A_1\hat u = -\hat w + \hat\delta`, $`A_1\hat w = \hat u - \hat w`, and $`\hat\delta` is
fixed. That this is the contragredient is `A₁_eq_transpose_sq`:
$`A_1 = (T_1^2)^{\mathsf T}`, which is $`(T_1^{-1})^{\mathsf T}` because $`T_1^3 = I`.
Writing the inverse as a power is the encoding choice that keeps the identity decidable —
no matrix inversion over $`\Z` is ever performed. Its first row is $`(1,0,0,0)`, the
statement that $`\gamma \circ A_1 = \gamma`.
:::

:::definition "def:a-two" (lean := "Mathoverflow1973.A₂") (parent := "lattice-dual") (uses := "def:lattice, def:t-two")
The dual of $`T_2`:

$$`A_2 = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 0 & 0 & -1 & 0 \\ -6 & 1 & 0 & 0 \\ 3 & 0 & 1 & 1 \end{pmatrix}`

that is $`A_2\hat\gamma = \hat\gamma - 6\hat w + 3\hat\delta`, $`A_2\hat u = \hat w`,
$`A_2\hat w = -\hat u + \hat\delta`, with $`\hat\delta` fixed; and
$`A_2 = (T_2^3)^{\mathsf T} = (T_2^{-1})^{\mathsf T}` by `A₂_eq_transpose_cube`, again
because $`T_2^4 = I`. The pair $`(A_1, A_2)` generates the dual monodromy group, and the
Mayer–Vietoris connecting maps of the family are the integer maps
$`\delta(b,c) = (A_1 - I)b + (A_2 - I)c` and their exterior-power analogues — the entire
homology computation for the total space is the kernel-and-cokernel analysis of that one
family of matrices.
:::

:::definition "def:m" (lean := "Mathoverflow1973.M₀") (parent := "lattice-dual") (uses := "def:lattice, def:t-zero")
The dual cusp monodromy:

$$`M_0 = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 1 & 1 & 0 \\ -1 & 0 & 0 & 1 \end{pmatrix}`

so $`M_0\hat\gamma = \hat\gamma - \hat\delta`, $`M_0\hat u = \hat u + \hat w`, and
$`\hat w, \hat\delta` are fixed; equivalently $`M_0 = I - N^{\mathsf T}`. It is the dual of
$`T_0`, verified as such in `SpecialPeriods.triangleDualRepresentation_cusp_matrix`, and it
satisfies $`A_1A_2M_0 = I` in step with $`g_1g_2g_0 = 1`. Its unipotent difference is
completely explicit: `M₀_sub_one_mulVec` gives $`(M_0 - I)v = (0, 0, v_1, -v_0)`. Every
coinvariant computation over the cusp — the Wang-sequence input for the homology of the
cusp neighbourhood, and the local system on the punctured disc — is run against this one
matrix, which makes it the single most-referenced definition of the development.
:::

:::definition "def:gamma" (lean := "Mathoverflow1973.γ") (parent := "lattice-dual") (uses := "def:lattice")
The functional $`\gamma \colon \Lambda \to \Z`, $`\gamma(v) = v_0` — evaluation at the basis
vector $`\gamma \in V`, so that $`\gamma(a\hat\gamma + b\hat u + c\hat w + d\hat\delta) = a`
and $`\ker\gamma = \langle \hat u, \hat w, \hat\delta\rangle`. Its significance is
invariance: the first row of each of $`A_1`, $`A_2` and $`M_0` is $`(1,0,0,0)`, so
$`\gamma \circ A_1 = \gamma \circ A_2 = \gamma \circ M_0 = \gamma`, and $`\gamma` is
therefore constant on monodromy orbits. That is what makes the twist invariants
$`\ell_j = \gamma(v_j)` well defined, and it is the reason $`\gamma` — not any other
coordinate — is the functional through which the image of the fibre lattice in
$`\pi_1(X)` is indexed.
:::

:::definition "def:epsilon" (lean := "Mathoverflow1973.ε") (parent := "lattice-dual") (uses := "def:lattice")
The twist vector $`\varepsilon = (1, 2, -4, 0)`, that is
$`\hat\gamma + 2\hat u - 4\hat w`. It is fixed by $`A_1` (`A₁_fixes_ε`, by `decide`) and has
$`\gamma(\varepsilon) = 1`. Its companion `ε'` is
$`\varepsilon' = (1, 3, -3, 0) = \hat\gamma + 3\hat u - 3\hat w`, fixed by $`A_2` with
$`\gamma(\varepsilon') = 1` (`γ_ε'`).
The paper's twist data is $`v_1 = \varepsilon`, $`v_2 = -\varepsilon'`, with invariants
$`(\ell_0, \ell_1, \ell_2) = (0, 1, -1)`; those three integers are what the order
$`12\ell_0 - 4\ell_1 - 3\ell_2` of $`\pi_1(X)` is computed from, and at $`(0,1,-1)` it is
$`-1`, so the group is trivial. The link back to $`\gamma` is
`LatticeCuspNormalClosure.image_eq_zpow_gamma`: any homomorphism out of $`\Lambda`
satisfying the van Kampen relations sends $`v \mapsto \varphi(\varepsilon)^{\gamma(v)}`.
:::

:::theorem "thm:a-fixed-iff" (lean := "Mathoverflow1973.A₁_fixed_iff") (parent := "lattice-dual") (uses := "def:a")
*Theorem.* For $`v \in \Lambda`, $`A_1 v = v` if and only if $`v_1 = 2v_0` and
$`v_2 = -4v_0`.

The fixed sublattice is therefore
$`\Lambda^{A_1} = \{(a, 2a, -4a, d)\} = \langle \varepsilon, \hat\delta\rangle`, free of
rank two and saturated in $`\Lambda`: no
condition is placed on $`v_3`, and the two conditions are $`\Z`-linear with unit leading
coefficients. The companion `A₂_fixed_iff` reads $`v_1 = 3v_0`, $`v_2 = -3v_0`, giving
$`\Lambda^{A_2} = \langle\varepsilon', \hat\delta\rangle`. Intersecting the two forces
$`v_0 = 0`, so $`\Lambda^{A_1} \cap \Lambda^{A_2} = \Z\hat\delta` — the rank-one invariant
lattice of the full dual action, which is what generates the vertical vector field on the
threefold.
:::

:::proof "thm:a-fixed-iff"
Both directions are the four scalar equations $`(A_1v)_i = v_i` read off the literal.
Forward, the rows for $`i = 1, 2, 3` give $`6v_0 + v_2 = v_1`, $`-6v_0 - v_1 - v_2 = v_2`
and $`-2v_0 + v_1 + v_3 = v_3`; the last is $`v_1 = 2v_0`, and substituting into the first
gives $`v_2 = -4v_0`. Backward, substituting $`v_1 = 2v_0` and $`v_2 = -4v_0` into all four
rows leaves identities in $`v_0` and $`v_3`. The Lean proof does exactly this: `simp` on
the matrix literal to expose the row equations, then `omega` for the linear-integer step.
$`\blacksquare`
:::

:::theorem "thm:m-sub-one-range" (lean := "Mathoverflow1973.M₀_sub_one_range") (parent := "lattice-dual") (uses := "def:m")
*Theorem.* A vector $`v \in \Lambda` lies in the image of $`M_0 - I` if and only if
$`v_0 = v_1 = 0`.

The companion `M₀_sub_one_kernel` gives the same condition for the kernel, so kernel and
image coincide, both equal to
$`\Lambda_{\mathrm{tor}} := \langle \hat w, \hat\delta\rangle`.
This coincidence — an exact square-zero pattern, the dual form of
$`N^2 = 0` — is the whole local structure at the puncture: the invariants of the cusp
monodromy are a rank-two direct summand, the variation lands in exactly that summand, and
$`M_0 - I` therefore induces a map
$`\Lambda/\Lambda_{\mathrm{tor}} \to \Lambda_{\mathrm{tor}}` between two free rank-two
modules. Whether that induced map is an isomorphism is the question $`B_0` answers.
:::

:::proof "thm:m-sub-one-range"
By `M₀_sub_one_mulVec`, $`(M_0 - I)w = (0, 0, w_1, -w_0)`, which visibly has vanishing first
two coordinates, giving one inclusion. Conversely, given $`v` with $`v_0 = v_1 = 0`, the
explicit preimage $`w = (-v_3, v_2, 0, 0)` satisfies $`(M_0 - I)w = (0, 0, v_2, v_3) = v`.
The kernel statement is the same computation read the other way: $`(0,0,w_1,-w_0) = 0`
holds exactly when $`w_0 = w_1 = 0`. $`\blacksquare`
:::

:::definition "def:b-zero" (lean := "Mathoverflow1973.B₀") (parent := "lattice-dual") (uses := "def:m")
The two-by-two block $`B_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}`. Because
$`M_0 - I` has equal kernel and image
$`\Lambda_{\mathrm{tor}} = \langle\hat w, \hat\delta\rangle`, it induces a map
$`\overline\Lambda = \Lambda/\Lambda_{\mathrm{tor}} \to \Lambda_{\mathrm{tor}}`,
and in the bases $`(\bar{\hat\gamma}, \bar{\hat u})` and
$`(\hat w, \hat\delta)` that map is $`B_0`: from $`(M_0 - I)v = (0, 0, v_1, -v_0)` one reads
$`\bar{\hat\gamma} \mapsto -\hat\delta` and $`\bar{\hat u} \mapsto \hat w`. Its determinant
is $`1`. That unimodularity is the arithmetic fact behind the shape of the degenerate
fibre: $`B_0\overline\Lambda = \Lambda_{\mathrm{tor}}` exactly, so the toric filling over the
cusp has an irreducible central fibre containing a single copy of the degree-six del Pezzo
surface, where $`|\det B_0| = k` would give $`k` components. In the development $`B_0`
resurfaces as the logarithmic term of the cusp period matrix, in
`CuspUniformization.logarithmicPeriod`, which is $`s \cdot B_0` plus a term depending only
on $`\exp(s)`.
:::

Passing from the fibre to its higher homology means passing to exterior powers of
$`\Lambda`. The development does this concretely rather than through an exterior algebra:
for a $`4 \times 4` integer matrix it writes down the matrices of $`\Lambda^2` and
$`\Lambda^3` as arrays of minors, indexed by the six increasing pairs and the four
increasing triples from $`\{0,1,2,3\}`. With the wedge basis in increasing index order this
is exactly the induced map — no signs are needed — and the resulting matrices are again
integer literals, so the identities about them stay decidable. The instances used are
$`\Lambda^2` and $`\Lambda^3` of $`A_1`, $`A_2` and $`M_0`, whose explicit values are
recorded as `decide`-proved equalities; among them $`\Lambda^3 M_0 = M_0`
(`CuspCoinvariants.cubeM₀_eq_M₀`), so the degree-three coinvariants at the cusp are
computed by the same matrix as the degree-one ones.

:::definition "def:exterior-square" (lean := "Mathoverflow1973.LocalSystemMatrices.exteriorSquare") (parent := "lattice-dual") (uses := "def:lattice")
For $`T \in M_4(\Z)`, the $`6 \times 6` integer matrix of the induced map on
$`\Lambda^2\Z^4`, with $`(i,j)` entry the $`2 \times 2` minor of $`T` on the rows indexed by
the $`i`-th pair and the columns indexed by the $`j`-th pair, the six pairs being
$`(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)` in that order (`pairIndices`). Since the wedge
basis $`e_i \wedge e_j` is taken in increasing order, the matrix of $`\Lambda^2 T` in that
basis is precisely this array of minors. Applied to the dual monodromy it gives the local
system on $`H_2` of the torus fibre, whose coinvariants and invariants are read off by
`decide` from the resulting explicit matrices.
:::

:::definition "def:exterior-cube" (lean := "Mathoverflow1973.LocalSystemMatrices.exteriorCube") (parent := "lattice-dual") (uses := "def:lattice")
The same construction one degree up: for $`T \in M_4(\Z)`, the $`4 \times 4` matrix of
$`\Lambda^3 T`, with $`(i,j)` entry the $`3 \times 3` minor of $`T` on the rows and columns
given by the $`i`-th and $`j`-th increasing triples $`(0,1,2), (0,1,3), (0,2,3), (1,2,3)`
(`tripleIndices`). Together with the square this supplies the monodromy on $`H_2` and
$`H_3` of the four-torus fibre; $`H_1` is $`\Lambda` itself and $`H_4` is the determinant,
which is $`1` for all three matrices, so the full local system on the homology of the fibre
is generated by $`A_1`, $`A_2`, $`M_0` and their exterior powers.
:::

What this section fixes is small and completely explicit, and the rest of the argument is
the work of realizing it. The two matrices $`T_1, T_2` determine $`T_0`, the dual triple
$`A_1, A_2, M_0`, the invariant functional $`\gamma`, the two fixed vectors
$`\varepsilon, \varepsilon'`, the unimodular block $`B_0`, and the induced action on all
exterior powers — every one of them a table of integers checkable by evaluation. The
analytic content begins where these matrices have to be realized as the monodromy of an
actual holomorphic family of two-tori over the punctured base, and the topological content
begins where the resulting total space has to be completed over the cusp and the two cone
points, and its homotopy type computed. Both computations are run, at every stage, against
the matrices above.
