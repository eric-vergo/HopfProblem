/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

This module is part of the split of the original single-file `Solution.lean`
of plby/HopfProblem into a thematic module tree.  Full provenance, attribution
and copyright notices are retained in `Solution.lean` at the repository root.
Declarations are verbatim from the original file and keep their original
relative order within each module.  The modules form a single import chain
whose concatenation is a linear extension of the true dependency order of the
original file (computed from the compiled environment): a declaration may
elaborate before some declarations that textually preceded it, but never
before anything it depends on.  Two `private` lemmas whose users fell into a
neighbouring module were made public (`SpecialPeriods.TauCusp.
exists_upperHalfPlane_qParam_small_mo1973_17412` and
`isOpen_qParam_norm_lt_mo1973_17413`); no other declaration text was edited.
-/
import HopfProblem.Hurewicz.ThirdHurewicz

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

theorem PeriodTorusHigherHomology.formalPointCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} (q : ℕ) {c : SingularMayerVietoris.FormalChains V 1}
    {d : SingularMayerVietoris.FormalChains W (q + 1)}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported S 1)
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1)) :
    formalPointCrossProduct q c d ∈
      SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1) := by
  apply
    SingularMayerVietoris.formalLinearMap_mem_of_supported ((formalPointCrossProduct q).flip d)
      (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1)) hc
  intro v hv
  change formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d ∈ _
  rw [formalPointCrossProduct_simplex_left]
  exact
    SingularMayerVietoris.formalMap_mem_supported (S := T) (T := S ×ˢ T) (fun w => (v 0, w))
      (fun _ hw => ⟨hv 0, hw⟩) hd

theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} :
    ∀ (q : ℕ) {c : SingularMayerVietoris.FormalChains V 2}
      {d : SingularMayerVietoris.FormalChains W (q + 1)},
      c ∈ SingularMayerVietoris.formalChainsSupported S 2 →
        d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1) →
          formalEdgeCrossProduct q c d ∈
            SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 2) := by
  intro q
  induction q with
  | zero =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported (formalEdgeCrossProduct 0 c)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) 2) hd
    intro w hw
    rw [formalEdgeCrossProduct_zero_simplex_right]
    exact
      SingularMayerVietoris.formalMap_mem_supported (S := S) (T := S ×ˢ T) (fun v => (v, w 0))
        (fun _ hv => ⟨hv, hw 0⟩) hc
  | succ q ih =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        ((formalEdgeCrossProduct (q + 1)).flip d)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hc
    intro v hv
    change formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v) d ∈ _
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        (formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v))
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hd
    intro w hw
    rw [formalEdgeCrossProduct_simplex_succ]
    apply
      SingularMayerVietoris.formalCone_mem_supported (show (v 0, w 0) ∈ S ×ˢ T from ⟨hv 0, hw 0⟩)
    apply Submodule.sub_mem
    · exact
        formalPointCrossProduct_mem_supported (q + 1)
          (SingularMayerVietoris.formalBoundary_mem_supported 1
            (SingularMayerVietoris.formalSimplex_mem_supported hv))
          (SingularMayerVietoris.formalSimplex_mem_supported hw)
    · exact
        ih (SingularMayerVietoris.formalSimplex_mem_supported hv)
          (SingularMayerVietoris.formalBoundary_mem_supported (q + 1)
            (SingularMayerVietoris.formalSimplex_mem_supported hw))

end Mathoverflow1973

end
