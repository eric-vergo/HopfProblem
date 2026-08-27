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
import HopfProblem.HomologyOfX.ThreefoldHomologyStarCoproduct

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

instance SphereHomology.suspension_middleBand_pathConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : PathConnectedSpace (CuspCentralHomology.Suspension.middleBand X) :=
  (CuspCentralHomology.Suspension.middleBandHomeomorph (X :=
        X)).symm.surjective.pathConnectedSpace
    (CuspCentralHomology.Suspension.middleBandHomeomorph (X := X)).symm.continuous

def SphereHomology.suspensionHomologyOneEquivKernel (X : Type) [TopologicalSpace X] [Nonempty X] :
    SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension X) 1 ≃ₗ[ℤ]
      LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
          ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
          0) :=
  CuspCentralHomology.contractibleCoverHomologyOneEquivKernel
    ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
    ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
    CuspCentralHomology.Suspension.northOpen_isOpen
    CuspCentralHomology.Suspension.southOpen_isOpen CuspCentralHomology.Suspension.open_cover

theorem SphereHomology.suspensionLeftHomologyMap_zero_ker (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
          ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
          0) =
      ⊥ :=
  leftHomologyMap_zero_ker
    ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
    ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))

theorem SphereHomology.suspension_homology_one_subsingleton (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    Subsingleton (SingularMayerVietoris.SingularHomology (CuspCentralHomology.Suspension X) 1) := by
  let :
    Subsingleton
      (LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap
          ((CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X)))
          ((CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X)))
          0)) := by
    rw [suspensionLeftHomologyMap_zero_ker X]
    infer_instance
  exact (suspensionHomologyOneEquivKernel X).injective.subsingleton

theorem SphereHomology.unitSphere_homology_one_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (UnitSphere (n + 2)) 1) := by
  let := suspension_homology_one_subsingleton (UnitSphere (n + 1))
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (suspensionSphereHomeomorph (n + 1)).symm
        1).injective.subsingleton

theorem SphereHomology.unitSphere_homology_subsingleton (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) k) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact (hkn rfl).elim
      | succ k => exact sphereCircle_homology_subsingleton k
  | succ n ih =>
    cases k with
    | zero => exact (hk rfl).elim
    | succ k =>
      cases k with
      | zero => exact unitSphere_homology_one_subsingleton n
      | succ k =>
        let := ih (k + 1) (Nat.succ_ne_zero _) (by omega)
        exact (unitSphereHomologySuspensionEquiv (n + 1) k).injective.subsingleton

end Mathoverflow1973

end
