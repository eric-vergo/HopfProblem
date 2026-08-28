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
import HopfProblem.PeriodFamily.Core4

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

def TrianglePeriodFamilyHomologySplitting.freeRightSection {M K : Type*} [AddCommGroup M]
    [AddCommGroup K] [Module ℤ M] [Module ℤ K] [Module.Free ℤ K] (g : M →ₗ[ℤ] K)
    (hg : Function.Surjective g) : K →ₗ[ℤ] M :=
  Classical.choose (Module.projective_lifting_property g (LinearMap.id : K →ₗ[ℤ] K) hg)

theorem TrianglePeriodFamilyHomologySplitting.freeRightSection_comp {M K : Type*} [AddCommGroup M]
    [AddCommGroup K] [Module ℤ M] [Module ℤ K] [Module.Free ℤ K] (g : M →ₗ[ℤ] K)
    (hg : Function.Surjective g) : g.comp (freeRightSection g hg) = LinearMap.id :=
  Classical.choose_spec (Module.projective_lifting_property g (LinearMap.id : K →ₗ[ℤ] K) hg)

@[simp]
theorem TrianglePeriodFamilyHomologySplitting.freeRightSection_rightInverse {M K : Type*}
    [AddCommGroup M] [AddCommGroup K] [Module ℤ M] [Module ℤ K] [Module.Free ℤ K] (g : M →ₗ[ℤ] K)
    (hg : Function.Surjective g) (k : K) : g (freeRightSection g hg k) = k :=
  LinearMap.congr_fun (freeRightSection_comp g hg) k

def TrianglePeriodFamilyHomologySplitting.freeRightSumMap {L M K : Type*} [AddCommGroup L]
    [AddCommGroup M] [AddCommGroup K] [Module ℤ L] [Module ℤ M] [Module ℤ K] [Module.Free ℤ K]
    (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K) (hg : Function.Surjective g) : (L × K) →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun x := f x.1 + freeRightSection g hg x.2
      map_zero' := by simp
      map_add' x
        y := by
        dsimp
        rw [map_add, map_add]
        exact add_add_add_comm _ _ _ _ }

@[simp]
theorem TrianglePeriodFamilyHomologySplitting.freeRightSumMap_apply {L M K : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup K] [Module ℤ L] [Module ℤ M] [Module ℤ K]
    [Module.Free ℤ K] (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K) (hg : Function.Surjective g) (x : L × K) :
    freeRightSumMap f g hg x = f x.1 + freeRightSection g hg x.2 :=
  rfl

theorem TrianglePeriodFamilyHomologySplitting.freeRightSumMap_injective {L M K : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup K] [Module ℤ L] [Module ℤ M] [Module ℤ K]
    [Module.Free ℤ K] (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K) (hex : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Function.Injective (freeRightSumMap f g hg) := by
  rintro ⟨a, k⟩ ⟨a', k'⟩ h
  change f a + freeRightSection g hg k = f a' + freeRightSection g hg k' at h
  have hk : k = k' := by
    have h' := congrArg g h
    simpa only [map_add, hex.apply_apply_eq_zero, freeRightSection_rightInverse, zero_add] using
      h'
  subst k'
  exact Prod.ext (hf (add_right_cancel h)) rfl

theorem TrianglePeriodFamilyHomologySplitting.freeRightSumMap_surjective {L M K : Type*}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup K] [Module ℤ L] [Module ℤ M] [Module ℤ K]
    [Module.Free ℤ K] (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K) (hex : Function.Exact f g)
    (hg : Function.Surjective g) : Function.Surjective (freeRightSumMap f g hg) := by
  intro m
  have hm : g (m - freeRightSection g hg (g m)) = 0 := by
    rw [map_sub, freeRightSection_rightInverse, sub_self]
  obtain ⟨a, ha⟩ := (hex _).mp hm
  refine ⟨(a, g m), ?_⟩
  rw [freeRightSumMap_apply, ha, sub_add_cancel]

def TrianglePeriodFamilyHomologySplitting.freeRightSplitEquiv {L M K : Type*} [AddCommGroup L]
    [AddCommGroup M] [AddCommGroup K] [Module ℤ L] [Module ℤ M] [Module ℤ K] [Module.Free ℤ K]
    (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K) (hex : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) : M ≃ₗ[ℤ] (L × K) :=
  (LinearEquiv.ofBijective (freeRightSumMap f g hg)
      ⟨freeRightSumMap_injective f g hex hf hg, freeRightSumMap_surjective f g hex hg⟩).symm

def TrianglePeriodFamilyHomologyFreeCoordinates.freeCoordinateSumEquiv (a b : ℕ) :
    ((Fin a → ℤ) × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (a + b) → ℤ) :=
  (((LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℤ ℤ).symm.toAddEquiv).trans
      (LinearEquiv.piCongrLeft' ℤ (fun _ : Fin a ⊕ Fin b => ℤ)
          (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).toAddEquiv).toIntLinearEquiv

def TrianglePeriodFamilyHomologyFreeCoordinates.integerFreeCoordinateEquiv (b : ℕ) :
    (ℤ × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (1 + b) → ℤ) :=
  ((((LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.toAddEquiv.prodCongr
          (AddEquiv.refl (Fin b → ℤ))).trans
      (freeCoordinateSumEquiv 1 b).toAddEquiv)).toIntLinearEquiv

end Mathoverflow1973

end
