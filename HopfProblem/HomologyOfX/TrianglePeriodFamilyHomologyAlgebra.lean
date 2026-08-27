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
import HopfProblem.PeriodFamily.Core3

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

def TrianglePeriodFamilyHomologyAlgebra.diagonalCokernelProjection {H K : Type*} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] (f : K →ₗ[ℤ] H) :
    (H × H) →ₗ[ℤ] H ⧸ LinearMap.range f :=
  (LinearMap.range f).mkQ.comp (LinearMap.snd ℤ H H)

@[instance_reducible]
def TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule {B : Type u} [AddCommGroup B]
    [Module ℤ B] (p : Submodule ℤ B) : Module ℤ (B ⧸ p) :=
  Submodule.Quotient.module p

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule in
@[instance_reducible]
def TrianglePeriodFamilyHomologyAlgebra.kernelModule {D : Type u} [AddCommGroup D] [Module ℤ D]
    (p : Submodule ℤ D) : Module ℤ p :=
  Submodule.module p

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
def TrianglePeriodFamilyHomologyAlgebra.cokernelToMiddle {A B C : Type u} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (f : A →ₗ[ℤ] B)
    (j : B →ₗ[ℤ] C) (hfj : Function.Exact f j) : (B ⧸ LinearMap.range f) →ₗ[ℤ] C :=
  (LinearMap.range f).liftQ j hfj.linearMap_ker_eq.ge

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
theorem TrianglePeriodFamilyHomologyAlgebra.cokernelToMiddle_injective {A B C : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (hfj : Function.Exact f j) :
    Function.Injective (cokernelToMiddle f j hfj) := by
  apply LinearMap.ker_eq_bot.mp
  exact (LinearMap.range f).ker_liftQ_eq_bot j _ hfj.linearMap_ker_eq.le

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
def TrianglePeriodFamilyHomologyAlgebra.middleToKernel {C D E : Type u} [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [Module ℤ C] [Module ℤ D] [Module ℤ E] (δ : C →ₗ[ℤ] D)
    (d : D →ₗ[ℤ] E) (hδd : Function.Exact δ d) : C →ₗ[ℤ] LinearMap.ker d :=
  δ.codRestrict (LinearMap.ker d) hδd.apply_apply_eq_zero

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
theorem TrianglePeriodFamilyHomologyAlgebra.middleToKernel_surjective {C D E : Type u}
    [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E) (hδd : Function.Exact δ d) :
    Function.Surjective (middleToKernel δ d hδd) := by
  intro y
  obtain ⟨c, hc⟩ := (hδd y.1).mp y.2
  exact ⟨c, Subtype.ext hc⟩

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
theorem TrianglePeriodFamilyHomologyAlgebra.middleToKernel_comp_cokernelToMiddle
    {A B C D E : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E) (hfj : Function.Exact f j)
    (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d) :
    (middleToKernel δ d hδd).comp (cokernelToMiddle f j hfj) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨b, rfl⟩ := (LinearMap.range f).mkQ_surjective q
  apply Subtype.ext
  change δ (j b) = 0
  exact hjδ.apply_apply_eq_zero b

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
theorem TrianglePeriodFamilyHomologyAlgebra.cokernelToMiddle_middleToKernel_exact
    {A B C D E : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (f : A →ₗ[ℤ] B) (j : B →ₗ[ℤ] C) (δ : C →ₗ[ℤ] D) (d : D →ₗ[ℤ] E) (hfj : Function.Exact f j)
    (hjδ : Function.Exact j δ) (hδd : Function.Exact δ d) :
    Function.Exact (cokernelToMiddle f j hfj) (middleToKernel δ d hδd) := by
  intro c
  constructor
  · intro hc
    have hδc : δ c = 0 := congrArg Subtype.val hc
    obtain ⟨b, hb⟩ := (hjδ c).mp hδc
    exact ⟨(LinearMap.range f).mkQ b, hb⟩
  · rintro ⟨q, rfl⟩
    exact LinearMap.congr_fun (middleToKernel_comp_cokernelToMiddle f j δ d hfj hjδ hδd) q

def TrianglePeriodFamilyHomologyAlgebra.overlapKerEquiv {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) : LinearMap.ker (overlapMap P Q) ≃ₗ[ℤ] LinearMap.ker (delta P Q) :=
  ({    toFun x := ⟨x.val.2, ((overlapMap_eq_zero_iff P Q x.val).mp x.property).2⟩
        invFun
          y :=
          ⟨(-y.val.1 - y.val.2, y.val),
            (overlapMap_eq_zero_iff P Q _).mpr ⟨by dsimp; abel, y.property⟩⟩
        left_inv
          x := by
          apply Subtype.ext
          apply Prod.ext
          · have h := ((overlapMap_eq_zero_iff P Q x.val).mp x.property).1
            change -x.val.2.1 - x.val.2.2 = x.val.1
            calc
              -x.val.2.1 - x.val.2.2 = x.val.1 - (x.val.1 + x.val.2.1 + x.val.2.2) := by abel
              _ = x.val.1 := by rw [h, sub_zero]
          · rfl
        right_inv _ := rfl
        map_add' _ _ := rfl } :
      LinearMap.ker (overlapMap P Q) ≃+ LinearMap.ker (delta P Q)).toIntLinearEquiv

def TrianglePeriodFamilyHomologyAlgebra.overlapCokernelProjection {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) : (H × H) →ₗ[ℤ] H ⧸ LinearMap.range (delta P Q) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((diagonalCokernelProjection (delta P Q)).toAddMonoidHom.comp
      (rowEquiv H).toAddEquiv.toAddMonoidHom)

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.overlapCokernelProjection_apply {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H) (y : H × H) :
    overlapCokernelProjection P Q y = Submodule.Quotient.mk (-y.1 - y.2) :=
  rfl

theorem TrianglePeriodFamilyHomologyAlgebra.overlapCokernelProjection_surjective {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H) :
    Function.Surjective (overlapCokernelProjection P Q) := by
  intro q
  obtain ⟨y, rfl⟩ := (LinearMap.range (delta P Q)).mkQ_surjective q
  refine ⟨(0, -y), ?_⟩
  simp only [overlapCokernelProjection_apply, neg_zero, zero_sub, neg_neg]
  rfl

theorem TrianglePeriodFamilyHomologyAlgebra.overlapMap_range_eq_ker_projection {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H) :
    LinearMap.range (overlapMap P Q) = LinearMap.ker (overlapCokernelProjection P Q) := by
  ext y
  rw [overlapMap_mem_range_iff]
  change
    -y.1 - y.2 ∈ LinearMap.range (delta P Q) ↔
      (Submodule.Quotient.mk (-y.1 - y.2) : H ⧸ LinearMap.range (delta P Q)) = 0
  exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range (delta P Q)) (x := -y.1 - y.2)).symm

def TrianglePeriodFamilyHomologyAlgebra.overlapCokernelEquiv {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) :
    ((H × H) ⧸ LinearMap.range (overlapMap P Q)) ≃ₗ[ℤ] H ⧸ LinearMap.range (delta P Q) :=
  ((Submodule.quotEquivOfEq _ _ (overlapMap_range_eq_ker_projection P Q)).toAddEquiv.trans
      ((overlapCokernelProjection P Q).quotKerEquivOfSurjective
          (overlapCokernelProjection_surjective P Q)).toAddEquiv).toIntLinearEquiv

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.overlapCokernelEquiv_mk {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (y : H × H) :
    overlapCokernelEquiv P Q (Submodule.Quotient.mk y) = Submodule.Quotient.mk (-y.1 - y.2) := by
  change
    (overlapCokernelProjection P Q).quotKerEquivOfSurjective
        (overlapCokernelProjection_surjective P Q)
        (Submodule.quotEquivOfEq _ _ (overlapMap_range_eq_ker_projection P Q)
          (Submodule.Quotient.mk y)) =
      _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    overlapCokernelProjection_apply]

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.overlapCokernelEquiv_symm_mk {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H) (y : H) :
    (overlapCokernelEquiv P Q).symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk (0, -y) := by
  apply (overlapCokernelEquiv P Q).injective
  rw [LinearEquiv.apply_symm_apply, overlapCokernelEquiv_mk]
  simp only [neg_zero, zero_sub, neg_neg]

def TrianglePeriodFamilyHomologyAlgebra.inverseFirstCoordinate {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P : H ≃ₗ[ℤ] H) : (H × H) ≃ₗ[ℤ] (H × H) :=
  ({    toFun x := (-P.symm x.1, x.2)
        invFun x := (-P x.1, x.2)
        left_inv x := by simp
        right_inv x := by simp
        map_add' x y := by simp [map_add, add_comm] } : (H × H) ≃+ (H × H)).toIntLinearEquiv

def TrianglePeriodFamilyHomologyAlgebra.inverseSecondCoordinate {H : Type*} [AddCommGroup H]
    [Module ℤ H] (Q : H ≃ₗ[ℤ] H) : (H × H) ≃ₗ[ℤ] (H × H) :=
  ({    toFun x := (x.1, -Q.symm x.2)
        invFun x := (x.1, -Q x.2)
        left_inv x := by simp
        right_inv x := by simp
        map_add' x y := by simp [map_add, add_comm] } : (H × H) ≃+ (H × H)).toIntLinearEquiv

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.inverseFirstCoordinate_apply {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P : H ≃ₗ[ℤ] H) (x : H × H) :
    inverseFirstCoordinate P x = (-P.symm x.1, x.2) :=
  rfl

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.inverseSecondCoordinate_apply {H : Type*}
    [AddCommGroup H] [Module ℤ H] (Q : H ≃ₗ[ℤ] H) (x : H × H) :
    inverseSecondCoordinate Q x = (x.1, -Q.symm x.2) :=
  rfl

theorem TrianglePeriodFamilyHomologyAlgebra.delta_inverse_first {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P : H ≃ₗ[ℤ] H) (Q : H →ₗ[ℤ] H) (x : H × H) :
    delta P.toLinearMap Q (inverseFirstCoordinate P x) = delta P.symm.toLinearMap Q x := by
  simp only [delta_apply, inverseFirstCoordinate_apply, LinearEquiv.coe_coe, map_neg,
    LinearEquiv.apply_symm_apply]
  abel

theorem TrianglePeriodFamilyHomologyAlgebra.delta_inverse_second {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P : H →ₗ[ℤ] H) (Q : H ≃ₗ[ℤ] H) (x : H × H) :
    delta P Q.toLinearMap (inverseSecondCoordinate Q x) = delta P Q.symm.toLinearMap x := by
  simp only [delta_apply, inverseSecondCoordinate_apply, LinearEquiv.coe_coe, map_neg,
    LinearEquiv.apply_symm_apply]
  abel

theorem TrianglePeriodFamilyHomologyAlgebra.range_eq_of_coordinates {H : Type*} [AddCommGroup H]
    [Module ℤ H] (f g : (H × H) →ₗ[ℤ] H) (e : (H × H) ≃ₗ[ℤ] (H × H)) (he : ∀ x, f (e x) = g x) :
    LinearMap.range g = LinearMap.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, he x⟩
  · rintro ⟨x, rfl⟩
    refine ⟨e.symm x, ?_⟩
    rw [← he, LinearEquiv.apply_symm_apply]

def TrianglePeriodFamilyHomologyAlgebra.kernelEquivOfCoordinates {H : Type*} [AddCommGroup H]
    [Module ℤ H] (f g : (H × H) →ₗ[ℤ] H) (e : (H × H) ≃ₗ[ℤ] (H × H)) (he : ∀ x, f (e x) = g x) :
    LinearMap.ker g ≃ₗ[ℤ] LinearMap.ker f :=
  ({    toFun x := ⟨e x.val, by rw [LinearMap.mem_ker, he]; exact x.property⟩
        invFun
          y :=
          ⟨e.symm y.val,
            by
            rw [LinearMap.mem_ker, ← he, LinearEquiv.apply_symm_apply]
            exact y.property⟩
        left_inv x := Subtype.ext (e.symm_apply_apply x.val)
        right_inv y := Subtype.ext (e.apply_symm_apply y.val)
        map_add' x y := Subtype.ext (e.map_add x.val y.val) } :
      LinearMap.ker g ≃+ LinearMap.ker f).toIntLinearEquiv

def TrianglePeriodFamilyHomologyAlgebra.integralQuotientCongr {H : Type*} [AddCommGroup H]
    [Module ℤ H] (S T : Submodule ℤ H) (h : S = T) : (H ⧸ S) ≃ₗ[ℤ] (H ⧸ T) :=
  ({    toEquiv :=
          @Quotient.congr H H (Submodule.quotientRel S) (Submodule.quotientRel T) (Equiv.refl H)
            (fun _ _ => by rw [h]; rfl)
        map_add' := by
          rintro ⟨x⟩ ⟨y⟩
          rfl } :
      (H ⧸ S) ≃+ (H ⧸ T)).toIntLinearEquiv

end Mathoverflow1973

end
