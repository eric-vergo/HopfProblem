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
import HopfProblem.Pi1.ThreefoldOverlapMappingTorus2

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

def FreeMeridianMarking.orientedClass (reverse b : Bool) :
    FundamentalGroup SpecialPeriods.Triangle.TwicePuncturedPlane
      SpecialPeriods.Triangle.meridianBasepoint :=
  if reverse then (SpecialPeriods.Triangle.meridianClass b)⁻¹
  else SpecialPeriods.Triangle.meridianClass b

@[simp]
theorem FreeMeridianMarking.orientedClass_true (b : Bool) :
    orientedClass Bool.true b = (SpecialPeriods.Triangle.meridianClass b)⁻¹ :=
  rfl

def FreeMeridianMarking.orientedEquiv (reverse : Bool) :
    FundamentalGroup SpecialPeriods.Triangle.TwicePuncturedPlane
        SpecialPeriods.Triangle.meridianBasepoint ≃*
      FreeGroup Bool :=
  reorient SpecialPeriods.Triangle.twicePuncturedFundamentalGroupFreeEquiv reverse

@[simp]
theorem FreeMeridianMarking.orientedEquiv_symm_of (reverse b : Bool) :
    (orientedEquiv reverse).symm (FreeGroup.of b) = orientedClass reverse b := by
  simp only [orientedEquiv, reorient_symm_of,
    SpecialPeriods.Triangle.twicePuncturedFundamentalGroupFreeEquiv_symm_of, orientedClass]

@[simp]
theorem FreeMeridianMarking.orientedEquiv_orientedClass (reverse b : Bool) :
    orientedEquiv reverse (orientedClass reverse b) = FreeGroup.of b := by
  rw [← orientedEquiv_symm_of, MulEquiv.apply_symm_apply]

theorem fundamentalGroup_basepoint_change_apply {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (p : Path x₀ x₁) (γ : FundamentalGroup X x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p γ =
      (Path.Homotopic.Quotient.mk p).symm.trans (γ.trans (Path.Homotopic.Quotient.mk p)) :=
  rfl

theorem fundamentalGroup_basepoint_change_mk {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (p : Path x₀ x₁) (γ : Path x₀ x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p (Path.Homotopic.Quotient.mk γ) =
      Path.Homotopic.Quotient.mk (p.symm.trans (γ.trans p)) :=
  rfl

theorem fundamentalGroup_basepoint_naturality {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ x₁ : X} (f : C(X, Y)) (p : Path x₀ x₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f x₀) =
      (FundamentalGroup.map f x₁).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom := by
  apply MonoidHom.ext
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk
    γ =>
    change
      Path.Homotopic.Quotient.mk
          ((p.map f.continuous).symm.trans ((γ.map f.continuous).trans (p.map f.continuous))) =
        Path.Homotopic.Quotient.mk ((p.symm.trans (γ.trans p)).map f.continuous)
    apply congrArg Path.Homotopic.Quotient.mk
    rw [Path.map_trans, Path.map_trans, Path.map_symm]

theorem fundamentalGroup_basepoint_naturality_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ x₁ : X} (f : C(X, Y)) (p : Path x₀ x₁) (γ : FundamentalGroup X x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x₀ γ) =
      FundamentalGroup.map f x₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ) :=
  DFunLike.congr_fun (fundamentalGroup_basepoint_naturality f p) γ

theorem fundamentalGroup_map_surjective_at_of_path {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ x₁ : X} (f : C(X, Y)) (p : Path x₀ x₁)
    (hf : Function.Surjective (FundamentalGroup.map f x₀)) :
    Function.Surjective (FundamentalGroup.map f x₁) := by
  intro γ
  obtain ⟨δ, rfl⟩ :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)).surjective γ
  obtain ⟨ε, hε⟩ := hf δ
  refine ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath p ε, ?_⟩
  exact
    (fundamentalGroup_basepoint_naturality_apply f p ε).symm.trans
      (congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)) hε)

theorem fundamentalGroup_map_surjective_at_of_pathConnected {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] (f : C(X, Y)) (x₀ x₁ : X)
    (hf : Function.Surjective (FundamentalGroup.map f x₀)) :
    Function.Surjective (FundamentalGroup.map f x₁) :=
  fundamentalGroup_map_surjective_at_of_path f (PathConnectedSpace.somePath x₀ x₁) hf

theorem covering_exists_restricted_loop_homotopic {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [SimplyConnectedSpace E] {p : E → X} (hp : IsCoveringMap p) (S : Set X)
    (hS : IsPathConnected (p ⁻¹' S)) (e : E) (he : p e ∈ S) (γ : Path (p e) (p e)) :
    ∃ δ : Path (⟨p e, he⟩ : S) ⟨p e, he⟩, (δ.map continuous_subtype_val).Homotopic γ := by
  obtain ⟨Γ, hΓ, hΓ₀⟩ := hp.exists_path_lifts γ e γ.source
  have hΓ₁ : p (Γ 1) = p e := (congr_fun hΓ 1).trans γ.target
  let Γ' : Path e (Γ 1) := ⟨Γ, hΓ₀, rfl⟩
  obtain ⟨Δ, hΔ⟩ :=
    hS.joinedIn e he (Γ 1)
      (by
        change p (Γ 1) ∈ S
        rwa [hΓ₁])
  let δ : Path (⟨p e, he⟩ : S) ⟨p e, he⟩ :=
    { toFun t := ⟨p (Δ t), hΔ t⟩
      continuous_toFun := (hp.continuous.comp Δ.continuous).subtype_mk _
      source' := Subtype.ext (congrArg p Δ.source)
      target' := Subtype.ext ((congrArg p Δ.target).trans hΓ₁) }
  have hδ : δ.map continuous_subtype_val = (Δ.map hp.continuous).cast rfl hΓ₁.symm := by
    ext t
    rfl
  have hγ : (Γ'.map hp.continuous).cast rfl hΓ₁.symm = γ := by
    ext t
    exact congr_fun hΓ t
  have H :=
    ((SimplyConnectedSpace.paths_homotopic Δ Γ').map (⟨p, hp.continuous⟩ : C(E, X))).pathCast rfl
      hΓ₁.symm
  exact ⟨δ, by simpa only [← hδ, hγ] using H⟩

theorem covering_restriction_fundamentalGroup_map_surjective_at {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [SimplyConnectedSpace E] {p : E → X} (hp : IsCoveringMap p) (S : Set X)
    (hS : IsPathConnected (p ⁻¹' S)) (e : E) (he : p e ∈ S) :
    Function.Surjective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) ⟨p e, he⟩) := by
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    obtain ⟨δ, hδ⟩ := covering_exists_restricted_loop_homotopic hp S hS e he γ
    exact ⟨Path.Homotopic.Quotient.mk δ, Path.Homotopic.Quotient.eq.mpr hδ⟩

theorem covering_restriction_fundamentalGroup_map_surjective {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [SimplyConnectedSpace E] {p : E → X} (hp : IsCoveringMap p)
    (hps : Function.Surjective p) (S : Set X) (hS : IsPathConnected (p ⁻¹' S)) (x : S) :
    Function.Surjective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) x) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨e, rfl⟩ := hps x
  exact covering_restriction_fundamentalGroup_map_surjective_at hp S hS e hx

def SplitGroupExtension.hom {N E H : Type*} [Group N] [Group E] [Group H] (i : N →* E)
    (s : H →* E) (φ : H →* MulAut N) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    N ⋊[φ] H →* E :=
  SemidirectProduct.lift i s
    (fun h => by
      ext n
      exact hconj h n)

@[simp]
theorem SplitGroupExtension.hom_apply {N E H : Type*} [Group N] [Group E] [Group H] (i : N →* E)
    (s : H →* E) (φ : H →* MulAut N) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹)
    (x : N ⋊[φ] H) : hom i s φ hconj x = i x.left * s x.right :=
  rfl

theorem SplitGroupExtension.projection_inclusion {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (hex : i.range = p.ker) (n : N) : p (i n) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [← hex]
  exact ⟨n, rfl⟩

theorem SplitGroupExtension.projection_section {E H : Type*} [Group E] [Group H] (p : E →* H)
    (s : H →* E) (hs : p.comp s = MonoidHom.id H) (h : H) : p (s h) = h :=
  DFunLike.congr_fun hs h

theorem SplitGroupExtension.projection_hom {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hs : p.comp s = MonoidHom.id H)
    (hex : i.range = p.ker) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (x : N ⋊[φ] H) :
    p (hom i s φ hconj x) = x.right := by
  rw [hom_apply, map_mul, projection_inclusion i p hex, projection_section p s hs, one_mul]

theorem SplitGroupExtension.hom_injective {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : Function.Injective (hom i s φ hconj) := by
  intro x y hxy
  have hr : x.right = y.right := by
    simpa only [projection_hom i p s φ hs hex hconj] using congrArg p hxy
  have hl : i x.left = i y.left := by
    rw [hom_apply, hom_apply, hr] at hxy
    exact mul_right_cancel hxy
  exact SemidirectProduct.ext (hi hl) hr

theorem SplitGroupExtension.hom_surjective {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hs : p.comp s = MonoidHom.id H)
    (hex : i.range = p.ker) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    Function.Surjective (hom i s φ hconj) := by
  intro e
  have he : e * (s (p e))⁻¹ ∈ i.range := by
    rw [hex, MonoidHom.mem_ker, map_mul, map_inv, projection_section p s hs]
    exact mul_inv_cancel (p e)
  obtain ⟨n, hn⟩ := he
  refine ⟨⟨n, p e⟩, ?_⟩
  change i n * s (p e) = e
  rw [hn, inv_mul_cancel_right]

theorem SplitGroupExtension.hom_bijective {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : Function.Bijective (hom i s φ hconj) :=
  ⟨hom_injective i p s φ hi hs hex hconj, hom_surjective i p s φ hs hex hconj⟩

def SplitGroupExtension.mulEquiv {N E H : Type*} [Group N] [Group E] [Group H] (i : N →* E)
    (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : N ⋊[φ] H ≃* E :=
  MulEquiv.ofBijective (hom i s φ hconj) (hom_bijective i p s φ hi hs hex hconj)

@[simp]
theorem SplitGroupExtension.mulEquiv_inl {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (n : N) :
    mulEquiv i p s φ hi hs hex hconj (SemidirectProduct.inl n) = i n := by
  change hom i s φ hconj (SemidirectProduct.inl n) = _
  simp

@[simp]
theorem SplitGroupExtension.mulEquiv_inr {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (h : H) :
    mulEquiv i p s φ hi hs hex hconj (SemidirectProduct.inr h) = s h := by
  change hom i s φ hconj (SemidirectProduct.inr h) = _
  simp

@[simp]
theorem SplitGroupExtension.mulEquiv_symm_inclusion {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (n : N) :
    (mulEquiv i p s φ hi hs hex hconj).symm (i n) = SemidirectProduct.inl n := by
  apply (mulEquiv i p s φ hi hs hex hconj).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_inl]

@[simp]
theorem SplitGroupExtension.mulEquiv_symm_section {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (h : H) :
    (mulEquiv i p s φ hi hs hex hconj).symm (s h) = SemidirectProduct.inr h := by
  apply (mulEquiv i p s φ hi hs hex hconj).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_inr]

end Mathoverflow1973

end
