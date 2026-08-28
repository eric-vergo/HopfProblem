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
import HopfProblem.Threefold.SpecialPeriods8

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

def ThreefoldHomology.originalPatchHomeomorph (i : SpecialPeriods.Threefold.Index) :
    SpecialPeriods.Threefold.localPiece i ≃ₜ SpecialPeriods.Threefold.liftedPatch i :=
  SpecialPeriods.Threefold.gluingData.patchHomeomorph i

def ThreefoldHomology.originalRegularPatchHomeomorph :
    SpecialPeriods.Threefold.SpecialRegularFamily ≃ₜ
      SpecialPeriods.Threefold.liftedPatch Option.none :=
  originalPatchHomeomorph Option.none

def ThreefoldHomology.originalPieceInclusion (i : SpecialPeriods.Threefold.Index) :
    C(SpecialPeriods.Threefold.localPiece i, SpecialPeriods.Threefold.Space) :=
  ⟨SpecialPeriods.Threefold.inclusion i,
    (SpecialPeriods.Threefold.inclusion_openEmbedding i).continuous⟩

def ThreefoldHomology.originalRegularInclusion :
    C(SpecialPeriods.Threefold.SpecialRegularFamily, SpecialPeriods.Threefold.Space) :=
  originalPieceInclusion Option.none

def ThreefoldHomology.overlapToRegularFamily (i : SpecialPeriods.Threefold.Puncture) :
    C(SpecialPeriods.Threefold.RegularOverlap i, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  (originalRegularPatchHomeomorph.symm :
        C(SpecialPeriods.Threefold.liftedPatch Option.none,
          SpecialPeriods.Threefold.SpecialRegularFamily)).comp
    (ContinuousMap.inclusion
      (Set.inter_subset_left :
        (SpecialPeriods.Threefold.liftedPatch Option.none : Set SpecialPeriods.Threefold.Space) ∩
            SpecialPeriods.Threefold.liftedPatch (Option.some i) ⊆
          SpecialPeriods.Threefold.liftedPatch Option.none))

def ThreefoldHomology.overlapToFilling (i : SpecialPeriods.Threefold.Puncture) :
    C(SpecialPeriods.Threefold.RegularOverlap i,
      SpecialPeriods.Threefold.localPiece (Option.some i)) :=
  ((originalPatchHomeomorph (Option.some i)).symm :
        C(SpecialPeriods.Threefold.liftedPatch (Option.some i),
          SpecialPeriods.Threefold.localPiece (Option.some i))).comp
    (SpecialPeriods.Threefold.overlapFillingInclusion i)

@[simp]
theorem ThreefoldHomology.inclusion_overlapToRegularFamily (i : SpecialPeriods.Threefold.Puncture)
    (x : SpecialPeriods.Threefold.RegularOverlap i) :
    SpecialPeriods.Threefold.inclusion Option.none (overlapToRegularFamily i x) = x.val :=
  congrArg Subtype.val (originalRegularPatchHomeomorph.apply_symm_apply ⟨x.val, x.property.1⟩)

@[simp]
theorem ThreefoldHomology.inclusion_overlapToFilling (i : SpecialPeriods.Threefold.Puncture)
    (x : SpecialPeriods.Threefold.RegularOverlap i) :
    SpecialPeriods.Threefold.inclusion (Option.some i) (overlapToFilling i x) = x.val :=
  congrArg Subtype.val
    ((originalPatchHomeomorph (Option.some i)).apply_symm_apply ⟨x.val, x.property.2⟩)

theorem ThreefoldHomology.exact_of_linearEquiv_squares {A B C A' B' C' : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] [AddCommGroup A']
    [Module ℤ A'] [AddCommGroup B'] [Module ℤ B'] [AddCommGroup C'] [Module ℤ C'] (f : A →ₗ[ℤ] B)
    (g : B →ₗ[ℤ] C) (f' : A' →ₗ[ℤ] B') (g' : B' →ₗ[ℤ] C') (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B')
    (eC : C ≃ₗ[ℤ] C') (hf : f'.comp eA.toLinearMap = eB.toLinearMap.comp f)
    (hg : g'.comp eB.toLinearMap = eC.toLinearMap.comp g) (hexact : Function.Exact f g) :
    Function.Exact f' g' := by
  intro b
  constructor
  · intro hb
    have hgb : g (eB.symm b) = 0 := by
      apply eC.injective
      have h := LinearMap.congr_fun hg (eB.symm b)
      change g' (eB (eB.symm b)) = eC (g (eB.symm b)) at h
      rw [LinearEquiv.apply_symm_apply, hb] at h
      exact h.symm.trans (map_zero eC).symm
    obtain ⟨a, ha⟩ := (hexact (eB.symm b)).mp hgb
    refine ⟨eA a, ?_⟩
    have h := LinearMap.congr_fun hf a
    change f' (eA a) = eB (f a) at h
    exact h.trans ((congrArg eB ha).trans (eB.apply_symm_apply b))
  · rintro ⟨a', rfl⟩
    obtain ⟨a, rfl⟩ := eA.surjective a'
    have hfa := LinearMap.congr_fun hf a
    change f' (eA a) = eB (f a) at hfa
    rw [hfa]
    have hga := LinearMap.congr_fun hg (f a)
    change g' (eB (f a)) = eC (g (f a)) at hga
    rw [hga, hexact.apply_apply_eq_zero, map_zero]

theorem ThreefoldHomologyCuspFibre.exists_smallHeight (D : SpecialPeriods.CuspFamily.Data) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius, ‖heightParameter D h‖ < δ := by
  let h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius :=
    ⟨Max.max (ThreefoldOverlapMappingTorus.Cusp.heightThreshold D.radius)
          (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ) +
        1,
      by
      change
        ThreefoldOverlapMappingTorus.Cusp.heightThreshold D.radius <
          Max.max (ThreefoldOverlapMappingTorus.Cusp.heightThreshold D.radius)
              (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ) +
            1
      exact (le_max_left _ _).trans_lt (lt_add_one _)⟩
  refine ⟨h, ?_⟩
  have hh : ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1 ≤ (h : ℝ) := by
    change
      ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1 ≤
        Max.max (ThreefoldOverlapMappingTorus.Cusp.heightThreshold D.radius)
            (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ) +
          1
    linarith [le_max_right (ThreefoldOverlapMappingTorus.Cusp.heightThreshold D.radius)
        (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ)]
  rw [heightParameter_norm]
  calc
    Real.exp (-2 * Real.pi * (h : ℝ)) ≤
        Real.exp (-2 * Real.pi * (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    _ < δ := ThreefoldHomologyFinitenessCusp.cutoffRadius_threshold_lt hδ

theorem ThreefoldHomologyCuspFibre.fibreToFull_homology_eq (D : SpecialPeriods.CuspFamily.Data)
    (h₀ h₁ : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (fibreToFull D h₀) n =
      SingularMayerVietoris.singularHomologyMap (fibreToFull D h₁) n :=
  PeriodTorusHigherHomology.homotopy_homologyMap (fibreHeightHomotopy D h₀ h₁) n

theorem ThreefoldHomologyCuspFibre.fibreToFull_homology_surjective
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (n : ℕ) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (fibreToFull D h) n) := by
  obtain ⟨δ, hδ, _hδr, hsmall⟩ := exists_smallFibreInclusion_homology_surjective D
  obtain ⟨h', hh'⟩ := exists_smallHeight D hδ
  rw [fibreToFull_homology_eq D h h' n, ← heightFibreHomeomorph_inclusion,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    (hsmall (heightParameter D h') (heightParameter_ne_zero D h') hh'.le n).comp
      (PeriodTorusHigherHomology.homeomorphHomologyEquiv (heightFibreHomeomorph D h')
          n).surjective

end Mathoverflow1973

end
