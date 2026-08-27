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
import HopfProblem.Uniformization.CuspUniformization2

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

theorem SpecialPeriods.CuspFamily.Data.totalPeriodQuotientMap_eq_of_familyCover_eq
    (D : SpecialPeriods.CuspFamily.Data) {x y : CuspUniformization.LogCover D.radius}
    (h : D.familyCover x = D.familyCover y) :
    CuspUniformization.totalPeriodQuotientMap D.correction D.radius x =
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius y := by
  obtain ⟨hs, m, n, hmn⟩ := (D.familyCover_eq_iff x y).mp h
  apply (CuspUniformization.totalPeriodQuotientMap_eq_iff D.correction D.radius x y).mpr
  exact ⟨0, m, n, by simpa only [Int.cast_zero, add_zero] using hs, hmn⟩

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_logDeck (D : SpecialPeriods.CuspFamily.Data)
    (g : CuspUniformization.LogDeck) (x : CuspUniformization.LogCover D.radius) :
    D.iteratedCover (CuspUniformization.logCoverTransform D.correction D.radius g x) =
      D.iteratedCover x := by
  let := D.totalAction
  change
    D.quotient (D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius g x)) =
      D.quotient (D.familyCover x)
  rw [D.familyCover_logDeck, D.quotient_smul]

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : CuspUniformization.LogCover D.radius) :
    D.iteratedCover x = D.iteratedCover y ↔
      CuspUniformization.TotalPeriodRelated D.correction x y := by
  let := D.totalAction
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (D.quotient_eq_iff (D.familyCover x) (D.familyCover y)).mp h
    let z := CuspUniformization.logCoverTransform D.correction D.radius ⟨-k.toAdd, 0, 0⟩ y
    have hz : D.familyCover z = k • D.familyCover y := by
      simpa only [neg_neg, ofAdd_toAdd] using D.familyCover_logarithmicShift (-k.toAdd) y
    have hxy := D.totalPeriodQuotientMap_eq_of_familyCover_eq (hk.symm.trans hz.symm)
    have hzy :
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius z =
        CuspUniformization.totalPeriodQuotientMap D.correction D.radius y := by
      apply (CuspUniformization.totalPeriodQuotientMap_eq_iff D.correction D.radius z y).mpr
      exact ⟨-k.toAdd, 0, 0, rfl, rfl⟩
    exact
      (CuspUniformization.totalPeriodQuotientMap_eq_iff D.correction D.radius x y).mp
        (hxy.trans hzy)
  · intro h
    obtain ⟨g, hg⟩ :=
      (CuspUniformization.totalPeriodRelated_iff_exists_logDeck D.correction x y).mp h
    have he : CuspUniformization.logCoverTransform D.correction D.radius g y = x := Subtype.ext hg
    rw [← he, D.iteratedCover_logDeck]

def SpecialPeriods.CuspFamily.Data.directToIterated (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.TotalPeriodQuotient D.correction D.radius → D.Space :=
  Quotient.lift D.iteratedCover (fun x y h => (D.iteratedCover_eq_iff x y).mpr h)

theorem SpecialPeriods.CuspFamily.Data.directToIterated_bijective
    (D : SpecialPeriods.CuspFamily.Data) : Function.Bijective D.directToIterated := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro he
        exact Quotient.sound ((D.iteratedCover_eq_iff x y).mp he)
  · intro y
    obtain ⟨x, rfl⟩ := D.iteratedCover_surjective y
    exact ⟨CuspUniformization.totalPeriodQuotientMap D.correction D.radius x, rfl⟩

def SpecialPeriods.CuspFamily.Data.directToIteratedEquiv (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.TotalPeriodQuotient D.correction D.radius ≃ D.Space :=
  Equiv.ofBijective D.directToIterated D.directToIterated_bijective

@[simp]
theorem SpecialPeriods.CuspFamily.Data.directToIteratedEquiv_symm_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (x : CuspUniformization.LogCover D.radius) :
    D.directToIteratedEquiv.symm (D.iteratedCover x) =
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius x :=
  D.directToIteratedEquiv.symm_apply_apply
    (CuspUniformization.totalPeriodQuotientMap D.correction D.radius x)

theorem SpecialPeriods.CuspFamily.Data.directToIterated_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI :=
      CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.directToIterated := by
  let := CuspUniformization.logCoverAction D.correction D.radius
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  apply
    CoveringQuotient.contMDiff_of_comp
      (CuspUniformization.totalPeriodQuotientMap_covering D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift)
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
  exact D.iteratedCover_holomorphic

theorem SpecialPeriods.CuspFamily.Data.directToIteratedEquiv_symm_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI :=
      CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.directToIteratedEquiv.symm := by
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  apply
    contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      D.iteratedCover_isLocalDiffeomorph D.iteratedCover_surjective
  have he :
    D.directToIteratedEquiv.symm ∘ D.iteratedCover =
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius :=
    funext D.directToIteratedEquiv_symm_iteratedCover
  rw [he]
  exact
    CuspUniformization.totalPeriodQuotientMap_holomorphic D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift

def SpecialPeriods.CuspFamily.Data.directQuotientBiholomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI :=
      CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspUniformization.TotalPeriodQuotient D.correction D.radius) D.Space ω := by
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  exact
    { toEquiv := D.directToIteratedEquiv
      contMDiff_toFun := D.directToIterated_holomorphic
      contMDiff_invFun := D.directToIteratedEquiv_symm_holomorphic }

def SpecialPeriods.CuspFamily.Data.puncturedFamilyBiholomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.chartedSpace
    letI :=
      CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
        D.smallDrift
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) D.Space
      (CuspUniformization.PuncturedQuotient D.correction D.radius) ω := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  exact
    D.directQuotientBiholomorph.symm.trans
      (CuspUniformization.totalUniformizationBiholomorph D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift)

@[simp]
theorem SpecialPeriods.CuspFamily.Data.puncturedFamilyBiholomorph_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (x : CuspUniformization.LogCover D.radius) :
    letI := D.chartedSpace
    letI :=
      CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
        D.smallDrift
    D.puncturedFamilyBiholomorph (D.iteratedCover x) =
      CuspUniformization.puncturedCuspCover D.correction D.radius x := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  change
    CuspUniformization.totalUniformizationBiholomorph D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
        (D.directToIteratedEquiv.symm (D.iteratedCover x)) =
      _
  rw [D.directToIteratedEquiv_symm_iteratedCover,
    CuspUniformization.totalUniformizationBiholomorph_quotientMap]

theorem SpecialPeriods.CuspFamily.Data.puncturedFamilyBiholomorph_preserves_base
    (D : SpecialPeriods.CuspFamily.Data) (x : D.Space) :
    letI := D.chartedSpace
    letI :=
      CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
        D.smallDrift
    CuspQuotient.projection D.correction D.radius (D.puncturedFamilyBiholomorph x) =
      (D.projection x : ℂ) := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  obtain ⟨y, rfl⟩ := D.iteratedCover_surjective x
  rw [D.puncturedFamilyBiholomorph_iteratedCover, D.projection_iteratedCover]
  exact CuspUniformization.projection_totalCuspCover D.correction D.radius y

end Mathoverflow1973

end
