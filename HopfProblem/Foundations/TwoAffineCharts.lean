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
import HopfProblem.Uniformization.SpecialPeriods2

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

structure TwoAffineCharts (Y : Type*) [TopologicalSpace Y] where
  left : ℂ → Y
  right : ℂ → Y
  continuous_left : Continuous left
  continuous_right : Continuous right
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  inversion : ∀ z : ℂ, z ≠ 0 → left z = right z⁻¹
  endpoints_ne : left 0 ≠ right 0
  covered : ∀ y : Y, (∃ z, left z = y) ∨ ∃ z, right z = y

theorem TwoAffineCharts.left_ne_right_zero {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) (z : ℂ) : A.left z ≠ A.right 0 := by
  by_cases hz : z = 0
  · subst z
    exact A.endpoints_ne
  · intro h
    have h' := A.right_injective ((A.inversion z hz).symm.trans h)
    exact inv_ne_zero hz h'

theorem TwoAffineCharts.cross_eq_iff {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (z w : ℂ) : A.left z = A.right w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  constructor
  · intro h
    have hw : w ≠ 0 := by
      rintro rfl
      exact A.left_ne_right_zero z h
    have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw)
    have hz : z = w⁻¹ := A.left_injective (h.trans hi.symm)
    refine ⟨by rw [hz]; exact inv_ne_zero hw, ?_⟩
    rw [hz, inv_inv]
  · rintro ⟨hz, rfl⟩
    exact A.inversion z hz

def TwoAffineCharts.symm {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y) :
    TwoAffineCharts Y where
  left := A.right
  right := A.left
  continuous_left := A.continuous_right
  continuous_right := A.continuous_left
  left_injective := A.right_injective
  right_injective := A.left_injective
  inversion z hz := by simpa using (A.inversion z⁻¹ (inv_ne_zero hz)).symm
  endpoints_ne := A.endpoints_ne.symm
  covered y := (A.covered y).symm

def TwoAffineCharts.extension {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (p : OnePoint ℂ) : Y :=
  p.elim (A.right 0) A.left

theorem TwoAffineCharts.extension_injective {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) : Function.Injective A.extension := by
  intro p q h
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => rfl
    | coe w => exact False.elim (A.left_ne_right_zero w h.symm)
  | coe z =>
    induction q using OnePoint.rec with
    | infty => exact False.elim (A.left_ne_right_zero z h)
    | coe w => exact congrArg ((↑) : ℂ → OnePoint ℂ) (A.left_injective h)

theorem TwoAffineCharts.extension_surjective {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) : Function.Surjective A.extension := by
  intro y
  obtain ⟨z, hz⟩ | ⟨w, hw⟩ := A.covered y
  · exact ⟨(z : OnePoint ℂ), hz⟩
  · by_cases hw0 : w = 0
    · subst w
      exact ⟨(OnePoint.infty), hw⟩
    · refine ⟨(w⁻¹ : ℂ), ?_⟩
      change A.left w⁻¹ = y
      have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw0)
      exact hi.trans hw

theorem TwoAffineCharts.extension_continuous {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) : Continuous A.extension := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Filter.Tendsto A.left (Filter.coclosedCompact ℂ) (𝓝 (A.right 0))
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have h : Filter.Tendsto (fun z : ℂ => A.right z⁻¹) (Bornology.cobounded ℂ) (𝓝 (A.right 0)) :=
      A.continuous_right.continuousAt.tendsto.comp Filter.tendsto_inv₀_cobounded
    apply h.congr'
    filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (A.inversion z hz).symm
  · exact A.continuous_left

def TwoAffineCharts.homeomorph {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    [T2Space Y] : OnePoint ℂ ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective A.extension ⟨A.extension_injective, A.extension_surjective⟩)
    A.extension_continuous

theorem TwoAffineCharts.left_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) [T2Space Y] : Topology.IsOpenEmbedding A.left := by
  have h := A.homeomorph.isOpenEmbedding.comp (OnePoint.isOpenEmbedding_coe (X := ℂ))
  exact h

theorem TwoAffineCharts.right_isOpenEmbedding {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) [T2Space Y] : Topology.IsOpenEmbedding A.right :=
  A.symm.left_isOpenEmbedding

theorem TwoAffineCharts.range_left {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y) :
    Set.range A.left = {A.right 0}ᶜ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact A.left_ne_right_zero z
  · intro hy
    change y ≠ A.right 0 at hy
    obtain ⟨z, hz⟩ | ⟨w, hw⟩ := A.covered y
    · exact ⟨z, hz⟩
    · have hw0 : w ≠ 0 := fun h => hy (by rw [← hw, h])
      refine ⟨w⁻¹, ?_⟩
      have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw0)
      exact hi.trans hw

theorem TwoAffineCharts.range_right {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y) :
    Set.range A.right = {A.left 0}ᶜ :=
  A.symm.range_left

def TwoAffineCharts.affineMap {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (b : Bool) : ℂ → Y :=
  if b then A.right else A.left

theorem TwoAffineCharts.affineMap_isOpenEmbedding {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) : Topology.IsOpenEmbedding (A.affineMap b) := by
  cases b
  · exact A.left_isOpenEmbedding
  · exact A.right_isOpenEmbedding

theorem TwoAffineCharts.affineMap_cross_eq_iff {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) (b : Bool) (z w : ℂ) :
    A.affineMap b z = A.affineMap (!b) w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  cases b
  · exact A.cross_eq_iff z w
  · exact A.symm.cross_eq_iff z w

theorem TwoAffineCharts.affineMap_inversion {Y : Type*} [TopologicalSpace Y]
    (A : TwoAffineCharts Y) (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    A.affineMap b z = A.affineMap (!b) z⁻¹ :=
  (A.affineMap_cross_eq_iff b z z⁻¹).mpr ⟨hz, rfl⟩

def TwoAffineCharts.parametrization {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) : OpenPartialHomeomorph ℂ Y :=
  (A.affineMap_isOpenEmbedding b).toOpenPartialHomeomorph (A.affineMap b)

@[simp]
theorem TwoAffineCharts.parametrization_target {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) :
    (A.parametrization b).target = Set.range (A.affineMap b) := by simp [parametrization]

@[simp]
theorem TwoAffineCharts.parametrization_symm_apply {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) (z : ℂ) :
    (A.parametrization b).symm (A.affineMap b z) = z :=
  (A.parametrization b).left_inv (Set.mem_univ z)

theorem TwoAffineCharts.transition_cross {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) (z : ℂ)
    (hz : z ∈ ((A.parametrization b).trans (A.parametrization (!b)).symm).source) :
    z ≠ 0 ∧ ((A.parametrization b).trans (A.parametrization (!b)).symm) z = z⁻¹ := by
  have hparam (b : Bool) (z : ℂ) : A.parametrization b z = A.affineMap b z := rfl
  have hy : A.affineMap b z ∈ Set.range (A.affineMap (!b)) := by simpa [hparam] using hz.2
  obtain ⟨w, hw⟩ := hy
  have hn := ((A.affineMap_cross_eq_iff b z w).mp hw.symm).1
  refine ⟨hn, ?_⟩
  change (A.parametrization (!b)).symm (A.affineMap b z) = z⁻¹
  rw [A.affineMap_inversion b z hn, parametrization_symm_apply]

theorem TwoAffineCharts.transition_holomorphic {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b c : Bool) :
    ContDiffOn ℂ ω ((A.parametrization b).trans (A.parametrization c).symm)
      ((A.parametrization b).trans (A.parametrization c).symm).source := by
  by_cases hbc : b = c
  · subst c
    apply contDiffOn_id.congr
    intro z _
    exact A.parametrization_symm_apply b z
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    have hi :
      ContDiffOn ℂ ω (fun z : ℂ => z⁻¹)
        ((A.parametrization b).trans (A.parametrization (!b)).symm).source := by
      intro z hz
      exact (contDiffAt_inv ℂ (A.transition_cross b z hz).1).contDiffWithinAt
    exact hi.congr (fun z hz => (A.transition_cross b z hz).2)

def TwoAffineCharts.preferredChart {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (y : Y) : Bool := by classical exact if y ∈ Set.range A.left then Bool.false else Bool.true

theorem TwoAffineCharts.preferred_mem {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)
    (y : Y) : y ∈ Set.range (A.affineMap (A.preferredChart y)) := by
  classical
  by_cases hy : y ∈ Set.range A.left
  · simp [preferredChart, hy, affineMap]
  · obtain h | h := A.covered y
    · exact False.elim (hy h)
    · simpa [preferredChart, hy, affineMap] using h

@[instance_reducible]
def TwoAffineCharts.chartedSpace {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) : ChartedSpace ℂ Y
    where
  atlas := Set.range (fun b : Bool => (A.parametrization b).symm)
  chartAt y := (A.parametrization (A.preferredChart y)).symm
  mem_chart_source
    y := by
    change y ∈ (A.parametrization (A.preferredChart y)).target
    rw [parametrization_target]
    exact A.preferred_mem y
  chart_mem_atlas _ := Set.mem_range_self _

theorem TwoAffineCharts.isManifold {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) :
    letI := A.chartedSpace
    IsManifold (modelWithCornersSelf ℂ ℂ) ω Y := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨b, rfl⟩ := he
  obtain ⟨c, rfl⟩ := he'
  simpa using A.transition_holomorphic b c

theorem TwoAffineCharts.affineMap_holomorphic {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) (b : Bool) :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (A.affineMap b) := by
  let := A.chartedSpace
  let := A.isManifold
  have he : (A.parametrization b).symm ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ω Y :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self b)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (A.affineMap b)
      Set.univ at h
  exact contMDiffOn_univ.mp h

theorem TwoAffineCharts.contMDiff_of_comp_affineMaps {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : TwoAffineCharts Y) {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N] (I : ModelWithCorners ℂ F H)
    (f : Y → N) (hf : ∀ b, ContMDiff (modelWithCornersSelf ℂ ℂ) I ω (f ∘ A.affineMap b)) :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) I ω f := by
  have hparam (b : Bool) (z : ℂ) : A.parametrization b z = A.affineMap b z := rfl
  let := A.chartedSpace
  intro y
  rw [contMDiffAt_iff_source]
  have hchart : chartAt ℂ y = (A.parametrization (A.preferredChart y)).symm := rfl
  simpa [hparam, extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    (hf (A.preferredChart y)).contMDiffAt.contMDiffWithinAt (s := Set.univ) (x :=
      (A.parametrization (A.preferredChart y)).symm y)

end Mathoverflow1973

end
