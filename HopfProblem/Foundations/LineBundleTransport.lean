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
import HopfProblem.Uniformization.HolomorphicCousin

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

theorem LineBundleTransport.exists_smooth_cutoff_near_closed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
        tsupport χ ⊆ U ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn χ (fun _ => 1) W := by
  classical
  let O : Bool → Set E := fun b => if b then Kᶜ else U
  have hOo (b : Bool) : IsOpen (O b) := by
    cases b
    · exact hU
    · exact hK.isOpen_compl
  have hOc : Set.univ ⊆ ⋃ b, O b := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, fun hk => hx (hKU hk)⟩
  obtain ⟨W, hWo, hKW, hWU, ρ, hρ, hρone, -, -⟩ :=
    HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed (modelWithCornersSelf ℝ E)
      O hOo hOc Bool.false hK hKU
  exact ⟨ρ Bool.false, (ρ Bool.false).contMDiff.contDiff, hρ Bool.false, W, hWo, hKW, hWU, hρone⟩

theorem LineBundleTransport.exists_smooth_extension_near_closed {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K U : Set E} {f : E → F} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn G f W := by
  obtain ⟨χ, hχ, hχU, W, hWo, hKW, hWU, hχone⟩ := exists_smooth_cutoff_near_closed hK hU hKU
  let G : E → F := fun x => χ x • f x
  have hG : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ G := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU : x ∈ U := hχU (tsupport_smul_subset_left χ f hx)
    exact hχ.contMDiff.contMDiffAt.smul ((hf.contDiffAt (hU.mem_nhds hxU)).contMDiffAt)
  refine ⟨G, hG.contDiff, W, hWo, hKW, hWU, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [hχone hx, one_smul]

theorem LineBundleTransport.exists_interval_cutoff (a b : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ Set.EqOn χ (fun _ => 1) (Set.uIcc a b) := by
  obtain ⟨R, -, hR⟩ :=
    (isCompact_uIcc : IsCompact (Set.uIcc a b)).isBounded.subset_ball_lt (0 : ℝ) 0
  obtain ⟨χ, hχ, hχU, W, -, hKW, -, hχone⟩ :=
    exists_smooth_cutoff_near_closed (isCompact_uIcc : IsCompact (Set.uIcc a b)).isClosed
      Metric.isOpen_ball hR
  refine ⟨χ, hχ, ?_, hχone.mono hKW⟩
  exact
    (ProperSpace.isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport χ)
      (hχU.trans Metric.ball_subset_closedBall)

end Mathoverflow1973

end
