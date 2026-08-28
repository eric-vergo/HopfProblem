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
import Mathlib

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

theorem HolomorphicCousin.exists_smoothPartitionOfUnity_normalized_near_closed {ι E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : Set.univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M,
      IsOpen V ∧
        K ⊆ V ∧
          closure V ⊆ U i₀ ∧
            ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
              ρ.IsSubordinate U ∧
                Set.EqOn (ρ i₀) (fun _ => 1) (closure V) ∧
                  ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) (closure V) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨V, hVo, hKV, hVU⟩ := normal_exists_closure_subset hK (hUo i₀) hKU
  let W : ι → Set M := fun i => if i = i₀ then U i else U i \ closure V
  have hWo (i : ι) : IsOpen (W i) := by
    by_cases hi : i = i₀
    · simpa only [W, if_pos hi] using hUo i
    · simpa only [W, if_neg hi] using (hUo i).sdiff isClosed_closure
  have hWc : Set.univ ⊆ ⋃ i, W i := by
    intro x hx
    by_cases hxV : x ∈ closure V
    · apply Set.mem_iUnion_of_mem i₀
      simpa only [W, if_pos rfl] using hVU hxV
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hUc hx)
      apply Set.mem_iUnion_of_mem i
      by_cases hi : i = i₀
      · simpa only [W, if_pos hi] using hxi
      · simpa only [W, if_neg hi, Set.mem_sdiff] using And.intro hxi hxV
  obtain ⟨ρ, hρW⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ W hWo hWc
  have hρU : ρ.IsSubordinate U := by
    intro i x hx
    have hxi := hρW i hx
    by_cases hi : i = i₀
    · simpa only [W, if_pos hi] using hxi
    · exact (show x ∈ U i \ closure V by simpa only [W, if_neg hi] using hxi).1
  have hdisjoint (i : ι) (hi : i ≠ i₀) : Disjoint (tsupport (ρ i)) (closure V) := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    have hxi : x ∈ U i \ closure V := by simpa only [W, if_neg hi] using hρW i hx
    exact hxi.2 hxV
  have hzero (x : M) (hx : x ∈ closure V) (i : ι) (hi : i ≠ i₀) : ρ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => Set.disjoint_left.mp (hdisjoint i hi) hs hx
  refine ⟨V, hVo, hKV, hVU, ρ, hρU, ?_, hdisjoint⟩
  intro x hx
  exact
    (finsum_eq_single (fun i => ρ i x) i₀ (hzero x hx)).symm.trans (ρ.sum_eq_one (Set.mem_univ x))

theorem HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed {ι E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : Set.univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M,
      IsOpen V ∧
        K ⊆ V ∧
          V ⊆ U i₀ ∧
            ∃ ρ : SmoothPartitionOfUnity ι I M Set.univ,
              ρ.IsSubordinate U ∧
                (∀ x ∈ V, ρ i₀ x = 1) ∧
                  (∀ i, i ≠ i₀ → ∀ x ∈ V, ρ i x = 0) ∧
                    ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) V := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρU, hρone, hρdisjoint⟩ :=
    exists_smoothPartitionOfUnity_normalized_near_closed I U hUo hUc i₀ hK hKU
  refine ⟨V, hVo, hKV, subset_closure.trans hVU, ρ, hρU, ?_, ?_, ?_⟩
  · intro x hx
    exact hρone (subset_closure hx)
  · intro i hi x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => Set.disjoint_left.mp (hρdisjoint i hi) hs (subset_closure hx)
  · intro i hi
    exact (hρdisjoint i hi).mono_right subset_closure

end Mathoverflow1973

end
