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
import HopfProblem.Lattice.Core2

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

def standardLattice : Submodule ℤ RealPlane₄ :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))

instance standardLattice_discrete : DiscreteTopology standardLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))

instance standardLattice_isZLattice : IsZLattice ℝ standardLattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))

instance standardLattice_closed : IsClosed (standardLattice : Set RealPlane₄) := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  exact AddSubgroup.isClosed_of_discrete (H := standardLattice.toAddSubgroup)

abbrev RealTorus₄ :=
  RealPlane₄ ⧸ standardLattice

instance realTorus_secondCountable : SecondCountableTopology RealTorus₄ :=
  standardLattice.isQuotientMap_mkQ.secondCountableTopology standardLattice.isOpenMap_mkQ

instance realTorus_pathConnected : PathConnectedSpace RealTorus₄ :=
  standardLattice.mkQ_surjective.pathConnectedSpace standardLattice.continuous_mkQ

instance realTorus_compact : CompactSpace RealTorus₄ := by
  have hper : ∀ z w, w ∈ standardLattice → standardLattice.mkQ (z + w) = standardLattice.mkQ z := by
    intro z w hw
    have hw' : standardLattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero standardLattice).mpr hw
    rw [map_add, hw', add_zero]
  have h :=
    IsZLattice.isCompact_range_of_periodic standardLattice standardLattice.mkQ
      standardLattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr standardLattice.mkQ_surjective] using h⟩

theorem contMDiff_of_comp_localDiffeomorph {E F F' H K K' M N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace P] [ChartedSpace K' P] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f) {g : N → P}
    (hgf : ContMDiff I L ω (g ∘ f)) : ContMDiff J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := hgf.contMDiffAt.comp (f x) (hf x).localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with z hz
  change g z = g (f ((hf x).localInverse z))
  rw [show f ((hf x).localInverse z) = z from hz]

end Mathoverflow1973

end
