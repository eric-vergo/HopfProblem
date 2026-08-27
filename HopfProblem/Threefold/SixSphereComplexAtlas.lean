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
import HopfProblem.Recognition.Smale13

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

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
def SixSphereComplexAtlas.threefoldHomeomorph : SpecialPeriods.Threefold.Space ≃ₜ unitSphere 6 :=
  Classical.choice
    (Smale.homeomorphic_sixSphere_of_homotopySixSphere (ℂ × ComplexPlane₂)
      SpecialPeriods.Threefold.Space SpecialPeriods.Threefold.real_dimension
      Degree.threefoldHomotopyEquiv)

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
def SixSphereComplexAtlas.modelEquiv : (ℂ × ComplexPlane₂) ≃L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  SpecialPeriods.Threefold.cuspModelEquiv.symm.trans (EuclideanSpace.equiv (Fin 3) ℂ).symm

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
theorem SixSphereComplexAtlas.exists_complex_analytic_atlas :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω (unitSphere 6) := by
  let := ManifoldAtlasTransport.chartedSpace (H := ℂ × ComplexPlane₂) threefoldHomeomorph
  let := ManifoldAtlasTransport.isManifold 𝓘(ℂ, ℂ × ComplexPlane₂) ω threefoldHomeomorph
  exact
    ⟨SpecialPeriods.Threefold.ModelChange.chartedSpace modelEquiv (unitSphere 6),
      SpecialPeriods.Threefold.ModelChange.isManifold modelEquiv (unitSphere 6) ω⟩

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_isManifold SpecialPeriods.Threefold.space_isSmoothRealManifold
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_secondCountable in
theorem SixSphereComplexAtlas.exists_complex_atlas :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  obtain ⟨atlas, h⟩ := exists_complex_analytic_atlas
  refine ⟨atlas, ?_⟩
  let := atlas
  let := h
  infer_instance

end Mathoverflow1973

end
