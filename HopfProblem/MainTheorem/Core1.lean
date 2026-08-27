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
import HopfProblem.Foundations.CanonicalProduct

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

theorem complexManifold_isRealManifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    (n : ℕ∞ω) [IsManifold 𝓘(ℂ, E) n M] : IsManifold 𝓘(ℝ, E) n M := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, E) n M
  intro e e' he he'
  have h := (contDiffGroupoid n 𝓘(ℂ, E)).compatible he he'
  have hc : ContDiffOn ℂ n (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa only [contDiffPregroupoid, mfld_simps] using h.1
  simpa only [mfld_simps] using hc.restrict_scalars ℝ

end Mathoverflow1973

end
