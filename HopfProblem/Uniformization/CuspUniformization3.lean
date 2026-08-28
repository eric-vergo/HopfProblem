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
import HopfProblem.HomologyOfX.ThreefoldGluing2

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

def CuspUniformization.localLog (z0 z : ℂ) : ℂ :=
  logarithm z0 + logarithm (z / z0)

theorem CuspUniformization.localLog_contDiffAt_of_mem_slitPlane {z0 z : ℂ}
    (hz : z / z0 ∈ Complex.slitPlane) : ContDiffAt ℂ ω (localLog z0) z := by
  change
    ContDiffAt ℂ ω (fun w : ℂ => logarithm z0 + Complex.log (w / z0) / (2 * Real.pi * Complex.I))
      z
  exact
    contDiffAt_const.add
      (((Complex.contDiffAt_log hz).comp z (contDiffAt_id.div_const z0)).div_const _)

theorem CuspUniformization.localLog_contDiffAt {z0 : ℂ} (hz0 : z0 ≠ 0) :
    ContDiffAt ℂ ω (localLog z0) z0 :=
  localLog_contDiffAt_of_mem_slitPlane (by simp [hz0])

theorem CuspUniformization.exponential_localLog {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    exponential (localLog z0 z) = z := by
  rw [localLog, exponential_add, exponential_logarithm hz0,
    exponential_logarithm (div_ne_zero hz hz0), mul_div_cancel₀ _ hz0]

theorem CuspUniformization.logarithm_eq_localLog_add_int {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    ∃ n : ℤ, logarithm z = localLog z0 z + n := by
  apply (exponential_eq_iff (logarithm z) (localLog z0 z)).mp
  rw [exponential_logarithm hz, exponential_localLog hz0 hz]

end Mathoverflow1973

end
