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
import HopfProblem.Threefold.SpecialPeriods6

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

theorem PeriodTorusHigherHomology.positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv
        (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm 1
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) :=
  crossProductHomology_pointClass_right (PeriodTorusHigherHomology.CircleTopology.Circle) Unit
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) ()

@[simp]
theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop :
    circleHomologyOneEquiv (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) = 1 := by
  rw [circleHomologyOneEquiv_apply, ← positiveCircleCross_pointClass,
    circleBoundary_positiveCircleCross]
  exact connectedHomologyZeroEquiv_pointClass ()

@[simp]
theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one :
    circleHomologyOneEquiv.symm 1 = FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, circleHomologyOneEquiv_positiveLoop]

theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int (k : ℤ) :
    circleHomologyOneEquiv.symm k =
      k • FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, map_zsmul, circleHomologyOneEquiv_positiveLoop]
  simp

end Mathoverflow1973

end
