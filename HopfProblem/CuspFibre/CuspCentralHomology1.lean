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
import HopfProblem.TorusHomology.PeriodTorusHigherHomology1

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

theorem CuspCentralHomology.singularHomologyMap_const_eq_zero {Y : Type} [TopologicalSpace Y]
    (X : Type) [TopologicalSpace X] (y : Y) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X y) n = 0 := by
  let := PeriodTorusHigherHomology.point_homology_subsingleton n hn
  change
    SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.const Unit y).comp (ContinuousMap.const X ())) n =
      0
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const Unit y) n
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a) =
      0
  rw [Subsingleton.elim (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a)
      (0 : SingularMayerVietoris.SingularHomology Unit n),
    map_zero]

theorem CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (hf : f.Nullhomotopic) (n : ℕ)
    (hn : n ≠ 0) : SingularMayerVietoris.singularHomologyMap f n = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hy n]
  exact singularHomologyMap_const_eq_zero X y n hn

end Mathoverflow1973

end
