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
import HopfProblem.Threefold.SpecialPeriods10

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

def PeriodTorusHigherHomology.rightTranslation {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (a : G) : C(G, G) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

@[simp]
theorem PeriodTorusHigherHomology.rightTranslation_apply {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] (a x : G) : rightTranslation a x = x + a :=
  rfl

def PeriodTorusHigherHomology.rightTranslationHomotopyAlong {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a) :
    (ContinuousMap.id G).Homotopy (rightTranslation a)
    where
  toFun z := z.2 + p z.1
  continuous_toFun := continuous_snd.add (p.continuous.comp continuous_fst)
  map_zero_left x := by simp
  map_one_left x := by simp

theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap_of_path {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_homologyMap (rightTranslationHomotopyAlong p) n, singularHomologyMap_id]

@[simp]
theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] (a : G)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (PathConnectedSpace.somePath 0 a) n

end Mathoverflow1973

end
