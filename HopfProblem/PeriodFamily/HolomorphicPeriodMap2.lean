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
import HopfProblem.Foundations.FibreTopology

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

@[instance_reducible]
def HolomorphicPeriodMap.periodPullbackCoveringChartedSpace {V B : Type*} [NormedAddCommGroup V]
    [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace in
theorem HolomorphicPeriodMap.periodPullbackCoveringManifold {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ V) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B
      ComplexPlane₂

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.quotientMap_isLocalDiffeomorph {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B] (P : HolomorphicPeriodMap V B) :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.quotientMap := by
  let := P.coveringAction
  let := P.totalChartedSpace
  exact
    CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap P.coveringAction_holomorphic

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
def HolomorphicPeriodMap.periodPullbackMap {B C : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [TopologicalSpace C] [ChartedSpace ℂ C] (P : HolomorphicPeriodMap ℂ B)
    (Q : HolomorphicPeriodMap ℂ C) (f : B → C) : P.TotalSpace → Q.TotalSpace := fun x =>
  (f x.1, x.2)

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
def HolomorphicPeriodMap.periodPullbackVectorMap {B C : Type*} (f : B → C) :
    (B × ComplexPlane₂) → (C × ComplexPlane₂) := fun x => (f x.1, x.2)

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.periodEquiv_pullback_eq {B C : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C] (P : HolomorphicPeriodMap ℂ B)
    (Q : HolomorphicPeriodMap ℂ C) (f : B → C) (hpoint : ∀ b, Q.point (f b) = P.point b) (b : B) :
    Q.periodEquiv (f b) = P.periodEquiv b := by simp only [periodEquiv, hpoint b]

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.periodPullbackMap_quotientMap {B C : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C] (P : HolomorphicPeriodMap ℂ B)
    (Q : HolomorphicPeriodMap ℂ C) (f : B → C) (hpoint : ∀ b, Q.point (f b) = P.point b)
    (x : B × ComplexPlane₂) :
    periodPullbackMap P Q f (P.quotientMap x) = Q.quotientMap (periodPullbackVectorMap f x) := by
  change
    (f x.1, standardLattice.mkQ ((P.periodEquiv x.1).symm x.2)) =
      (f x.1, standardLattice.mkQ ((Q.periodEquiv (f x.1)).symm x.2))
  rw [periodEquiv_pullback_eq P Q f hpoint]

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.periodPullbackMap_isLocalDiffeomorph {B C : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C]
    (P : HolomorphicPeriodMap ℂ B) (Q : HolomorphicPeriodMap ℂ C) (f : B → C)
    [IsManifold 𝓘(ℂ) ω B] [IsManifold 𝓘(ℂ) ω C] (hpoint : ∀ b, Q.point (f b) = P.point b)
    (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) :
    letI := P.totalChartedSpace
    letI := Q.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodPullbackMap P Q f) := by
  let := P.totalChartedSpace
  let := Q.totalChartedSpace
  exact
    SpecialPeriods.EllipticFilling.periodFamilyMap_isLocalDiffeomorph P Q f
      (fun b => (hpoint b).symm) hf

end Mathoverflow1973

end
