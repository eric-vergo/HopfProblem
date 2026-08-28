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
import HopfProblem.PeriodFamily.Core6

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

def CanonicalProduct.prodLine {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (e : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) M N ω) :
    PartialDiffeomorph (((modelWithCornersSelf ℂ E)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ F)).prod (modelWithCornersSelf ℂ ℂ)) (M × ℂ) (N × ℂ) ω
    where
  toFun p := (e p.1, p.2)
  invFun p := (e.symm p.1, p.2)
  source := e.source ×ˢ Set.univ
  target := e.target ×ˢ Set.univ
  map_source' _ h := ⟨e.map_source h.1, Set.mem_univ _⟩
  map_target' _ h := ⟨e.map_target h.1, Set.mem_univ _⟩
  left_inv' _ h := Prod.ext (e.left_inv h.1) rfl
  right_inv' _ h := Prod.ext (e.right_inv h.1) rfl
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun :=
    (e.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd
  contMDiffOn_invFun :=
    (e.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd

theorem CanonicalProduct.isLocalDiffeomorphAt_prodLine {E F M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N] {f : M → N} {p : M × ℂ}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω f p.1) :
    IsLocalDiffeomorphAt (((modelWithCornersSelf ℂ E)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ F)).prod (modelWithCornersSelf ℂ ℂ)) ω
      (fun q : M × ℂ => (f q.1, q.2)) p := by
  obtain ⟨e, he, hfe⟩ := hf
  refine ⟨prodLine e, ⟨he, Set.mem_univ _⟩, ?_⟩
  intro q hq
  exact Prod.ext (hfe hq.1) rfl

theorem CanonicalProduct.isLocalDiffeomorph_prodLine {E F M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N] {f : M → N}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω f) :
    IsLocalDiffeomorph (((modelWithCornersSelf ℂ E)).prod (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ F)).prod (modelWithCornersSelf ℂ ℂ)) ω
      (fun q : M × ℂ => (f q.1, q.2)) :=
  fun p => isLocalDiffeomorphAt_prodLine (hf p.1)

end Mathoverflow1973

end
