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
import HopfProblem.Foundations.Core1

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

abbrev Lattice :=
  Fin 4 → ℤ

def T₁ : LatticeMatrix :=
  !![1, 0, -6, 2; 0, -1, 1, 1; 0, -1, 0, 1; 0, 0, 0, 1]

def T₂ : LatticeMatrix :=
  !![1, 6, 0, -3; 0, 0, -1, 1; 0, 1, 0, 0; 0, 0, 0, 1]

def T₀ : LatticeMatrix :=
  !![1, 0, 0, 1; 0, 1, -1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def A₁ : LatticeMatrix :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]

def A₂ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]

def M₀ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1]

def B₀ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; -1, 0]

theorem T₁_cube : T₁ ^ 3 = 1 := by decide

theorem T₂_fourth : T₂ ^ 4 = 1 := by decide

theorem A₁_eq_transpose_sq : A₁ = (T₁ ^ 2).transpose := by decide

theorem A₂_eq_transpose_cube : A₂ = (T₂ ^ 3).transpose := by decide

end Mathoverflow1973

end
