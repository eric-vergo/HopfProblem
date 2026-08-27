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
import HopfProblem.Uniformization.SpecialPeriods9

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

def twistOrder (ℓ₀ ℓ₁ ℓ₂ : ℤ) : ℤ :=
  12 * ℓ₀ - 4 * ℓ₁ - 3 * ℓ₂

theorem main_twist_value : twistOrder 0 1 (-1) = -1 := by decide

def twistRelators (a b d : ℤ) : Fin 5 → FreeGroup (Fin 3) :=
  let c := FreeGroup.of (0 : Fin 3)
  let x := FreeGroup.of (1 : Fin 3)
  let y := FreeGroup.of (2 : Fin 3)
  ![c * x * (x * c)⁻¹, c * y * (y * c)⁻¹, x * y * (c ^ a)⁻¹, x ^ 3 * (c ^ b)⁻¹, y ^ 4 * (c ^ d)⁻¹]

end Mathoverflow1973

end
