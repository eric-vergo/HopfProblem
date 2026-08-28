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
import HopfProblem.Toric.DiagonalQuotient2

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

@[simp]
theorem CuspUniformization.exponentialPoint_zero (t : ℂ) :
    exponentialPoint t 0 =
      ToricSpace.inclusion ToricSpace.referenceTriangle (CuspQuotient.sectionCoordinates t) := by
  change
    ToricSpace.inclusion ToricSpace.referenceTriangle
        (ToricCharts.monomial ToricSpace.referenceTriangle.dual (exponentialCoordinates t 0)) =
      _
  apply congrArg (ToricSpace.inclusion ToricSpace.referenceTriangle)
  ext i
  fin_cases i <;>
    simp [ToricCharts.monomial, ToricSpace.referenceTriangle, ToricFan.Triangle.dual,
      exponentialCoordinates, CuspQuotient.sectionCoordinates, Fin.prod_univ_succ]

theorem CuspUniformization.totalExponentialLift_eq_sectionLift_of_zero (r : ℝ) (x : LogCover r)
    (hx : x.1.2 = 0) (t : CuspQuotient.disc r) (ht : (t : ℂ) = exponential x.1.1) :
    totalExponentialLift r x = CuspQuotient.sectionLift r t := by
  apply Subtype.ext
  change
    exponentialPoint (exponential x.1.1) x.1.2 =
      ToricSpace.inclusion ToricSpace.referenceTriangle (CuspQuotient.sectionCoordinates t)
  rw [hx, exponentialPoint_zero, ← ht]

theorem CuspUniformization.totalCuspCover_eq_zeroSection_of_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : LogCover r) (hx : x.1.2 = 0)
    (t : CuspQuotient.disc r) (ht : (t : ℂ) = exponential x.1.1) :
    totalCuspCover C r x = CuspQuotient.zeroSection C r t :=
  congrArg (CuspQuotient.quotientMap C r)
    (totalExponentialLift_eq_sectionLift_of_zero r x hx t ht)

theorem CuspUniformization.puncturedCuspCover_eq_zeroSection_of_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : LogCover r) (hx : x.1.2 = 0)
    (t : CuspQuotient.disc r) (ht : (t : ℂ) = exponential x.1.1) :
    (puncturedCuspCover C r x : CuspQuotient.QuotientSpace C r) =
      CuspQuotient.zeroSection C r t :=
  totalCuspCover_eq_zeroSection_of_zero C r x hx t ht

theorem CuspUniformization.puncturedCuspCover_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (s : SpecialPeriods.CuspFamily.LogBase r) (t : CuspQuotient.disc r)
    (ht : (t : ℂ) = exponential s) :
    (puncturedCuspCover C r ⟨((s : ℂ), 0), s.property⟩ : CuspQuotient.QuotientSpace C r) =
      CuspQuotient.zeroSection C r t :=
  puncturedCuspCover_eq_zeroSection_of_zero C r _ rfl t ht

def SpecialPeriods.triangleLatticeMulAutHom : TriangleGroup →* MulAut (Multiplicative Lattice)
    where
  toFun
    g :=
    (Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation g)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply Multiplicative.toAdd.injective
    change Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation 1) n.toAdd = n.toAdd
    rw [map_one, map_one]
    rfl
  map_mul' g
    h := by
    apply MulEquiv.ext
    intro n
    apply Multiplicative.toAdd.injective
    change
      Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation (g * h)) n.toAdd =
        Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation g)
          (Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation h) n.toAdd)
    rw [map_mul, map_mul]
    rfl

@[simp]
theorem SpecialPeriods.triangleLatticeMulAutHom_toAdd (g : TriangleGroup)
    (n : Multiplicative Lattice) :
    (triangleLatticeMulAutHom g n).toAdd =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ n.toAdd :=
  rfl

end Mathoverflow1973

end
