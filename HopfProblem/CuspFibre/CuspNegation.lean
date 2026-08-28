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
import HopfProblem.PeriodFamily.Core9

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

def CuspNegation.fibreNeg : C(RealTorus₄, RealTorus₄) :=
  ⟨Neg.neg, ContinuousNeg.continuous_neg⟩

theorem CuspNegation.monodromy_map_neg (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.Cusp.monodromy (-x) =
      -ThreefoldOverlapMappingTorus.Cusp.monodromy x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  change
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (-standardLattice.mkQ v) =
      -SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (standardLattice.mkQ v)
  rw [← map_neg, SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ, map_neg, map_neg,
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ]

theorem CuspNegation.fibreNeg_monodromy (x : RealTorus₄) :
    fibreNeg (ThreefoldOverlapMappingTorus.Cusp.monodromy x) =
      ThreefoldOverlapMappingTorus.Cusp.monodromy (fibreNeg x) :=
  (monodromy_map_neg x).symm

def CuspNegation.boundaryNeg :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary, ThreefoldOverlapMappingTorus.Cusp.Boundary) :=
  CuspBoundaryGammaZero.mappingTorusMap ThreefoldOverlapMappingTorus.Cusp.monodromy
    ThreefoldOverlapMappingTorus.Cusp.monodromy fibreNeg fibreNeg_monodromy

@[simp]
theorem CuspNegation.boundaryNeg_mk (t : ℝ) (x : RealTorus₄) :
    boundaryNeg (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x)) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, -x) :=
  rfl

theorem CuspNegation.quotientNegation_boundaryCylinder (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (t : ℝ) (x : RealTorus₄) :
    quotientNegation D.correction D.radius
        (ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder D h (t, x)).val =
      (ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder D h (t, -x)).val := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  have hneg : -standardLattice.mkQ v = standardLattice.mkQ (-v) := (map_neg _ _).symm
  rw [hneg, ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates,
    ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates,
    quotientNegation_puncturedCuspCover]
  apply
    congrArg
      (fun p : CuspUniformization.LogCover D.radius =>
        (CuspUniformization.puncturedCuspCover D.correction D.radius p).val)
  apply Subtype.ext
  change
    ((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ),
        -D.periods.periodEquiv
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h) v) =
      ((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ),
        D.periods.periodEquiv
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h) (-v))
  rw [map_neg]

theorem CuspNegation.quotientNegation_boundaryInclusion (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (x : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    quotientNegation D.correction D.radius
        (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion D h x).val =
      (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion D h (boundaryNeg x)).val := by
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy x
  rw [boundaryNeg_mk]
  exact quotientNegation_boundaryCylinder D h t y

def CuspNegation.specialCapHomeomorph :
    SpecialPeriods.Threefold.SpecialCuspPiece ≃ₜ SpecialPeriods.Threefold.SpecialCuspPiece :=
  quotientHomeomorph SpecialPeriods.specialCuspData.correction
    (SpecialPeriods.Threefold.specialBaseCover.radius Option.none)

def CuspNegation.specialCapMap :
    C(SpecialPeriods.Threefold.SpecialCuspPiece, SpecialPeriods.Threefold.SpecialCuspPiece) :=
  ⟨specialCapHomeomorph, specialCapHomeomorph.continuous⟩

theorem CuspNegation.specialCapMap_specialBoundaryToPiece
    (x : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    specialCapMap (ThreefoldOverlapMappingTorus.Cusp.specialBoundaryToPiece x) =
      ThreefoldOverlapMappingTorus.Cusp.specialBoundaryToPiece (boundaryNeg x) := by
  change
    quotientNegation ThreefoldOverlapMappingTorus.Cusp.specialData.correction
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius
        (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion
            ThreefoldOverlapMappingTorus.Cusp.specialData
            ThreefoldOverlapMappingTorus.Cusp.specialHeight x).val =
      (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion
          ThreefoldOverlapMappingTorus.Cusp.specialData
          ThreefoldOverlapMappingTorus.Cusp.specialHeight (boundaryNeg x)).val
  exact
    quotientNegation_boundaryInclusion ThreefoldOverlapMappingTorus.Cusp.specialData
      ThreefoldOverlapMappingTorus.Cusp.specialHeight x

theorem CuspNegation.boundaryToFilling_neg :
    (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp boundaryNeg =
      specialCapMap.comp (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none) := by
  rw [ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  apply ContinuousMap.ext
  intro x
  exact (specialCapMap_specialBoundaryToPiece x).symm

end Mathoverflow1973

end
