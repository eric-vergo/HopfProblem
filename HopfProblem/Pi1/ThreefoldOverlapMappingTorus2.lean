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
import HopfProblem.HomologyOfX.ThreefoldHomology2

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

def ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral (j : Elliptic.Kind) :
    C(SpecialBoundary j, BoundaryCentralSurface j) :=
  ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingSurfaceRetraction j.twist
        (Elliptic.mainTwist_admissible j)).comp
    (specialBoundaryToFullFilling j)

theorem ThreefoldOverlapMappingTorus.Elliptic.centralInclusion_surfaceRetraction
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (y : D.Space v hv) :
    D.centralFibreInclusion v hv (D.fillingSurfaceRetraction v hv y) = D.fillingRadial v hv 1 y :=
  congrArg (fun f : C(D.Space v hv, D.Space v hv) => f y)
    (D.surfaceIntoFilling_comp_retraction v hv)

theorem ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_realCoordinates
    (j : Elliptic.Kind) (t : ℝ) (x : Elliptic.RealCoordinates) :
    specialBoundaryToCentral j
        (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, standardLattice.mkQ x)) =
      Elliptic.surfaceProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)
        (Elliptic.flatProjection
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val x) := by
  let y :
    (SpecialPeriods.EllipticFilling.specialLocalData j).Space j.twist
      (Elliptic.mainTwist_admissible j) :=
    specialBoundaryToFullFilling j
      (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, standardLattice.mkQ x))
  have hy :
    y =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j)
        (ThreefoldOverlapMappingTorus.root j.order
            (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
            (specialRootRadius j) ((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle),
          standardLattice.mkQ x) :=
    specialBoundaryInclusion_mk j t (standardLattice.mkQ x)
  apply
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralFibreInclusion_injective j.twist
      (Elliptic.mainTwist_admissible j)
  change
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralFibreInclusion j.twist
        (Elliptic.mainTwist_admissible j)
        ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingSurfaceRetraction j.twist
          (Elliptic.mainTwist_admissible j) y) =
      _
  rw [centralInclusion_surfaceRetraction, hy, Elliptic.Equivariant.Data.fillingRadial_quotient,
    Elliptic.discRadial_one, Elliptic.Equivariant.Data.centralFibreInclusion_surfaceProjection,
    Elliptic.Equivariant.Data.centralInclusion_flatProjection]
  rfl

theorem ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk (j : Elliptic.Kind)
    (t : ℝ) (x : RealTorus₄) :
    specialBoundaryToCentral j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      Elliptic.surfaceProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)
        (Elliptic.flatTorusPeriodHomeomorph
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val x) := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [Elliptic.flatTorusPeriodHomeomorph_mkQ]
  exact specialBoundaryToCentral_realCoordinates j t u

theorem ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_angle (j : Elliptic.Kind)
    (t s : ℝ) (x : RealTorus₄) :
    specialBoundaryToCentral j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      specialBoundaryToCentral j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (s, x)) := by
  rw [specialBoundaryToCentral_mk, specialBoundaryToCentral_mk]

theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (hV : Function.Surjective D.overlapHomV) : Function.Surjective D.inclusionHomU := by
  intro γ
  obtain ⟨q, rfl⟩ := D.pushoutEquiv.surjective γ
  induction q using Monoid.PushoutI.induction_on with
  | of i g =>
    cases i with
    | false => exact ⟨g, (D.pushoutEquiv_of Bool.false g).symm⟩
    | true =>
      obtain ⟨a, rfl⟩ := hV g
      exact
        ⟨D.overlapHomU a,
          (DFunLike.congr_fun D.inclusionHom_compatible a).trans
            (D.pushoutEquiv_of Bool.true (D.overlapHomV a)).symm⟩
  | base a =>
    refine ⟨D.overlapHomU a, ?_⟩
    exact
      (D.pushoutEquiv_of Bool.false (D.overlapHomU a)).symm.trans
        (congrArg D.pushoutEquiv (Monoid.PushoutI.of_apply_eq_base D.overlapHom Bool.false a))
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

end Mathoverflow1973

end
