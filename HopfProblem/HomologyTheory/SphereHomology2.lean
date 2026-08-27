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
import HopfProblem.TorusHomology.PeriodTorusHigherHomology3

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

def SphereHomology.unitCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (unitCircleHomologyEquiv 1).trans PeriodTorusHigherHomology.circleHomologyOneEquiv

theorem SphereHomology.unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology _root_.Circle (n + 2)) := by
  let := PeriodTorusHigherHomology.circle_homology_subsingleton n
  exact (unitCircleHomologyEquiv (n + 2)).injective.subsingleton

def SphereHomology.sphereCircleHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        0 ≃ₗ[ℤ]
      ℤ :=
  (sphereCircleHomologyEquiv 0).trans unitCircleHomologyZeroEquiv

def SphereHomology.sphereCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        1 ≃ₗ[ℤ]
      ℤ :=
  (sphereCircleHomologyEquiv 1).trans unitCircleHomologyOneEquiv

theorem SphereHomology.sphereCircle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (sphereCircleHomologyEquiv (n + 2)).injective.subsingleton

def SphereHomology.unitSphereHomologyZeroEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv (UnitSphere (n + 1))

def SphereHomology.unitSphereHomologyTopEquiv :
    (n : ℕ) → SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (n + 1) ≃ₗ[ℤ] ℤ
  | 0 => sphereCircleHomologyOneEquiv
  | n + 1 => (unitSphereHomologySuspensionEquiv (n + 1) n).trans (unitSphereHomologyTopEquiv n)

def SphereHomology.unitSphereTopClass (n : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (n + 1) :=
  (unitSphereHomologyTopEquiv n).symm 1

end Mathoverflow1973

end
