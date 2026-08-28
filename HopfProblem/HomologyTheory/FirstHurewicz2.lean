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
import HopfProblem.Pi1.FundamentalGroupVanKampen1

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

theorem SphereHomology.twoOpenCover_pathConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩

theorem SphereHomology.twoOpenCover_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] (g : FundamentalGroup X D.base) : g = 1 := by
  have h :
    MonoidHom.id (FundamentalGroup X D.base) =
      (1 : FundamentalGroup X D.base →* FundamentalGroup X D.base) := by
    apply D.hom_ext
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomU a = 1
      rw [ha, map_one]
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomV a = 1
      rw [ha, map_one]
  exact DFunLike.congr_fun h g

theorem SphereHomology.twoOpenCover_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] : SimplyConnectedSpace X := by
  let := twoOpenCover_pathConnectedSpace D
  exact
    simplyConnectedSpace_of_fundamentalGroup_eq_one D.base
      (twoOpenCover_fundamentalGroup_eq_one D)

def SphereHomology.suspensionConeCover (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) : FundamentalGroupVanKampen.TwoOpenCover (CuspCentralHomology.Suspension X)
    where
  U := ⟨CuspCentralHomology.Suspension.northOpen, CuspCentralHomology.Suspension.northOpen_isOpen⟩
  V := ⟨CuspCentralHomology.Suspension.southOpen, CuspCentralHomology.Suspension.southOpen_isOpen⟩
  cover := CuspCentralHomology.Suspension.open_cover
  pathConnectedU := by
    change
      IsPathConnected
        (CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedV := by
    change
      IsPathConnected
        (CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedIntersection := by
    change IsPathConnected (CuspCentralHomology.Suspension.middleBand X)
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  base := CuspCentralHomology.Suspension.mk ⟨1 / 2, by norm_num⟩ x
  baseU := by
    change (1 / 2 : ℝ) < 3 / 4
    norm_num
  baseV := by
    change (1 / 4 : ℝ) < 1 / 2
    norm_num

instance SphereHomology.suspension_simplyConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : SimplyConnectedSpace (CuspCentralHomology.Suspension X) := by
  let D := suspensionConeCover X (Classical.choice (inferInstance : Nonempty X))
  let : SimplyConnectedSpace D.U := by
    change
      SimplyConnectedSpace
        (CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X))
    infer_instance
  let : SimplyConnectedSpace D.V := by
    change
      SimplyConnectedSpace
        (CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X))
    infer_instance
  exact twoOpenCover_simplyConnectedSpace D

instance SphereHomology.unitSphere_simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace (UnitSphere (n + 2)) :=
  (suspensionSphereHomeomorph (n + 1)).symm.toHomotopyEquiv.simplyConnectedSpace

@[simp]
theorem FirstHurewicz.simplexFace_vertex (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    simplexFace n i (stdSimplex.vertex (S := ℝ) k) = stdSimplex.vertex (S := ℝ) (i.succAbove k) :=
  by rw [simplexFace_apply, stdSimplex.map_vertex]

theorem FirstHurewicz.simplex_contractible (n : ℕ) : ContractibleSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨(stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).val,
      (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).property⟩

theorem FirstHurewicz.simplex_simplyConnected (n : ℕ) : SimplyConnectedSpace (Simplex n) := by
  let _ := simplex_contractible n
  infer_instance

def FirstHurewicz.triangleFacePath {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X))
    (i : Fin 3) :
    Path (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2))))
      (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2)))) :=
  (simplexPath (σ.comp (simplexFace 1 i))).cast (congrArg σ (simplexFace_vertex 1 i 0)).symm
    (congrArg σ (simplexFace_vertex 1 i 1)).symm

abbrev FirstHurewicz.triangleEdge01 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3))) :=
  triangleFacePath σ 2

abbrev FirstHurewicz.triangleEdge12 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 0

abbrev FirstHurewicz.triangleEdge02 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 1

theorem FirstHurewicz.triangleEdges_homotopic {X : Type*} [TopologicalSpace X]
    (σ : C(Simplex 2, X)) :
    ((triangleEdge01 σ).trans (triangleEdge12 σ)).Homotopic (triangleEdge02 σ) := by
  let _ := simplex_simplyConnected 2
  have h :=
    SimplyConnectedSpace.paths_homotopic
      ((triangleEdge01 (ContinuousMap.id (Simplex 2))).trans
        (triangleEdge12 (ContinuousMap.id (Simplex 2))))
      (triangleEdge02 (ContinuousMap.id (Simplex 2)))
  have hmap := h.map σ
  rw [Path.map_trans] at hmap
  exact hmap

end Mathoverflow1973

end
