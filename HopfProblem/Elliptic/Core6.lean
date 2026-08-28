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
import HopfProblem.Toric.DiagonalQuotient3

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

def Elliptic.LogGauge.logMeridianParameter (j : Elliptic.Kind) (s₀ : ℂ) (t : (unitInterval)) :
    ℂ :=
  s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)

theorem Elliptic.LogGauge.logMeridianParameter_continuous (j : Elliptic.Kind) (s₀ : ℂ) :
    Continuous (logMeridianParameter j s₀) := by
  unfold logMeridianParameter
  fun_prop

@[simp]
theorem Elliptic.LogGauge.logMeridianParameter_zero (j : Elliptic.Kind) (s₀ : ℂ) :
    logMeridianParameter j s₀ 0 = s₀ := by simp [logMeridianParameter]

@[simp]
theorem Elliptic.LogGauge.logMeridianParameter_one (j : Elliptic.Kind) (s₀ : ℂ) :
    logMeridianParameter j s₀ 1 = s₀ - 1 / (j.order : ℂ) := by simp [logMeridianParameter]

@[simp]
theorem Elliptic.LogGauge.logMeridianParameter_im (j : Elliptic.Kind) (s₀ : ℂ)
    (t : (unitInterval)) : (logMeridianParameter j s₀ t).im = s₀.im := by
  simp [logMeridianParameter, Complex.div_im]

theorem Elliptic.LogGauge.logMeridianParameter_exponential_norm (j : Elliptic.Kind) (s₀ : ℂ)
    (t : (unitInterval)) :
    ‖CuspUniformization.exponential (logMeridianParameter j s₀ t)‖ =
      ‖CuspUniformization.exponential s₀‖ := by
  simp [CuspUniformization.exponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

def Elliptic.LogGauge.logMeridianRoot (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) : SpecialPeriods.Disc :=
  ⟨CuspUniformization.exponential (logMeridianParameter j s₀ t),
    by
    change Dist.dist (CuspUniformization.exponential (logMeridianParameter j s₀ t)) 0 < 1
    rw [dist_zero_right]
    apply SpecialPeriods.TauCusp.exponential_norm_lt_one_of_upperHalfPlane
    simpa only [logMeridianParameter_im] using hs₀⟩

@[simp]
theorem Elliptic.LogGauge.logMeridianRoot_coe (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) :
    (logMeridianRoot j s₀ hs₀ t : ℂ) =
      CuspUniformization.exponential (logMeridianParameter j s₀ t) :=
  rfl

theorem Elliptic.LogGauge.logMeridianRoot_continuous (j : Elliptic.Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) : Continuous (logMeridianRoot j s₀ hs₀) :=
  (CuspUniformization.exponential_holomorphic.continuous.comp
        (logMeridianParameter_continuous j s₀)).subtype_mk
    _

@[simp]
theorem Elliptic.LogGauge.logMeridianRoot_ne_zero (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) : (logMeridianRoot j s₀ hs₀ t : ℂ) ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

@[simp]
theorem Elliptic.LogGauge.logMeridianRoot_zero (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    (logMeridianRoot j s₀ hs₀ 0 : ℂ) = CuspUniformization.exponential s₀ := by simp

@[simp]
theorem Elliptic.LogGauge.logMeridianRoot_one (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    logMeridianRoot j s₀ hs₀ 1 = Elliptic.familyRotation j (logMeridianRoot j s₀ hs₀ 0) := by
  apply Subtype.ext
  rw [familyRotation_val_exponential, logMeridianRoot_zero, logMeridianRoot_coe,
    logMeridianParameter_one, sub_eq_add_neg, CuspUniformization.exponential_add]
  exact mul_comm _ _

theorem Elliptic.LogGauge.logMeridianRoot_norm (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) :
    ‖(logMeridianRoot j s₀ hs₀ t : ℂ)‖ = ‖CuspUniformization.exponential s₀‖ :=
  logMeridianParameter_exponential_norm j s₀ t

theorem Elliptic.LogGauge.logMeridianRoot_pow_norm (j : Elliptic.Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (n : ℕ) (t : (unitInterval)) :
    ‖(logMeridianRoot j s₀ hs₀ t : ℂ) ^ n‖ = ‖CuspUniformization.exponential s₀‖ ^ n := by
  rw [norm_pow, logMeridianRoot_norm]

def Elliptic.LogGauge.negativeLogFlat {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (z : SpecialPeriods.Disc) (s : ℂ) : Elliptic.RealCoordinates :=
  (D.periods.periodEquiv z).symm (-s • periodVector D.periods v z)

theorem Elliptic.LogGauge.negativeLogFlat_rotation {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (z : SpecialPeriods.Disc) (s : ℂ) :
    negativeLogFlat D v (Elliptic.familyRotation j z) (s - 1 / (j.order : ℂ)) =
      Elliptic.flatAffine j v (negativeLogFlat D v z s) := by
  apply (D.periods.periodEquiv (Elliptic.familyRotation j z)).injective
  simp only [negativeLogFlat, LinearEquiv.apply_symm_apply, Elliptic.flatAffine, map_add,
    D.periodEquiv_flatLinear, complexLift_translation, Matrix.mulVec_smul,
    periodVector_covariance D v hv]
  rw [← add_smul]
  congr 1
  ring

def Elliptic.LogGauge.logMeridianComplex {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : (unitInterval)) : ComplexPlane₂ :=
  -logMeridianParameter j s₀ t • periodVector D.periods v (logMeridianRoot j s₀ hs₀ t)

theorem Elliptic.LogGauge.logMeridianComplex_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianComplex D v s₀ hs₀) :=
  (logMeridianParameter_continuous j s₀).neg.smul
    ((periodVector_holomorphic D.periods v).continuous.comp (logMeridianRoot_continuous j s₀ hs₀))

def Elliptic.LogGauge.logMeridianFlat {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : (unitInterval)) : Elliptic.RealCoordinates :=
  negativeLogFlat D v (logMeridianRoot j s₀ hs₀ t) (logMeridianParameter j s₀ t)

theorem Elliptic.LogGauge.logMeridianFlat_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianFlat D v s₀ hs₀) := by
  change
    Continuous
      ((fun q : SpecialPeriods.Disc × ComplexPlane₂ => (D.periods.periodEquiv q.1).symm q.2) ∘
        (fun t : (unitInterval) => (logMeridianRoot j s₀ hs₀ t, logMeridianComplex D v s₀ hs₀ t)))
  apply D.periods.continuous_periodEquiv_symm.comp
  exact (logMeridianRoot_continuous j s₀ hs₀).prodMk (logMeridianComplex_continuous D v s₀ hs₀)

theorem Elliptic.LogGauge.logMeridianFlat_one {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    logMeridianFlat D v s₀ hs₀ 1 = Elliptic.flatAffine j v (logMeridianFlat D v s₀ hs₀ 0) := by
  simp only [logMeridianFlat, logMeridianRoot_one, logMeridianParameter_one,
    logMeridianParameter_zero]
  exact negativeLogFlat_rotation D v hv _ _

def Elliptic.LogGauge.logMeridianFlatPath {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (logMeridianFlat D v s₀ hs₀ 0) (Elliptic.flatAffine j v (logMeridianFlat D v s₀ hs₀ 0))
    where
  toFun := logMeridianFlat D v s₀ hs₀
  continuous_toFun := logMeridianFlat_continuous D v s₀ hs₀
  source' := rfl
  target' := logMeridianFlat_one D v hv s₀ hs₀

def Elliptic.LogGauge.logMeridianFamily {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : (unitInterval)) : D.TotalSpace :=
  (logMeridianRoot j s₀ hs₀ t, standardLattice.mkQ (logMeridianFlat D v s₀ hs₀ t))

theorem Elliptic.LogGauge.logMeridianFamily_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (logMeridianFamily D v s₀ hs₀) :=
  (logMeridianRoot_continuous j s₀ hs₀).prodMk
    (standardLattice.continuous_mkQ.comp (logMeridianFlat_continuous D v s₀ hs₀))

theorem Elliptic.LogGauge.logMeridianFamily_one {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    logMeridianFamily D v s₀ hs₀ 1 = D.permutation v (logMeridianFamily D v s₀ hs₀ 0) := by
  simp only [logMeridianFamily, D.permutation_apply, logMeridianRoot_one,
    logMeridianFlat_one D v hv, Elliptic.flatTorusAffine_mkQ]

theorem Elliptic.LogGauge.quotient_permutation {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.TotalSpace) : D.quotient v hv (D.permutation v x) = D.quotient v hv x := by
  let := D.action v hv.1
  have hg : Elliptic.CyclicAction.generator j.order • x = D.permutation v x :=
    Elliptic.familyAction_generator_smul j v hv.1 x
  rw [← hg]
  exact D.quotient_smul v hv (Elliptic.CyclicAction.generator j.order) x

def Elliptic.LogGauge.logMeridianLoop {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (D.quotient v hv (logMeridianFamily D v s₀ hs₀ 0))
      (D.quotient v hv (logMeridianFamily D v s₀ hs₀ 0))
    where
  toFun t := D.quotient v hv (logMeridianFamily D v s₀ hs₀ t)
  continuous_toFun := (D.quotient_continuous v hv).comp (logMeridianFamily_continuous D v s₀ hs₀)
  source' := rfl
  target' :=
    (congrArg (D.quotient v hv) (logMeridianFamily_one D v hv.1 s₀ hs₀)).trans
      (quotient_permutation D v hv _)

def Elliptic.LogGauge.logMeridianRootStar {j : Elliptic.Kind} (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) : BaseStar :=
  ⟨logMeridianRoot j s₀ hs₀ t, logMeridianRoot_ne_zero j s₀ hs₀ t⟩

theorem Elliptic.LogGauge.logMeridianRootStar_continuous {j : Elliptic.Kind} (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) : Continuous (logMeridianRootStar (j := j) s₀ hs₀) :=
  (logMeridianRoot_continuous j s₀ hs₀).subtype_mk _

def Elliptic.LogGauge.logMeridianComplexPoint {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) : CoverStar :=
  ⟨(logMeridianRoot j s₀ hs₀ t, logMeridianComplex D v s₀ hs₀ t),
    logMeridianRoot_ne_zero j s₀ hs₀ t⟩

def Elliptic.LogGauge.logMeridianFamilyStar {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : (unitInterval)) : FamilyStar D.periods :=
  ⟨logMeridianFamily D v s₀ hs₀ t, logMeridianRoot_ne_zero j s₀ hs₀ t⟩

theorem Elliptic.LogGauge.logMeridianFamilyStar_eq_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) :
    logMeridianFamilyStar D v s₀ hs₀ t =
      project D.periods (logMeridianComplexPoint D v s₀ hs₀ t) :=
  rfl

theorem Elliptic.LogGauge.gaugeMap_logMeridianFamilyStar {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (t : (unitInterval)) :
    gaugeMap D.periods v (logMeridianFamilyStar D v s₀ hs₀ t) =
      zeroSection D.periods (logMeridianRootStar (j := j) s₀ hs₀ t) := by
  apply Subtype.ext
  rw [logMeridianFamilyStar_eq_project,
    gaugeMap_project_of_exponential D.periods v (logMeridianComplexPoint D v s₀ hs₀ t)
      (logMeridianParameter j s₀ t) rfl]
  change
    D.periods.quotientMap
        (logMeridianRoot j s₀ hs₀ t,
          logMeridianComplex D v s₀ hs₀ t +
            logMeridianParameter j s₀ t • periodVector D.periods v (logMeridianRoot j s₀ hs₀ t)) =
      (logMeridianRoot j s₀ hs₀ t, 0)
  simp only [logMeridianComplex, neg_smul, neg_add_cancel]
  change
    (logMeridianRoot j s₀ hs₀ t, standardLattice.mkQ ((D.periods.periodEquiv _).symm 0)) =
      (logMeridianRoot j s₀ hs₀ t, 0)
  simp only [map_zero]

def Elliptic.LogGauge.logMeridianFillingPoint {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : (unitInterval)) : FillingStar D v hv :=
  fillingStarProject D v hv (logMeridianFamilyStar D v s₀ hs₀ t)

def Elliptic.LogGauge.tautologicalZeroPoint {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : (unitInterval)) : TautologicalStar D :=
  starProject D 0 (Matrix.mulVec_zero j.matrix)
    (zeroSection D.periods (logMeridianRootStar (j := j) s₀ hs₀ t))

theorem Elliptic.LogGauge.fillingToTautological_logMeridian {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : (unitInterval)) :
    fillingToTautologicalBiholomorph D v hv (logMeridianFillingPoint D v hv s₀ hs₀ t) =
      tautologicalZeroPoint D s₀ hs₀ t := by
  rw [logMeridianFillingPoint, fillingToTautologicalBiholomorph_project,
    gaugeMap_logMeridianFamilyStar]
  rfl

theorem Elliptic.affineCoverProjection_deck (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (g : AffineDeckGroup j v) :
    affineCoverProjection j p v hv (g • y) = affineCoverProjection j p v hv y :=
  (affineCoverProjection_orbit_iff j p v hv _ _).mpr ⟨g, rfl⟩

def Elliptic.affineDeckPathLoop (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (g : AffineDeckGroup j v)
    (q : Path y (g • y)) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  (q.map (affineCoverProjection_continuous j p v hv)).cast rfl
    (affineCoverProjection_deck j p v hv y g).symm

theorem Elliptic.affineDeckPathLoop_monodromy (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (g : AffineDeckGroup j v)
    (q : Path y (g • y)) :
    (affineCoverProjection_isQuotientCoveringMap j p v hv).isCoveringMap.monodromy
        (FundamentalGroup.fromPath ⟦affineDeckPathLoop j p v hv y g q⟧) ⟨y, rfl⟩ =
      ⟨g • y, affineCoverProjection_deck j p v hv y g⟩ := by
  let hq := affineCoverProjection_isQuotientCoveringMap j p v hv
  apply hq.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk q)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem Elliptic.surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop (j : Kind)
    (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (g : AffineDeckGroup j v) (q : Path y (g • y)) :
    surfaceFundamentalGroupDeckEquiv j p v hv y
        (FundamentalGroup.fromPath ⟦affineDeckPathLoop j p v hv y g q⟧) =
      g⁻¹ := by
  apply inv_injective
  rw [inv_inv]
  apply affineDeckGroup_eval_injective j v hv y
  exact
    (surfaceFundamentalGroupDeckEquiv_monodromy j p v hv y _).trans
      (congrArg Subtype.val (affineDeckPathLoop_monodromy j p v hv y g q))

def Elliptic.affineGeneratorPathLoop (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (q : Path y (flatAffine j v y)) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  affineDeckPathLoop j p v hv y (deckGenerator j v) q

theorem Elliptic.surfaceFundamentalGroupDeckEquiv_affineGeneratorPathLoop (j : Kind)
    (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (q : Path y (flatAffine j v y)) :
    surfaceFundamentalGroupDeckEquiv j p v hv y
        (FundamentalGroup.fromPath ⟦affineGeneratorPathLoop j p v hv y q⟧) =
      (deckGenerator j v)⁻¹ :=
  surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop j p v hv y (deckGenerator j v) q

def Elliptic.affineTranslationPath (y : RealCoordinates) (w : Lattice) :
    Path y (y + realCast w) :=
  Path.segment y (y + realCast w)

theorem Elliptic.affineTranslationPath_apply (y : RealCoordinates) (w : Lattice)
    (t : unitInterval) : affineTranslationPath y w t = y + (t : ℝ) • realCast w := by
  change AffineMap.lineMap y (y + realCast w) (t : ℝ) = _
  rw [AffineMap.lineMap_apply_module]
  module

theorem Elliptic.deckTranslationHom_smul (j : Kind) (v : Lattice) (y : RealCoordinates)
    (w : Lattice) : deckTranslationHom j v (Multiplicative.ofAdd w) • y = y + realCast w :=
  add_comm _ _

def Elliptic.affineTranslationLoop (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (w : Lattice) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  affineDeckPathLoop j p v hv y (deckTranslationHom j v (Multiplicative.ofAdd w))
    ((affineTranslationPath y w).cast rfl (deckTranslationHom_smul j v y w))

@[simp]
theorem Elliptic.affineTranslationLoop_apply (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) (w : Lattice) (t : unitInterval) :
    affineTranslationLoop j p v hv y w t =
      affineCoverProjection j p v hv (y + (t : ℝ) • realCast w) := by
  change affineCoverProjection j p v hv (affineTranslationPath y w t) = _
  rw [affineTranslationPath_apply]

theorem Elliptic.surfaceFundamentalGroupDeckEquiv_affineTranslationLoop (j : Kind)
    (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (w : Lattice) :
    surfaceFundamentalGroupDeckEquiv j p v hv y
        (FundamentalGroup.fromPath ⟦affineTranslationLoop j p v hv y w⟧) =
      deckTranslationHom j v (Multiplicative.ofAdd (-w)) := by
  change
    surfaceFundamentalGroupDeckEquiv j p v hv y
        (FundamentalGroup.fromPath ⟦affineDeckPathLoop j p v hv y _ _⟧) =
      _
  rw [surfaceFundamentalGroupDeckEquiv_affineDeckPathLoop]
  exact (map_inv (deckTranslationHom j v) (Multiplicative.ofAdd w)).symm

theorem Elliptic.LogGauge.fillingSurfaceRetraction_quotient_flat {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.fillingSurfaceRetraction v hv (D.quotient v hv (z, standardLattice.mkQ x)) =
      Elliptic.affineCoverProjection j D.centralPeriod v hv x := by
  apply D.centralFibreInclusion_injective v hv
  have h :=
    congrArg
      (fun f : C(D.Space v hv, D.Space v hv) => f (D.quotient v hv (z, standardLattice.mkQ x)))
      (D.surfaceIntoFilling_comp_retraction v hv)
  change
    D.centralFibreInclusion v hv
        (D.fillingSurfaceRetraction v hv (D.quotient v hv (z, standardLattice.mkQ x))) =
      D.fillingRadial v hv 1 (D.quotient v hv (z, standardLattice.mkQ x)) at h
  rw [h, D.fillingRadial_quotient, Elliptic.discRadial_one]
  change
    D.quotient v hv (Elliptic.discZero, standardLattice.mkQ x) =
      D.centralFibreInclusion v hv
        (Elliptic.surfaceProjection j D.centralPeriod v hv
          (Elliptic.flatProjection D.centralPeriod.val x))
  rw [D.centralFibreInclusion_surfaceProjection, D.centralInclusion_flatProjection]
  rfl

theorem Elliptic.LogGauge.fundamentalGroup_cast_loop {Y : Type*} [TopologicalSpace Y] {a b : Y}
    (h : a = b) (γ : Path a a) :
    MulEquiv.cast (M := FundamentalGroup Y) h (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.cast h.symm h.symm⟧ := by
  cases h
  rfl

def Elliptic.LogGauge.retractedFlatLoop {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (z : SpecialPeriods.Disc)
    (x : Elliptic.RealCoordinates)
    (γ :
      Path (D.quotient v hv (z, standardLattice.mkQ x))
        (D.quotient v hv (z, standardLattice.mkQ x))) :
    Path (Elliptic.affineCoverProjection j D.centralPeriod v hv x)
      (Elliptic.affineCoverProjection j D.centralPeriod v hv x) :=
  (γ.map (D.fillingSurfaceRetraction v hv).continuous).cast
    (fillingSurfaceRetraction_quotient_flat D v hv z x).symm
    (fillingSurfaceRetraction_quotient_flat D v hv z x).symm

def Elliptic.LogGauge.logMeridianSurfaceLoop {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Path (Elliptic.affineCoverProjection j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0))
      (Elliptic.affineCoverProjection j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0)) :=
  retractedFlatLoop D v hv (logMeridianRoot j s₀ hs₀ 0) (logMeridianFlat D v s₀ hs₀ 0)
    (logMeridianLoop D v hv s₀ hs₀)

@[simp]
theorem Elliptic.LogGauge.logMeridianSurfaceLoop_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : (unitInterval)) :
    logMeridianSurfaceLoop D v hv s₀ hs₀ t =
      Elliptic.affineCoverProjection j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ t) :=
  fillingSurfaceRetraction_quotient_flat D v hv (logMeridianRoot j s₀ hs₀ t)
    (logMeridianFlat D v s₀ hs₀ t)

theorem Elliptic.LogGauge.logMeridianSurfaceLoop_eq_affineGeneratorPathLoop {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    logMeridianSurfaceLoop D v hv s₀ hs₀ =
      Elliptic.affineGeneratorPathLoop j D.centralPeriod v hv (logMeridianFlat D v s₀ hs₀ 0)
        (logMeridianFlatPath D v hv.1 s₀ hs₀) := by
  ext t
  exact logMeridianSurfaceLoop_apply D v hv s₀ hs₀ t

theorem Elliptic.LogGauge.surfaceFundamentalGroupDeckEquiv_logMeridian {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) :
    Elliptic.surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv
        (logMeridianFlat D v s₀ hs₀ 0)
        (FundamentalGroup.fromPath ⟦logMeridianSurfaceLoop D v hv s₀ hs₀⟧) =
      (Elliptic.deckGenerator j v)⁻¹ := by
  rw [logMeridianSurfaceLoop_eq_affineGeneratorPathLoop]
  exact
    Elliptic.surfaceFundamentalGroupDeckEquiv_affineGeneratorPathLoop j D.centralPeriod v hv _ _

theorem Elliptic.LogGauge.standardLattice_mkQ_realCast (w : Lattice) :
    standardLattice.mkQ (Elliptic.realCast w) = 0 :=
  (Submodule.Quotient.mk_eq_zero standardLattice).mpr
    ((Elliptic.standardLattice_mem_iff _).mpr ⟨w, rfl⟩)

def Elliptic.LogGauge.fibreTranslationFamily {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) (w : Lattice) (t : (unitInterval)) :
    D.TotalSpace :=
  (z, standardLattice.mkQ (x + (t : ℝ) • Elliptic.realCast w))

theorem Elliptic.LogGauge.fibreTranslationFamily_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates)
    (w : Lattice) : Continuous (fibreTranslationFamily D z x w) :=
  continuous_const.prodMk
    (standardLattice.continuous_mkQ.comp
      (continuous_const.add (continuous_subtype_val.smul continuous_const)))

@[simp]
theorem Elliptic.LogGauge.fibreTranslationFamily_zero {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates)
    (w : Lattice) : fibreTranslationFamily D z x w 0 = (z, standardLattice.mkQ x) := by
  simp [fibreTranslationFamily]

@[simp]
theorem Elliptic.LogGauge.fibreTranslationFamily_one {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates)
    (w : Lattice) : fibreTranslationFamily D z x w 1 = (z, standardLattice.mkQ x) := by
  change (z, standardLattice.mkQ (x + (1 : ℝ) • Elliptic.realCast w)) = (z, standardLattice.mkQ x)
  rw [one_smul, map_add, standardLattice_mkQ_realCast, add_zero]

theorem Elliptic.LogGauge.periodEquiv_fibreTranslation {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates)
    (w : Lattice) (t : (unitInterval)) :
    D.periods.periodEquiv z (x + (t : ℝ) • Elliptic.realCast w) =
      D.periods.periodEquiv z x + (t : ℂ) • periodVector D.periods w z := by
  simp only [map_add, map_smul, periodVector, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem Elliptic.LogGauge.fibreTranslationFamily_complex_formula {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates)
    (w : Lattice) (t : (unitInterval)) :
    fibreTranslationFamily D z x w t =
      D.periods.quotientMap
        (z, D.periods.periodEquiv z x + (t : ℂ) • periodVector D.periods w z) := by
  rw [← periodEquiv_fibreTranslation]
  change
    (z, standardLattice.mkQ (x + (t : ℝ) • Elliptic.realCast w)) =
      (z,
        standardLattice.mkQ
          ((D.periods.periodEquiv z).symm
            (D.periods.periodEquiv z (x + (t : ℝ) • Elliptic.realCast w))))
  rw [LinearEquiv.symm_apply_apply]

def Elliptic.LogGauge.fibreTranslationLoop {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (z : SpecialPeriods.Disc)
    (x : Elliptic.RealCoordinates) (w : Lattice) :
    Path (D.quotient v hv (z, standardLattice.mkQ x)) (D.quotient v hv (z, standardLattice.mkQ x))
    where
  toFun t := D.quotient v hv (fibreTranslationFamily D z x w t)
  continuous_toFun :=
    (D.quotient_continuous v hv).comp (fibreTranslationFamily_continuous D z x w)
  source' := congrArg (D.quotient v hv) (fibreTranslationFamily_zero D z x w)
  target' := congrArg (D.quotient v hv) (fibreTranslationFamily_one D z x w)

def Elliptic.LogGauge.fibreTranslationSurfaceLoop {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) (w : Lattice) :
    Path (Elliptic.affineCoverProjection j D.centralPeriod v hv x)
      (Elliptic.affineCoverProjection j D.centralPeriod v hv x) :=
  retractedFlatLoop D v hv z x (fibreTranslationLoop D v hv z x w)

theorem Elliptic.LogGauge.fibreTranslationSurfaceLoop_eq {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) (w : Lattice) :
    fibreTranslationSurfaceLoop D v hv z x w =
      Elliptic.affineTranslationLoop j D.centralPeriod v hv x w := by
  ext t
  change
    D.fillingSurfaceRetraction v hv
        (D.quotient v hv (z, standardLattice.mkQ (x + (t : ℝ) • Elliptic.realCast w))) =
      Elliptic.affineTranslationLoop j D.centralPeriod v hv x w t
  rw [fillingSurfaceRetraction_quotient_flat, Elliptic.affineTranslationLoop_apply]

theorem Elliptic.LogGauge.fibreTranslationSurfaceLoop_deck {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) (w : Lattice) :
    Elliptic.surfaceFundamentalGroupDeckEquiv j D.centralPeriod v hv x
        (FundamentalGroup.fromPath ⟦fibreTranslationSurfaceLoop D v hv z x w⟧) =
      Elliptic.deckTranslationHom j v (Multiplicative.ofAdd (-w)) := by
  rw [fibreTranslationSurfaceLoop_eq]
  exact Elliptic.surfaceFundamentalGroupDeckEquiv_affineTranslationLoop j D.centralPeriod v hv x w

def Elliptic.LogGauge.fibreTranslationFamilyStar {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : BaseStar) (x : Elliptic.RealCoordinates) (w : Lattice)
    (t : (unitInterval)) : FamilyStar D.periods :=
  ⟨fibreTranslationFamily D z.1 x w t, z.2⟩

theorem Elliptic.LogGauge.gaugeMap_fibreTranslationFamilyStar_formula {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (z : BaseStar) (x : Elliptic.RealCoordinates)
    (w : Lattice) (s : ℂ) (hs : CuspUniformization.exponential s = (z.1 : ℂ))
    (t : (unitInterval)) :
    (gaugeMap D.periods v (fibreTranslationFamilyStar D z x w t) : D.TotalSpace) =
      D.periods.quotientMap
        (z.1,
          D.periods.periodEquiv z.1 x + (t : ℂ) • periodVector D.periods w z.1 +
            s • periodVector D.periods v z.1) := by
  let a : CoverStar :=
    ⟨(z.1, D.periods.periodEquiv z.1 x + (t : ℂ) • periodVector D.periods w z.1), z.2⟩
  have ha : fibreTranslationFamilyStar D z x w t = project D.periods a :=
    Subtype.ext (fibreTranslationFamily_complex_formula D z.1 x w t)
  rw [ha]
  exact gaugeMap_project_of_exponential D.periods v a s hs

theorem Elliptic.LogGauge.gaugeMap_fibreTranslationFamilyStar_negativeLog {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (z : BaseStar) (w : Lattice) (s : ℂ)
    (hs : CuspUniformization.exponential s = (z.1 : ℂ)) (t : (unitInterval)) :
    gaugeMap D.periods v
        (fibreTranslationFamilyStar D z
          ((D.periods.periodEquiv z.1).symm (-s • periodVector D.periods v z.1)) w t) =
      fibreTranslationFamilyStar D z 0 w t := by
  apply Subtype.ext
  rw [gaugeMap_fibreTranslationFamilyStar_formula D v z _ w s hs]
  change D.periods.quotientMap _ = fibreTranslationFamily D z.1 0 w t
  rw [fibreTranslationFamily_complex_formula]
  congr 1
  apply congrArg (fun u : ComplexPlane₂ => (z.1, u))
  simp only [LinearEquiv.apply_symm_apply, map_zero, zero_add, neg_smul]
  abel

def Elliptic.LogGauge.fibreTranslationFillingPoint {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (z : BaseStar) (x : Elliptic.RealCoordinates) (w : Lattice) (t : (unitInterval)) :
    FillingStar D v hv :=
  fillingStarProject D v hv (fibreTranslationFamilyStar D z x w t)

theorem Elliptic.LogGauge.fillingToTautological_fibreTranslation {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (z : BaseStar) (w : Lattice) (s : ℂ) (hs : CuspUniformization.exponential s = (z.1 : ℂ))
    (t : (unitInterval)) :
    fillingToTautologicalBiholomorph D v hv
        (fibreTranslationFillingPoint D v hv z
          ((D.periods.periodEquiv z.1).symm (-s • periodVector D.periods v z.1)) w t) =
      starProject D 0 (Matrix.mulVec_zero j.matrix) (fibreTranslationFamilyStar D z 0 w t) := by
  rw [fibreTranslationFillingPoint, fillingToTautologicalBiholomorph_project,
    gaugeMap_fibreTranslationFamilyStar_negativeLog D v z w s hs]

theorem Elliptic.LogGauge.exists_logMeridian_parameters (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) :
    ∃ s : ℂ, 0 < s.im ∧ ‖CuspUniformization.exponential s‖ ^ j.order < r := by
  let a : ℝ := Min.min r 1 / 2
  have ha0 : 0 < a := half_pos (lt_min hr zero_lt_one)
  have ha1 : a < 1 := by
    have h := min_le_right r (1 : ℝ)
    dsimp only [a]
    linarith
  have har : a < r := by
    have h := min_le_left r (1 : ℝ)
    dsimp only [a] at ha0 ⊢
    linarith
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hnorm : ‖CuspUniformization.exponential (CuspUniformization.logarithm (a : ℂ))‖ = a := by
    rw [CuspUniformization.exponential_logarithm hane, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha0]
  have hpow : a ^ j.order ≤ a := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero j.order_pos.ne'
    rw [hn, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1.le) ha0.le).trans_eq (one_mul a)
  refine ⟨CuspUniformization.logarithm (a : ℂ), ?_, ?_⟩
  · exact
      SpecialPeriods.TauCusp.upperHalfPlane_of_exponential_norm_lt_one (by rw [hnorm]; exact ha1)
  · rw [hnorm]
    exact hpow.trans_lt har

theorem EllipticRetractionTopology.fundamentalGroup_map_bijective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact E.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)

def EllipticRetractionTopology.fundamentalGroupEquivAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x) (fundamentalGroup_map_bijective e x)

end Mathoverflow1973

end
