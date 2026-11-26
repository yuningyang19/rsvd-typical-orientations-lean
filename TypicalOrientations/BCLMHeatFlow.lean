import TypicalOrientations.BCLMCasimir
import TypicalOrientations.BCLMSpectralHeat
import TypicalOrientations.BCLMHeatPositivity

namespace TypicalOrientations

open Filter Matrix MeasureTheory Set
open scoped Topology

noncomputable section

variable {n d : ℕ}

def soPolyEvaluation (U : SO n) : soPolyL2 n d →ₗ[ℝ] ℝ where
  toFun x := soPolyCont n d x U
  map_add' f g := by simp
  map_smul' a f := by simp

def soHeat (t : ℝ) : soPolyL2 n d →ₗ[ℝ] soPolyL2 n d :=
  spectralHeat (casimir_isSymmetric n d) t

def heatValue (x : soPolyL2 n d) (t : ℝ) (U : SO n) : ℝ :=
  soPolyCont n d (soHeat t x) U

@[simp] theorem soHeat_zero (x : soPolyL2 n d) : soHeat 0 x = x :=
  spectralHeat_zero _ _

theorem hasDerivAt_heatValue (x : soPolyL2 n d) (U : SO n) (t : ℝ) :
    HasDerivAt (fun s => heatValue x s U) (soPolyCont n d (casimir n d (soHeat t x)) U) t :=
  (soPolyEvaluation U).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spectralHeat (casimir_isSymmetric n d) t x)

theorem continuous_soHeat (x : soPolyL2 n d) : Continuous (fun t : ℝ => soHeat t x) :=
  Differentiable.continuous fun t => (hasDerivAt_spectralHeat (casimir_isSymmetric n d) t x).differentiableAt

theorem continuous_heatValue (x : soPolyL2 n d) :
    Continuous (fun z : ℝ × SO n => heatValue x z.1 z.2) :=
  continuous_soPolyContEval.comp (((continuous_soHeat x).comp continuous_fst).prodMk continuous_snd)

theorem continuous_heatDirection (x : soPolyL2 n d)
    (A : soPolyL2 n d →ₗ[ℝ] soPolyL2 n d) :
    Continuous (fun z : ℝ × SO n => soPolyCont n d (A (soHeat z.1 x)) z.2) :=
  continuous_soPolyContEval.comp
    ((A.toContinuousLinearMap.continuous.comp ((continuous_soHeat x).comp continuous_fst)).prodMk
      continuous_snd)

theorem heatValue_lower (x : soPolyL2 n d) (c : ℝ) (hc : ∀ U, c ≤ soPolyCont n d x U) :
    ∀ t, 0 ≤ t → ∀ U, c ≤ heatValue x t U := by
  apply heat_lower_bound_of_time_deriv_at_spatial_min (heatValue x)
    (fun t U => soPolyCont n d (casimir n d (soHeat t x)) U) c
    (continuous_heatValue x).continuousOn
  · exact fun t _ U => hasDerivAt_heatValue x U t
  · intro t _ U hmin
    let y := soHeat t x
    change 0 ≤ soPolyEvaluation U (casimir n d y)
    rw [casimir_apply, map_sum]
    apply Finset.sum_nonneg
    intro j _
    let L := skewBasis n j
    have hMin (s : ℝ) :
        soPolyCont n d y (U * skewRotation L 0) ≤ soPolyCont n d y (U * skewRotation L s) := by
      change heatValue x t (U * skewRotation L 0) ≤ heatValue x t (U * skewRotation L s)
      simpa only [skewRotation, soExponential_zero, mul_one] using hmin (U * skewRotation L s)
    have h := second_derivative_nonneg_of_curve_min
      (fun s => hasDerivAt_soDirectional L y U s)
      (hasDerivAt_soDirectional L (soDirectional n d L y) U 0) hMin
    change 0 ≤ soPolyCont n d (soDirectional n d L (soDirectional n d L y)) U
    simpa only [skewRotation, soExponential_zero, mul_one] using h
  · simpa only [heatValue, soHeat_zero] using hc

theorem heatValue_upper (x : soPolyL2 n d) (c : ℝ) (hc : ∀ U, soPolyCont n d x U ≤ c) :
    ∀ t, 0 ≤ t → ∀ U, heatValue x t U ≤ c := by
  have hn : ∀ U, -c ≤ soPolyCont n d (-x) U := by
    intro U
    rw [map_neg, ContinuousMap.neg_apply]
    exact neg_le_neg (hc U)
  intro t ht U
  have h := heatValue_lower (-x) (-c) hn t ht U
  rw [heatValue, map_neg, map_neg, ContinuousMap.neg_apply, neg_le_neg_iff] at h
  exact h

theorem heatValue_tendsto (x : soPolyL2 n d) (U : SO n) :
    Tendsto (fun t => heatValue x t U) atTop (𝓝 (soPolyIntegral n d x)) := by
  obtain ⟨y, hy, hI, h⟩ := spectralHeat_tendsto_kernel (casimir_isSymmetric n d)
    casimir_nonpositive (soPolyIntegral n d) soPolyIntegral_casimir_zero x
  have hLimit := ((soPolyEvaluation U).toContinuousLinearMap.continuous.tendsto y).comp h
  change Tendsto (fun t => heatValue x t U) atTop (𝓝 (soPolyCont n d y U)) at hLimit
  rwa [soPolyCont_const_of_casimir_zero y hy U, hI] at hLimit

theorem heatValue_translation_invariant (R : SO n) (x : soPolyL2 n d)
    (hx : ∀ U, soPolyCont n d x (U * R) = soPolyCont n d x U) (t : ℝ) (U : SO n) :
    heatValue x t (U * R) = heatValue x t U := by
  have h : soPolyL2translation R x = x := by
    apply soPolyCont_eval_injective
    ext U
    rw [soPolyCont_translation, hx]
  have hcomm := spectralHeat_commutes (casimir_isSymmetric n d) (soPolyL2translation R)
    (casimir_translation R) t x
  change soPolyL2translation R (soHeat t x) = soHeat t (soPolyL2translation R x) at hcomm
  rw [h] at hcomm
  have he := congrArg (soPolyEvaluation U) hcomm
  change soPolyCont n d (soPolyL2translation R (soHeat t x)) U = soPolyCont n d (soHeat t x) U at he
  simpa only [heatValue, soPolyCont_translation] using he

end

end TypicalOrientations
