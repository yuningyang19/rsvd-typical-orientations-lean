import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance

namespace TypicalOrientations

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology

private theorem interior_integrableExpSet_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (B : ℝ) (hB : ∀ ω, |X ω| ≤ B) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by
  suffices integrableExpSet X μ = univ by simp [this]
  ext s
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
  apply Integrable.of_bound ((measurable_const.mul hX).exp.aestronglyMeasurable)
    (Real.exp (|s| * B))
  exact ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    calc
      s * X ω ≤ |s * X ω| := le_abs_self _
      _ = |s| * |X ω| := abs_mul _ _
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hB ω) (abs_nonneg _)

private theorem cgf_second_at_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (h : 0 ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) 0 = Var[X; μ] := by
  rw [iteratedDeriv_two_cgf_eq_integral h, deriv_cgf_zero h,
    variance_eq_integral hX.aemeasurable]
  simp

private theorem second_nonneg_of_min {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) (h0 : deriv F 0 = 0)
    (hMin : ∀ t, F 0 ≤ F t) : 0 ≤ deriv (deriv F) 0 := by
  by_contra! hneg
  have hSign := eventually_nhdsWithin_sign_eq_of_deriv_neg hneg h0
  have hRight := deriv_neg_right_of_sign_deriv (nhdsWithin_le_nhds hSign)
  rw [eventually_nhdsWithin_iff] at hRight
  obtain ⟨δ, hδ, hNeg⟩ := Metric.eventually_nhds_iff.mp hRight
  have hδ' : 0 < δ / 2 := half_pos hδ
  obtain ⟨t, ht, hSlope⟩ :=
    exists_deriv_eq_slope (f := F) hδ' hF.continuous.continuousOn hF.differentiableOn
  have htNear : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  have hDeriv := hNeg htNear ht.1
  rw [hSlope, sub_zero] at hDeriv
  exact (not_lt_of_ge (div_nonneg (sub_nonneg.mpr (hMin _)) hδ'.le)) hDeriv

/-- Comparison of second cumulants at zero. The input is precisely the
rescaled log-mgf comparison obtained from the product inequality, together
with common mean; no independence of the two variables is used. -/
theorem variance_le_of_cgf_comparison
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ξ → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (a B C : ℝ) (ha : 0 < a)
    (hB : ∀ ω, |X ω| ≤ B) (hC : ∀ y, |Y y| ≤ C)
    (hMean : ∫ ω, X ω ∂μ = ∫ y, Y y ∂ν)
    (hBound : ∀ t, a * cgf X μ t ≤ cgf (fun y => a * Y y) ν t) :
    Var[X; μ] ≤ a * Var[Y; ν] := by
  let Z := fun y => a * Y y
  let F := fun t => cgf Z ν t - a * cgf X μ t
  have hz : Measurable Z := measurable_const.mul hY
  have hZi (t : ℝ) : t ∈ interior (integrableExpSet Z ν) :=
    interior_integrableExpSet_of_bounded hz (a * C) (fun y => by
      dsimp [Z]; rw [abs_mul, abs_of_pos ha]; gcongr; exact hC y) t
  have hXi (t : ℝ) : t ∈ interior (integrableExpSet X μ) :=
    interior_integrableExpSet_of_bounded hX B hB t
  have hZX : ∀ t, AnalyticAt ℝ (cgf Z ν) t := fun t => analyticAt_cgf (hZi t)
  have hXX : ∀ t, AnalyticAt ℝ (cgf X μ) t := fun t => analyticAt_cgf (hXi t)
  have hDiff : Differentiable ℝ F :=
    fun t => (hZX t).differentiableAt.sub ((hXX t).differentiableAt.const_mul a)
  have hF0 : deriv F 0 = 0 := by
    change deriv (cgf Z ν - fun t => a * cgf X μ t) 0 = 0
    rw [deriv_sub (hZX 0).differentiableAt ((hXX 0).differentiableAt.const_mul a),
      deriv_const_mul _ (hXX 0).differentiableAt, deriv_cgf_zero (hXi 0),
      deriv_cgf_zero (hZi 0)]
    unfold Z
    simp [integral_const_mul, hMean]
  have hMin (t : ℝ) : F 0 ≤ F t := by
    simpa only [F, cgf_zero, mul_zero, sub_zero, sub_nonneg] using hBound t
  have hSecond := second_nonneg_of_min hDiff hF0 hMin
  have hIter : iteratedDeriv 2 F = deriv (deriv F) := by
    rw [show 2 = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one]
  rw [← hIter] at hSecond
  change 0 ≤ iteratedDeriv 2 (cgf Z ν - fun t => a * cgf X μ t) 0 at hSecond
  have hZd : ContDiffAt ℝ (↑(2 : ℕ)) (cgf Z ν) 0 := (hZX 0).contDiffAt
  have hXd : ContDiffAt ℝ (↑(2 : ℕ)) (cgf X μ) 0 := (hXX 0).contDiffAt
  have hAXd : ContDiffAt ℝ (↑(2 : ℕ)) (fun t => a * cgf X μ t) 0 :=
    contDiffAt_const.mul hXd
  rw [iteratedDeriv_sub hZd hAXd, iteratedDeriv_const_mul a hXd,
    cgf_second_at_zero hX (hXi 0), cgf_second_at_zero hz (hZi 0)] at hSecond
  change 0 ≤ Var[fun y => a * Y y; ν] - a * Var[X; μ] at hSecond
  rw [variance_const_mul] at hSecond
  apply (le_of_mul_le_mul_left _ ha)
  nlinarith

end TypicalOrientations
