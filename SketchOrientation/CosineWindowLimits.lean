import SketchOrientation.CosineGaussianRidge
import SketchOrientation.BlockLoss
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace SketchOrientation.Cosine

open MeasureTheory Matrix Filter Topology Set

/-- The exact deterministic transfer from the actual loss to the ridge
statistic for each draw in the cosine window argument. -/
theorem centeredRankLoss_ridge_difference {n k l : ℕ} {L : ℝ}
    (hk : 0 < k) (hkn : k < n) (hL : 0 < L) (hgap : 1 ≤ (n : ℝ) * k * L)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (U : Matrix (Fin n) (Fin l) ℝ) (hU : Uᵀ * U = 1) :
    |centeredRankLoss k (twoLevelInput V ((n : ℝ) * k * L)) U -
      ridgeInverseTrace L (scaledTargetBlock V U)| ≤
      ((k : ℝ)^2 * L + 1 + (l : ℝ) / k) / (n - (k : ℝ)) := by
  rw [centeredRankLoss_eq_scaledTargetBlock V hV U hU hk hkn hgap,
    ridgeInverseTrace_eq_sum hL.le]
  simpa only [twoLevelLoss, ridge, mul_comm L (k : ℝ), one_div] using
    finiteGap_transfer (ℓ := l) hk hkn hL hgap
      (gramEigenvalues_nonneg (scaledTargetBlock V U))

/-- The uniform-in-rank Gaussian expectation limit from Theorem 1.3. -/
theorem gaussianRidge_tendsto {k : ℕ → ℕ} {p : ℕ} {L : ℕ → ℝ}
    (hk : ∀ j, 0 < k j) (hp : 2 ≤ p) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => ∫ Z, ridgeInverseTrace (L j) Zᵀ ∂gaussianMatrixLaw (k j + p) (k j))
      atTop (𝓝 (1 / ((p : ℝ) - 1))) := by
  let q := 1 / ((p : ℝ) - 1)
  let m (j : ℕ) := ∫ Z, ridgeInverseTrace (L j) Zᵀ ∂gaussianMatrixLaw (k j + p) (k j)
  have hErr : Tendsto (fun j => q - m j) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun j => L j ^ (-(1 / 4 : ℝ)) * chiSquareNegativeMoment (p + 1) (5 / 4 : ℝ))
      ?_ ?_ ?_
    · filter_upwards [hL.eventually_gt_atTop 0] with j hj
      exact (gaussianRidge_bias (hk j) hp hj).1
    · filter_upwards [hL.eventually_gt_atTop 0] with j hj
      exact (gaussianRidge_bias (hk j) hp hj).2
    · simpa only [Function.comp_apply, zero_mul] using
        ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hL).mul_const
          (chiSquareNegativeMoment (p + 1) (5 / 4 : ℝ))
  have h := tendsto_const_nhds (x := q) |>.sub hErr
  simpa only [sub_sub_cancel, sub_zero] using h

/-- Pick the gap (L=q^{-1/4}) for any positive error parameter (q)
going to zero. This is the sequence used in both windows. -/
theorem exists_slowGap {q : ℕ → ℝ} (hq : ∀ j, 0 < q j) (h0 : Tendsto q atTop (𝓝 0)) :
    ∃ L : ℕ → ℝ, (∀ j, 0 < L j) ∧ Tendsto L atTop atTop ∧
      Tendsto (fun j => L j ^ 2 * q j) atTop (𝓝 0) := by
  let L (j : ℕ) := q j ^ (-(1 / 4 : ℝ))
  have h0' : Tendsto q atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall hq⟩
  refine ⟨L, fun j => Real.rpow_pos_of_pos (hq j) _, ?_, ?_⟩
  · exact (tendsto_rpow_neg_nhdsGT_zero (by norm_num : -(1 / 4 : ℝ) < 0)).comp h0'
  · have he (j : ℕ) : L j ^ 2 * q j = Real.sqrt (q j) := by
      have hSquare : L j ^ 2 = q j ^ (-(1 / 2 : ℝ)) := by
        unfold L
        rw [← Real.rpow_natCast (q j ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul (hq j).le]
        norm_num
      calc
        _ = q j ^ (-(1 / 2 : ℝ)) * q j ^ (1 : ℝ) := by rw [hSquare, Real.rpow_one]
        _ = q j ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add (hq j) _ _).symm
        _ = _ := by rw [Real.sqrt_eq_rpow]; norm_num
    simp_rw [he]
    have hS : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt
    exact Real.sqrt_zero ▸ hS.comp h0

/-- The scalar limits of the dimension factors that multiply the
unregularized and regularized comparisons. -/
theorem cosineWindow_scale_limits {n k L : ℕ → ℝ}
    (hn : ∀ i, 0 < n i) (hk : ∀ i, 1 ≤ k i)
    (hL : Tendsto L atTop atTop)
    (hQ : Tendsto (fun i => L i ^ 2 * k i ^ 5 / n i) atTop (𝓝 0)) :
    Tendsto (fun i => k i / n i) atTop (𝓝 0) ∧
      Tendsto (fun i => k i ^ 2 * L i / (n i - k i)) atTop (𝓝 0) := by
  have hQ₀ : ∀ᶠ i in atTop, 1 ≤ L i := hL.eventually_ge_atTop 1
  have hKn : Tendsto (fun i => k i / n i) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun i => div_nonneg (zero_le_one.trans (hk i)) (hn i).le) ?_ hQ
    filter_upwards [hQ₀] with i hLi
    apply div_le_div_of_nonneg_right _ (hn i).le
    calc
      _ = 1 * k i := by ring
      _ ≤ L i ^ 2 * (k i ^ 4 * k i) :=
        mul_le_mul (one_le_pow₀ hLi)
          (le_mul_of_one_le_left (zero_le_one.trans (hk i)) (one_le_pow₀ (hk i)))
          (zero_le_one.trans (hk i)) (sq_nonneg _)
      _ = _ := by ring
  have hNum : Tendsto (fun i => k i ^ 2 * L i / n i) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hQ
    · filter_upwards [hQ₀] with i hi
      exact div_nonneg (mul_nonneg (sq_nonneg _) (zero_le_one.trans hi)) (hn i).le
    · filter_upwards [hQ₀] with i hi
      apply div_le_div_of_nonneg_right _ (hn i).le
      calc
        _ = (L i * 1) * (k i ^ 2 * 1) := by ring
        _ ≤ (L i * L i) * (k i ^ 2 * k i ^ 3) := by
          gcongr
          · exact one_le_pow₀ (hk i)
        _ = _ := by ring
  refine ⟨hKn, ?_⟩
  have hSub : Tendsto (fun i => 1 - k i / n i) atTop (𝓝 1) := by
    simpa only [sub_zero] using hKn.const_sub 1
  have h := hNum.div hSub one_ne_zero
  simp only [zero_div] at h
  refine h.congr (fun i => ?_)
  change (k i ^ 2 * L i / n i) / (1 - k i / n i) = _
  nth_rw 1 [← div_self (hn i).ne']
  rw [div_sub_div_same, div_div_div_cancel_right₀ (hn i).ne']

end SketchOrientation.Cosine
