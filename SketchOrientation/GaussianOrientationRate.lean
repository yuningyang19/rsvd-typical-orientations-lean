import SketchOrientation.GaussianOrientationGap

namespace SketchOrientation

open MeasureTheory Matrix

variable {n k ℓ : ℕ}

/-- The unconditional finite-to-infinite gap bound. It uses no smallness
of the mean projector. -/
theorem haarOrientationGap_integral_bound (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ) (hk : 0 < k)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {Γ r : ℝ} (hΓ : 1 < Γ) (hr : 1 < r) (hr₂ : r ≤ 2)
    (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    (∫ V, haarOrientationEndpoint ν V - haarOrientationFiniteMean ν Γ V
      ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
        (((n : ℝ) - k - 1) / ((n : ℝ) - k)) *
          (chiSquareNegativeMoment (ℓ - k + 1) r *
            ((k : ℝ) * ((n : ℝ) - k - 1) / (Γ - 1)) ^ (r - 1)) := by
  have hkn : k < n := by omega
  let η := gaussianHaarFrameLaw hkn.le
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  let C := (Γ - 1) ^ (1 - r) * (k : ℝ) ^ r / ((k : ℝ) * c)
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hΓ' : 0 < Γ - 1 := sub_pos.mpr hΓ
  have hb : 0 < b := by
    have hn : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
    dsimp [b]
    linarith
  have hc : 0 < c := by dsimp [b, c] at *; linarith
  have hC : 0 ≤ C :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg hΓ'.le _) (Real.rpow_nonneg hk'.le _))
      (mul_nonneg hk'.le hc.le)
  have hEnd := (haarOrientationEndpoint_mean hℓn hk hkℓ ν).1
  have hFin := integrable_haarOrientationFiniteMean hk hkn ν hΓ.le
  have hMom := haarOrientationScore_moment_prod hℓn hk hkℓ ν hr.le hr'
  have hMInt : Integrable (fun V => C * ∫ P, gaussianOrientationScore P V ^ r ∂ν) η :=
    hMom.1.integral_prod_right.const_mul _
  have hle :
      (fun V => haarOrientationEndpoint ν V - haarOrientationFiniteMean ν Γ V) ≤ᵐ[η]
        (fun V => C * ∫ P, gaussianOrientationScore P V ^ r ∂ν) := by
    filter_upwards [ae_haarOrientationGap_bound hℓn hkℓ hk ν hr hr₂ hr'] with V hV
    exact (hV Γ hΓ).2
  refine (integral_mono_ae (hEnd.sub hFin) hMInt hle).trans ?_
  rw [integral_const_mul, ← integral_prod_symm _ hMom.1]
  refine (mul_le_mul_of_nonneg_left hMom.2 hC).trans_eq ?_
  let M := chiSquareNegativeMoment (ℓ - k + 1) r
  change C * (b ^ r * M) = (b / c) * (M * ((k : ℝ) * b / (Γ - 1)) ^ (r - 1))
  rw [Real.div_rpow (mul_nonneg hk'.le hb.le) hΓ'.le, Real.mul_rpow hk'.le hb.le,
    Real.rpow_sub_one hk'.ne', Real.rpow_sub_one hb.ne']
  unfold C
  rw [show 1 - r = -(r - 1) by ring, Real.rpow_neg hΓ'.le]
  field_simp [hk'.ne', hb.ne', hc.ne']

set_option maxHeartbeats 1000000 in
/-- The sharper finite-dimensional bound in Equation (3.8), including
the entire unbounded finite interval and its infinite endpoint. -/
theorem haarOrientationUniformDeviation_bound (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ) (hk : 0 < k)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {Γ₀ r : ℝ} (hΓ₀ : 1 < Γ₀) (hr : 1 < r) (hr₂ : r ≤ 2)
    (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    (∫ V, haarOrientationUniformDeviation ν Γ₀ V ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      (((n : ℝ) - k - 1) / ((n : ℝ) - k)) *
        (3 * gaussianOrientationMomentConstant (ℓ - k) r *
          meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) +
          chiSquareNegativeMoment (ℓ - k + 1) r *
            ((k : ℝ) * ((n : ℝ) - k - 1) / (Γ₀ - 1)) ^ (r - 1)) := by
  have hkn : k < n := by omega
  let η := gaussianHaarFrameLaw hkn.le
  let f := haarOrientationFiniteMean (k := k) ν Γ₀
  let e := haarOrientationEndpoint (k := k) ν
  let h := haarOrientationBenchmark n k ℓ
  have heI : Integrable e η := (haarOrientationEndpoint_mean hℓn hk hkℓ ν).1
  have hfI : Integrable f η := integrable_haarOrientationFiniteMean hk hkn ν hΓ₀.le
  have haI : Integrable (fun V => |e V - h|) η := (heI.sub (integrable_const h)).abs
  have hbI : Integrable (fun V => |f V - h|) η := (hfI.sub (integrable_const h)).abs
  have hI : Integrable (fun V => max |f V - h| |e V - h|) η := hbI.sup haI
  have hle : (fun V => max |f V - h| |e V - h|) ≤ᵐ[η]
      (fun V => |e V - h| + (e V - f V)) := by
    filter_upwards [ae_haarOrientationGap_bound hℓn hkℓ hk ν hr hr₂ hr'] with V hV
    have hn : 0 ≤ e V - f V := (hV Γ₀ hΓ₀).1
    apply max_le
    · have ht := abs_sub (e V - h) (e V - f V)
      have heq : e V - h - (e V - f V) = f V - h := by ring
      rwa [heq, abs_of_nonneg hn] at ht
    · linarith
  have hE := haarOrientationEndpoint_centered_bound hℓn hk hkℓ ν hr hr₂ hr'
  have hG := haarOrientationGap_integral_bound hℓn hkℓ hk ν hΓ₀ hr hr₂ hr'
  rw [integral_congr_ae (ae_haarOrientationUniformDeviation_eq_max hℓn hkℓ hk ν hΓ₀ hr hr₂ hr')]
  refine (integral_mono_ae hI (haI.add (heI.sub hfI)) hle).trans ?_
  change (∫ V, |e V - h| + (e V - f V) ∂η) ≤ _
  rw [integral_add haI (show Integrable (fun V => e V - f V) η from heI.sub hfI), mul_add]
  exact add_le_add hE hG

/-- A constant depending only on oversampling and the chosen moment order. -/
noncomputable def orientationRateConstant (p : ℕ) (r : ℝ) : ℝ :=
  max (3 * gaussianOrientationMomentConstant p r) (chiSquareNegativeMoment (p + 1) r)

/-- The orientation rate in Theorem 1.1 with a uniform constant even when
the target rank varies. -/
theorem haarOrientationUniformDeviation_bound_paper {p : ℕ}
    (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n)
    (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    {Γ₀ r : ℝ} (hΓ₀ : 1 < Γ₀) (hr : 1 < r) (hr₂ : r ≤ 2)
    (hr' : 2 * r < (p : ℝ) + 1) :
    (∫ V, haarOrientationUniformDeviation ν Γ₀ V ∂gaussianHaarFrameLaw (show k ≤ n by omega)) ≤
      orientationRateConstant p r *
        (meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) +
          ((n : ℝ) * k / (Γ₀ - 1)) ^ (r - 1)) := by
  have hkp : k + 1 < k + p := by omega
  have harg : r < (((k + p) - k + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.add_sub_cancel_left]
    push_cast
    linarith
  have hrank := sketchRank_le_dim_mul_meanProjectedEnergy ν
  have hρ : 0 ≤ meanProjectedEnergy ν orientationRowSpace := by
    by_contra! hneg
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    exact (mul_neg_of_pos_of_neg hn' hneg).not_ge
      ((Nat.cast_nonneg (k + p)).trans hrank)
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  have hnk : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hbc : b / c ≤ 1 := by
    apply (div_le_one hc).2
    dsimp [b, c]
    linarith
  have hbn : b ≤ (n : ℝ) := by
    dsimp [b]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hM : 0 ≤ chiSquareNegativeMoment (p + 1) r := by
    unfold chiSquareNegativeMoment
    push_cast
    have h₁ := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 - r by linarith)
    have h₂ := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 by linarith)
    positivity
  have hK : 0 ≤ gaussianOrientationMomentConstant p r := Real.rpow_nonneg hM _
  have hd : 0 < Γ₀ - 1 := sub_pos.mpr hΓ₀
  have hBase : (k : ℝ) * b / (Γ₀ - 1) ≤ (n : ℝ) * k / (Γ₀ - 1) := by
    apply div_le_div_of_nonneg_right _ hd.le
    rw [mul_comm (n : ℝ)]
    exact mul_le_mul_of_nonneg_left hbn (Nat.cast_nonneg _)
  have hPow := Real.rpow_le_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hb.le) hd.le)
    hBase (sub_nonneg.mpr hr.le)
  have hρpow := Real.rpow_nonneg hρ (1 - 1 / r)
  have h := haarOrientationUniformDeviation_bound hn hkp hk ν hΓ₀ hr hr₂ harg
  rw [Nat.add_sub_cancel_left] at h
  refine h.trans ?_
  change (b / c) * (3 * gaussianOrientationMomentConstant p r *
    meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) +
    chiSquareNegativeMoment (p + 1) r * ((k : ℝ) * b / (Γ₀ - 1)) ^ (r - 1)) ≤ _
  refine (mul_le_of_le_one_left (by positivity) hbc).trans ?_
  rw [mul_add]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hρpow
  · refine (mul_le_mul_of_nonneg_left hPow hM).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

end SketchOrientation
