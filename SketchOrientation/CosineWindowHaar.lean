import SketchOrientation.CosineWindowAssemble
import SketchOrientation.GaussianOrientationRate

namespace SketchOrientation.Cosine

open Matrix MeasureTheory Filter Topology Edge.Walsh

noncomputable section

variable {n k l : ℕ}

private def frameProjector (U : Matrix (Fin n) (Fin l) ℝ) (hU : Uᵀ * U = 1) :
    OrthogonalProjector n l :=
  ⟨U * Uᵀ, by simp, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul],
    by rw [Matrix.rank_self_mul_transpose, ← Matrix.rank_transpose_mul_self, hU,
      Matrix.rank_one, Fintype.card_fin]⟩

private def haarFrameProjector (hl : l ≤ n) (U : Matrix (Fin n) (Fin l) ℝ) :
    OrthogonalProjector n l :=
  if hU : Uᵀ * U = 1 then frameProjector U hU
  else frameProjector (exists_stiefel_frame hl).choose (exists_stiefel_frame hl).choose_spec

private theorem haarFrameProjector_val (hl : l ≤ n) {U : Matrix (Fin n) (Fin l) ℝ}
    (hU : Uᵀ * U = 1) : (haarFrameProjector hl U).val = U * Uᵀ := by
  rw [haarFrameProjector, dif_pos hU]
  rfl

private theorem measurable_haarFrameProjector (hl : l ≤ n) :
    Measurable (haarFrameProjector hl) := by
  apply Measurable.subtype_mk
  change Measurable (fun U : Matrix (Fin n) (Fin l) ℝ =>
    (haarFrameProjector hl U).val)
  have hs : MeasurableSet {U : Matrix (Fin n) (Fin l) ℝ | Uᵀ * U = 1} :=
    (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).measurableSet
  let P₀ := frameProjector (exists_stiefel_frame hl).choose (exists_stiefel_frame hl).choose_spec
  have he : (fun U => (haarFrameProjector hl U).val) =
      {U : Matrix (Fin n) (Fin l) ℝ | Uᵀ * U = 1}.piecewise
        (fun U => U * Uᵀ) (fun _ => P₀.val) := by
    funext U
    by_cases hU : Uᵀ * U = 1
    · simp [Set.piecewise, hU, haarFrameProjector_val]
    · simp [Set.piecewise, hU, haarFrameProjector, P₀]
  rw [he]
  exact (continuous_id.matrix_mul continuous_id.matrix_transpose).measurable.piecewise hs
    measurable_const

/-- The Haar sketch law on rank-l projectors, obtained from the Haar
orthonormal frame by taking its range projection. -/
def haarSketchProjectorLaw (hl : l ≤ n) : Measure (OrthogonalProjector n l) :=
  (gaussianHaarFrameLaw hl).map (haarFrameProjector hl)

instance (hl : l ≤ n) : IsProbabilityMeasure (haarSketchProjectorLaw hl) :=
  Measure.isProbabilityMeasure_map (measurable_haarFrameProjector hl).aemeasurable

/-- The mean of the actual finite-gap Haar-sketch residual at a fixed target. -/
def haarSketchFiniteMean (hl : l ≤ n) (Γ : ℝ) (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  haarOrientationFiniteMean (haarSketchProjectorLaw hl) Γ V

private theorem measurable_orientationFiniteLoss_fixed (Γ : ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) :
    Measurable (fun P : OrthogonalProjector n l => orientationFiniteLoss Γ P V) := by
  have h : Measurable (fun P : OrthogonalProjector n l => (P, V)) :=
    measurable_id.prodMk measurable_const
  simpa only [Function.comp_def, Function.uncurry_def] using
    (@measurable_orientationFiniteLoss n k l Γ).comp h

private theorem haarSketchFiniteMean_eq_integral (hl : l ≤ n) (hk : 0 < k) (hkn : k < n)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    haarSketchFiniteMean hl Γ V =
      ∫ U, orientationFiniteLoss Γ (haarFrameProjector hl U) V ∂gaussianHaarFrameLaw hl := by
  let ν := haarSketchProjectorLaw hl
  change (∫ P, projectorTwoLevelLoss V P Γ ∂ν) = _
  calc
    _ = ∫ P, orientationFiniteLoss Γ P V ∂ν :=
      integral_congr_ae (ae_of_all ν fun P => (orientationFiniteLoss_eq_actual hk hkn Γ hΓ P V hV).symm)
    _ = _ := integral_map (measurable_haarFrameProjector hl).aemeasurable
      (measurable_orientationFiniteLoss_fixed Γ V).aestronglyMeasurable

/-- The projector-law expression is also the actual Haar-frame sketch mean. -/
theorem haarSketchFiniteMean_eq_frame (hl : l ≤ n) (hk : 0 < k) (hkn : k < n)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    haarSketchFiniteMean hl Γ V =
      ∫ U, centeredRankLoss k (twoLevelInput V Γ) U ∂gaussianHaarFrameLaw hl := by
  rw [haarSketchFiniteMean_eq_integral hl hk hkn hΓ V hV]
  apply integral_congr_ae
  filter_upwards [ae_gaussianHaarFrame_orthonormal hl] with U hU
  rw [orientationFiniteLoss_eq_actual hk hkn Γ hΓ _ V hV, projectorTwoLevelLoss,
    haarFrameProjector_val hl hU]
  unfold centeredRankLoss tailRelativeError
  rw [squaredResidual_frame_projector _ _ hU]

/-- Haar rotation invariance makes the finite-gap mean constant over all
target frames, including at the same dimension-dependent gap. -/
theorem haarSketchFiniteMean_eq_of_frames (hl : l ≤ n) (hk : 0 < k) (hkn : k < n)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) (V W : Matrix (Fin n) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1) :
    haarSketchFiniteMean hl Γ V = haarSketchFiniteMean hl Γ W := by
  obtain ⟨Q, hQ, hQV⟩ := exists_orthogonal_mul_frame_eq hkn.le hV hW
  let η := gaussianHaarFrameLaw hl
  let F (Z : Matrix (Fin n) (Fin k) ℝ) (U : Matrix (Fin n) (Fin l) ℝ) :=
    orientationFiniteLoss Γ (haarFrameProjector hl U) Z
  have hF : Measurable (F V) :=
    (measurable_orientationFiniteLoss_fixed Γ V).comp (measurable_haarFrameProjector hl)
  have hQt : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hrot := gaussianHaarFrameLaw_map_left hl Qᵀ (by simpa only [transpose_transpose] using hQt)
  change η.map (fun U => Qᵀ * U) = η at hrot
  rw [haarSketchFiniteMean_eq_integral hl hk hkn hΓ V hV,
    haarSketchFiniteMean_eq_integral hl hk hkn hΓ W hW]
  change (∫ U, F V U ∂η) = ∫ U, F W U ∂η
  calc
    _ = ∫ U, F V (Qᵀ * U) ∂η := by
      have hm : Measurable (fun U : Matrix (Fin n) (Fin l) ℝ => Qᵀ * U) :=
        (continuous_const.matrix_mul continuous_id).measurable
      rw [← integral_map (f := F V) hm.aemeasurable hF.aestronglyMeasurable, hrot]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_gaussianHaarFrame_orthonormal hl] with U hU
      have hU' : (Qᵀ * U)ᵀ * (Qᵀ * U) = 1 := by
        rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᵀ,
          hQt, Matrix.one_mul, hU]
      dsimp only [F, orientationFiniteLoss]
      rw [haarFrameProjector_val hl hU', haarFrameProjector_val hl hU, ← hQV]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- The exact difference between the finite-dimensional Haar benchmark and
the limit of the normalized inverse-Wishart trace. -/
theorem haarOrientationBenchmark_window_difference {p : ℕ} (hk : 0 < k)
    (hp : 2 ≤ p) (hl : k + p ≤ n) :
    1 / ((p : ℝ) - 1) - haarOrientationBenchmark n k (k + p) =
      (p : ℝ) * ((k : ℝ)⁻¹ + 1 / ((p : ℝ) - 1)) / ((n : ℝ) - k) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast (show p ≠ 1 by omega))
  have hn' : (n : ℝ) - k ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast (show n ≠ k by omega))
  unfold haarOrientationBenchmark
  push_cast
  rw [add_sub_cancel_left]
  field_simp [hk', hp', hn']
  ring

set_option maxHeartbeats 500000 in
/-- The finite-gap bias for every target is bounded uniformly in its rank
by the same inverse-chi-square moment used in the averaged gap comparison. -/
theorem haarSketchFiniteMean_window_difference {p : ℕ} (hk : 0 < k)
    (hp : 2 ≤ p) (hl : k + p ≤ n) {L : ℝ} (hL : 0 < L)
    (hΓ : 2 ≤ (n : ℝ) * k * L) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    0 ≤ haarOrientationBenchmark n k (k + p) - haarSketchFiniteMean hl ((n : ℝ) * k * L) V ∧
      haarOrientationBenchmark n k (k + p) - haarSketchFiniteMean hl ((n : ℝ) * k * L) V ≤
        chiSquareNegativeMoment (p + 1) (5 / 4 : ℝ) * (2 / L) ^ (1 / 4 : ℝ) := by
  let Γ := (n : ℝ) * k * L
  let ν := haarSketchProjectorLaw hl
  let η := gaussianHaarFrameLaw (show k ≤ n by omega)
  let h := haarOrientationBenchmark n k (k + p)
  let r : ℝ := 5 / 4
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  let M := chiSquareNegativeMoment (p + 1) r
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkp : k + 1 < k + p := by omega
  have hkn : k < n := by omega
  have hnp : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
  have hb : 0 < b := by dsimp [b]; linarith
  have hc : 0 < c := by dsimp [b, c] at *; linarith
  have hΓ' : 1 < Γ := lt_of_lt_of_le (by norm_num) hΓ
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hr' : r < (((k + p) - k + 1 : ℕ) : ℝ) / 2 := by
    rw [Nat.add_sub_cancel_left, Nat.cast_add]
    dsimp [r]
    push_cast
    linarith
  have hM : 0 ≤ M := by
    unfold M chiSquareNegativeMoment
    push_cast
    have h₁ := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 - r by dsimp [r]; linarith)
    have h₂ := Real.Gamma_pos_of_pos (show 0 < ((p : ℝ) + 1) / 2 by linarith)
    positivity
  have hMean := haarOrientationEndpoint_mean hl hk hkp ν
  have hFin := integrable_haarOrientationFiniteMean hk hkn ν hΓ'.le
  have he : (∫ W, haarOrientationFiniteMean ν Γ W ∂η) =
      haarSketchFiniteMean hl Γ V := by
    calc
      _ = ∫ _W : Matrix (Fin n) (Fin k) ℝ, haarSketchFiniteMean hl Γ V ∂η := by
        apply integral_congr_ae
        filter_upwards [ae_gaussianHaarFrame_orthonormal hkn.le] with W hW
        exact haarSketchFiniteMean_eq_of_frames hl hk hkn hΓ'.le W V hW hV
      _ = _ := by simp [integral_const]
  have hEq : (∫ W, haarOrientationEndpoint ν W - haarOrientationFiniteMean ν Γ W ∂η) =
      h - haarSketchFiniteMean hl Γ V := by
    rw [integral_sub hMean.1 hFin, hMean.2, he]
  constructor
  · rw [← hEq]
    apply integral_nonneg_of_ae
    filter_upwards [ae_haarOrientationGap_bound hl hkp hk ν
      (show 1 < r by norm_num [r]) (show r ≤ 2 by norm_num [r]) hr'] with W hW
    exact (hW Γ hΓ').1
  · rw [← hEq]
    have hGap := haarOrientationGap_integral_bound hl hkp hk ν hΓ'
      (show 1 < r by norm_num [r]) (show r ≤ 2 by norm_num [r]) hr'
    rw [Nat.add_sub_cancel_left] at hGap
    refine hGap.trans ?_
    have hbc : b / c ≤ 1 := (div_le_one hc).2 (by dsimp [b,c]; linarith)
    have harg : 0 ≤ (k : ℝ) * b / (Γ - 1) := by positivity
    have hratio : (k : ℝ) * b / (Γ - 1) ≤ 2 / L := by
      apply (div_le_iff₀ (sub_pos.mpr hΓ')).2
      calc
        (k : ℝ) * b ≤ (n : ℝ) * k := by
          rw [mul_comm (n : ℝ)]
          exact mul_le_mul_of_nonneg_left (by dsimp [b]; linarith) hk'.le
        _ ≤ (2 / L) * (Γ - 1) := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hL).2
          change Γ ≤ 2 * (Γ - 1)
          linarith only [hΓ]
    change b / c * (M * ((k : ℝ) * b / (Γ - 1)) ^ (r - 1)) ≤ _
    refine (mul_le_of_le_one_left (mul_nonneg hM (Real.rpow_nonneg harg _)) hbc).trans ?_
    have hPow := Real.rpow_le_rpow harg hratio (show 0 ≤ r - 1 by norm_num [r])
    simpa [M, r, show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] using
      mul_le_mul_of_nonneg_left hPow hM

/-- The finite-dimensional benchmark converges at fixed oversampling as
the dimension of the orthogonal complement tends to infinity. -/
theorem haarOrientationBenchmark_tendsto_window {n k : ℕ → ℕ} {p : ℕ}
    (hk : ∀ i, 0 < k i) (hp : 2 ≤ p) (hl : ∀ i, k i + p ≤ n i)
    (hDen : Tendsto (fun i => (n i : ℝ) - k i) atTop atTop) :
    Tendsto (fun i => haarOrientationBenchmark (n i) (k i) (k i + p))
      atTop (𝓝 (1 / ((p : ℝ) - 1))) := by
  let q := 1 / ((p : ℝ) - 1)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 0 ≤ q := one_div_nonneg.mpr (by linarith)
  have h := hDen.inv_tendsto_atTop.const_mul ((p : ℝ) * (1 + q))
  simp only [mul_zero] at h
  have hErr : Tendsto (fun i => q - haarOrientationBenchmark (n i) (k i) (k i + p))
      atTop (𝓝 0) := by
    refine squeeze_zero (g := fun i => (p : ℝ) * (1 + q) * ((n i : ℝ) - k i)⁻¹) ?_ ?_ h
    · intro i
      rw [haarOrientationBenchmark_window_difference (hk i) hp (hl i)]
      have hd : 0 ≤ (n i : ℝ) - k i := by
        exact sub_nonneg.mpr (by exact_mod_cast (show k i ≤ n i by have := hl i; omega))
      change 0 ≤ (p : ℝ) * ((k i : ℝ)⁻¹ + q) / ((n i : ℝ) - k i)
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (by positivity) hq)) hd
    · intro i
      rw [haarOrientationBenchmark_window_difference (hk i) hp (hl i), ← div_eq_mul_inv]
      have hd : 0 ≤ (n i : ℝ) - k i := by
        exact sub_nonneg.mpr (by exact_mod_cast (show k i ≤ n i by have := hl i; omega))
      have hk' : (1 : ℝ) ≤ k i := by exact_mod_cast (show 1 ≤ k i from hk i)
      apply div_le_div_of_nonneg_right _ hd
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      change (k i : ℝ)⁻¹ + q ≤ 1 + q
      linarith only [inv_le_one_of_one_le₀ hk']
  simpa only [sub_zero, sub_sub_cancel] using hErr.const_sub q

/-- Fixed-oversampling convergence of the native Haar mean at the finite
cosine-window gap, allowing the target rank and frame to vary arbitrarily. -/
theorem haarSketchFiniteMean_tendsto_window {n k : ℕ → ℕ} {p : ℕ} {L : ℕ → ℝ}
    (hk : ∀ i, 0 < k i) (hp : 2 ≤ p) (hl : ∀ i, k i + p ≤ n i)
    (hDen : Tendsto (fun i => (n i : ℝ) - k i) atTop atTop) (hL : Tendsto L atTop atTop)
    (V : (i : ℕ) → Matrix (Fin (n i)) (Fin (k i)) ℝ) (hV : ∀ i, (V i)ᵀ * V i = 1) :
    Tendsto (fun i => haarSketchFiniteMean (hl i) ((n i : ℝ) * k i * L i) (V i))
      atTop (𝓝 (1 / ((p : ℝ) - 1))) := by
  have hFeasible : ∀ᶠ i in atTop, 0 < L i ∧ 2 ≤ (n i : ℝ) * k i * L i := by
    filter_upwards [hL.eventually_ge_atTop 2] with i hi
    have hK : (1 : ℝ) ≤ k i := by exact_mod_cast (show 1 ≤ k i from hk i)
    have hN : (1 : ℝ) ≤ n i := by exact_mod_cast (show 1 ≤ n i by have := hl i; have := hk i; omega)
    have hNK : (1 : ℝ) ≤ (n i : ℝ) * k i := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hK), hK, hN]
    exact ⟨by linarith, hi.trans (le_mul_of_one_le_left (by linarith) hNK)⟩
  have hd : Tendsto (fun i => 2 / L i) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hL
  have hPow := (Real.continuous_rpow_const (show 0 ≤ (1 / 4 : ℝ) by norm_num)).continuousAt
    (x := 0) |>.tendsto.comp hd
  rw [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] at hPow
  have hBound := hPow.const_mul (chiSquareNegativeMoment (p + 1) (5 / 4 : ℝ))
  simp only [mul_zero] at hBound
  have hErr : Tendsto (fun i => haarOrientationBenchmark (n i) (k i) (k i + p) -
      haarSketchFiniteMean (hl i) ((n i : ℝ) * k i * L i) (V i)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hBound
    · filter_upwards [hFeasible] with i hi
      exact (haarSketchFiniteMean_window_difference (hk i) hp (hl i) hi.1 hi.2 (V i) (hV i)).1
    · filter_upwards [hFeasible] with i hi
      exact (haarSketchFiniteMean_window_difference (hk i) hp (hl i) hi.1 hi.2 (V i) (hV i)).2
  simpa only [sub_zero, sub_sub_cancel] using
    (haarOrientationBenchmark_tendsto_window hk hp hl hDen).sub hErr

/-- The actual one- or two-pass cosine window suffices for both the
infinite-gap Haar benchmark and the Haar mean at the same finite gap. -/
theorem cosineWindow_haar_limits {n k : ℕ → ℕ} {p : ℕ} {L : ℕ → ℝ} (hp : 2 ≤ p)
    (hn : Tendsto n atTop atTop) (hk : ∀ i, 0 < k i) (hl : ∀ i, k i + p ≤ n i)
    (mode : DctPasses) (V : (i : ℕ) → Matrix (Fin (n i)) (Fin (k i)) ℝ)
    (hV : ∀ i, (V i)ᵀ * V i = 1) (hL : Tendsto L atTop atTop)
    (hWindow : Tendsto (fun i => L i ^ 2 * (k i : ℝ) * ((k i + p : ℕ) : ℝ)^2 *
      meanDctRowEnergy mode (V i)) atTop (𝓝 0)) :
    Tendsto (fun i => haarOrientationBenchmark (n i) (k i) (k i + p))
      atTop (𝓝 (1 / ((p : ℝ) - 1))) ∧
    Tendsto (fun i => haarSketchFiniteMean (hl i) ((n i : ℝ) * k i * L i) (V i))
      atTop (𝓝 (1 / ((p : ℝ) - 1))) := by
  let N (i : ℕ) := (n i : ℝ)
  let K (i : ℕ) := (k i : ℝ)
  have hn' (i : ℕ) : 0 < n i := by have := hl i; omega
  have hN (i : ℕ) : 0 < N i := Nat.cast_pos.mpr (hn' i)
  have hK (i : ℕ) : 1 ≤ K i := by
    dsimp [K]
    exact_mod_cast (show 1 ≤ k i from hk i)
  have hQ : Tendsto (fun i => L i ^ 2 * K i ^ 5 / N i) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hWindow
    · exact Eventually.of_forall fun i => by have := hN i; have := hK i; positivity
    · exact Eventually.of_forall fun i =>
        window_controls_power (hN i) (zero_le_one.trans (hK i))
          (by dsimp [K]; exact_mod_cast Nat.le_add_right (k i) p)
          (meanDctRowEnergy_lower (hn' i) mode (hV i))
  have hRatio := (cosineWindow_scale_limits hN hK hL hQ).1
  have hnR : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hDen : Tendsto (fun i => N i - K i) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (hnR.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hRatio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hi
    linarith [(div_lt_iff₀ (hN i)).mp hi]
  exact ⟨haarOrientationBenchmark_tendsto_window hk hp hl hDen,
    haarSketchFiniteMean_tendsto_window hk hp hl hDen hL V hV⟩

private theorem tailRelativeError_eq_centered (hk : 0 < k) (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin l) ℝ) :
    tailRelativeError k A U = 1 + (k : ℝ) * centeredRankLoss k A U := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold centeredRankLoss
  field_simp
  ring

/-- The native Haar mean in tail-relative normalization at the finite gap. -/
theorem haarSketchTailRelativeMean_eq (hl : l ≤ n) (hk : 0 < k) (hkn : k < n)
    {L : ℝ} (hL : 0 < L) (hΓ : 1 ≤ (n : ℝ) * k * L)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    (∫ U, tailRelativeError k (twoLevelInput V ((n : ℝ) * k * L)) U ∂gaussianHaarFrameLaw hl) =
      1 + (k : ℝ) * haarSketchFiniteMean hl ((n : ℝ) * k * L) V := by
  let Γ := (n : ℝ) * k * L
  let F (U : Matrix (Fin n) (Fin l) ℝ) := orientationFiniteLoss Γ (haarFrameProjector hl U) V
  let η := gaussianHaarFrameLaw hl
  have hF : Measurable F :=
    (measurable_orientationFiniteLoss_fixed Γ V).comp (measurable_haarFrameProjector hl)
  have hFC (U : Matrix (Fin n) (Fin l) ℝ) (hU : Uᵀ * U = 1) :
      F U = centeredRankLoss k (twoLevelInput V Γ) U := by
    unfold F
    rw [orientationFiniteLoss_eq_actual hk hkn Γ hΓ _ V hV, projectorTwoLevelLoss,
      haarFrameProjector_val hl hU]
    unfold centeredRankLoss tailRelativeError
    rw [squaredResidual_frame_projector _ _ hU]
  have hI : Integrable F η := by
    refine (integrable_const ((k : ℝ) * L + ((k : ℝ)^2 * L + 1 + (l : ℝ) / k) / (n - (k : ℝ)))).mono'
      hF.aestronglyMeasurable ?_
    filter_upwards [ae_gaussianHaarFrame_orthonormal hl] with U hU
    let R := ridgeInverseTrace L (scaledTargetBlock V U)
    have hR := ridgeInverseTrace_bounds hL.le (scaledTargetBlock V U)
    have hGap := centeredRankLoss_ridge_difference hk hkn hL hΓ V hV U hU
    change |F U| ≤ _
    rw [hFC U hU]
    have he : centeredRankLoss k (twoLevelInput V Γ) U - R + R =
        centeredRankLoss k (twoLevelInput V Γ) U := sub_add_cancel _ _
    have hAbs := abs_add_le (centeredRankLoss k (twoLevelInput V Γ) U - R) R
    rw [he, abs_of_nonneg hR.1] at hAbs
    exact hAbs.trans (add_le_add hGap hR.2 |>.trans_eq (by ring))
  change (∫ U, tailRelativeError k (twoLevelInput V Γ) U ∂η) = _
  rw [haarSketchFiniteMean_eq_integral hl hk hkn hΓ V hV]
  calc
    _ = ∫ U, 1 + (k : ℝ) * F U ∂η := by
      apply integral_congr_ae
      filter_upwards [ae_gaussianHaarFrame_orthonormal hl] with U hU
      rw [hFC U hU, tailRelativeError_eq_centered hk]
    _ = _ := by
      change (∫ U, 1 + (k : ℝ) * F U ∂η) = 1 + (k : ℝ) * ∫ U, F U ∂η
      rw [integral_add (integrable_const _) (hI.const_mul _), integral_const_mul]
      simp

/-- At fixed rank the actual Haar tail-relative mean tends to the same
limit as the structured sketch in the window. -/
theorem cosineWindow_haarTailRelative_tendsto {n : ℕ → ℕ} {k p : ℕ} {L : ℕ → ℝ}
    (hp : 2 ≤ p) (hn : Tendsto n atTop atTop) (hk : 0 < k) (hl : ∀ i, k + p ≤ n i)
    (mode : DctPasses) (V : (i : ℕ) → Matrix (Fin (n i)) (Fin k) ℝ)
    (hV : ∀ i, (V i)ᵀ * V i = 1) (hL : Tendsto L atTop atTop)
    (hWindow : Tendsto (fun i => L i ^ 2 * (k : ℝ) * ((k + p : ℕ) : ℝ)^2 *
      meanDctRowEnergy mode (V i)) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ U, tailRelativeError k (twoLevelInput (V i) ((n i : ℝ) * k * L i)) U
      ∂gaussianHaarFrameLaw (hl i)) atTop (𝓝 (1 + (k : ℝ) / ((p : ℝ) - 1))) := by
  have hm := (cosineWindow_haar_limits hp hn (fun _ => hk) hl mode V hV hL hWindow).2
  have h := (hm.const_mul (k : ℝ)).const_add 1
  rw [mul_one_div] at h
  refine h.congr' ?_
  filter_upwards [hL.eventually_ge_atTop 1] with i hi
  have hN : (1 : ℝ) ≤ n i := by exact_mod_cast (show 1 ≤ n i by have := hl i; omega)
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k from hk)
  have hG : 1 ≤ (n i : ℝ) * k * L i := by
    have hNK : (1 : ℝ) ≤ (n i : ℝ) * k := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hK), hN, hK]
    exact hi.trans (le_mul_of_one_le_left (by linarith) hNK)
  exact (haarSketchTailRelativeMean_eq (hl i) hk (by have := hl i; omega)
    (by linarith) hG (V i) (hV i)).symm

/-- Fixed-rank conversion for the actual finite signed DCT draw law. -/
theorem dctTailRelative_tendsto_of_dctLossMean {n : ℕ → ℕ} {k p : ℕ} {L : ℕ → ℝ}
    (hk : 0 < k) (hl : ∀ i, k + p ≤ n i)
    (mode : DctPasses) (V : (i : ℕ) → Matrix (Fin (n i)) (Fin k) ℝ)
    (h : Tendsto (fun i => dctLossMean (l := k + p) mode (V i) (L i))
      atTop (𝓝 (1 / ((p : ℝ) - 1)))) :
    Tendsto (fun i => uniformMean (fun d : DctDraw (n i) (k + p) =>
      tailRelativeError k (twoLevelInput (V i) ((n i : ℝ) * k * L i)) (mode.sketch d)))
      atTop (𝓝 (1 + (k : ℝ) / ((p : ℝ) - 1))) := by
  have hh := (h.const_mul (k : ℝ)).const_add 1
  rw [mul_one_div] at hh
  refine hh.congr (fun i => ?_)
  let : Nonempty (DctDraw (n i) (k + p)) := ⟨⟨Fin.castLEEmb (hl i), fun _ => false, fun _ => false⟩⟩
  simp_rw [tailRelativeError_eq_centered hk]
  unfold dctLossMean uniformMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_one]
  rw [div_self (by exact_mod_cast Fintype.card_ne_zero)]

end

end SketchOrientation.Cosine
