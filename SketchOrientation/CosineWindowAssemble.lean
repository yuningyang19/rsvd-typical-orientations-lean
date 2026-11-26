import SketchOrientation.CosineWindowLimits
import SketchOrientation.DctBlockLimit

namespace SketchOrientation.Cosine

open Matrix MeasureTheory Filter Topology Edge.Walsh

/-- The actual finite-sketch loss mean in the two-level window. -/
noncomputable def dctLossMean {n k l : ℕ} (mode : DctPasses)
    (V : Matrix (Fin n) (Fin k) ℝ) (L : ℝ) : ℝ :=
  uniformMean (fun d : DctDraw n l =>
    centeredRankLoss k (twoLevelInput V ((n : ℝ) * k * L)) (mode.sketch d))

/-- The actual regularized inverse trace of the same sketch law. -/
noncomputable def dctRidgeMean {n k l : ℕ} (mode : DctPasses)
    (V : Matrix (Fin n) (Fin k) ℝ) (L : ℝ) : ℝ :=
  uniformMean (fun d : DctDraw n l => ridgeInverseTrace L (scaledTargetBlock V (mode.sketch d)))

theorem meanDctRowEnergy_lower {n k : ℕ} (hn : 0 < n) (mode : DctPasses)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    ((k : ℝ)^2 / n) ≤ meanDctRowEnergy mode V := by
  rw [← uniformMean_const (A := Fin n → Bool) (((k : ℝ)^2 / n))]
  exact uniformMean_mono fun b => rowEnergy_lower hn (intermediateFrame_orthonormal mode hV b)

private theorem dctLossMean_ridgeMean_difference {n k l : ℕ}
    (hl : l ≤ n) (mode : DctPasses) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (hk : 0 < k) (hkn : k < n) {L : ℝ} (hL : 0 < L) (hΓ : 1 ≤ (n : ℝ) * k * L) :
    |dctLossMean (l := l) mode V L - dctRidgeMean (l := l) mode V L| ≤
      ((k : ℝ)^2 * L + 1 + (l : ℝ) / k) / (n - k) := by
  letI : Nonempty (Fin l ↪ Fin n) := ⟨Fin.castLEEmb hl⟩
  rw [dctLossMean, dctRidgeMean, ← uniformMean_sub]
  exact (abs_uniformMean_le _).trans ((uniformMean_mono (fun d : DctDraw n l =>
    centeredRankLoss_ridge_difference hk hkn hL hΓ V hV (mode.sketch d)
      (mode.sketch_orthonormal d))).trans_eq (uniformMean_const _))

/-- With Proposition 5.1's comparison estimate as input, the paper's
complete growing-gap conclusion for either finite DCT draw law follows. -/
theorem cosineWindow_tendsto_of_comparison {n k : ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p)
    (hn : Tendsto n atTop atTop) (hk : ∀ i, 0 < k i) (hl : ∀ i, k i + p ≤ n i)
    (mode : DctPasses) (V : (i : ℕ) → Matrix (Fin (n i)) (Fin (k i)) ℝ)
    (hV : ∀ i, (V i)ᵀ * V i = 1) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hWindow : Tendsto (fun i => L i ^ 2 * (k i : ℝ) * ((k i + p : ℕ) : ℝ)^2 *
      meanDctRowEnergy mode (V i)) atTop (𝓝 0))
    (hCompare : ∀ i, 0 < L i →
      |dctRidgeMean (l := k i + p) mode (V i) (L i) -
        (∫ Z, ridgeInverseTrace (L i) Zᵀ ∂gaussianMatrixLaw (k i + p) (k i))| ≤
      (1856 / ((p : ℝ) - 1)) * L i ^ 2 * (k i : ℝ) * ((k i + p : ℕ) : ℝ)^2 *
        meanDctRowEnergy mode (V i) +
      14 * L i * (k i : ℝ) * ((k i + p : ℕ) : ℝ)^2 *
        ((n i : ℝ) / (n i - 1)) * meanDctRowEnergy mode (V i)) :
    Tendsto (fun i => dctLossMean (l := k i + p) mode (V i) (L i))
      atTop (𝓝 (1 / ((p : ℝ) - 1))) := by
  let N (i : ℕ) := (n i : ℝ)
  let K (i : ℕ) := (k i : ℝ)
  let E (i : ℕ) := ((k i + p : ℕ) : ℝ)
  let η (i : ℕ) := meanDctRowEnergy mode (V i)
  let q (i : ℕ) := L i ^ 2 * K i * E i ^ 2 * η i
  have hN (i : ℕ) : (1 : ℝ) < N i := by
    dsimp [N]
    exact_mod_cast (show 1 < n i by have := hl i; omega)
  have hK (i : ℕ) : (1 : ℝ) ≤ K i := by
    dsimp [K]
    exact_mod_cast (show 1 ≤ k i from hk i)
  have hE (i : ℕ) : K i ≤ E i := by
    dsimp [K, E]
    exact_mod_cast Nat.le_add_right (k i) p
  have hKn (i : ℕ) : k i < n i := by have := hl i; omega
  have hKnR (i : ℕ) : K i ≤ N i := by
    dsimp [K, N]
    exact_mod_cast (hKn i).le
  have hnR : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hQ : Tendsto (fun i => L i ^ 2 * K i ^ 5 / N i) atTop (𝓝 0) := by
    refine squeeze_zero (g := q) (fun _ => by positivity) ?_ hWindow
    exact fun i => window_controls_power (by linarith [hN i]) (by linarith [hK i]) (hE i)
      (meanDctRowEnergy_lower (Nat.zero_lt_of_lt (hKn i)) mode (hV i))
  obtain ⟨hKnLim, hScale⟩ := cosineWindow_scale_limits (fun i => by linarith [hN i]) hK hL hQ
  have hDen : Tendsto (fun i => N i - K i) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (hnR.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hKnLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hi
    have hNi : 0 < N i := by linarith [hN i]
    have h := (div_lt_iff₀ hNi).mp hi
    linarith
  have hSecond : Tendsto (fun i => (1 + E i / K i) / (N i - K i)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun i => (2 + (p : ℝ)) * (N i - K i)⁻¹) ?_ ?_ ?_
    · intro i
      have hd : 0 ≤ N i - K i := sub_nonneg.mpr (hKnR i)
      have hKi : 0 ≤ K i := by linarith [hK i]
      have hEi : 0 ≤ E i := by dsimp [E]; positivity
      positivity
    · intro i
      have hd : 0 ≤ N i - K i := sub_nonneg.mpr (hKnR i)
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right _ hd
      have he : E i = K i + (p : ℝ) := by dsimp [E, K]; push_cast; rfl
      have hk0 : 0 < K i := by linarith [hK i]
      rw [he, add_div, div_self hk0.ne']
      linarith only [div_le_self (show (0 : ℝ) ≤ p by positivity) (hK i)]
    · simpa only [Pi.inv_apply, mul_zero] using hDen.inv_tendsto_atTop.const_mul (2 + (p : ℝ))
  have hFinite : Tendsto (fun i => |dctLossMean (l := k i + p) mode (V i) (L i) -
      dctRidgeMean (l := k i + p) mode (V i) (L i)|) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun i => K i ^ 2 * L i / (N i - K i) +
      (1 + E i / K i) / (N i - K i)) (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
    · filter_upwards [hL.eventually_ge_atTop 1] with i hi
      have hNi : 1 ≤ N i := (hN i).le
      have hΓ : 1 ≤ N i * K i * L i :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hNi (hK i)) hi
      have h := dctLossMean_ridgeMean_difference (hl i) mode (V i) (hV i) (hk i) (hKn i)
        (zero_lt_one.trans_le hi) hΓ
      simpa only [N, K, E, ← add_div, add_assoc] using h
    · simpa only [add_zero] using hScale.add hSecond
  have hCompareLimit : Tendsto (fun i => |dctRidgeMean (l := k i + p) mode (V i) (L i) -
      (∫ Z, ridgeInverseTrace (L i) Zᵀ ∂gaussianMatrixLaw (k i + p) (k i))|) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun i => (1856 / ((p : ℝ) - 1) + 28) * q i)
      (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
    · filter_upwards [hL.eventually_ge_atTop 1] with i hi
      have hni : (2 : ℝ) ≤ N i := by
        dsimp [N]
        exact_mod_cast (show 2 ≤ n i by have := hl i; omega)
      have hRatio : N i / (N i - 1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      have hQp : 0 ≤ K i * E i ^ 2 * η i :=
        mul_nonneg (mul_nonneg (by linarith [hK i]) (sq_nonneg _)) (meanDctRowEnergy_nonneg _ _)
      have hLPos : 0 ≤ L i := zero_le_one.trans hi
      have hEx : 14 * L i * (N i / (N i - 1)) ≤ 28 * L i ^ 2 := by
        calc
          _ ≤ 14 * L i * 2 := mul_le_mul_of_nonneg_left hRatio (by positivity)
          _ = 28 * L i := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hLPos (sub_nonneg.mpr hi)])
            (by norm_num)
      refine (hCompare i (zero_lt_one.trans_le hi)).trans ?_
      have hEx' := mul_le_mul_of_nonneg_right hEx hQp
      change 1856 / ((p : ℝ) - 1) * L i ^ 2 * K i * E i ^ 2 * η i +
        14 * L i * K i * E i ^ 2 * (N i / (N i - 1)) * η i ≤ _
      unfold q
      linarith only [hEx']
    · simpa only [mul_zero] using hWindow.const_mul (1856 / ((p : ℝ) - 1) + 28)
  have hA : Tendsto (fun i => dctLossMean (l := k i + p) mode (V i) (L i) -
      dctRidgeMean (l := k i + p) mode (V i) (L i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hFinite
  have hB : Tendsto (fun i => dctRidgeMean (l := k i + p) mode (V i) (L i) -
      (∫ Z, ridgeInverseTrace (L i) Zᵀ ∂gaussianMatrixLaw (k i + p) (k i))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hCompareLimit
  have h := (gaussianRidge_tendsto hk hp hL).add (hB.add hA)
  simp only [add_zero] at h
  exact h.congr (fun i => by ring)

end SketchOrientation.Cosine
