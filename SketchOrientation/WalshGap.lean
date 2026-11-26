import SketchOrientation.WalshMiss
import SketchOrientation.WalshSignedPerm

/-!
# Divergence at a prescribed gap
-/

open Filter
open scoped Topology BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

/-- Mean of the rank-one loss over the signed Walsh law. -/
def meanLoss (m s ell : ℕ) (L : ℝ) : ℝ :=
  uniformMean fun d : Draw m s ell =>
    rankOneLoss ((2 : ℝ)^m) L ell (walshTableEnergy (table d))

theorem meanLoss_eq_signedPerm {m s ell : ℕ}
    (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) (L : ℝ) :
    (uniformMean fun d : SignedPermDraw m => rankOneLoss ((2 : ℝ)^m) L ell
      (∑ j, (normalizedProjection rows cols d j)^2)) = meanLoss m s ell L := by
  simp_rw [projectionEnergy_eq_tableEnergy]
  exact uniformMean_restrictSignedPerm rows cols (fun d =>
    rankOneLoss ((2 : ℝ)^m) L ell (walshTableEnergy (table d)))

theorem missProbability_eq_signedPerm {m s ell : ℕ}
    (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) :
    (uniformProbability fun d : SignedPermDraw m =>
      (∑ j, (normalizedProjection rows cols d j)^2) = 0) = missProbability m s ell := by
  simp_rw [uniformProbability, projectionEnergy_eq_tableEnergy]
  exact uniformMean_restrictSignedPerm rows cols (fun d =>
    indicator (walshTableEnergy (table d) = 0))

private theorem uniformMean_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

private theorem meanLoss_lower_bound {m s ell : ℕ}
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)] (hm : 1 ≤ m) {L : ℝ}
    (hL : 1 ≤ L) :
    L * missProbability m s ell - (ell : ℝ) ≤ meanLoss m s ell L := by
  classical
  let n : ℝ := 2^m
  have hn : 2 ≤ n := by
    simpa [n] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hdiv : (ell : ℝ) / (n - 1) ≤ ell := by
    exact div_le_self (by positivity) (by linarith)
  have h₁ : 1 ≤ n / (n - 1) := (le_div_iff₀ (by linarith)).2 (by linarith)
  have hLn : 0 ≤ L - 1 / n := by
    have hinv : (1 : ℝ) / n ≤ 1 := (div_le_iff₀ (by linarith)).2 (by nlinarith)
    linarith
  have hpoint (y : ℝ) (hy : 0 ≤ y) :
      L * indicator (y = 0) - (ell : ℝ) ≤ rankOneLoss n L ell y := by
    by_cases h : y = 0
    · rw [h, rankOneLoss]
      simp only [indicator, ↓reduceIte, mul_zero, add_zero, div_one, mul_one]
      linarith [mul_le_mul_of_nonneg_right h₁ (show 0 ≤ L by linarith)]
    · simp only [indicator, h, if_false, mul_zero, zero_sub, rankOneLoss]
      have hfrac : 0 ≤ n / (n - 1) * (L / (1 + (L - 1 / n) * y)) := by
        apply mul_nonneg (by linarith)
        exact div_nonneg (by linarith) (by positivity)
      linarith
  have h := uniformMean_mono (A := Draw m s ell)
    (fun d => hpoint (walshTableEnergy (table d)) (by
      exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)))
  simpa only [meanLoss, missProbability, uniformProbability, uniformMean_sub, uniformMean_mul_const,
    uniformMean_const] using h

/-- The flat support chosen from the gap gives mean divergence for the actual
Walsh signed-permutation law. -/
theorem tendsto_prescribedGap_meanLoss {ell : ℕ} (hell : 2 < ell) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto (fun i => meanLoss (m i) (walshSupport ell ((2 : ℝ) ^ m i) (L i)) ell (L i))
      atTop atTop := by
  let n (i : ℕ) : ℝ := 2 ^ m i
  let s (i : ℕ) := walshSupport ell (n i) (L i)
  have hn : Tendsto n atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  have hL₀ : ∀ᶠ i in atTop, 0 ≤ L i := hL.eventually_ge_atTop 0
  have hs : Tendsto s atTop atTop := tendsto_walshSupport (by omega) hn hL
  have hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i := by
    filter_upwards [hL₀] with i hi
    have hni : 1 ≤ (2 : ℕ)^m i := Nat.one_le_pow _ _ (by decide)
    simpa only [s, n, Nat.cast_pow, Nat.cast_ofNat] using
      (walshSupport_le_dimension (ell := ell) hni hi)
  have hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i := by
    have hn' : Tendsto (fun i => (2 : ℕ)^m i) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2)).comp hm
    exact hn'.eventually_ge_atTop ell
  have hnorm := tendsto_scaled_missProbability hs
    (Eventually.of_forall fun i => walshSupport_even ell (n i) (L i))
    hr hc (walshSupport_growth hn hL₀)
  have hm0 := walshSupport_atomScale (ell := ell) (by omega) hn hL
  let K : ℝ := (2 / Real.pi : ℝ) ^ ((ell : ℝ) / 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hπ : Tendsto (fun i => L i * missProbability (m i) (s i) ell) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (hm0.const_mul_atTop (half_pos hK))
    have hlim : ∀ᶠ i in atTop,
        K / 2 ≤ missProbability (m i) (s i) ell * (s i : ℝ) ^ ((ell : ℝ) / 2) :=
      hnorm.eventually (le_mem_nhds (by linarith : K / 2 < K))
    filter_upwards [hlim, hL₀, hs.eventually_ge_atTop 1] with i hi hLi hsi
    have hsr : 0 < (s i : ℝ) := by exact_mod_cast (show 0 < s i by omega)
    have hf : 0 < (s i : ℝ) ^ ((ell : ℝ) / 2) := Real.rpow_pos_of_pos hsr _
    change K / 2 * (L i * (s i : ℝ) ^ (-(ell : ℝ) / 2)) ≤ _
    rw [neg_div, Real.rpow_neg hsr.le, ← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ hf]
    calc
      K / 2 * L i ≤ (missProbability (m i) (s i) ell * (s i : ℝ) ^ ((ell : ℝ) / 2)) * L i :=
        mul_le_mul_of_nonneg_right hi hLi
      _ = _ := by ring
  change Tendsto (fun i => meanLoss (m i) (s i) ell (L i)) atTop atTop
  refine tendsto_atTop.2 fun b => ?_
  have hπ' := hπ.eventually_ge_atTop (b + (ell : ℝ))
  filter_upwards [hπ', hr, hc, hm.eventually_ge_atTop 1, hL.eventually_ge_atTop 1] with i hi hri hci hmi hLi
  letI := label_embedding_nonempty (m := m i) hri
  letI := label_embedding_nonempty (m := m i) hci
  linarith only [hi, meanLoss_lower_bound (s := s i) (ell := ell) hmi hLi]

end SketchOrientation.Edge.Walsh
