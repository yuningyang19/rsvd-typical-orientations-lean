import SketchOrientation.DctSampling
import SketchOrientation.CosineReflection
import SketchOrientation.GramResidual

namespace SketchOrientation.Cosine

open Matrix Edge.Walsh

private noncomputable def blockSq {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑ a, ∑ b, (C a b) ^ 2

/-- Conditional covariance, with each sampled output coordinate paired with
its target coordinate in the vectorized block. -/
noncomputable def sampledCovariance {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (J : Fin l ↪ Fin n) : Matrix (Fin l × Fin k) (Fin l × Fin k) ℝ :=
  fun a b => covarianceBlock V (J a.1) (J b.1) a.2 b.2

private theorem sum_trace_diagonal {n k : ℕ} {V : Matrix (Fin n) (Fin k) ℝ}
    (hV : Vᵀ * V = 1) :
    ∑ r, (covarianceBlock V r r).trace = (n : ℝ) * k := by
  have h := congrArg Matrix.trace (covarianceBlock_diag_sum hV)
  simpa only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
    Fintype.card_fin] using h

/-- The mean covariance trace defect vanishes before the expectation over
the first-pass signs, as used in Proposition 5.1. -/
theorem sampledCovariance_trace_defect_mean {n k l : ℕ} (hn : 0 < n) (hl : l ≤ n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    uniformMean (fun J : Fin l ↪ Fin n => (sampledCovariance V J - 1).trace) = 0 := by
  letI : Nonempty (Fin l ↪ Fin n) := ⟨Fin.castLEEmb hl⟩
  simp only [trace_sub, trace_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  rw [uniformMean_sub, uniformMean_const]
  have hTrace (J : Fin l ↪ Fin n) :
      (sampledCovariance V J).trace = ∑ j, (covarianceBlock V (J j) (J j)).trace := by
    simp only [trace, diag, sampledCovariance, Fintype.sum_prod_type]
  simp_rw [hTrace]
  rw [uniformMean_sum]
  have hMean (j : Fin l) : uniformMean (fun J : Fin l ↪ Fin n =>
      (covarianceBlock V (J j) (J j)).trace) = uniformMean
      (fun r => (covarianceBlock V r r).trace) :=
    uniformMean_orderedSample_apply hl j (fun r => (covarianceBlock V r r).trace)
  simp_rw [hMean]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [uniformMean, Fintype.card_fin, sum_trace_diagonal hV, mul_div_cancel_left₀ _ hnR,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]

/-- The raw diagonal block energy differs from the centered diagonal energy
by exactly n k. -/
theorem covarianceBlock_diagonal_raw_energy {n k : ℕ} (hn : 0 < n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    ∑ r, blockSq (covarianceBlock V r r) =
      (n : ℝ) * (covarianceBlock_diagonalMeanSq V + k) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hId : ∑ a : Fin k, ∑ b : Fin k, ((1 : Matrix (Fin k) (Fin k) ℝ) a b) ^ 2 = k := by
    simp [Matrix.one_apply]
  have hCross (r : Fin n) :
      ∑ a : Fin k, ∑ b : Fin k,
        covarianceBlock V r r a b * (1 : Matrix (Fin k) (Fin k) ℝ) a b
      = (covarianceBlock V r r).trace := by
    unfold Matrix.trace Matrix.diag
    apply Finset.sum_congr rfl
    intro a _
    simp [Matrix.one_apply]
  have hCenter :
      (∑ r, ∑ a, ∑ b, (covarianceBlock V r r a b - (1 : Matrix (Fin k) (Fin k) ℝ) a b) ^ 2) =
        (∑ r, blockSq (covarianceBlock V r r)) - (n : ℝ) * k := by
    have hPoint (r : Fin n) :
        (∑ a, ∑ b, (covarianceBlock V r r a b -
          (1 : Matrix (Fin k) (Fin k) ℝ) a b) ^ 2) =
          blockSq (covarianceBlock V r r) + (k : ℝ) -
            2 * (covarianceBlock V r r).trace := by
      simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hMul :
          (∑ a, ∑ b, 2 * covarianceBlock V r r a b *
            (1 : Matrix (Fin k) (Fin k) ℝ) a b) =
            2 * (covarianceBlock V r r).trace := by
        rw [← hCross r]
        simp_rw [Finset.mul_sum, mul_assoc]
      rw [hMul, hId]
      unfold blockSq
      ring
    simp_rw [hPoint]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_trace_diagonal hV]
    simp [nsmul_eq_mul]
    ring
  unfold covarianceBlock_diagonalMeanSq
  rw [hCenter]
  field_simp
  ring

theorem uniformMean_diag_pair_sum {n l : ℕ} (hl : l ≤ n)
    (d : Fin n → ℝ) (f : Fin n → Fin n → ℝ) :
    uniformMean (fun J : Fin l ↪ Fin n =>
      (∑ j, d (J j)) + ∑ p ∈ (Finset.univ : Finset (Fin l)).offDiag, f (J p.1) (J p.2)) =
      (l : ℝ) * uniformMean d +
        ((l : ℝ) * (l - 1)) *
          ((∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2) /
            ((n : ℝ) * (n - 1))) := by
  classical
  have hAdd (g h : (Fin l ↪ Fin n) → ℝ) :
      uniformMean (fun J => g J + h J) = uniformMean g + uniformMean h := by
    simp only [uniformMean, Finset.sum_add_distrib, add_div]
  rw [hAdd]
  congr 1
  · rw [uniformMean_sum]
    simp_rw [uniformMean_orderedSample_apply hl]
    simp [nsmul_eq_mul]
  · let s := (Finset.univ : Finset (Fin l)).offDiag
    have he (J : Fin l ↪ Fin n) : (∑ p ∈ s, f (J p.1) (J p.2)) =
        ∑ p : s, f (J p.val.1) (J p.val.2) :=
      (Finset.sum_coe_sort s (fun p : Fin l × Fin l => f (J p.1) (J p.2))).symm
    change uniformMean (fun J : Fin l ↪ Fin n => ∑ p ∈ s, f (J p.1) (J p.2)) = _
    rw [funext he]
    rw [uniformMean_sum]
    have hne (p : s) : p.val.1 ≠ p.val.2 := (Finset.mem_offDiag.mp p.property).2.2
    have hPair (p : s) : uniformMean (fun J : Fin l ↪ Fin n => f (J p.val.1) (J p.val.2)) =
        (∑ q ∈ (Finset.univ : Finset (Fin n)).offDiag, f q.1 q.2) /
          ((n : ℝ) * (n - 1)) :=
      uniformMean_orderedSample_pair hl p.val.1 p.val.2 (hne p) f
    simp_rw [hPair]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      s, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    cases l with
    | zero => simp
    | succ ll =>
      have he : (ll + 1) * (ll + 1) - (ll + 1) = (ll + 1) * ll := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
      rw [he, Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]


theorem squaredFrobenius_eq_sum_entries {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℝ) : squaredFrobenius A = ∑ i, ∑ j, (A i j) ^ 2 := by
  simp only [squaredFrobenius, trace, diag, mul_apply, transpose_apply, pow_two]
  exact Finset.sum_comm

/-- The exact sampled covariance energy identity (cos:cov-sample). -/
theorem sampledCovariance_meanSq_eq {n k l : ℕ} (hn : 1 < n) (hl : l ≤ n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    uniformMean (fun J : Fin l ↪ Fin n => squaredFrobenius (sampledCovariance V J - 1)) =
      (l : ℝ) * (l - 1) / (n - 1) * ((n : ℝ) * rowEnergy V - k) +
        (l : ℝ) * (n - l) / (n - 1) * covarianceBlock_diagonalMeanSq V := by
  classical
  let d (r : Fin n) : ℝ := blockSq (covarianceBlock V r r - 1)
  let f (r s : Fin n) : ℝ := blockSq (covarianceBlock V r s)
  have hSplit (J : Fin l ↪ Fin n) :
      squaredFrobenius (sampledCovariance V J - 1) =
        (∑ j, d (J j)) + ∑ p ∈ (Finset.univ : Finset (Fin l)).offDiag, f (J p.1) (J p.2) := by
    rw [squaredFrobenius_eq_sum_entries, sum_offDiag_eq_sum_sub_diag
      (fun r s : Fin l => f (J r) (J s))]
    simp only [Fintype.sum_prod_type]
    have hF (r s : Fin l) :
        (∑ a : Fin k, ∑ b : Fin k,
          ((sampledCovariance V J - 1) (r, a) (s, b)) ^ 2) =
          (if r = s then d (J r) else f (J r) (J s)) := by
      by_cases h : r = s
      · subst s
        simp [sampledCovariance, blockSq, d, Matrix.one_apply]
      · simp [sampledCovariance, blockSq, f, h]
    rw [show (∑ r : Fin l, ∑ a : Fin k, ∑ s : Fin l, ∑ b : Fin k,
          ((sampledCovariance V J - 1) (r,a) (s,b)) ^ 2) =
        ∑ r : Fin l, ∑ s : Fin l, ∑ a : Fin k, ∑ b : Fin k,
          ((sampledCovariance V J - 1) (r,a) (s,b)) ^ 2 by
      exact Finset.sum_congr rfl (fun r _ => Finset.sum_comm)]
    simp_rw [hF]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_erase_add _ (fun s => if r = s then d (J r) else f (J r) (J s))
      (Finset.mem_univ r)]
    rw [← Finset.sum_erase_add _ (fun s => f (J r) (J s)) (Finset.mem_univ r)]
    simp only [if_true, add_sub_cancel_right]
    have he :
        (∑ s ∈ Finset.univ.erase r, if r = s then d (J r) else f (J r) (J s)) =
          ∑ s ∈ Finset.univ.erase r, f (J r) (J s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact if_neg (Finset.ne_of_mem_erase hs).symm
    rw [he]
    abel
  have hMean : uniformMean d = covarianceBlock_diagonalMeanSq V := by
    simp only [uniformMean, Fintype.card_fin, d, blockSq, Matrix.sub_apply,
      covarianceBlock_diagonalMeanSq]
  have hRaw : ∑ r, ∑ s, f r s = (n : ℝ) ^ 2 * rowEnergy V :=
    covarianceBlock_frobenius_sum V
  have hDiag : ∑ r, f r r = (n : ℝ) * (covarianceBlock_diagonalMeanSq V + k) :=
    covarianceBlock_diagonal_raw_energy (Nat.zero_lt_of_lt hn) hV
  simp_rw [hSplit]
  rw [uniformMean_diag_pair_sum hl, hMean, sum_offDiag_eq_sum_sub_diag, hRaw, hDiag]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Bound (cos:cov-estimates) conditional on the input frame. -/
theorem sampledCovariance_meanSq_le {n k l : ℕ} (hn : 1 < n) (hl : l ≤ n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    uniformMean (fun J : Fin l ↪ Fin n => squaredFrobenius (sampledCovariance V J - 1)) ≤
      (l : ℝ)^2 * n / (n - 1) * rowEnergy V := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlR : (l : ℝ) ≤ n := by exact_mod_cast hl
  have h0 := covarianceBlock_diagonalMeanSq_le (Nat.zero_lt_of_lt hn) hV
  have hd := mul_le_mul_of_nonneg_left h0
    (show 0 ≤ (l : ℝ) * (n - l) / (n - 1) by positivity)
  have hη : 0 ≤ rowEnergy V := by
    unfold rowEnergy
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [sampledCovariance_meanSq_eq hn hl hV]
  by_cases hl0 : l = 0
  · subst l; simp
  · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hl0
    have hnr : 0 < (n : ℝ) - 1 := sub_pos.mpr hnR
    have hnk : 0 ≤ (k : ℝ) / n := by positivity
    have hNk : 0 ≤ (k : ℝ) := by positivity
    refine (add_le_add (le_refl _) hd).trans ?_
    have hA : 0 ≤ (l : ℝ) * (l - 1) / (n - 1) := by positivity
    have hB : 0 ≤ (l : ℝ) * (n - l) / (n - 1) := by positivity
    refine (add_le_add (mul_le_mul_of_nonneg_left (sub_le_self _ hNk) hA)
      (mul_le_mul_of_nonneg_left (sub_le_self _ hnk) hB)).trans ?_
    have he : (l : ℝ) * (l - 1) / (n - 1) * ((n : ℝ) * rowEnergy V) +
        (l : ℝ) * (n - l) / (n - 1) * rowEnergy V = (l : ℝ)^2 * rowEnergy V
        := by
      field_simp
      ring
    rw [he]
    calc
      _ = ((l : ℝ)^2 * rowEnergy V) * 1 := by ring
      _ ≤ ((l : ℝ)^2 * rowEnergy V) * ((n : ℝ) / (n - 1)) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ hnr).2 (by linarith)) (by positivity)
      _ = _ := by ring

end SketchOrientation.Cosine
