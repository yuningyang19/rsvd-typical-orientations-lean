import SketchOrientation.DctSampling

namespace SketchOrientation

open Edge.Walsh

private theorem uniformMean_const_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum, mul_div_assoc]

/-- The exact off-diagonal covariance of a centered finite population.
The diagonal covariance is the mean square of the same population. -/
theorem uniformMean_centeredSample_covariance {n : ℕ} (hn : 1 < n) (z : Fin n → ℝ)
    (hz : ∑ r, z r = 0) (i j : Fin n) :
    uniformMean (fun J : Fin n ↪ Fin n => z (J i) * z (J j)) =
      if i = j then (∑ r, z r ^ 2) / n
      else -(∑ r, z r ^ 2) / ((n : ℝ) * (n - 1)) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simpa only [uniformMean, Fintype.card_fin, pow_two] using
      uniformMean_orderedSample_apply le_rfl i (fun x => z x * z x)
  · rw [if_neg hij, uniformMean_orderedSample_pair le_rfl i j hij (fun r s => z r * z s),
      sum_offDiag_eq_sum_sub_diag (fun r s => z r * z s),
      ← Finset.sum_mul_sum, hz, zero_mul, zero_sub]
    simp only [pow_two]

/-- Exact variance of a weighted sum under a uniform permutation. The
weights may have arbitrary mean; the population has been centered. -/
theorem uniformMean_permutation_centered_sq {n : ℕ} (hn : 1 < n) (w z : Fin n → ℝ)
    (hz : ∑ r, z r = 0) :
    uniformMean (fun J : Fin n ↪ Fin n => (∑ i, w i * z (J i)) ^ 2) =
      ((∑ r, z r ^ 2) / n) * ((n : ℝ) / (n - 1)) *
        ((∑ i, w i ^ 2) - (∑ i, w i) ^ 2 / n) := by
  classical
  have hExpand (J : Fin n ↪ Fin n) :
      (∑ i, w i * z (J i)) ^ 2 = ∑ i, ∑ j, (w i * w j) * (z (J i) * z (J j)) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hExpand, uniformMean_sum, uniformMean_const_mul,
    uniformMean_centeredSample_covariance hn z hz]
  let s := ∑ r, z r ^ 2
  have hSummand (i j : Fin n) :
      w i * w j * (if i = j then s / n else -s / ((n : ℝ) * (n - 1))) =
        (w i * w j) * (-s / ((n : ℝ) * (n - 1))) +
          (if i = j then w i ^ 2 * (s / n + s / ((n : ℝ) * (n - 1))) else 0) := by
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
  change (∑ i, ∑ j, w i * w j *
    (if i = j then s / n else -s / ((n : ℝ) * (n - 1)))) = _
  have hDiag (i : Fin n) : (∑ j : Fin n, if i = j then
      w i ^ 2 * (s / n + s / ((n : ℝ) * (n - 1))) else 0) =
        w i ^ 2 * (s / n + s / ((n : ℝ) * (n - 1))) := by simp
  simp_rw [hSummand, Finset.sum_add_distrib, hDiag, ← Finset.sum_mul]
  rw [← Finset.sum_mul_sum]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀ : (n : ℝ) ≠ 0 := by linarith
  have hn₁ : (n : ℝ) - 1 ≠ 0 := by linarith
  change (∑ i, w i) * (∑ i, w i) * (-s / ((n : ℝ) * (n - 1))) +
    (∑ i, w i ^ 2) * (s / n + s / ((n : ℝ) * (n - 1))) = _
  field_simp
  ring

/-- The weighted permutation variance (edge:perm-var), with the centered
weights and the centered population both exhibited in the conclusion. -/
theorem uniformMean_permutation_variance {n : ℕ} (hn : 1 < n) (w z : Fin n → ℝ) :
    uniformMean (fun J : Fin n ↪ Fin n =>
      ((∑ i, w i * z (J i)) - (∑ i, w i) * uniformMean z) ^ 2) =
      ((n : ℝ) / (n - 1)) * (uniformMean fun r => (z r - uniformMean z) ^ 2) *
        (∑ i, (w i - uniformMean w) ^ 2) := by
  let y := fun r => z r - uniformMean z
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hCenter : (∑ r, y r) = 0 := by
    simp only [y, Finset.sum_sub_distrib, uniformMean, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hRecenter (J : Fin n ↪ Fin n) :
      ((∑ i, w i * z (J i)) - (∑ i, w i) * uniformMean z) ^ 2 =
        (∑ i, w i * y (J i)) ^ 2 := by
    simp only [y, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  simp_rw [hRecenter]
  rw [uniformMean_permutation_centered_sq hn w y hCenter]
  have hCenterW : (∑ i, (w i - uniformMean w) ^ 2) =
      (∑ i, w i ^ 2) - (∑ i, w i) ^ 2 / n := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      uniformMean, Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    rw [← Finset.mul_sum]
    ring
  rw [hCenterW, uniformMean]
  simp only [Fintype.card_fin, y]
  ring

end SketchOrientation
