import SketchOrientation.PermutationVariance
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt

namespace SketchOrientation

open Edge.Walsh

private theorem uniformMean_abs_sq_le {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (uniformMean fun a => |f a|) ^ 2 ≤ uniformMean (fun a => f a ^ 2) := by
  have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset A))
    (f := fun a => |f a|)
  simp only [Finset.card_univ, sq_abs] at h
  simp only [uniformMean, div_pow]
  apply (div_le_div_iff₀ (pow_pos hcard _) hcard).mpr
  calc
    _ ≤ ((Fintype.card A : ℝ) * ∑ a, f a ^ 2) * Fintype.card A :=
      mul_le_mul_of_nonneg_right h hcard.le
    _ = _ := by ring

theorem uniformMean_abs_le_sqrt_mean_sq {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (uniformMean fun a => |f a|) ≤ Real.sqrt (uniformMean fun a => f a ^ 2) :=
  Real.le_sqrt_of_sq_le (uniformMean_abs_sq_le f)

private theorem uniformMean_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ uniformMean f := by
  unfold uniformMean
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

/-- L¹ bound used after the exact weighted permutation variance, uniform in
the locations of the bounded population entries. -/
theorem uniformMean_permutation_abs_le {n : ℕ} (hn : 1 < n) (w z : Fin n → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, |z i| ≤ M) :
    uniformMean (fun J : Fin n ↪ Fin n =>
      |(∑ i, w i * z (J i)) - (∑ i, w i) * uniformMean z|) ≤
      Real.sqrt (8 * M ^ 2 * ∑ i, w i ^ 2) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin n ↪ Fin n) := ⟨Function.Embedding.refl _⟩
  have hmean : |uniformMean z| ≤ M := by
    calc
      _ ≤ _ := abs_uniformMean_le z
      _ ≤ uniformMean (fun _ : Fin n => M) := uniformMean_mono hz
      _ = _ := uniformMean_const M
  have hz₂ (r : Fin n) : (z r - uniformMean z) ^ 2 ≤ (2 * M) ^ 2 := by
    have hb : |z r - uniformMean z| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hz r])
    rw [← sq_abs (z r - uniformMean z)]
    exact pow_le_pow_left₀ (abs_nonneg _) hb _
  have hV : (uniformMean fun r => (z r - uniformMean z) ^ 2) ≤ (2 * M) ^ 2 :=
    (uniformMean_mono hz₂).trans_eq (uniformMean_const _)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (n : ℝ) / (n - 1) ≤ 2 :=
    (div_le_iff₀ (by linarith)).2 (by linarith)
  have hNW : 0 ≤ (n : ℝ) / (n - 1) := div_nonneg (by positivity) (by linarith)
  have hw₂ : (∑ i, (w i - uniformMean w) ^ 2) ≤ ∑ i, w i ^ 2 := by
    have hsum : (∑ i, w i) = (n : ℝ) * uniformMean w := by
      rw [uniformMean, Fintype.card_fin, mul_comm, div_mul_cancel₀]
      positivity
    simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, hsum]
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (sq_nonneg (uniformMean w))]
  refine (uniformMean_abs_le_sqrt_mean_sq _).trans ?_
  apply Real.sqrt_le_sqrt
  rw [uniformMean_permutation_variance hn w z]
  calc
    _ ≤ 2 * (2 * M) ^ 2 * ∑ i, w i ^ 2 := by
      gcongr
      exact uniformMean_nonneg fun _ => sq_nonneg _
    _ = _ := by ring

/-- A coordinate expansion under one common permutation. Bounding each
centered weighted sum and using the triangle inequality controls their
sum without any independence assumption between its coordinates. -/
theorem uniformMean_abs_permutation_sum_le {n : ℕ} (hn : 1 < n) {D : Type*} [Fintype D]
    (w z : D → Fin n → ℝ) {M U : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hz : ∀ d i, |z d i| ≤ M) (hw : ∀ d, ∑ i, w d i ^ 2 ≤ U) :
    uniformMean (fun J : Fin n ↪ Fin n =>
      |(∑ d, ∑ i, w d i * z d (J i)) - ∑ d, (∑ i, w d i) * uniformMean (z d)|) ≤
      (Fintype.card D : ℝ) * Real.sqrt (8 * M ^ 2 * U) := by
  classical
  simp_rw [← Finset.sum_sub_distrib]
  refine (uniformMean_mono (fun J => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [uniformMean_sum]
  calc
    _ ≤ ∑ d : D, Real.sqrt (8 * M ^ 2 * U) := by
      apply Finset.sum_le_sum
      intro d _
      exact (uniformMean_permutation_abs_le hn (w d) (z d) hM (hz d)).trans
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hw d) (by positivity)))
    _ = _ := by simp

end SketchOrientation
