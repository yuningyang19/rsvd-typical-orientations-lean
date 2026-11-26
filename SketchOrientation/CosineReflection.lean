import SketchOrientation.CosineCovariance

/-!
# Reflected DCT diagonal frequencies

The direct and reflected indices in the diagonal covariance calculation at
`cosine.tex:109–121` and `spectrum.tex:55–60` of commit `68dd06e`.
-/

open Matrix
open scoped BigOperators

namespace SketchOrientation.Cosine

private noncomputable def fullFrequency (n : ℕ) (t : ℤ) (r : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * (t : ℝ) / (n : ℝ) * (r : ℝ))

private theorem fullFrequency_sum {n : ℕ} (hn : 0 < n) (t : ℤ) :
    ∑ r : Fin n, fullFrequency n t r.val = if (n : ℤ) ∣ t then (n : ℝ) else 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h : (n : ℤ) ∣ t
  · rw [if_pos h]
    obtain ⟨z, rfl⟩ := h
    have ht (r : Fin n) : fullFrequency n ((n : ℤ) * z) r.val = 1 := by
      unfold fullFrequency
      rw [← Real.cos_int_mul_two_pi (z * (r.val : ℤ))]
      congr 1
      push_cast
      field_simp
    simp [ht]
  · rw [if_neg h]
    let a := 2 * Real.pi * (t : ℝ) / (n : ℝ)
    have hsin : Real.sin (a / 2) ≠ 0 := by
      intro hz
      obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hz
      apply h
      refine ⟨z, ?_⟩
      have h' : (t : ℝ) = (n : ℝ) * (z : ℝ) := by
        dsimp [a] at hz
        field_simp at hz
        simpa [mul_comm] using hz.symm
      exact_mod_cast h'
    have hr : Real.sin ((n : ℝ) * a / 2) = 0 := by
      rw [show (n : ℝ) * a / 2 = (t : ℝ) * Real.pi by dsimp [a]; field_simp,
        Real.sin_int_mul_pi]
    have hsum := Real.sin_mul_sum_cos n a 0
    rw [hr, zero_mul] at hsum
    have hsum' := (mul_eq_zero.mp hsum).resolve_left hsin
    rw [Fin.sum_univ_eq_sum_range]
    simpa [fullFrequency, a] using hsum'

/-- The cosine coefficients of the centered diagonal blocks, prior to
removing the constant row's term. -/
noncomputable def doubledCosine {n : ℕ} (r i : Fin n) : ℝ :=
  Real.cos (2 * (Real.pi * ((2 * i.val + 1) * r.val : ℕ) / (2 * (n : ℝ))))

/-- The finite doubled-cosine Gram identity resolves the direct and reflected
indices. It counts both terms when a middle index reflects to itself. -/
theorem doubledCosine_product_sum {n : ℕ} (i j : Fin n) :
    ∑ r, doubledCosine r i * doubledCosine r j =
      ((n : ℝ) / 2) * ((if i = j then 1 else 0) +
        (if i.val + j.val + 1 = n then 1 else 0)) := by
  let d : ℤ := (i.val : ℤ) - j.val
  let a : ℤ := (i.val : ℤ) + j.val + 1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt i.pos)
  have hpair (r : Fin n) :
      2 * doubledCosine r i * doubledCosine r j =
        fullFrequency n d r.val + fullFrequency n a r.val := by
    unfold doubledCosine fullFrequency
    rw [Real.two_mul_cos_mul_cos]
    dsimp [d, a]
    push_cast
    congr 1 <;> congr 1 <;> field_simp <;> ring
  have hd : (n : ℤ) ∣ d ↔ i = j := by
    constructor
    · intro h
      by_cases hd : d < 0
      · have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ -d by omega)
          (show -d < (n : ℤ) by dsimp [d]; omega) (dvd_neg.mpr h)
        apply Fin.ext
        dsimp [d] at hzero
        omega
      · have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ d by omega)
          (show d < (n : ℤ) by dsimp [d]; omega) h
        apply Fin.ext
        dsimp [d] at hzero
        omega
    · intro h
      subst j
      simp [d]
  have ha : (n : ℤ) ∣ a ↔ i.val + j.val + 1 = n := by
    constructor
    · intro h
      have hlow : (n : ℤ) ≤ a := by
        by_contra! hlt
        have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ a by dsimp [a]; omega) hlt h
        dsimp [a] at hzero
        omega
      have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ a - (n : ℤ) by omega)
        (show a - (n : ℤ) < (n : ℤ) by dsimp [a]; omega) (dvd_sub h (dvd_refl _))
      dsimp [a] at hzero
      omega
    · intro h
      have h' : a = (n : ℤ) := by dsimp [a]; omega
      rw [h']
  have hs :
      2 * ∑ r, doubledCosine r i * doubledCosine r j =
        (∑ r : Fin n, fullFrequency n d r.val) +
          (∑ r : Fin n, fullFrequency n a r.val) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← mul_assoc, hpair]
  simp only [fullFrequency_sum i.pos, hd, ha] at hs
  split_ifs at hs ⊢ <;> linarith

/-- The exact pointwise formula for the squared DCT-II entries. The DC row
has all entries squared equal to one over the ambient dimension. -/
theorem dctII_squares_centered {n : ℕ} (r i : Fin n) :
    (n : ℝ) * (dctII n r i)^2 = if r.val = 0 then 1 else 1 + doubledCosine r i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast r.pos
  simp only [dctII, Matrix.transpose_apply, SketchOrientation.cosineCore, doubledCosine]
  split_ifs with hr
  · simp only [hr, mul_zero, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one, div_pow,
      one_pow, Real.sq_sqrt hn.le]
    field_simp
  · rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hn.le, Real.cos_two_mul]
    field_simp
    ring

theorem doubledCosine_weighted_sumSq {n : ℕ} (v : Fin n → ℝ) :
    (∑ r, (∑ i, doubledCosine r i * v i)^2) =
      (n : ℝ) / 2 * ((∑ i, (v i)^2) + ∑ i, v i * v i.rev) := by
  have hrev (i j : Fin n) : i.val + j.val + 1 = n ↔ j = i.rev := by
    constructor
    · intro h
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    · rintro rfl
      simp only [Fin.val_rev]
      omega
  let f (r i j : Fin n) := (doubledCosine r i * doubledCosine r j) * (v i * v j)
  calc
    _ = ∑ r, ∑ i, ∑ j, f r i j := by
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f]
      ring
    _ = ∑ i, ∑ r, ∑ j, f r i j := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ r, f r i j := by exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ j, (n : ℝ) / 2 *
        (((if i = j then 1 else 0) + (if j = i.rev then 1 else 0)) * (v i * v j)) := by
      simp_rw [f, ← Finset.sum_mul, doubledCosine_product_sum, hrev, mul_assoc]
    _ = _ := by
      simp_rw [← Finset.mul_sum, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, pow_two]

private theorem centeredCovariance_diagonal_entry {n k : ℕ}
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1)
    (r : Fin n) (a b : Fin k) :
    covarianceBlock V r r a b - (1 : Matrix (Fin k) (Fin k) ℝ) a b =
      if r.val = 0 then 0 else ∑ i, doubledCosine r i * (V i a * V i b) := by
  have hunit : ∑ i, V i a * V i b = (1 : Matrix (Fin k) (Fin k) ℝ) a b := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
      congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦ M a b) hV
  unfold covarianceBlock
  rw [← hunit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [← pow_two, ← mul_assoc (n : ℝ), dctII_squares_centered]
  split_ifs with hr
  · simp
  · simp_rw [add_mul, one_mul, add_sub_cancel_left]

/-- The exact diagonal covariance calculation entry by entry. The last term
subtracts the artificial frequency-zero contribution. -/
theorem covarianceBlock_diagonalEntry_sumSq {n k : ℕ} (hn : 0 < n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) (a b : Fin k) :
    (∑ r, (covarianceBlock V r r a b - (1 : Matrix (Fin k) (Fin k) ℝ) a b)^2) =
      (n : ℝ) / 2 *
        ((∑ i, (V i a * V i b)^2) + ∑ i, (V i a * V i b) * (V i.rev a * V i.rev b)) -
        ((1 : Matrix (Fin k) (Fin k) ℝ) a b)^2 := by
  let v (i : Fin n) := V i a * V i b
  let z : Fin n := ⟨0, hn⟩
  let q (r : Fin n) := (∑ i, doubledCosine r i * v i)^2
  have hz (r : Fin n) : r.val = 0 ↔ r = z := by
    change r.val = z.val ↔ r = z
    exact Fin.ext_iff.symm
  have hq (r : Fin n) : (covarianceBlock V r r a b - (1 : Matrix (Fin k) (Fin k) ℝ) a b)^2 =
      q r - (if r = z then q r else 0) := by
    simp only [centeredCovariance_diagonal_entry hV, hz]
    split_ifs <;> simp [q, v]
  have h0 : q z = ((1 : Matrix (Fin k) (Fin k) ℝ) a b)^2 := by
    have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ ↦ M a b) hV
    have hv : ∑ i, v i = (1 : Matrix (Fin k) (Fin k) ℝ) a b := by
      simpa only [v, Matrix.mul_apply, Matrix.transpose_apply] using h
    simp [q, doubledCosine, z, hv]
  simp_rw [hq, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ z), h0, doubledCosine_weighted_sumSq v]

/-- The reflected rank-one cross term in the DCT diagonal identity. -/
noncomputable def reflectedFrobenius {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∑ i, ∑ a, ∑ b, (V i a * V i b) * (V i.rev a * V i.rev b)

/-- Average squared Frobenius error of the unsampled diagonal covariance blocks. -/
noncomputable def covarianceBlock_diagonalMeanSq {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  (∑ r, ∑ a, ∑ b, (covarianceBlock V r r a b - (1 : Matrix (Fin k) (Fin k) ℝ) a b)^2) /
    (n : ℝ)

private theorem sumSq_rankOne {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) :
    ∑ i, ∑ a, ∑ b, (V i a * V i b)^2 = rowEnergy V := by
  unfold rowEnergy leverage
  simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two]

/-- The complete diagonal-reflection identity `cos:cov-diagonal` with the exact
DC-row correction, `cosine.tex:109–118`. -/
theorem covarianceBlock_diagonalMeanSq_eq {n k : ℕ} (hn : 0 < n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    covarianceBlock_diagonalMeanSq V =
      (rowEnergy V + reflectedFrobenius V) / 2 - (k : ℝ) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have swap (f : Fin n → Fin k → Fin k → ℝ) :
      (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
  have hI : ∑ a : Fin k, ∑ b : Fin k, ((1 : Matrix (Fin k) (Fin k) ℝ) a b)^2 = k := by
    simp [Matrix.one_apply]
  unfold covarianceBlock_diagonalMeanSq
  rw [swap]
  simp_rw [covarianceBlock_diagonalEntry_sumSq hn hV, Finset.sum_sub_distrib, hI,
    ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [← swap (fun i a b ↦ (V i a * V i b)^2),
    ← swap (fun i a b ↦ (V i a * V i b) * (V i.rev a * V i.rev b)), sumSq_rankOne]
  unfold reflectedFrobenius
  field_simp

/-- Reflection is a permutation of the rows, including the middle row at odd
size. Its rank-one cross term is bounded by the direct squared row energies. -/
theorem covarianceBlock_diagonalMeanSq_le {n k : ℕ} (hn : 0 < n)
    {V : Matrix (Fin n) (Fin k) ℝ} (hV : Vᵀ * V = 1) :
    covarianceBlock_diagonalMeanSq V ≤ rowEnergy V - (k : ℝ) / n := by
  have hrefl : reflectedFrobenius V ≤ rowEnergy V := by
    unfold reflectedFrobenius
    calc
      _ ≤ ∑ i, ∑ a, ∑ b,
          ((V i a * V i b)^2 + (V i.rev a * V i.rev b)^2) / 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        nlinarith [sq_nonneg (V i a * V i b - V i.rev a * V i.rev b)]
      _ = _ := by
        have h := Equiv.sum_comp (@Fin.revPerm n) (fun i ↦ ∑ a, ∑ b, (V i a * V i b)^2)
        simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
        change ((∑ i, ∑ a, ∑ b, (V i a * V i b)^2) +
          (∑ i, ∑ a, ∑ b, (V (Fin.revPerm i) a * V (Fin.revPerm i) b)^2)) / 2 = _
        rw [h, sumSq_rankOne]
        ring
  rw [covarianceBlock_diagonalMeanSq_eq hn hV]
  linarith

end SketchOrientation.Cosine
