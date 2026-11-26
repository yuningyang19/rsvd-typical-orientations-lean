import SketchOrientation.DctBlockCoefficients
import SketchOrientation.PermutationAbsoluteMean

namespace SketchOrientation.Cosine

open Matrix Edge.Walsh MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology

/-- Mean row energy of the frame entering the last pass. -/
noncomputable def meanDctRowEnergy {n k : ℕ} (mode : DctPasses)
    (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  uniformMean (fun b : Fin n → Bool => rowEnergy (mode.intermediateFrame V b))

theorem meanDctRowEnergy_one {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) :
    meanDctRowEnergy .one V = rowEnergy V := by
  simpa only [meanDctRowEnergy, DctPasses.intermediateFrame] using
    uniformMean_const (A := Fin n → Bool) (rowEnergy V)

theorem meanDctRowEnergy_two_le {n k : ℕ} {V : Matrix (Fin n) (Fin k) ℝ}
    (hV : Vᵀ * V = 1) : meanDctRowEnergy .two V ≤ 6 * (k : ℝ) ^ 2 / n := by
  simpa only [meanDctRowEnergy, uniformMean, DctPasses.intermediateFrame,
    Fintype.expect_eq_sum_div_card] using dctII_signedSpread hV

theorem meanDctRowEnergy_nonneg {n k : ℕ} (mode : DctPasses) (V : Matrix (Fin n) (Fin k) ℝ) :
    0 ≤ meanDctRowEnergy mode V := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by positivity)

/-- The Frobenius comparison controls the variance of a scalar test
without assuming independence across sampled rows. -/
theorem dctCoefficient_variance_defect_sq_le {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (J : Fin l ↪ Fin n)
    (T : EuclideanSpace ℝ (Fin l × Fin k)) :
    ((∑ i, ⟪dctBlockCoefficient V J i, T⟫ ^ 2) - ‖T‖ ^ 2) ^ 2 ≤
      ‖T‖ ^ 4 * squaredFrobenius (sampledCovariance V J - 1) := by
  classical
  rw [dctCoefficient_variance_defect_eq, squaredFrobenius_eq_sum_entries]
  let D := (Fin l × Fin k) × (Fin l × Fin k)
  let b (p : D) : ℝ := T p.1 * T p.2
  let a (p : D) := (sampledCovariance V J - 1) p.1 p.2
  have he : (∑ p, ∑ q, (T p * T q) * (sampledCovariance V J - 1) p q) = ∑ x : D, b x * a x := by
    exact (Fintype.sum_prod_type (fun p : D => b p * a p)).symm
  have hA : (∑ x : D, a x ^ 2) = ∑ p, ∑ q, (sampledCovariance V J - 1) p q ^ 2 := by
    exact Fintype.sum_prod_type (fun p : D => a p ^ 2)
  have hB : (∑ x : D, b x ^ 2) = ‖T‖ ^ 4 := by
    rw [show ‖T‖ ^ 4 = (‖T‖ ^ 2) ^ 2 by ring, EuclideanSpace.real_norm_sq_eq, pow_two,
      Finset.sum_mul_sum]
    rw [Fintype.sum_prod_type (fun p : D => b p ^ 2)]
    simp only [b, mul_pow]
  rw [he, ← hA, ← hB]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b a

private theorem dctCoefficient_norm_sq_le {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (J : Fin l ↪ Fin n) (i : Fin n) :
    ‖dctBlockCoefficient V J i‖ ^ 2 ≤ (2 * (l : ℝ)) * leverage V i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp only [dctBlockCoefficient, PiLp.toLp_apply, mul_pow, Real.sq_sqrt hn.le]
  have hEntry (r : Fin l) (a : Fin k) :
      (n : ℝ) * dctII n (J r) i ^ 2 * V i a ^ 2 ≤ 2 * V i a ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc
      _ ≤ (n : ℝ) * (2 / (n : ℝ)) := mul_le_mul_of_nonneg_left (dctII_apply_sq_le _ _) hn.le
      _ = _ := by field_simp
  calc
    _ ≤ ∑ r : Fin l, ∑ a : Fin k, 2 * V i a ^ 2 :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun a _ => hEntry r a
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        leverage]
      ring

/-- Fourth-order characteristic-function error for the DCT coefficient
array, controlled by the exact fourth-power row energy. -/
theorem dctCoefficient_fourth_sum_le {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (J : Fin l ↪ Fin n)
    (T : EuclideanSpace ℝ (Fin l × Fin k)) :
    (∑ i, ⟪dctBlockCoefficient V J i, T⟫ ^ 4) ≤
      (2 * (l : ℝ)) ^ 2 * ‖T‖ ^ 4 * rowEnergy V := by
  classical
  have hPoint (i : Fin n) :
      ⟪dctBlockCoefficient V J i, T⟫ ^ 4 ≤ (2 * (l : ℝ)) ^ 2 * ‖T‖ ^ 4 * (leverage V i) ^ 2 := by
    have h := abs_real_inner_le_norm (dctBlockCoefficient V J i) T
    have hp := pow_le_pow_left₀ (abs_nonneg _) h 4
    have hNorm := dctCoefficient_norm_sq_le V J i
    calc
      _ = |⟪dctBlockCoefficient V J i, T⟫| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ _ := hp
      _ = (‖dctBlockCoefficient V J i‖ ^ 2) ^ 2 * ‖T‖ ^ 4 := by ring
      _ ≤ ((2 * (l : ℝ)) * leverage V i) ^ 2 * ‖T‖ ^ 4 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hNorm _) (by positivity)
      _ = _ := by ring
  simpa only [rowEnergy, Finset.mul_sum] using (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hPoint i)

private theorem uniformMean_const_mul {A : Type*} [Fintype A] (g : A → ℝ) (c : ℝ) :
    uniformMean (fun a => c * g a) = c * uniformMean g := by
  simp only [uniformMean, ← Finset.mul_sum, mul_div_assoc]

abbrev DctBlockEnvironment (n l : ℕ) := (Fin n → Bool) × (Fin l ↪ Fin n)

private def dctSignEquiv (n l : ℕ) : DctDraw n l ≃ DctBlockEnvironment n l × (Fin n → Bool) where
  toFun d := ((d.2.2, d.1), d.2.1)
  invFun d := (d.1.2, d.2, d.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite probability law of the actual DCT block in sampled-row and
target-column order. -/
noncomputable def dctProjectedBlockLaw {n k l : ℕ} (hl : l ≤ n)
    (mode : DctPasses) (V : Matrix (Fin n) (Fin k) ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin l × Fin k)) := by
  letI : Nonempty (Fin l ↪ Fin n) := ⟨Fin.castLEEmb hl⟩
  exact finiteProbabilityLaw (fun d : DctDraw n l =>
    WithLp.toLp 2 (fun p : Fin l × Fin k => scaledTargetBlock V (mode.sketch d) p.2 p.1))

set_option maxHeartbeats 500000 in
private theorem dctEnv_variance_abs_le {n k l : ℕ} (hn : 1 < n) (hl : l ≤ n)
    (mode : DctPasses) (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (T : EuclideanSpace ℝ (Fin l × Fin k)) :
    uniformMean (fun q : DctBlockEnvironment n l =>
      |(∑ r, ⟪dctBlockCoefficient (mode.intermediateFrame V q.1) q.2 r, T⟫ ^ 2) - ‖T‖ ^ 2|) ≤
      Real.sqrt (‖T‖ ^ 4 * (l : ℝ)^2 * 2 * meanDctRowEnergy mode V) := by
  letI : Nonempty (Fin l ↪ Fin n) := ⟨Fin.castLEEmb hl⟩
  let f (q : DctBlockEnvironment n l) :=
    (∑ r, ⟪dctBlockCoefficient (mode.intermediateFrame V q.1) q.2 r, T⟫ ^ 2) - ‖T‖ ^ 2
  change (uniformMean fun q => |f q|) ≤ _
  refine (uniformMean_abs_le_sqrt_mean_sq f).trans (Real.sqrt_le_sqrt ?_)
  have hP (q : DctBlockEnvironment n l) :=
    dctCoefficient_variance_defect_sq_le (mode.intermediateFrame V q.1) q.2 T
  refine (uniformMean_mono hP).trans ?_
  rw [uniformMean_const_mul]
  rw [uniformMean_prod' (fun q : DctBlockEnvironment n l =>
    squaredFrobenius (sampledCovariance (mode.intermediateFrame V q.1) q.2 - 1))]
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hRatio : (n : ℝ) / (n - 1) ≤ 2 :=
    (div_le_iff₀ (by linarith)).2 (by linarith)
  have hCond (b : Fin n → Bool) :
      uniformMean (fun J : Fin l ↪ Fin n =>
        squaredFrobenius (sampledCovariance (mode.intermediateFrame V b) J - 1)) ≤
        ((l : ℝ)^2 * 2) * rowEnergy (mode.intermediateFrame V b) := by
    refine (sampledCovariance_meanSq_le hn hl (intermediateFrame_orthonormal mode hV b)).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRatio (sq_nonneg _))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    _ ≤ ‖T‖ ^ 4 * uniformMean (fun b => ((l : ℝ)^2 * 2) *
      rowEnergy (mode.intermediateFrame V b)) :=
      mul_le_mul_of_nonneg_left (uniformMean_mono hCond) (by positivity)
    _ = _ := by rw [uniformMean_const_mul]; unfold meanDctRowEnergy; ring

private theorem dctEnv_fourth_mean_le {n k l : ℕ} (hl : l ≤ n)
    (mode : DctPasses) (V : Matrix (Fin n) (Fin k) ℝ)
    (T : EuclideanSpace ℝ (Fin l × Fin k)) :
    uniformMean (fun q : DctBlockEnvironment n l =>
      ∑ r, ⟪dctBlockCoefficient (mode.intermediateFrame V q.1) q.2 r, T⟫ ^ 4) ≤
      (2 * (l : ℝ)) ^ 2 * ‖T‖ ^ 4 * meanDctRowEnergy mode V := by
  letI : Nonempty (Fin l ↪ Fin n) := ⟨Fin.castLEEmb hl⟩
  have hP (q : DctBlockEnvironment n l) :=
    dctCoefficient_fourth_sum_le (mode.intermediateFrame V q.1) q.2 T
  refine (uniformMean_mono hP).trans_eq ?_
  rw [uniformMean_const_mul]
  rw [uniformMean_prod' (fun q : DctBlockEnvironment n l =>
    rowEnergy (mode.intermediateFrame V q.1))]
  simp only [uniformMean_const, meanDctRowEnergy]

set_option maxHeartbeats 700000 in
/-- Joint Gaussian limit of the actual DCT block when the entering row
energy vanishes in mean. This covers both passes and fixed target width. -/
theorem tendsto_dctProjectedBlockLaw {n : ℕ → ℕ} {k l : ℕ}
    (hn : ∀ i, 1 < n i) (hl : ∀ i, l ≤ n i)
    (mode : DctPasses) (V : (i : ℕ) → Matrix (Fin (n i)) (Fin k) ℝ)
    (hV : ∀ i, (V i)ᵀ * V i = 1)
    (hη : Tendsto (fun i => meanDctRowEnergy mode (V i)) atTop (𝓝 0)) :
    Tendsto (fun i => dctProjectedBlockLaw (hl i) mode (V i)) atTop
      (𝓝 (⟨stdGaussian (EuclideanSpace ℝ (Fin l × Fin k)), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin l × Fin k)))) := by
  haveI (i : ℕ) : Nonempty (Fin l ↪ Fin (n i)) := ⟨Fin.castLEEmb (hl i)⟩
  let a (i : ℕ) (q : DctBlockEnvironment (n i) l) (r : Fin (n i)) :=
    dctBlockCoefficient (mode.intermediateFrame (V i) q.1) q.2 r
  refine (tendsto_signedCoefficientLaw (I := fun i => Fin (n i)) a ?_ ?_).congr (fun i => ?_)
  · intro T
    let C := ‖T‖ ^ 4 * (l : ℝ)^2 * 2
    refine squeeze_zero (g := fun i => Real.sqrt (C * meanDctRowEnergy mode (V i))) ?_ ?_ ?_
    · intro i
      exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    · exact fun i => dctEnv_variance_abs_le (hn i) (hl i) mode (V i) (hV i) T
    · have h := hη.const_mul C
      rw [mul_zero] at h
      have hS : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt
      exact Real.sqrt_zero ▸ hS.comp h
  · intro T
    let C := (2 * (l : ℝ)) ^ 2 * ‖T‖ ^ 4
    refine squeeze_zero (g := fun i => C * meanDctRowEnergy mode (V i)) ?_ ?_ ?_
    · intro i
      exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
        (by positivity)
    · exact fun i => dctEnv_fourth_mean_le (hl i) mode (V i) T
    · simpa only [mul_zero] using hη.const_mul C
  · let f (q : DctBlockEnvironment (n i) l × (Fin (n i) → Bool)) :=
      signedCoefficientSum (a i q.1) q.2
    change finiteProbabilityLaw f = finiteProbabilityLaw _
    rw [← finiteProbabilityLaw_reindex (dctSignEquiv (n i) l) f]
    congr 1
    funext d
    exact (dctSketch_projected_eq_signedSum mode (V i) d).symm

/-- The actual two-pass law has the same fixed-block Gaussian limit for
every deterministic sequence of target frames. -/
theorem tendsto_dctProjectedBlockLaw_two {n : ℕ → ℕ} {k l : ℕ}
    (hn : ∀ i, 1 < n i) (hnInf : Tendsto n atTop atTop) (hl : ∀ i, l ≤ n i)
    (V : (i : ℕ) → Matrix (Fin (n i)) (Fin k) ℝ) (hV : ∀ i, (V i)ᵀ * V i = 1) :
    Tendsto (fun i => dctProjectedBlockLaw (hl i) .two (V i)) atTop
      (𝓝 (⟨stdGaussian (EuclideanSpace ℝ (Fin l × Fin k)), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin l × Fin k)))) := by
  apply tendsto_dctProjectedBlockLaw hn hl .two V hV
  apply squeeze_zero (fun i => meanDctRowEnergy_nonneg .two (V i))
    (fun i => meanDctRowEnergy_two_le (hV i))
  have hn' : Tendsto (fun i => (n i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hnInf
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_zero.comp hn').const_mul (6 * (k : ℝ) ^ 2)

end SketchOrientation.Cosine
