import SketchOrientation.CosineWindow
import SketchOrientation.GaussianGramTracePowers
import SketchOrientation.SpectralCapGaussian

namespace SketchOrientation.Cosine

open Matrix MeasureTheory Filter Topology

/-- Z_L for the paper's actual rectangular block. -/
noncomputable def ridgeInverseTrace {k l : ℕ} (L : ℝ) (B : Matrix (Fin k) (Fin l) ℝ) : ℝ :=
  L * ((1 + (L * k) • (B * Bᵀ))⁻¹).trace

theorem ridgeInverseTrace_eq_sum {k l : ℕ} {L : ℝ} (hL : 0 ≤ L) (B : Matrix (Fin k) (Fin l) ℝ) :
    ridgeInverseTrace L B = ∑ j, L / (1 + (L * (k : ℝ)) * gramEigenvalues B j) := by
  have hB : (B * Bᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose B
  unfold ridgeInverseTrace
  rw [trace_inverse_one_add_smul_of_posSemidef hB _ (mul_nonneg hL (by positivity)), Finset.mul_sum]
  rfl

theorem ridgeInverseTrace_bounds {k l : ℕ} {L : ℝ} (hL : 0 ≤ L) (B : Matrix (Fin k) (Fin l) ℝ) :
    0 ≤ ridgeInverseTrace L B ∧ ridgeInverseTrace L B ≤ (k : ℝ) * L := by
  rw [ridgeInverseTrace_eq_sum hL]
  have hden (j : Fin k) : 1 ≤ 1 + (L * (k : ℝ)) * gramEigenvalues B j :=
    le_add_of_nonneg_right (mul_nonneg (by positivity) (gramEigenvalues_nonneg B j))
  constructor
  · exact Finset.sum_nonneg fun j _ => div_nonneg hL (zero_le_one.trans (hden j))
  · calc
      _ ≤ ∑ _ : Fin k, L := Finset.sum_le_sum fun j _ => div_le_self hL (hden j)
      _ = _ := by simp

theorem ridgeInverseTrace_measurable {k l : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    Measurable (fun B : Matrix (Fin k) (Fin l) ℝ => ridgeInverseTrace L B) := by
  simp_rw [ridgeInverseTrace_eq_sum hL]
  exact Finset.measurable_sum _ fun j _ => measurable_const.div
    (measurable_const.add (measurable_const.mul
      (((continuous_apply j).comp continuous_gramEigenvalues).measurable)))

private theorem ridge_error_pointwise {k l : ℕ} {L : ℝ}
    (hk : 0 < k) (hL : 0 < L) (B : Matrix (Fin k) (Fin l) ℝ)
    (hB : ∀ j, 0 < gramEigenvalues B j) :
    0 ≤ ((B * Bᵀ)⁻¹).trace / k - ridgeInverseTrace L B ∧
      ((B * Bᵀ)⁻¹).trace / k - ridgeInverseTrace L B ≤
        L ^ (-(1 / 4 : ℝ)) * (((B * Bᵀ)⁻¹).trace / k) ^ (5 / 4 : ℝ) := by
  let x (j : Fin k) := ((k : ℝ) * gramEigenvalues B j)⁻¹
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx (j : Fin k) : 0 < x j := inv_pos.mpr (mul_pos hk' (hB j))
  have hSum : ∑ j, x j = ((B * Bᵀ)⁻¹).trace / k := by
    rw [trace_inverse_rowGram_eq_sum B hB]
    simp_rw [x, mul_inv, ← Finset.mul_sum, div_eq_mul_inv]
    ring
  have hRidge : ∑ j, L * x j / (L + x j) = ridgeInverseTrace L B := by
    rw [ridgeInverseTrace_eq_sum hL.le]
    apply Finset.sum_congr rfl
    intro j _
    have hDen : 0 < 1 + (L * (k : ℝ)) * gramEigenvalues B j := by
      have := hB j
      positivity
    have hDen' : 0 < L + x j := add_pos hL (hx j)
    have hXT : x j * ((k : ℝ) * gramEigenvalues B j) = 1 :=
      inv_mul_cancel₀ (mul_pos hk' (hB j)).ne'
    apply (div_eq_div_iff hDen'.ne' hDen.ne').2
    linear_combination (L * L) * hXT
  have h := ridgeRemoval_bound hL (θ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    (fun j => (hx j).le)
  rw [hSum, hRidge] at h
  convert h using 2 <;> norm_num

/-- The uniform-in-rank Gaussian ridge-bias estimate used in Theorem 1.3,
with the paper's choice θ = 1/4 and its chi-square moment. -/
theorem gaussianRidge_bias {k p : ℕ} (hk : 0 < k) (hp : 2 ≤ p) {L : ℝ} (hL : 0 < L) :
    0 ≤ 1 / ((p : ℝ) - 1) -
        (∫ Z, ridgeInverseTrace L Zᵀ ∂gaussianMatrixLaw (k + p) k) ∧
      1 / ((p : ℝ) - 1) - (∫ Z, ridgeInverseTrace L Zᵀ ∂gaussianMatrixLaw (k + p) k) ≤
        L ^ (-(1 / 4 : ℝ)) * chiSquareNegativeMoment (p + 1) (5 / 4 : ℝ) := by
  let μ := gaussianMatrixLaw (k + p) k
  let f := fun Z : Matrix (Fin (k + p)) (Fin k) ℝ => (gaussianGram Z)⁻¹.trace / (k : ℝ)
  let g := fun Z : Matrix (Fin (k + p)) (Fin k) ℝ => ridgeInverseTrace L Zᵀ
  have hiF₀ := gaussianGram_inv_trace_mean (k := k) (d := k + p) (by omega)
  have hiF : Integrable f μ := hiF₀.1.div_const _
  have hm : Measurable g := (ridgeInverseTrace_measurable hL.le).comp
    continuous_id.matrix_transpose.measurable
  have hiG : Integrable g μ := Integrable.of_bound hm.aestronglyMeasurable ((k : ℝ) * L)
    (Filter.Eventually.of_forall fun Z => by
      have h := ridgeInverseTrace_bounds hL.le Zᵀ
      simpa [g, Real.norm_of_nonneg h.1] using h.2)
  have hdf : k + p - k + 1 = p + 1 := by omega
  have hr : (5 / 4 : ℝ) < ((k + p - k + 1 : ℕ) : ℝ) / 2 := by
    rw [hdf, Nat.cast_add, Nat.cast_one]
    have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hMoment := gaussianGram_inv_trace_moment (d := k + p) hk (by omega) (by norm_num) hr
  have hin : Integrable (fun Z => (f Z) ^ (5 / 4 : ℝ)) μ := hMoment.1
  have hBoth : ∀ᵐ Z ∂μ, 0 ≤ f Z - g Z ∧
      f Z - g Z ≤ L ^ (-(1 / 4 : ℝ)) * (f Z) ^ (5 / 4 : ℝ) := by
    filter_upwards [ae_gaussianMatrix_injective (k := k) (d := k + p) (by omega)] with Z hZ
    have hPos : (Zᵀ * (Zᵀ)ᵀ).PosDef := by
      simpa only [transpose_transpose, gaussianGram] using gaussianGram_posDef Z hZ
    simpa only [f, g, gaussianGram, transpose_transpose] using
      ridge_error_pointwise hk hL Zᵀ (orderedEigenvaluesFin_pos hPos)
  have hExp : (∫ Z, f Z ∂μ) = 1 / ((p : ℝ) - 1) := by
    dsimp [f, μ]
    rw [integral_div, hiF₀.2]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have he : ((k + p : ℕ) : ℝ) - k - 1 = (p : ℝ) - 1 := by push_cast; ring
    rw [he, div_right_comm, div_self hk']
  change 0 ≤ 1 / ((p : ℝ) - 1) - (∫ Z, g Z ∂μ) ∧
    1 / ((p : ℝ) - 1) - (∫ Z, g Z ∂μ) ≤ _
  rw [← hExp, ← integral_sub hiF hiG]
  refine ⟨integral_nonneg_of_ae (hBoth.mono fun _ h => h.1), ?_⟩
  calc
    _ ≤ ∫ Z, L ^ (-(1 / 4 : ℝ)) * (f Z) ^ (5 / 4 : ℝ) ∂μ :=
      integral_mono_ae (hiF.sub hiG) (hin.const_mul _) (hBoth.mono fun _ h => h.2)
    _ ≤ _ := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hL.le _)
      simpa only [hdf, show (1 : ℝ) ≤ 5 / 4 by norm_num, if_true, one_mul] using hMoment.2

end SketchOrientation.Cosine
