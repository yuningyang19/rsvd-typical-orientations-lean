import SketchOrientation.SpectralCap
import SketchOrientation.TwoLevelResidual

namespace SketchOrientation

open Matrix MeasureTheory

/-- B = √n VᵀU in Sections 2 and 6. -/
noncomputable def scaledTargetBlock {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin n) (Fin l) ℝ) : Matrix (Fin k) (Fin l) ℝ :=
  Real.sqrt (n : ℝ) • (Vᵀ * U)

theorem continuous_scaledTargetBlock {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) :
    Continuous (fun U : Matrix (Fin n) (Fin l) ℝ => scaledTargetBlock V U) := by
  unfold scaledTargetBlock
  fun_prop

theorem scaledTargetBlock_rowGram {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin n) (Fin l) ℝ) :
    scaledTargetBlock V U * (scaledTargetBlock V U)ᵀ = (n : ℝ) • (Vᵀ * (U * Uᵀ) * V) := by
  unfold scaledTargetBlock
  rw [transpose_smul, transpose_mul, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two, Real.sq_sqrt (by positivity)]
  simp only [Matrix.mul_assoc]

private theorem blockCompression_psd {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin n) (Fin l) ℝ) : (Vᵀ * (U * Uᵀ) * V).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose,
    Matrix.mul_assoc] using posSemidef_self_mul_conjTranspose (Vᵀ * U)

private theorem orderedEigenvaluesFin_eq_of_eq {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (heq : A = B) (ha : A.IsHermitian) (hb : B.IsHermitian) (j : Fin k) :
    orderedEigenvaluesFin ha j = orderedEigenvaluesFin hb j := by
  subst B
  rfl

theorem scaledTargetBlock_eigenvalues {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin n) (Fin l) ℝ) (j : Fin k) :
    gramEigenvalues (scaledTargetBlock V U) j = (n : ℝ) *
      orderedEigenvaluesFin (blockCompression_psd V U).isHermitian j := by
  let T := Vᵀ * (U * Uᵀ) * V
  have hs : ((n : ℝ) • T).IsHermitian :=
    ((blockCompression_psd V U).smul (show (0 : ℝ) ≤ n by positivity)).isHermitian
  unfold gramEigenvalues
  rw [orderedEigenvaluesFin_eq_of_eq (scaledTargetBlock_rowGram V U) _ hs]
  exact orderedEigenvaluesFin_smul_nonneg (blockCompression_psd V U).isHermitian
    (by positivity) hs j

/-- The finite contribution in Eq. (edge:loss) is exactly the centered
actual residual, including rank-deficient draws. -/
theorem centeredRankLoss_eq_scaledTargetBlock {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (U : Matrix (Fin n) (Fin l) ℝ) (hU : Uᵀ * U = 1)
    (hk : 0 < k) (hkn : k < n) {L : ℝ} (hΓ : 1 ≤ (n : ℝ) * k * L) :
    centeredRankLoss k (twoLevelInput V ((n : ℝ) * k * L)) U =
      (n : ℝ) / (n - k) *
        (∑ j, L / (1 + ((k : ℝ) * L - (n : ℝ)⁻¹) * gramEigenvalues (scaledTargetBlock V U) j)) -
      (l : ℝ) / (k * (n - k)) := by
  let Γ := (n : ℝ) * k * L
  have hGram := twoLevelInput_gram V hV (zero_le_one.trans hΓ)
  have hLoss := twoLevel_centeredRankLoss _ U V hU hV hΓ hGram
    (by simpa only [Fintype.card_fin] using hk)
    (by simpa only [Fintype.card_fin] using hkn)
  simp only [Fintype.card_fin] at hLoss
  rw [hLoss, trace_inverse_one_add_smul_of_posSemidef (blockCompression_psd V U) _
    (sub_nonneg.mpr hΓ)]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkn' : (n : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkn.ne')
  have hFactor (x : ℝ) : 1 + ((k : ℝ) * L - (n : ℝ)⁻¹) * ((n : ℝ) * x) =
      1 + (Γ - 1) * x := by
    dsimp [Γ]
    field_simp
  simp_rw [scaledTargetBlock_eigenvalues, hFactor]
  simp_rw [div_eq_mul_inv, ← Finset.mul_sum]
  dsimp [Γ]
  field_simp

/-- Law of the observed block under an actual frame law. -/
noncomputable def projectedBlockLaw {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (ν : ProbabilityMeasure (Matrix (Fin n) (Fin l) ℝ)) :
    ProbabilityMeasure (Matrix (Fin k) (Fin l) ℝ) :=
  ν.map (continuous_scaledTargetBlock V).measurable.aemeasurable

/-- The expected scaled spectral loss is the expectation of the actual
centered residual for the same sketch law. -/
theorem rowBlockExpectedLoss_eq_integral_centeredRankLoss {n k l : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (ν : ProbabilityMeasure (Matrix (Fin n) (Fin l) ℝ))
    (hU : ∀ᵐ U ∂(ν : Measure (Matrix (Fin n) (Fin l) ℝ)), Uᵀ * U = 1)
    (hk : 0 < k) (hkn : k < n) {L : ℝ} (hΓ : 1 ≤ (n : ℝ) * k * L) :
    rowBlockExpectedLoss (projectedBlockLaw V ν) n L =
      ∫ U, centeredRankLoss k (twoLevelInput V ((n : ℝ) * k * L)) U ∂(ν : Measure (Matrix (Fin n) (Fin l) ℝ)) := by
  let f (j : Fin k) (B : Matrix (Fin k) (Fin l) ℝ) :=
    L / (1 + ((k : ℝ) * L - (n : ℝ)⁻¹) * gramEigenvalues B j)
  have hnonneg : 0 ≤ (k : ℝ) * L - (n : ℝ)⁻¹ := by
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [sub_nonneg, inv_eq_one_div, div_le_iff₀ hn]
    nlinarith only [hΓ]
  have hL : 0 ≤ L := by
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    exact nonneg_of_mul_nonneg_right (zero_le_one.trans hΓ) (mul_pos hn hk')
  have hf (j : Fin k) : Measurable (f j) :=
    measurable_const.div (measurable_const.add (measurable_const.mul
      ((continuous_apply j).comp continuous_gramEigenvalues).measurable))
  have hb (j : Fin k) (B : Matrix (Fin k) (Fin l) ℝ) : ‖f j B‖ ≤ L := by
    have hden : 1 ≤ 1 + ((k : ℝ) * L - (n : ℝ)⁻¹) * gramEigenvalues B j :=
      le_add_of_nonneg_right (mul_nonneg hnonneg (gramEigenvalues_nonneg B j))
    dsimp [f]
    rw [abs_of_nonneg (div_nonneg hL (zero_le_one.trans hden))]
    exact div_le_self hL hden
  let B := scaledTargetBlock (l := l) V
  have hB := (continuous_scaledTargetBlock (l := l) V).measurable
  have hInt (j : Fin k) : Integrable (fun U => f j (B U)) (ν : Measure (Matrix (Fin n) (Fin l) ℝ)) :=
    Integrable.of_bound ((hf j).comp hB).aestronglyMeasurable L
      (Filter.Eventually.of_forall fun U => hb j (B U))
  unfold rowBlockExpectedLoss Edge.scaledGapMean
  change (n : ℝ) / (n - k) * (∑ j,
    ∫ W, f j W ∂((ν : Measure (Matrix (Fin n) (Fin l) ℝ)).map B)) - (l : ℝ) / (k * (n - k)) = _
  have hMap (j : Fin k) :
      (∫ W, f j W ∂((ν : Measure (Matrix (Fin n) (Fin l) ℝ)).map B)) =
        ∫ U, f j (B U) ∂(ν : Measure (Matrix (Fin n) (Fin l) ℝ)) :=
    integral_map hB.aemeasurable (hf j).aestronglyMeasurable
  simp only [hMap]
  rw [← integral_finsetSum _ (fun j _ => hInt j), ← integral_const_mul]
  have hSum : Integrable (fun U => ∑ j, f j (B U)) (ν : Measure (Matrix (Fin n) (Fin l) ℝ)) :=
    integrable_finsetSum _ (fun j _ => hInt j)
  have hConst :
      (∫ _ : Matrix (Fin n) (Fin l) ℝ, (l : ℝ) / (k * (n - k))
        ∂(ν : Measure (Matrix (Fin n) (Fin l) ℝ))) = (l : ℝ) / (k * (n - k)) := by simp
  rw [← hConst, ← integral_sub (hSum.const_mul _) (integrable_const _)]
  apply integral_congr_ae
  filter_upwards [hU] with U hFrame
  exact (centeredRankLoss_eq_scaledTargetBlock V hV U hFrame hk hkn hΓ).symm

end SketchOrientation
