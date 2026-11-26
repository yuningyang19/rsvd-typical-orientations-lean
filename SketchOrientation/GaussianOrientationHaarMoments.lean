import SketchOrientation.GaussianOrientationEndpoint

namespace SketchOrientation

open MeasureTheory Matrix

variable {n k ℓ : ℕ}

/-- Full rank of the compression almost surely for every rank-ℓ sketch. -/
theorem ae_gaussianHaarFrame_projectedGram_invertible (hℓn : ℓ ≤ n) (hkℓ : k ≤ ℓ)
    (P : OrthogonalProjector n ℓ) :
    ∀ᵐ V ∂gaussianHaarFrameLaw (hkℓ.trans hℓn), (Vᵀ * P.val * V).det ≠ 0 := by
  have hdet : MeasurableSet {V : Matrix (Fin n) (Fin k) ℝ | (Vᵀ * P.val * V).det ≠ 0} :=
    (isClosed_singleton.preimage
      ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul
        continuous_id).matrix_det).isOpen_compl.measurableSet
  rw [← gaussianPolarFrameLaw_eq_haar (hkℓ.trans hℓn),
    ae_map_iff measurable_gaussianPolarFrame.aemeasurable hdet]
  filter_upwards [ae_gaussianMatrix_injective (hkℓ.trans hℓn),
    ae_gaussianMatrix_projectedGram_invertible hℓn hkℓ P.val P.property.1 P.property.2.1
      P.property.2.2] with G hG hPG
  let H := gaussianPolarRadial G
  let V := gaussianPolarFrame G
  have he : Gᵀ * P.val * G = H * (Vᵀ * P.val * V) * H := by
    rw [← gaussianPolarFrame_mul_radial G hG]
    simp [H, V, transpose_mul, gaussianPolarRadial_transpose, Matrix.mul_assoc]
  change (Vᵀ * P.val * V).det ≠ 0
  intro h0
  rw [he, det_mul, det_mul, h0, mul_zero, zero_mul] at hPG
  exact hPG rfl

private theorem gaussianOrientationScore_moment_prod (hℓn : ℓ ≤ n) (hk : 0 < k)
    (hkℓ : k ≤ ℓ) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 ≤ r) (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    let F := fun p : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
      gaussianOrientationScore p.1 p.2 ^ r
    Integrable F (ν.prod (gaussianMatrixLaw n k)) ∧
      (∫ p, F p ∂ν.prod (gaussianMatrixLaw n k)) ≤ chiSquareNegativeMoment (ℓ - k + 1) r := by
  intro F
  let M := chiSquareNegativeMoment (ℓ - k + 1) r
  have hM : 0 ≤ M := by
    unfold M chiSquareNegativeMoment
    have h₁ := Real.Gamma_pos_of_pos (sub_pos.mpr hr')
    have h₂ := Real.Gamma_pos_of_pos ((zero_lt_one.trans_le hr).trans hr')
    positivity
  have hF : Measurable F := (@measurable_gaussianOrientationScore n k ℓ).pow_const _
  have h0 (P : OrthogonalProjector n ℓ) (G : Matrix (Fin n) (Fin k) ℝ) :
      0 ≤ F (P, G) := Real.rpow_nonneg (gaussianOrientationScore_nonneg P G) _
  have hFbound (P : OrthogonalProjector n ℓ) :=
    gaussianMatrix_projectedGram_inv_trace_moment hℓn hk hkℓ hr hr' P.val
      P.property.1 P.property.2.1 P.property.2.2
  have hFi : Integrable F (ν.prod (gaussianMatrixLaw n k)) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).2
    refine ⟨ae_of_all _ fun P => (hFbound P).1, ?_⟩
    refine (integrable_const M).mono' (hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
    filter_upwards [] with P
    simp_rw [Real.norm_of_nonneg (h0 P _)]
    rw [Real.norm_of_nonneg (integral_nonneg (h0 P))]
    exact (hFbound P).2
  refine ⟨hFi, ?_⟩
  rw [integral_prod _ hFi]
  exact (integral_mono hFi.integral_prod_left (integrable_const M) (fun P => (hFbound P).2)).trans_eq
    (by simp [M])

set_option maxHeartbeats 1000000 in
/-- Radial conditioning bounds the Haar frame's inverse-trace moments,
independently of the orientation of the sketch law. -/
theorem haarOrientationScore_moment_prod (hℓn : ℓ ≤ n) (hk : 0 < k) (hkℓ : k + 1 < ℓ)
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 ≤ r) (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    let η := ν.prod (gaussianHaarFrameLaw (show k ≤ n by omega))
    let F := fun p : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
      gaussianOrientationScore p.1 p.2 ^ r
    Integrable F η ∧ (∫ p, F p ∂η) ≤
      ((n : ℝ) - k - 1) ^ r * chiSquareNegativeMoment (ℓ - k + 1) r := by
  intro η F
  let μ := ν.prod (gaussianMatrixLaw n k)
  let X := Prod.map (id : OrthogonalProjector n ℓ → OrthogonalProjector n ℓ)
    (@gaussianPolarFrame n k)
  let T := Function.uncurry (@gaussianOrientationScore n k ℓ)
  let b := (n : ℝ) - k - 1
  have hb : 0 < b := by
    have hn : (k : ℝ) + 1 < n := by exact_mod_cast (show k + 1 < n by omega)
    dsimp [b]
    linarith
  have hXm : Measurable X := measurable_id.prodMap measurable_gaussianPolarFrame
  have hX : μ.map X = η := by
    change (ν.prod (gaussianMatrixLaw n k)).map X =
      ν.prod (gaussianHaarFrameLaw (show k ≤ n by omega))
    rw [← Measure.map_prod_map _ _ measurable_id measurable_gaussianPolarFrame, Measure.map_id,
      gaussianPolarFrameLaw_eq_haar (show k ≤ n by omega)]
  have hF : Measurable F := (@measurable_gaussianOrientationScore n k ℓ).pow_const _
  have hT (p : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ) : 0 ≤ T p :=
    gaussianOrientationScore_nonneg p.1 p.2
  have hRad := gaussianPolar_projectedInverseTrace_condExp_comp hℓn hkℓ ν Subtype.val
    measurable_subtype_coe (ae_of_all _ fun P => P.property)
  let f := gaussianProjectedInverseTrace ∘ (Prod.map (@Subtype.val _ _) id :
    OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ → _)
  have he : T = (k : ℝ)⁻¹ • f := by
    funext p
    change f p / (k : ℝ) = (k : ℝ)⁻¹ * f p
    ring
  have hCond : μ[T | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun p => T (X p) / b := by
    rw [he]
    refine (condExp_smul (m := MeasurableSpace.comap X inferInstance) ((k : ℝ)⁻¹) f).trans ?_
    filter_upwards [hRad] with p hp
    change μ[f | MeasurableSpace.comap X inferInstance] p = f (X p) / b at hp
    simp only [Pi.smul_apply, smul_eq_mul, hp]
    ring
  have hNorm : (fun p => ‖T p‖ ^ r) = F := by
    funext p
    rw [Real.norm_of_nonneg (hT p)]
    rfl
  have hMom := gaussianOrientationScore_moment_prod hℓn hk (by omega) ν hr hr'
  have hNormI : Integrable (fun p => ‖T p‖ ^ r) μ := by
    rw [hNorm]
    exact hMom.1
  have hDom : Integrable (fun p => ‖μ[T | MeasurableSpace.comap X inferInstance] p‖ ^ r) μ := by
    refine (integrable_condExp (f := fun p => ‖T p‖ ^ r) (m := MeasurableSpace.comap X inferInstance)).mono'
      ((stronglyMeasurable_condExp.mono hXm.comap_le).norm.measurable.pow_const _).aestronglyMeasurable ?_
    filter_upwards [Integrable.norm_condExp_rpow_le (m := MeasurableSpace.comap X inferInstance) hr hNormI] with p hp
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hp
  have hEq : F ∘ X =ᵐ[μ] fun p => b ^ r * ‖μ[T | MeasurableSpace.comap X inferInstance] p‖ ^ r := by
    filter_upwards [hCond] with p hp
    rw [hp]
    change (T (X p)) ^ r = b ^ r * |T (X p) / b| ^ r
    rw [abs_of_nonneg (div_nonneg (hT _) hb.le), Real.div_rpow (hT _) hb.le]
    have hb' := Real.rpow_pos_of_pos hb r
    field_simp
  rw [← hX, integrable_map_measure hF.aestronglyMeasurable hXm.aemeasurable,
    integral_map hXm.aemeasurable hF.aestronglyMeasurable]
  refine ⟨(hDom.const_mul _).congr hEq.symm, ?_⟩
  change (∫ p, (F ∘ X) p ∂μ) ≤ _
  rw [integral_congr_ae hEq, integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hb.le _)
  refine (integral_norm_condExp_rpow_le (m := MeasurableSpace.comap X inferInstance) hr hNormI).trans ?_
  rw [hNorm]
  exact hMom.2

end SketchOrientation
