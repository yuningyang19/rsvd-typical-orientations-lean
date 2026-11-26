import SketchOrientation.GaussianOrientationEndpoint
import SketchOrientation.GaussianTailGram

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix

variable {n k ℓ : ℕ}

private theorem gaussianRow_mul_mean (a b : Fin k) :
    let μ := Measure.pi (fun _ : Fin k => gaussianReal 0 1)
    Integrable (fun x : Fin k → ℝ => x a * x b) μ ∧
      (∫ x : Fin k → ℝ, x a * x b ∂μ) = (1 : Matrix (Fin k) (Fin k) ℝ) a b := by
  classical
  let μ := fun _ : Fin k => gaussianReal 0 1
  have hEval (c : Fin k) : MeasurePreserving (fun x : Fin k → ℝ => x c)
      (Measure.pi μ) (gaussianReal 0 1) := measurePreserving_eval μ c
  by_cases hab : a = b
  · subst b
    let f := fun x : ℝ => x ^ 2
    have hf : Integrable f (gaussianReal 0 1) := standardGaussian_power_integrable 2
    simp only [← sq, Matrix.one_apply_eq]
    exact ⟨(hEval a).integrable_comp_of_integrable hf,
      (integral_comp_eval (μ := μ) (i := a) hf.aestronglyMeasurable).trans
        standardGaussian_second_moment⟩
  · have hInd : IndepFun (fun x : Fin k → ℝ => x a) (fun x : Fin k → ℝ => x b)
        (Measure.pi μ) :=
      (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hab
    have hId : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
      simpa using standardGaussian_power_integrable 1
    have hI (c : Fin k) : Integrable (fun x : Fin k → ℝ => x c) (Measure.pi μ) :=
      (hEval c).integrable_comp_of_integrable hId
    refine ⟨hInd.integrable_mul (hI a) (hI b), ?_⟩
    have hMean (c : Fin k) : (∫ x : Fin k → ℝ, x c ∂Measure.pi μ) = 0 := by
      exact (integral_comp_eval (μ := μ) (i := c) hId.aestronglyMeasurable).trans (by simp [μ])
    rw [Matrix.one_apply_ne hab]
    change (∫ x, ((fun y : Fin k → ℝ => y a) * (fun y : Fin k → ℝ => y b)) x ∂Measure.pi μ) = 0
    rw [hInd.integral_mul_eq_mul_integral (hI a).aestronglyMeasurable (hI b).aestronglyMeasurable,
      hMean a, zero_mul]

private theorem gaussianGram_entry_mean (a b : Fin k) :
    Integrable (fun G => gaussianGram G a b) (gaussianMatrixLaw n k) ∧
      (∫ G, gaussianGram G a b ∂gaussianMatrixLaw n k) =
        (n : ℝ) * (1 : Matrix (Fin k) (Fin k) ℝ) a b := by
  let μ := fun _ : Fin n => Measure.pi (fun _ : Fin k => gaussianReal 0 1)
  let f (x : Fin k → ℝ) := x a * x b
  have hf : ∀ i, Integrable f (μ i) := fun _ => (gaussianRow_mul_mean a b).1
  have hi (i : Fin n) :
      Integrable (fun G : Fin n → Fin k → ℝ => f (G i)) (Measure.pi μ) :=
    (measurePreserving_eval μ i).integrable_comp_of_integrable (hf i)
  rw [gaussianMatrixLaw_eq_row_product]
  change Integrable (fun G : Fin n → Fin k → ℝ => ∑ i, f (G i)) (Measure.pi μ) ∧
    (∫ G : Fin n → Fin k → ℝ, ∑ i, f (G i) ∂Measure.pi μ) = _
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [fun i => (integral_comp_eval (μ := μ) (i := i) (hf i).aestronglyMeasurable).trans
    (gaussianRow_mul_mean a b).2]
  simp

/-- The radial square has integrable entries and mean `n I`. -/
theorem gaussianPolarRadial_sq_entry_mean (a b : Fin k) :
    Integrable (fun H => (H * H) a b) (gaussianRadialFactorLaw n k) ∧
      (∫ H, (H * H) a b ∂gaussianRadialFactorLaw n k) =
        (n : ℝ) * (1 : Matrix (Fin k) (Fin k) ℝ) a b := by
  have hF : Continuous (fun H : Matrix (Fin k) (Fin k) ℝ => (H * H) a b) :=
    (continuous_id.matrix_mul continuous_id).matrix_elem a b
  have hR := continuous_gaussianPolarRadial (n := n) (k := k)
  unfold gaussianRadialFactorLaw
  rw [integrable_map_measure hF.measurable.aestronglyMeasurable hR.measurable.aemeasurable,
    integral_map hR.measurable.aemeasurable hF.measurable.aestronglyMeasurable]
  have he : (fun H : Matrix (Fin k) (Fin k) ℝ => (H * H) a b) ∘ gaussianPolarRadial =
      (fun G : Matrix (Fin n) (Fin k) ℝ => gaussianGram G a b) :=
    funext fun G => congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A a b) (gaussianPolarRadial_sq G)
  rw [he]
  simpa only [gaussianPolarRadial_sq] using gaussianGram_entry_mean (n := n) a b

private theorem gaussianPolarRadial_weightedSquare_mean (A : Matrix (Fin k) (Fin k) ℝ) :
    Integrable (fun H => (A * (H * H)).trace) (gaussianRadialFactorLaw n k) ∧
      (∫ H, (A * (H * H)).trace ∂gaussianRadialFactorLaw n k) = (n : ℝ) * A.trace := by
  have hi (i j : Fin k) :
      Integrable (fun H => A i j * (H * H) j i) (gaussianRadialFactorLaw n k) :=
    ((gaussianPolarRadial_sq_entry_mean j i).1).const_mul _
  have hE (i : Fin k) : (∑ j : Fin k, A i j * ((n : ℝ) * (1 : Matrix (Fin k) (Fin k) ℝ) j i)) =
      (n : ℝ) * A i i := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j _ hj
      rw [Matrix.one_apply_ne hj, mul_zero, mul_zero]
    · simp
  change Integrable (fun H => ∑ i, ∑ j, A i j * (H * H) j i) (gaussianRadialFactorLaw n k) ∧
    (∫ H, ∑ i, ∑ j, A i j * (H * H) j i ∂gaussianRadialFactorLaw n k) =
      (n : ℝ) * ∑ i, A i i
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, fun i j =>
    (gaussianPolarRadial_sq_entry_mean (n := n) j i).2, hE, Finset.mul_sum]

private theorem gaussianPolar_projectedEnergy_factor
    (P : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin k) ℝ)
    (hG : Function.Injective G.mulVec) :
    (Gᵀ * P * G).trace =
      (((gaussianPolarFrame G)ᵀ * P * gaussianPolarFrame G) *
        (gaussianPolarRadial G * gaussianPolarRadial G)).trace := by
  let H := gaussianPolarRadial G
  let V := gaussianPolarFrame G
  have hW : Gᵀ * P * G = H * (Vᵀ * P * V) * H := by
    conv_lhs => rw [← gaussianPolarFrame_mul_radial G hG]
    simp only [H, V, transpose_mul, gaussianPolarRadial_transpose, Matrix.mul_assoc]
  rw [hW, Matrix.mul_assoc, trace_mul_comm H, Matrix.mul_assoc]

/-- The captured energy agrees with the trace of the projected Gram. -/
theorem gaussianProjectedEnergy_eq_squaredFrobenius (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) :
    (Gᵀ * P.val * G).trace = squaredFrobenius (P.val * G) := by
  unfold squaredFrobenius
  rw [transpose_mul, P.property.1]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P.val P.val, P.property.2.1]

private theorem measurable_gaussianPolar_weightedSquare (P : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
      ((p.1ᵀ * P * p.1) * (p.2 * p.2)).trace) :=
  measurable_matrix_trace.comp (measurable_matrix_product
    (measurable_matrix_product (measurable_matrix_product
      (measurable_matrix_transpose measurable_fst) measurable_const) measurable_fst)
    (measurable_matrix_product measurable_snd measurable_snd))

/-- Conditioning the Gaussian captured energy on its polar frame averages its
radial square to `n I`. -/
theorem gaussianPolar_projectedEnergy_condExp (hkn : k ≤ n) (P : OrthogonalProjector n ℓ) :
    let γ := gaussianMatrixLaw n k
    γ[(fun G => (Gᵀ * P.val * G).trace) | MeasurableSpace.comap gaussianPolarFrame inferInstance] =ᵐ[γ]
      fun G => (n : ℝ) * ((gaussianPolarFrame G)ᵀ * P.val * gaussianPolarFrame G).trace := by
  let γ := gaussianMatrixLaw n k
  let η := gaussianRadialFactorLaw n k
  let V := @gaussianPolarFrame n k
  let H := @gaussianPolarRadial n k
  let F := fun p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
    ((p.1ᵀ * P.val * p.1) * (p.2 * p.2)).trace
  have hProd : γ.map (fun G => (V G, H G)) = (γ.map V).prod η := by
    rw [gaussianPolarFrameLaw_eq_haar hkn]
    exact gaussianPolarLaw_eq_prod hkn
  have hEq : (fun G => (Gᵀ * P.val * G).trace) =ᵐ[γ] fun G => F (V G, H G) := by
    filter_upwards [ae_gaussianMatrix_injective hkn] with G hG
    exact gaussianPolar_projectedEnergy_factor P.val G hG
  have hI : Integrable (fun G => (Gᵀ * P.val * G).trace) γ :=
    (gaussianCompressedGram_moments (k := k) P.property.1).2.2.1
  refine (condExp_congr_ae hEq).trans (((condExp_of_product_image γ η V H
    measurable_gaussianPolarFrame continuous_gaussianPolarRadial.measurable hProd F
    (measurable_gaussianPolar_weightedSquare P.val) (hI.congr hEq))).trans ?_)
  filter_upwards [] with G
  exact (gaussianPolarRadial_weightedSquare_mean ((V G)ᵀ * P.val * V G)).2

private theorem haar_projectedEnergy_le (P : OrthogonalProjector n ℓ)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1) :
    (Vᵀ * P.val * V).trace ≤ (k : ℝ) := by
  let Q := 1 - P.val
  have hQs : Qᵀ = Q := by simp [Q, P.property.1]
  have hQi : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, P.property.2.1]
    abel
  have h := Matrix.posSemidef_conjTranspose_mul_self (Q * V)
  rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, hQs,
    Matrix.mul_assoc Vᵀ, ← Matrix.mul_assoc Q Q, hQi, ← Matrix.mul_assoc Vᵀ] at h
  have ht := h.trace_nonneg
  simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV, Matrix.trace_sub,
    Matrix.trace_one, Fintype.card_fin] at ht
  exact sub_nonneg.mp ht

private theorem ae_radial_weightedSquare_nonneg (P : OrthogonalProjector n ℓ)
    (V : Matrix (Fin n) (Fin k) ℝ) :
    ∀ᵐ H ∂gaussianRadialFactorLaw n k, 0 ≤ ((Vᵀ * P.val * V) * (H * H)).trace := by
  have hS : MeasurableSet {H : Matrix (Fin k) (Fin k) ℝ | Hᵀ = H} :=
    (isClosed_eq continuous_id.matrix_transpose continuous_id).measurableSet
  have hSymm : ∀ᵐ H ∂gaussianRadialFactorLaw n k, Hᵀ = H := by
    unfold gaussianRadialFactorLaw
    exact (ae_map_iff continuous_gaussianPolarRadial.measurable.aemeasurable hS).2
      (ae_of_all _ gaussianPolarRadial_transpose)
  filter_upwards [hSymm] with H hH
  have h := (targetCompression_posSemidef (V * H) P).trace_nonneg
  rw [transpose_mul, hH] at h
  simp only [Matrix.mul_assoc] at h
  rw [← Matrix.mul_assoc Vᵀ P.val, ← Matrix.mul_assoc (Vᵀ * P.val) V,
    ← Matrix.mul_assoc H] at h
  rw [Matrix.mul_assoc H, Matrix.trace_mul_comm H, Matrix.mul_assoc] at h
  exact h

/-- Transport a mixed energy moment from the Gaussian lift to the Haar frame.
Both products are integrable whenever the test on the frame is integrable. -/
theorem gaussianPolar_projectedEnergy_integral_mul (hkn : k ≤ n)
    (P : OrthogonalProjector n ℓ) {f : Matrix (Fin n) (Fin k) ℝ → ℝ}
    (hf : Integrable f (gaussianHaarFrameLaw hkn)) :
    Integrable (fun G => f (gaussianPolarFrame G) * (Gᵀ * P.val * G).trace) (gaussianMatrixLaw n k) ∧
    Integrable (fun V => f V * (Vᵀ * P.val * V).trace) (gaussianHaarFrameLaw hkn) ∧
    (∫ G, f (gaussianPolarFrame G) * (Gᵀ * P.val * G).trace ∂gaussianMatrixLaw n k) =
      (n : ℝ) * ∫ V, f V * (Vᵀ * P.val * V).trace ∂gaussianHaarFrameLaw hkn := by
  let γ := gaussianMatrixLaw n k
  let η := gaussianHaarFrameLaw hkn
  let ρ := gaussianRadialFactorLaw n k
  let E (V : Matrix (Fin n) (Fin k) ℝ) := (Vᵀ * P.val * V).trace
  let F (p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ) :=
    ((p.1ᵀ * P.val * p.1) * (p.2 * p.2)).trace
  let J (G : Matrix (Fin n) (Fin k) ℝ) := (gaussianPolarFrame G, gaussianPolarRadial G)
  let W (p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ) := f p.1 * F p
  have hF : Measurable F := measurable_gaussianPolar_weightedSquare P.val
  have hE : Measurable E := measurable_matrix_trace.comp
    (measurable_matrix_product (measurable_matrix_product
      (measurable_matrix_transpose measurable_id) measurable_const) measurable_id)
  have hE₀ (V : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ E V :=
    (targetCompression_posSemidef V P).trace_nonneg
  have hHaar : Integrable (fun V => f V * E V) η := by
    apply (hf.norm.mul_const (k : ℝ)).mono' (hf.aestronglyMeasurable.mul hE.aestronglyMeasurable)
    filter_upwards [ae_gaussianHaarFrame_orthonormal hkn] with V hV
    change ‖f V * E V‖ ≤ ‖f V‖ * (k : ℝ)
    rw [norm_mul, Real.norm_of_nonneg (hE₀ V)]
    exact mul_le_mul_of_nonneg_left (haar_projectedEnergy_le P V hV) (norm_nonneg _)
  have hNorm (V : Matrix (Fin n) (Fin k) ℝ) :
      (∫ H, ‖W (V, H)‖ ∂ρ) = ‖f V‖ * ((n : ℝ) * E V) := by
    have he := integral_congr_ae (show (fun H => ‖W (V, H)‖) =ᵐ[ρ] fun H => ‖f V‖ * F (V, H) from by
      filter_upwards [ae_radial_weightedSquare_nonneg (k := k) P V] with H hh
      exact (norm_mul _ _).trans (congrArg (_ * ·) (Real.norm_of_nonneg hh)))
    rw [he, integral_const_mul, (gaussianPolarRadial_weightedSquare_mean (Vᵀ * P.val * V)).2]
  have hW : Integrable W (η.prod ρ) := by
    have hm : AEStronglyMeasurable W (η.prod ρ) :=
      (hf.comp_fst ρ).aestronglyMeasurable.mul hF.aestronglyMeasurable
    refine (integrable_prod_iff hm).2 ⟨ae_of_all _ fun V => ?_, ?_⟩
    · exact ((gaussianPolarRadial_weightedSquare_mean (n := n) (Vᵀ * P.val * V)).1).const_mul (f V)
    · refine (hHaar.norm.const_mul (n : ℝ)).congr (ae_of_all _ fun V => ?_)
      change (n : ℝ) * ‖f V * E V‖ = ∫ H, ‖W (V, H)‖ ∂ρ
      rw [hNorm V, norm_mul, Real.norm_of_nonneg (hE₀ V)]
      ring
  have hJ : MeasurePreserving J γ (η.prod ρ) :=
    ⟨measurable_gaussianPolarFrame.prodMk continuous_gaussianPolarRadial.measurable,
      gaussianPolarLaw_eq_prod hkn⟩
  have hEq : (W ∘ J) =ᵐ[γ] fun G => f (gaussianPolarFrame G) * (Gᵀ * P.val * G).trace := by
    filter_upwards [ae_gaussianMatrix_injective hkn] with G hG
    exact congrArg (f (gaussianPolarFrame G) * ·)
      (gaussianPolar_projectedEnergy_factor P.val G hG).symm
  refine ⟨(hJ.integrable_comp_of_integrable hW).congr hEq, hHaar, ?_⟩
  rw [← integral_congr_ae hEq]
  calc
    (∫ G, (W ∘ J) G ∂γ) = ∫ p, W p ∂η.prod ρ := by
      have hm := hW.aestronglyMeasurable
      rw [← hJ.map_eq] at hm
      change (∫ G, W (J G) ∂γ) = _
      rw [← integral_map hJ.measurable.aemeasurable hm, hJ.map_eq]
    _ = ∫ V, f V * ((n : ℝ) * E V) ∂η := by
      rw [integral_prod _ hW]
      apply integral_congr_ae
      filter_upwards [] with V
      change (∫ H, f V * F (V, H) ∂ρ) = _
      rw [integral_const_mul, (gaussianPolarRadial_weightedSquare_mean (Vᵀ * P.val * V)).2]
    _ = (n : ℝ) * ∫ V, f V * E V ∂η := by
      rw [← integral_const_mul]
      congr 1
      funext V
      ring

private theorem covariance_as_left_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f e : Ω → ℝ} (hf : Integrable f μ)
    (hI : Integrable (fun x => (f x - (∫ y, f y ∂μ)) * e x) μ) :
    covariance f e μ = ∫ x, (f x - (∫ y, f y ∂μ)) * e x ∂μ := by
  have hfc : Integrable (fun x => f x - (∫ y, f y ∂μ)) μ :=
    hf.sub (integrable_const _)
  unfold covariance
  simp only [mul_sub]
  rw [integral_sub hI (hfc.mul_const _),
    integral_mul_const, integral_sub hf (integrable_const _)]
  simp

/-- Covariance with the captured Gaussian energy is the covariance with the
Haar overlap multiplied by the ambient dimension. -/
theorem gaussianPolar_projectedEnergy_covariance (hkn : k ≤ n)
    (P : OrthogonalProjector n ℓ) {f : Matrix (Fin n) (Fin k) ℝ → ℝ}
    (hf : Integrable f (gaussianHaarFrameLaw hkn)) :
    covariance (fun G => f (gaussianPolarFrame G)) (fun G => (Gᵀ * P.val * G).trace)
        (gaussianMatrixLaw n k) =
      (n : ℝ) * covariance f (fun V => (Vᵀ * P.val * V).trace) (gaussianHaarFrameLaw hkn) := by
  let γ := gaussianMatrixLaw n k
  let η := gaussianHaarFrameLaw hkn
  let V := @gaussianPolarFrame n k
  have hV : MeasurePreserving V γ η :=
    ⟨measurable_gaussianPolarFrame, gaussianPolarFrameLaw_eq_haar hkn⟩
  have hfi : Integrable (fun G => f (V G)) γ := hV.integrable_comp_of_integrable hf
  have hMean : (∫ G, f (V G) ∂γ) = ∫ v, f v ∂η := by
    have hm := hf.aestronglyMeasurable
    change AEStronglyMeasurable f η at hm
    rw [← hV.map_eq] at hm
    rw [← integral_map hV.measurable.aemeasurable hm, hV.map_eq]
  have hm := gaussianPolar_projectedEnergy_integral_mul hkn P
    (hf.sub (integrable_const (∫ v, f v ∂η)))
  have hA : Integrable (fun G => (f (V G) - (∫ H, f (V H) ∂γ)) * (Gᵀ * P.val * G).trace) γ := by
    rw [hMean]
    exact hm.1
  rw [covariance_as_left_centered_moment hfi hA, covariance_as_left_centered_moment hf hm.2.1,
    hMean]
  exact hm.2.2

/-- The first moment of the fixed-projector Haar inverse trace. -/
theorem haarProjectedInverseTrace_mean (hℓn : ℓ ≤ n) (hk : 0 < k) (hkℓ : k + 1 < ℓ)
    (P : OrthogonalProjector n ℓ) :
    let η := gaussianHaarFrameLaw (show k ≤ n by omega)
    Integrable (fun V => (Vᵀ * P.val * V)⁻¹.trace) η ∧
      (∫ V, (Vᵀ * P.val * V)⁻¹.trace ∂η) =
        (k : ℝ) * (((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1)) := by
  let η := gaussianHaarFrameLaw (show k ≤ n by omega)
  let ν := Measure.dirac P
  let c := (n : ℝ) - k
  let F := haarOrientationEndpoint (k := k) ν
  have hF := haarOrientationEndpoint_mean hℓn hk hkℓ ν
  have hc : c ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show n ≠ k by omega))
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrepr : (fun V : Matrix (Fin n) (Fin k) ℝ => (Vᵀ * P.val * V)⁻¹.trace) =
      fun V => (k : ℝ) * (c * F V + (ℓ : ℝ) / k) := by
    funext V
    unfold F haarOrientationEndpoint ν
    rw [integral_dirac]
    unfold gaussianOrientationScore gaussianProjectedInverseTrace
    change _ = (k : ℝ) * (c * (((Vᵀ * P.val * V)⁻¹.trace / (k : ℝ) - (ℓ : ℝ) / k) / c) +
        (ℓ : ℝ) / k)
    field_simp [hc, hk']
    ring
  change Integrable (fun V => (Vᵀ * P.val * V)⁻¹.trace) η ∧ _
  rw [hrepr]
  have hFi : Integrable F η := hF.1
  have hFe : (∫ V, F V ∂η) = haarOrientationBenchmark n k ℓ := hF.2
  refine ⟨((hFi.const_mul c).add (integrable_const _)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add (hFi.const_mul c) (integrable_const _),
    integral_const_mul, hFe, integral_const, probReal_univ, one_smul]
  change (k : ℝ) * (c * haarOrientationBenchmark n k ℓ + (ℓ : ℝ) / k) = _
  unfold haarOrientationBenchmark
  change (k : ℝ) * (c * ((((n : ℝ) - k - 1) * (1 / ((ℓ : ℝ) - k - 1)) -
    (ℓ : ℝ) / k) / c) + (ℓ : ℝ) / k) = _
  rw [mul_div_cancel₀ _ hc, sub_add_cancel]
  ring

/-- The mixed moment in the necessity proof, centered at the exact Haar
inverse-trace mean. -/
theorem gaussianPolar_projectedInverseTrace_centered_energy (hℓn : ℓ ≤ n)
    (hk : 0 < k) (hkℓ : k + 1 < ℓ) (P : OrthogonalProjector n ℓ) :
    let η := gaussianHaarFrameLaw (show k ≤ n by omega)
    let a := (k : ℝ) * (((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1))
    let g := fun V : Matrix (Fin n) (Fin k) ℝ => (Vᵀ * P.val * V)⁻¹.trace - a
    (∫ G, g (gaussianPolarFrame G) * (Gᵀ * P.val * G).trace ∂gaussianMatrixLaw n k) =
      (n : ℝ) * ∫ V, g V * (Vᵀ * P.val * V).trace ∂η :=
  (gaussianPolar_projectedEnergy_integral_mul (show k ≤ n by omega) P
    ((haarProjectedInverseTrace_mean hℓn hk hkℓ P).1.sub (integrable_const _))).2.2

end SketchOrientation
