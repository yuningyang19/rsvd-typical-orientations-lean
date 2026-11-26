import SketchOrientation.GaussianLiftEnergyCovarianceBlocks

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

noncomputable section

variable {n k ℓ : ℕ}

def gaussianLiftPolarInverseTrace (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ((gaussianPolarFrame G)ᵀ * P.val * gaussianPolarFrame G)⁻¹.trace

def gaussianLiftCrossTrace (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ((gaussianLiftProjectedGram P G)⁻¹ * gaussianLiftComplementGram P G).trace

def gaussianLiftEnergyWeight (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  (((gaussianLiftCapturedEnergy P G)⁻¹ • gaussianLiftProjectedGram P G)⁻¹ *
    gaussianLiftComplementGram P G).trace

private theorem measurable_trace_inv_mul {k : ℕ} :
    Measurable (fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
      (p.1⁻¹ * p.2).trace) := by
  have hMul : Measurable (fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
      p.1 * p.2) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun a _ =>
      ((continuous_id.matrix_elem i a).measurable.comp measurable_fst).mul
        ((continuous_id.matrix_elem a j).measurable.comp measurable_snd)
  have hTrace : Measurable (Matrix.trace : Matrix (Fin k) (Fin k) ℝ → ℝ) :=
    measurable_matrix_trace
  have hMix : Measurable (fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
      (p.1⁻¹, p.2)) := (measurable_matrix_nonsing_inv.comp measurable_fst).prodMk measurable_snd
  have h := (hTrace.comp hMul).comp hMix
  exact h

private theorem measurable_gaussianLiftEnergyWeight (P : OrthogonalProjector n ℓ) :
    Measurable (gaussianLiftEnergyWeight (k := k) P) := by
  have hN := (measurable_gaussianLiftCapturedEnergy (k := k) P).inv.smul
    (measurable_gaussianLiftProjectedGram P)
  have h := (measurable_trace_inv_mul (k := k)).comp
    (hN.prodMk (measurable_gaussianLiftComplementGram (k := k) P))
  exact h

private theorem gaussianLift_inv_entry_mean (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (P : OrthogonalProjector n ℓ) (i j : Fin k) :
    Integrable (fun G => (gaussianLiftProjectedGram P G)⁻¹ i j) (gaussianMatrixLaw n k) ∧
      (∫ G, (gaussianLiftProjectedGram P G)⁻¹ i j ∂gaussianMatrixLaw n k) =
        (1 : Matrix (Fin k) (Fin k) ℝ) i j / ((ℓ : ℝ) - k - 1) := by
  let W := gaussianLiftProjectedGram (k := k) P
  let R := fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹ i j
  have hR : Measurable R :=
    (continuous_id.matrix_elem i j).measurable.comp measurable_matrix_nonsing_inv
  have hW : Measurable W := measurable_gaussianLiftProjectedGram P
  have hG : Measurable (@gaussianGram ℓ k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  have hLaw : (gaussianMatrixLaw n k).map W = (gaussianMatrixLaw ℓ k).map gaussianGram :=
    gaussianMatrixLaw_map_projectedGram hℓn P.val P.property.1 P.property.2.1 P.property.2.2
  change Integrable (R ∘ W) _ ∧ (∫ G, R (W G) ∂gaussianMatrixLaw n k) = _
  rw [← integrable_map_measure hR.aestronglyMeasurable hW.aemeasurable,
    ← integral_map hW.aemeasurable hR.aestronglyMeasurable, hLaw,
    integrable_map_measure hR.aestronglyMeasurable hG.aemeasurable,
    integral_map hG.aemeasurable hR.aestronglyMeasurable]
  exact gaussianGram_inv_mean hkℓ i j

private theorem gaussianLift_complement_trace_mean (P : OrthogonalProjector n ℓ) :
    Integrable (fun G : Matrix (Fin n) (Fin k) ℝ => (gaussianLiftComplementGram P G).trace)
      (gaussianMatrixLaw n k) ∧
      (∫ G, (gaussianLiftComplementGram P G).trace ∂gaussianMatrixLaw n k) =
        (k : ℝ) * ((n : ℝ) - ℓ) := by
  have hP : (1 - P.val)ᵀ = 1 - P.val := by simp [P.property.1]
  have h := (gaussianCompressedGram_moments (k := k) hP).2.2
  have htr : P.val.trace = (ℓ : ℝ) := by
    rw [← rangeProjector_of_projector P.val P.property.1 P.property.2.1, trace_rangeProjector,
      P.property.2.2]
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, htr] at h
  exact h

private theorem gaussianLift_complement_psd (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : (gaussianLiftComplementGram P G).PosSemidef := by
  rw [gaussianLiftComplementGram_eq_gram]
  exact gaussianGram_posSemidef _

private theorem abs_entry_le_trace_of_posSemidef {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) (i j : Fin k) : |A i j| ≤ A.trace := by
  have hs : A j i = A i j := by simpa using hA.1.apply i j
  have hplus := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hminus := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_single_one,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, single_dotProduct,
    one_mul, col_apply, hs] at hplus hminus
  have he (i : Fin k) : A i i ≤ A.trace :=
    Finset.single_le_sum (f := fun j => A j j) (fun _ _ => hA.diag_nonneg) (Finset.mem_univ i)
  rw [abs_le]
  constructor <;> linarith [he i, he j]

private theorem integrable_gaussianLiftComplementGram_entry (P : OrthogonalProjector n ℓ)
    (i j : Fin k) : Integrable (fun G => gaussianLiftComplementGram P G i j) (gaussianMatrixLaw n k) := by
  have hm : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => gaussianLiftComplementGram P G i j) :=
    (continuous_id.matrix_elem i j).measurable.comp (measurable_gaussianLiftComplementGram P)
  refine (gaussianLift_complement_trace_mean (k := k) P).1.mono' hm.aestronglyMeasurable ?_
  exact ae_of_all _ fun G => by
    rw [Real.norm_eq_abs]
    exact abs_entry_le_trace_of_posSemidef (gaussianLift_complement_psd P G) i j

/-- The exact first moment of the inverse cross trace. Only first moments
of the projected inverse Gram are used, so oversampling two is admitted. -/
theorem gaussianLiftCrossTrace_mean (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (P : OrthogonalProjector n ℓ) :
    Integrable (gaussianLiftCrossTrace (k := k) P) (gaussianMatrixLaw n k) ∧
      (∫ G, gaussianLiftCrossTrace (k := k) P G ∂gaussianMatrixLaw n k) =
        (k : ℝ) * ((n : ℝ) - ℓ) / ((ℓ : ℝ) - k - 1) := by
  let μ := gaussianMatrixLaw n k
  let W := gaussianLiftProjectedGram (k := k) P
  let C := gaussianLiftComplementGram (k := k) P
  let a := (ℓ : ℝ) - k - 1
  let x (i j : Fin k) := fun G => (W G)⁻¹ i j
  let y (i j : Fin k) := fun G => C G j i
  let f (i j : Fin k) := fun G => x i j G * y i j G
  have hInd (i j : Fin k) : IndepFun (x i j) (y i j) μ := by
    have hf : Measurable (fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹ i j) :=
      (continuous_id.matrix_elem i j).measurable.comp measurable_matrix_nonsing_inv
    have hg : Measurable (fun A : Matrix (Fin k) (Fin k) ℝ => A j i) :=
      (continuous_id.matrix_elem j i).measurable
    exact (gaussianLift_projectedGram_indep_complementGram (k := k) P).comp hf hg
  have hX (i j : Fin k) := gaussianLift_inv_entry_mean hℓn hkℓ P i j
  have hY (i j : Fin k) : Integrable (y i j) μ :=
    integrable_gaussianLiftComplementGram_entry P j i
  have hI (i j : Fin k) : Integrable (f i j) μ :=
    (hInd i j).integrable_mul (hX i j).1 (hY i j)
  have hM (i j : Fin k) : (∫ G, f i j G ∂μ) =
      ((1 : Matrix (Fin k) (Fin k) ℝ) i j / a) * ∫ G, C G j i ∂μ :=
    ((hInd i j).integral_fun_mul_eq_mul_integral
      (hX i j).1.aestronglyMeasurable (hY i j).aestronglyMeasurable).trans
      (congrArg (fun z : ℝ => z * (∫ G, C G j i ∂μ)) (hX i j).2)
  change Integrable (fun G => ((W G)⁻¹ * C G).trace) μ ∧
    (∫ G, ((W G)⁻¹ * C G).trace ∂μ) = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  change Integrable (fun G => ∑ i : Fin k, ∑ j : Fin k, f i j G) μ ∧
    (∫ G, ∑ i : Fin k, ∑ j : Fin k, f i j G ∂μ) = _
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hI _ j), hM]
  have he (i : Fin k) : (∑ j : Fin k, ((1 : Matrix (Fin k) (Fin k) ℝ) i j / a) *
      (∫ G, C G j i ∂μ)) = (∫ G, C G i i ∂μ) / a := by
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_div, div_eq_mul_inv, mul_comm]
    · intro j _ hj
      rw [Matrix.one_apply_ne hj.symm, zero_div, zero_mul]
    · simp
  simp_rw [he]
  rw [← Finset.sum_div, ← integral_finsetSum _ (fun i _ => hY i i)]
  exact congrArg (fun z : ℝ => z / a) (gaussianLift_complement_trace_mean (k := k) P).2

/-- The trace of the inverse polar compression decomposes into the target
rank and the independent-complement cross trace. -/
theorem gaussianLiftPolarInverseTrace_eq (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) (hG : Function.Injective G.mulVec)
    (hW : IsUnit (gaussianLiftProjectedGram P G).det) :
    gaussianLiftPolarInverseTrace P G = (k : ℝ) + gaussianLiftCrossTrace P G := by
  let V := gaussianPolarFrame G
  let H := gaussianPolarRadial G
  let T := Vᵀ * P.val * V
  let W := gaussianLiftProjectedGram P G
  let C := gaussianLiftComplementGram P G
  have hH : IsUnit H.det := gaussianPolarRadial_det_isUnit G hG
  have hW₀ : W = H * T * H := by
    unfold W gaussianLiftProjectedGram
    conv_lhs => rw [← gaussianPolarFrame_mul_radial G hG]
    simp [H, T, V, transpose_mul, gaussianPolarRadial_transpose, Matrix.mul_assoc]
  have hTrace : (W⁻¹ * (H * H)).trace = T⁻¹.trace := by
    rw [hW₀, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc
      _ = (H⁻¹ * T⁻¹ * H).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc H⁻¹ H H, Matrix.nonsing_inv_mul H hH, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv H hH, Matrix.one_mul]
  rw [show H * H = W + C from (gaussianPolarRadial_sq G).trans (gaussianLift_gram_add P G).symm,
    Matrix.mul_add, Matrix.trace_add, Matrix.nonsing_inv_mul W hW, Matrix.trace_one,
    Fintype.card_fin] at hTrace
  exact hTrace.symm

private theorem gaussianLiftEnergyWeight_eq (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) (hS : gaussianLiftCapturedEnergy P G ≠ 0)
    (hW : IsUnit (gaussianLiftProjectedGram P G).det) :
    gaussianLiftEnergyWeight P G = gaussianLiftCapturedEnergy P G * gaussianLiftCrossTrace P G := by
  let a := Units.mk0 (gaussianLiftCapturedEnergy P G)⁻¹ (inv_ne_zero hS)
  have he := Matrix.inv_smul' (A := gaussianLiftProjectedGram P G) a hW
  change ((gaussianLiftCapturedEnergy P G)⁻¹ • gaussianLiftProjectedGram P G)⁻¹ =
    ((gaussianLiftCapturedEnergy P G)⁻¹)⁻¹ • (gaussianLiftProjectedGram P G)⁻¹ at he
  unfold gaussianLiftEnergyWeight gaussianLiftCrossTrace
  rw [he, inv_inv, Matrix.smul_mul, Matrix.trace_smul]
  rfl

private theorem gaussianLiftCrossTrace_nonneg (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ gaussianLiftCrossTrace P G := by
  let M := (1 - P.val) * G
  let A := (gaussianLiftProjectedGram P G)⁻¹
  have hA : A.PosSemidef := by
    unfold A
    rw [gaussianLiftProjectedGram_eq_gram]
    exact (gaussianGram_posSemidef _).inv
  unfold gaussianLiftCrossTrace
  rw [gaussianLiftComplementGram_eq_gram]
  change 0 ≤ (A * (Mᵀ * M)).trace
  rw [Matrix.trace_mul_comm A, Matrix.mul_assoc, Matrix.trace_mul_comm Mᵀ]
  have h := hA.mul_mul_conjTranspose_same M
  apply Matrix.PosSemidef.trace_nonneg
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using h

/-- The angular weight is independent of the chi-square energy. -/
theorem gaussianLiftEnergyWeight_indep_energy (hℓn : ℓ ≤ n) (h : 0 < k * ℓ)
    (P : OrthogonalProjector n ℓ) :
    IndepFun (gaussianLiftEnergyWeight (k := k) P) (gaussianLiftCapturedEnergy P)
      (gaussianMatrixLaw n k) :=
  (gaussianLift_normalizedGram_complement_indep_energy hℓn h P).comp
    measurable_trace_inv_mul measurable_id

private theorem ae_gaussianLiftProjectedGram_isUnit (hℓn : ℓ ≤ n) (hkℓ : k ≤ ℓ)
    (P : OrthogonalProjector n ℓ) :
    ∀ᵐ G ∂gaussianMatrixLaw n k, IsUnit (gaussianLiftProjectedGram P G).det :=
  (ae_gaussianMatrix_projectedGram_invertible hℓn hkℓ P.val P.property.1 P.property.2.1
    P.property.2.2).mono fun _ h => isUnit_iff_ne_zero.mpr h

/-- With a positive Gaussian energy, the polar inverse trace is the
rank plus an inverse-radius term with nonnegative angular weight. -/
theorem ae_gaussianLiftEnergy_decomposition (hℓn : ℓ ≤ n) (hkℓ : k ≤ ℓ)
    (h : 0 < k * ℓ) (P : OrthogonalProjector n ℓ) :
    ∀ᵐ G ∂gaussianMatrixLaw n k,
      0 ≤ gaussianLiftEnergyWeight P G ∧
      gaussianLiftPolarInverseTrace P G =
        (k : ℝ) + gaussianLiftEnergyWeight P G / gaussianLiftCapturedEnergy P G := by
  have hS : ∀ᵐ G ∂gaussianMatrixLaw n k, 0 < gaussianLiftCapturedEnergy P G := by
    apply ae_of_ae_map (measurable_gaussianLiftCapturedEnergy P).aemeasurable
    rw [gaussianLiftCapturedEnergy_law hℓn h P]
    exact ae_chiSquare_pos _
  filter_upwards [hS, ae_gaussianLiftProjectedGram_isUnit hℓn hkℓ P,
    ae_gaussianMatrix_injective (hkℓ.trans hℓn)] with G hS hW hG
  rw [gaussianLiftEnergyWeight_eq P G hS.ne' hW, gaussianLiftPolarInverseTrace_eq P G hG hW]
  refine ⟨mul_nonneg hS.le (gaussianLiftCrossTrace_nonneg P G), ?_⟩
  rw [mul_comm (gaussianLiftCapturedEnergy P G), mul_div_cancel_right₀ _ hS.ne']

/-- The exact mean that centers the polar inverse trace in the covariance. -/
theorem gaussianLiftPolarInverseTrace_mean (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (P : OrthogonalProjector n ℓ) :
    Integrable (gaussianLiftPolarInverseTrace (k := k) P) (gaussianMatrixLaw n k) ∧
      (∫ G, gaussianLiftPolarInverseTrace (k := k) P G ∂gaussianMatrixLaw n k) =
        (k : ℝ) * ((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1) := by
  let μ := gaussianMatrixLaw n k
  let g := gaussianLiftPolarInverseTrace (k := k) P
  let b := gaussianLiftCrossTrace (k := k) P
  have hMean := gaussianLiftCrossTrace_mean (k := k) hℓn hkℓ P
  have hG : g =ᵐ[μ] fun G => (k : ℝ) + b G := by
    filter_upwards [ae_gaussianLiftProjectedGram_isUnit hℓn (show k ≤ ℓ by omega) P,
      ae_gaussianMatrix_injective (show k ≤ n by omega)] with G hW hG
    exact gaussianLiftPolarInverseTrace_eq P G hG hW
  have hConst : Integrable (fun _ : Matrix (Fin n) (Fin k) ℝ => (k : ℝ)) μ := integrable_const _
  refine ⟨(hConst.add hMean.1).congr hG.symm, ?_⟩
  rw [integral_congr_ae hG, integral_add hConst hMean.1, hMean.2, integral_const]
  simp only [probReal_univ, one_smul]
  have hℓ : (k : ℝ) + 1 < ℓ := by exact_mod_cast hkℓ
  field_simp [show (ℓ : ℝ) - k - 1 ≠ 0 by linarith]
  ring

/-- The covariance numerator for the genuine Gaussian lift in Theorem 1.1.
The mixed integrand is integrable throughout the first inverse-moment regime. -/
theorem gaussianPolar_projectedInverseTrace_energy_covariance
    (hℓn : ℓ ≤ n) (hk : 0 < k) (hkℓ : k + 1 < ℓ)
    (P : OrthogonalProjector n ℓ) :
    let f := fun G : Matrix (Fin n) (Fin k) ℝ =>
      (((gaussianPolarFrame G)ᵀ * P.val * gaussianPolarFrame G)⁻¹.trace -
        (k : ℝ) * ((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1)) * (Gᵀ * P.val * G).trace
    Integrable f (gaussianMatrixLaw n k) ∧
      (∫ G, f G ∂gaussianMatrixLaw n k) =
        -(2 : ℝ) * k * ((n : ℝ) - ℓ) / ((ℓ : ℝ) - k - 1) := by
  let μ := gaussianMatrixLaw n k
  let S := gaussianLiftCapturedEnergy (k := k) P
  let b := gaussianLiftCrossTrace (k := k) P
  let B := gaussianLiftEnergyWeight (k := k) P
  let g := gaussianLiftPolarInverseTrace (k := k) P
  let d := k * ℓ
  let a : ℝ := (ℓ : ℝ) - k - 1
  let m : ℝ := (k : ℝ) * ((n : ℝ) - ℓ) / a
  let gbar : ℝ := (k : ℝ) * ((n : ℝ) - k - 1) / a
  let f := fun G => (g G - gbar) * S G
  have ha : 0 < a := by
    have ht : (k : ℝ) + 1 < ℓ := by exact_mod_cast hkℓ
    dsimp [a]
    linarith
  have hd : 2 < d := by
    calc
      2 < ℓ := by omega
      _ = 1 * ℓ := (one_mul ℓ).symm
      _ ≤ k * ℓ := Nat.mul_le_mul_right ℓ hk
  have hS : MeasurePreserving S μ (chiSquareLaw d) :=
    ⟨measurable_gaussianLiftCapturedEnergy P, gaussianLiftCapturedEnergy_law hℓn (by omega) P⟩
  have hSpos : ∀ᵐ G ∂μ, 0 < S G := by
    apply ae_of_ae_map hS.measurable.aemeasurable
    rw [hS.map_eq]
    exact ae_chiSquare_pos d
  have hSInt : Integrable S μ := hS.integrable_comp_of_integrable (chiSquare_mean (by omega : 0 < d)).1
  have hSMean : (∫ G, S G ∂μ) = (d : ℝ) := by
    have hmap := integral_map (μ := μ) hS.measurable.aemeasurable
      (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    rw [hS.map_eq, (chiSquare_mean (by omega : 0 < d)).2] at hmap
    exact hmap.symm
  have hSInvMean : (∫ G, (S G)⁻¹ ∂μ) = 1 / ((d : ℝ) - 2) := by
    have hmap := integral_map (μ := μ) hS.measurable.aemeasurable
      (f := fun x : ℝ => x⁻¹) measurable_id.inv.aestronglyMeasurable
    rw [hS.map_eq, (chiSquare_inverse_mean hd).2] at hmap
    exact hmap.symm
  have hRank : ∀ᵐ G ∂μ, IsUnit (gaussianLiftProjectedGram P G).det :=
    ae_gaussianLiftProjectedGram_isUnit hℓn (by omega) P
  have hbMean : Integrable b μ ∧ (∫ G, b G ∂μ) = m := gaussianLiftCrossTrace_mean hℓn hkℓ P
  have hWeight : ∀ᵐ G ∂μ, B G = S G * b G := by
    filter_upwards [hSpos, hRank] with G hPos hW
    exact gaussianLiftEnergyWeight_eq P G hPos.ne' hW
  have hSplit : (fun G => B G * (S G)⁻¹) =ᵐ[μ] b := by
    filter_upwards [hWeight, hSpos] with G hB hPos
    rw [hB, mul_comm (S G) (b G), mul_assoc, mul_inv_cancel₀ hPos.ne', mul_one]
  have hInd : IndepFun B (fun G => (S G)⁻¹) μ :=
    (gaussianLiftEnergyWeight_indep_energy hℓn (by omega) P).comp measurable_id measurable_id.inv
  have hBn : AEStronglyMeasurable B μ := (measurable_gaussianLiftEnergyWeight P).aestronglyMeasurable
  have hSn : AEStronglyMeasurable (fun G => (S G)⁻¹) μ := hS.measurable.inv.aestronglyMeasurable
  have hSNonzero : ¬(fun G => (S G)⁻¹) =ᵐ[μ] 0 := by
    intro h
    have h' : ∀ᵐ G ∂μ, (S G)⁻¹ ≠ 0 := hSpos.mono fun G hG => inv_ne_zero hG.ne'
    obtain ⟨G, hG₁, hG₂⟩ := (h.and h').exists
    exact hG₂ hG₁
  have hBInt : Integrable B μ := hInd.integrable_left_of_integrable_op
    (· * ·) 1 one_ne_zero (fun x y => by simp [enorm_mul])
    (hbMean.1.congr hSplit.symm) hBn hSn hSNonzero
  have hBMean : (∫ G, B G ∂μ) = ((d : ℝ) - 2) * m := by
    have hm : (∫ G, B G * (S G)⁻¹ ∂μ) = m :=
      (integral_congr_ae hSplit).trans hbMean.2
    rw [hInd.integral_fun_mul_eq_mul_integral hBn hSn, hSInvMean, mul_one_div] at hm
    have hd' : (2 : ℝ) < d := by exact_mod_cast hd
    exact (div_eq_iff (sub_ne_zero.mpr hd'.ne')).mp hm |>.trans (mul_comm _ _)
  have hgbar : gbar = (k : ℝ) + m := by
    dsimp [gbar, m, a] at *
    field_simp [ha.ne']
    ring
  have hf : f =ᵐ[μ] fun G => B G - m * S G := by
    filter_upwards [hRank, hWeight, ae_gaussianMatrix_injective (d := n) (k := k) (by omega)] with G hW hB hG
    have hg : g G = (k : ℝ) + b G := gaussianLiftPolarInverseTrace_eq P G hG hW
    change (g G - gbar) * S G = _
    rw [hg, hgbar, hB]
    ring
  change Integrable f μ ∧ (∫ G, f G ∂μ) = _
  refine ⟨(hBInt.sub (hSInt.const_mul m)).congr hf.symm, ?_⟩
  rw [integral_congr_ae hf, integral_sub hBInt (hSInt.const_mul m), integral_const_mul, hBMean, hSMean]
  dsimp [m, a]
  ring

end

end SketchOrientation
