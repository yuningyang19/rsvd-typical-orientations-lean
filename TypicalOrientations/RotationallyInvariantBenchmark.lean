import TypicalOrientations.PaperTheorems

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation

noncomputable section

variable {n k l : ℕ}

/-- The Haar sketch-projector law is invariant under every deterministic orthogonal rotation. -/
theorem haarSketchProjectorLaw_map_rotateProjector (hl : l ≤ n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    (haarSketchProjectorLaw hl).map (fun P => rotateProjector U P) =
      haarSketchProjectorLaw hl := by
  let R (P : OrthogonalProjector n l) := rotateProjector U P
  let L (V : Matrix (Fin n) (Fin l) ℝ) := U * V
  have hR : Measurable R := measurable_rotateProjector.comp
    (measurable_const.prodMk measurable_id)
  have hL : Measurable L := (continuous_const.matrix_mul continuous_id).measurable
  calc
    _ = ((gaussianHaarFrameLaw hl).map L).map (haarFrameProjector hl) := by
      change (haarSketchProjectorLaw hl).map R = _
      rw [haarSketchProjectorLaw, Measure.map_map hR (measurable_haarFrameProjector hl),
        Measure.map_map (measurable_haarFrameProjector hl) hL]
      apply Measure.map_congr
      filter_upwards [ae_gaussianHaarFrame_orthonormal hl] with V hV
      have hUV : (U * V)ᵀ * (U * V) = 1 := by
        rw [transpose_mul, Matrix.mul_assoc Vᵀ Uᵀ, ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, hV]
      change rotateProjector U (haarFrameProjector hl V) = haarFrameProjector hl (U * V)
      apply Subtype.ext
      rw [rotateProjector_val U hU, haarFrameProjector_val hl hV, haarFrameProjector_val hl hUV,
        transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [show (gaussianHaarFrameLaw hl).map L = gaussianHaarFrameLaw hl from
        gaussianHaarFrameLaw_map_left hl U hU]
      rfl

/-- A Gaussian sketch has the same conditional mean at every orthogonal orientation. -/
theorem conditionalMean_haarSketchProjector_eq_gaussianMean (hl : l ≤ n) (k : ℕ)
    (σ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    conditionalMean k σ (haarSketchProjectorLaw hl) U = gaussianMean k l σ := by
  let ν := haarSketchProjectorLaw hl
  let R (P : OrthogonalProjector n l) := rotateProjector U P
  let loss := subspaceLoss (l := l) k σ
  have hR : Measurable R := measurable_rotateProjector.comp
    (measurable_const.prodMk measurable_id)
  have hL : Measurable loss := measurable_subspaceLoss k σ
  rw [gaussianMean_eq_haarProjector hl]
  calc
    _ = ∫ P, loss (R P) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun P => (subspaceLoss_rotated_eq U hU P k σ).symm)
    _ = ∫ P, loss P ∂ν.map R := (integral_map hR.aemeasurable hL.aestronglyMeasurable).symm
    _ = _ := by rw [show ν.map R = ν from haarSketchProjectorLaw_map_rotateProjector hl U hU]

/-- The discrepancy is exactly zero for the fixed-width or growing-width
Gaussian benchmark law, including the square case. -/
theorem meanDiscrepancy_haarSketchProjector_eq_zero (hl : l ≤ n) (k : ℕ) :
    meanDiscrepancy k (haarSketchProjectorLaw hl) = 0 := by
  have hZero (σ : Spectra n k) :
      (∫ U, |conditionalMean k σ.val (haarSketchProjectorLaw hl) U - gaussianMean k l σ.val|
        ∂gaussianRightOrthogonalLaw n) = 0 := by
    calc
      _ = ∫ _ : Matrix (Fin n) (Fin n) ℝ, (0 : ℝ) ∂gaussianRightOrthogonalLaw n := by
        apply integral_congr_ae
        filter_upwards [ae_gaussianRightOrthogonal n] with U hU
        simp [conditionalMean_haarSketchProjector_eq_gaussianMean hl k σ.val U hU]
      _ = _ := integral_zero _ _
  unfold meanDiscrepancy
  simp only [hZero]
  by_cases h : Nonempty (Spectra n k)
  · let := h
    rw [Set.range_const, csSup_singleton]
  · let : IsEmpty (Spectra n k) := not_nonempty_iff.mp h
    rw [Set.range_eq_empty, Real.sSup_empty]

/-- The Gaussian matrix sketch induces exactly the Haar probability law
on rank-l range projectors. -/
theorem fullRankSketchLaw_gaussian_eq_haarSketchProjector (hl : l ≤ n) :
    fullRankSketchLaw hl (gaussianMatrixLaw n l) = haarSketchProjectorLaw hl := by
  rw [fullRankSketchLaw, haarSketchProjectorLaw, ← gaussianPolarFrameLaw_eq_haar hl,
    Measure.map_map (measurable_haarFrameProjector hl) measurable_gaussianPolarFrame]
  apply Measure.map_congr
  filter_upwards [ae_gaussianMatrix_injective hl] with G hG
  let V := gaussianPolarFrame G
  let H := gaussianPolarRadial G
  have hV : Vᵀ * V = 1 := gaussianPolarFrame_transpose_mul_self G hG
  have hD : (Gᵀ * G).det ≠ 0 := (gaussianGram_det_ne_zero_iff G).2 hG
  have hI : IsUnit H.det := gaussianPolarRadial_det_isUnit G hG
  have hSurj : Function.Surjective H.toEuclideanLin := by
    intro x
    refine ⟨H⁻¹.toEuclideanLin x, ?_⟩
    change (H.toEuclideanLin.comp H⁻¹.toEuclideanLin) x = x
    rw [← euclidean_mul, Matrix.mul_nonsing_inv _ hI]
    simp
  change fullRankColumnProjector hl G = haarFrameProjector hl V
  apply Subtype.ext
  rw [fullRankColumnProjector_val hl G hD, haarFrameProjector_val hl hV,
    ← rangeProjector_of_frame V hV]
  apply rangeProjector_eq_of_range_eq
  have hGH : V * H = G := gaussianPolarFrame_mul_radial G hG
  rw [← hGH, euclidean_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hSurj,
    Submodule.map_top]

theorem conditionalMean_gaussianSketch_eq_gaussianMean (hl : l ≤ n) (k : ℕ)
    (σ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    conditionalMean k σ (fullRankSketchLaw hl (gaussianMatrixLaw n l)) U =
      gaussianMean k l σ := by
  rw [fullRankSketchLaw_gaussian_eq_haarSketchProjector hl,
    conditionalMean_haarSketchProjector_eq_gaussianMean hl k σ U hU]

theorem meanDiscrepancy_gaussianSketch_eq_zero (hl : l ≤ n) (k : ℕ) :
    meanDiscrepancy k (fullRankSketchLaw hl (gaussianMatrixLaw n l)) = 0 := by
  rw [fullRankSketchLaw_gaussian_eq_haarSketchProjector hl,
    meanDiscrepancy_haarSketchProjector_eq_zero hl k]

/-- The same Gaussian law has diffuseness l/n, even at growing width. -/
theorem meanProjectorNorm_gaussianSketch (hn : 0 < n) (hl : l ≤ n) :
    meanProjectorNorm (fullRankSketchLaw hl (gaussianMatrixLaw n l)) = (l : ℝ) / n := by
  rw [fullRankSketchLaw_gaussian_eq_haarSketchProjector hl]
  let ν := haarSketchProjectorLaw hl
  have hInv (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
      (ν.map fun P => U * P.val * Uᵀ) = ν.map Subtype.val := by
    have hR : Measurable (fun P : OrthogonalProjector n l => rotateProjector U P) :=
      measurable_rotateProjector.comp (measurable_const.prodMk measurable_id)
    have h := congrArg (Measure.map (Subtype.val : OrthogonalProjector n l → _))
      (haarSketchProjectorLaw_map_rotateProjector hl U hU)
    rw [Measure.map_map measurable_subtype_coe hR] at h
    have he : (Subtype.val : OrthogonalProjector n l → _) ∘ (fun P => rotateProjector U P) =
        (fun P => U * P.val * Uᵀ) := funext (rotateProjector_val U hU)
    rw [he] at h
    exact h
  apply meanSketchProjector_norm_of_isotropic hn
  apply meanSketchProjector_of_signed_permutation_symmetry hn
  · intro s hs
    apply hInv
    rw [diagonal_transpose, diagonal_mul_diagonal]
    congr 1
    funext i
    rcases hs i with hi | hi <;> simp [hi]
  · intro π
    apply hInv
    rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

end

end TypicalOrientations
