import SketchOrientation.GaussianGramMoments

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix

variable {d k : ℕ}

private def gramSign (j i : Fin k) : ℝ := if i = j then -1 else 1

private def gramSignMatrix (j : Fin k) : Matrix (Fin k) (Fin k) ℝ := diagonal (gramSign j)

private theorem gramSignMatrix_mul_self (j : Fin k) :
    gramSignMatrix j * gramSignMatrix j = 1 := by
  unfold gramSignMatrix
  rw [diagonal_mul_diagonal]
  have h : (fun i => gramSign j i * gramSign j i) = fun _ => (1 : ℝ) := by
    funext i
    by_cases hi : i = j <;> norm_num [gramSign, hi]
  rw [h, diagonal_one]

private theorem gramSignMatrix_inv (j : Fin k) :
    (gramSignMatrix j)⁻¹ = gramSignMatrix j := by
  exact Matrix.inv_eq_left_inv (gramSignMatrix_mul_self j)

private theorem gaussianMatrixLaw_map_flipColumn (j : Fin k) :
    (gaussianMatrixLaw d k).map (fun Z => Z * gramSignMatrix j) = gaussianMatrixLaw d k := by
  let E := EuclideanSpace ℝ (Fin d)
  let f : Fin k → E → E := fun i x => if i = j then -x else x
  have hF : MeasurePreserving (fun (X : Fin k → E) i => f i (X i))
      (gaussianColumnLaw d k) (gaussianColumnLaw d k) := by
    apply measurePreserving_pi
    intro i
    by_cases hi : i = j
    · simpa [f, hi] using
        (show MeasurePreserving (LinearIsometryEquiv.neg ℝ (E := E))
          (stdGaussian E) (stdGaussian E) from
          ⟨(LinearIsometryEquiv.neg ℝ (E := E)).continuous.measurable, stdGaussian_map _⟩)
    · simp only [f, if_neg hi]
      exact MeasurePreserving.id (stdGaussian E)
  have hg : Measurable (fun Z : Matrix (Fin d) (Fin k) ℝ => Z * gramSignMatrix j) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have heq : (fun Z : Matrix (Fin d) (Fin k) ℝ => Z * gramSignMatrix j) ∘ matrixOfGaussianColumns =
      matrixOfGaussianColumns ∘ fun (X : Fin k → E) i => f i (X i) := by
    funext X
    ext a i
    simp only [Function.comp_apply, gramSignMatrix, mul_diagonal, matrixOfGaussianColumns, of_apply]
    by_cases hi : i = j
    · simp [f, gramSign, hi]
      rfl
    · simp [f, gramSign, hi]
  unfold gaussianMatrixLaw
  rw [Measure.map_map hg measurable_matrixOfGaussianColumns, heq,
    ← Measure.map_map measurable_matrixOfGaussianColumns hF.measurable, hF.map_eq]

private theorem gaussianGram_inv_flipColumn (Z : Matrix (Fin d) (Fin k) ℝ)
    {i j : Fin k} (hij : j ≠ i) :
    (gaussianGram (Z * gramSignMatrix i))⁻¹ i j = -(gaussianGram Z)⁻¹ i j := by
  have hT : (gramSignMatrix i)ᵀ = gramSignMatrix i := diagonal_transpose _
  unfold gaussianGram
  rw [transpose_mul, hT, ← Matrix.mul_assoc, Matrix.mul_assoc (gramSignMatrix i) Zᵀ Z,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev, gramSignMatrix_inv]
  simp [gramSignMatrix, diagonal_mul, mul_diagonal, gramSign, hij]

private theorem abs_entry_le_half_diagonal_sum {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) {i j : Fin k} :
    |A i j| ≤ (A i i + A j j) / 2 := by
  have hs : A j i = A i j := by simpa using hA.1.apply i j
  have hplus := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hminus := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_single_one,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, single_dotProduct,
    one_mul, col_apply, hs] at hplus hminus
  rw [abs_le]
  constructor <;> linarith

private theorem integrable_gaussianGram_inv_entry (hdk : k + 1 < d) (i j : Fin k) :
    Integrable (fun Z => (gaussianGram Z)⁻¹ i j) (gaussianMatrixLaw d k) := by
  have hbound := ((gaussianGram_inv_diag_mean hdk i).1.add
    (gaussianGram_inv_diag_mean hdk j).1).div_const (2 : ℝ)
  refine hbound.mono' (measurable_gaussianGram_inv_entry i j).aestronglyMeasurable ?_
  filter_upwards [ae_gaussianMatrix_injective (d := d) (k := k) (by omega)] with Z hZ
  simpa [Real.norm_eq_abs] using
    (abs_entry_le_half_diagonal_sum (gaussianGram_posDef Z hZ).inv.posSemidef (i := i) (j := j))

/-- Entrywise inverse Wishart mean under the primitive iid Gaussian matrix law. -/
theorem gaussianGram_inv_mean (hdk : k + 1 < d) (i j : Fin k) :
    Integrable (fun Z => (gaussianGram Z)⁻¹ i j) (gaussianMatrixLaw d k) ∧
      (∫ Z, (gaussianGram Z)⁻¹ i j ∂gaussianMatrixLaw d k) =
        (1 : Matrix (Fin k) (Fin k) ℝ) i j / ((d : ℝ) - k - 1) := by
  refine ⟨integrable_gaussianGram_inv_entry hdk i j, ?_⟩
  by_cases hij : j = i
  · subst j
    simpa using (gaussianGram_inv_diag_mean hdk i).2
  · have hm : Measurable (fun Z : Matrix (Fin d) (Fin k) ℝ => Z * gramSignMatrix i) :=
      (continuous_id.matrix_mul continuous_const).measurable
    have hf : Measurable (fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z)⁻¹ i j) :=
      measurable_gaussianGram_inv_entry i j
    have heq := integral_map (μ := gaussianMatrixLaw d k) hm.aemeasurable hf.aestronglyMeasurable
    rw [gaussianMatrixLaw_map_flipColumn i] at heq
    simp_rw [gaussianGram_inv_flipColumn _ hij] at heq
    rw [integral_neg] at heq
    rw [Matrix.one_apply_ne (Ne.symm hij), zero_div]
    linarith

end SketchOrientation
