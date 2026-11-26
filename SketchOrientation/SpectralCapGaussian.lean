import SketchOrientation.SpectralCap
import SketchOrientation.GaussianGramMoments

/-! Proposition 6.1 for weak convergence of the paper's rectangular block to the actual
standard-Gaussian law. -/

namespace SketchOrientation

open Edge Filter Matrix MeasureTheory Topology

variable {k ℓ p : ℕ}

private theorem measurable_real_matrix_transpose {m n : ℕ} :
    Measurable (fun Z : Matrix (Fin n) (Fin m) ℝ ↦ Zᵀ) :=
  continuous_id.matrix_transpose.measurable

/-- Law of the real `k × ℓ` block of independent standard Gaussian entries. -/
noncomputable def gaussianRowBlock (k ℓ : ℕ) : ProbabilityMeasure (Matrix (Fin k) (Fin ℓ) ℝ) :=
  ⟨(gaussianMatrixLaw ℓ k).map Matrix.transpose,
    Measure.isProbabilityMeasure_map measurable_real_matrix_transpose.aemeasurable⟩

theorem ae_gaussianRowBlock_gramEigenvalues_pos (hkℓ : k ≤ ℓ) :
    ∀ᵐ B ∂(gaussianRowBlock k ℓ : Measure (Matrix (Fin k) (Fin ℓ) ℝ)),
      ∀ j, 0 < gramEigenvalues B j := by
  simp only [ae_all_iff]
  intro j
  change ∀ᵐ B ∂(gaussianMatrixLaw ℓ k).map Matrix.transpose, 0 < gramEigenvalues B j
  have hm : MeasurableSet {B : Matrix (Fin k) (Fin ℓ) ℝ | 0 < gramEigenvalues B j} :=
    measurableSet_lt measurable_const ((continuous_apply j).comp continuous_gramEigenvalues).measurable
  rw [ae_map_iff measurable_real_matrix_transpose.aemeasurable hm]
  filter_upwards [ae_gaussianMatrix_injective hkℓ] with Z hZ
  have hpos : (Zᵀ * (Zᵀ)ᵀ).PosDef := by
    simpa only [gaussianGram, Matrix.transpose_transpose] using gaussianGram_posDef Z hZ
  exact orderedEigenvaluesFin_pos hpos j

private theorem measurable_real_rowGram_inv_trace :
    Measurable (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ ((B * Bᵀ)⁻¹).trace) := by
  have hm : Measurable (fun Z : Matrix (Fin ℓ) (Fin k) ℝ ↦ ((gaussianGram Z)⁻¹).trace) :=
    Finset.measurable_sum _ fun j _ ↦ measurable_gaussianGram_inv_entry j j
  have he : (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ ((B * Bᵀ)⁻¹).trace) =
      (fun Z : Matrix (Fin ℓ) (Fin k) ℝ ↦ ((gaussianGram Z)⁻¹).trace) ∘ Matrix.transpose := by
    funext B
    simp [gaussianGram]
  rw [he]
  exact hm.comp measurable_real_matrix_transpose

/-- Mean inverse trace and integrability for a Gaussian row Gram matrix. -/
theorem gaussianRowBlock_inverseTraceMean (h : k + 1 < ℓ) :
    Integrable (fun B : Matrix (Fin k) (Fin ℓ) ℝ ↦ ((B * Bᵀ)⁻¹).trace)
      (gaussianRowBlock k ℓ : Measure (Matrix (Fin k) (Fin ℓ) ℝ)) ∧
    (∫ B : Matrix (Fin k) (Fin ℓ) ℝ, ((B * Bᵀ)⁻¹).trace
      ∂(gaussianRowBlock k ℓ : Measure (Matrix (Fin k) (Fin ℓ) ℝ))) =
        (k : ℝ) / ((ℓ : ℝ) - k - 1) := by
  have hm := measurable_real_rowGram_inv_trace (k := k) (ℓ := ℓ)
  change Integrable _ ((gaussianMatrixLaw ℓ k).map Matrix.transpose) ∧
    (∫ B : Matrix (Fin k) (Fin ℓ) ℝ, ((B * Bᵀ)⁻¹).trace
      ∂((gaussianMatrixLaw ℓ k).map Matrix.transpose)) = _
  obtain ⟨hi, he⟩ := gaussianGram_inv_trace_mean h
  constructor
  · rw [integrable_map_measure hm.aestronglyMeasurable
      measurable_real_matrix_transpose.aemeasurable]
    simpa only [Function.comp_def, Matrix.transpose_transpose, gaussianGram] using hi
  · rw [integral_map measurable_real_matrix_transpose.aemeasurable hm.aestronglyMeasurable]
    simpa only [Matrix.transpose_transpose, gaussianGram] using he

private theorem gaussianRowBlock_inverseMean (hk : 0 < k) (hp : 2 ≤ p) :
    (∀ j, Integrable (fun B ↦ (gramEigenvalues B j)⁻¹)
      (gaussianRowBlock k (k + p) : Measure (Matrix (Fin k) (Fin (k + p)) ℝ))) ∧
    inverseMean (gaussianRowBlock k (k + p)) (fun j B ↦ gramEigenvalues B j) 0 / k =
      1 / ((p : ℝ) - 1) := by
  obtain ⟨hi, hm⟩ := gaussianRowBlock_inverseTraceMean (k := k) (ℓ := k + p) (by omega)
  obtain ⟨hin, he⟩ := rowBlockInverseMean_eq_integral_trace _
    (ae_gaussianRowBlock_gramEigenvalues_pos (by omega)) hi
  constructor
  · exact hin
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hd : ((k + p : ℕ) : ℝ) - k - 1 = (p : ℝ) - 1 := by push_cast; ring
    rw [he, hm, hd, div_right_comm, div_self hk'.ne']

/-- Proposition 6.1 at a prescribed diverging finite gap. The cutoff tests
`σ_min(Bₙ)^2 ≤ t` even for rank-deficient sketches. -/
theorem proposition_6_1_prescribedGap
    {μ : ℕ → ProbabilityMeasure (Matrix (Fin k) (Fin (k + p)) ℝ)}
    (hk : 0 < k) (hp : 2 ≤ p) (hμ : Tendsto μ atTop (𝓝 (gaussianRowBlock k (k + p))))
    {n L : ℕ → ℝ} (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop atTop) :
    Tendsto (fun j ↦ rowBlockExpectedLoss (μ j) (n j) (L j)) atTop
      (𝓝 (1 / ((p : ℝ) - 1))) ↔
      RowBlockVanishingCap μ hk (fun j ↦ gapRegularizer (n j) k (L j)) := by
  obtain ⟨hi, he⟩ := gaussianRowBlock_inverseMean hk hp
  have hpos := ae_gaussianRowBlock_gramEigenvalues_pos (k := k) (ℓ := k + p) (by omega)
  rw [← he]
  exact tendsto_rowBlockExpectedLoss_iff hμ hk (fun j ↦ hpos.mono fun _ h ↦ h j) hi hn hL

/-- Proposition 6.1 for every diverging finite gap with the same sequence of block laws. -/
theorem proposition_6_1_allGaps
    {μ : ℕ → ProbabilityMeasure (Matrix (Fin k) (Fin (k + p)) ℝ)}
    (hk : 0 < k) (hp : 2 ≤ p) (hμ : Tendsto μ atTop (𝓝 (gaussianRowBlock k (k + p))))
    {n : ℕ → ℝ} (hn : Tendsto n atTop atTop) :
    (∀ L : ℕ → ℝ, Tendsto L atTop atTop →
      Tendsto (fun j ↦ rowBlockExpectedLoss (μ j) (n j) (L j)) atTop
        (𝓝 (1 / ((p : ℝ) - 1)))) ↔
      RowBlockVanishingCap μ hk (fun _ ↦ 0) := by
  obtain ⟨hi, he⟩ := gaussianRowBlock_inverseMean hk hp
  have hpos := ae_gaussianRowBlock_gramEigenvalues_pos (k := k) (ℓ := k + p) (by omega)
  rw [← he]
  exact tendsto_rowBlockExpectedLoss_for_all_iff hμ hk (fun j ↦ hpos.mono fun _ h ↦ h j) hi hn

end SketchOrientation
