import SketchOrientation.GaussianPolarTrace
import SketchOrientation.GaussianProjectedGram
import SketchOrientation.GaussianProductConditional

namespace SketchOrientation

open MeasureTheory Matrix
open scoped ENNReal

variable {n k ℓ : ℕ}

theorem measurable_matrix_product {d k p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix (Fin d) (Fin k) ℝ} {B : Ω → Matrix (Fin k) (Fin p) ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun ξ => A ξ * B ξ) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun a _ =>
    ((continuous_id.matrix_elem i a).measurable.comp hA).mul
      ((continuous_id.matrix_elem a j).measurable.comp hB)

theorem measurable_matrix_transpose {d p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix (Fin d) (Fin p) ℝ} (hA : Measurable A) :
    Measurable (fun ξ => (A ξ)ᵀ) :=
  (show Continuous (fun M : Matrix (Fin d) (Fin p) ℝ => Mᵀ) from
    continuous_id.matrix_transpose).measurable.comp hA

theorem measurable_matrix_trace {p : ℕ} :
    Measurable (fun A : Matrix (Fin p) (Fin p) ℝ => A.trace) := by
  simp_rw [Matrix.trace, Matrix.diag_apply]
  exact Finset.measurable_sum _ fun i _ => (continuous_id.matrix_elem i i).measurable

theorem posSemidef_nonsingInverse {p : ℕ} {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.PosSemidef) :
    A⁻¹.PosSemidef := by
  by_cases h : A.det = 0
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [h])]
    exact Matrix.PosSemidef.zero
  · exact (hA.posDef_iff_det_ne_zero.mpr h).inv.posSemidef

/-- Projected inverse Gram trace as a function of the sketch and Gaussian draw. -/
noncomputable def gaussianProjectedInverseTrace
    (p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  (p.2ᵀ * p.1 * p.2)⁻¹.trace

theorem measurable_gaussianProjectedInverseTrace :
    Measurable (@gaussianProjectedInverseTrace n k) :=
  measurable_matrix_trace.comp (measurable_matrix_nonsing_inv.comp
    (measurable_matrix_product (measurable_matrix_product
      (measurable_matrix_transpose measurable_snd) measurable_fst) measurable_snd))

theorem gaussianProjectedInverseTrace_nonneg
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P) (hr : P.rank = ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ gaussianProjectedInverseTrace (P, G) := by
  obtain ⟨U, _, hU⟩ := exists_frame_of_projector P hs hi hr
  have he : Gᵀ * P * G = gaussianGram (Uᵀ * G) := by
    unfold gaussianGram
    rw [← hU, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
  change 0 ≤ (Gᵀ * P * G)⁻¹.trace
  rw [he]
  exact (posSemidef_nonsingInverse (gaussianGram_posSemidef _)).trace_nonneg

/-- Joint integrability for a measurable field of rank-ℓ sketch projectors. -/
theorem integrable_gaussianProjectedInverseTrace_comp (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (P : Ω → Matrix (Fin n) (Fin n) ℝ) (hP : Measurable P)
    (hν : ∀ᵐ ω ∂ν, (P ω)ᵀ = P ω ∧ P ω * P ω = P ω ∧ (P ω).rank = ℓ) :
    Integrable (gaussianProjectedInverseTrace ∘ Prod.map P id)
      (ν.prod (gaussianMatrixLaw n k)) := by
  apply (integrable_prod_iff
    (measurable_gaussianProjectedInverseTrace.comp (hP.prodMap measurable_id)).aestronglyMeasurable).2
  refine ⟨?_, ?_⟩
  · filter_upwards [hν] with ω hω
    exact (gaussianMatrix_projectedGram_inv_trace_mean hℓn hkℓ (P ω) hω.1 hω.2.1 hω.2.2).1
  · refine (integrable_const ((k : ℝ) / ((ℓ : ℝ) - k - 1))).congr ?_
    filter_upwards [hν] with ω hω
    have h0 (G : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ gaussianProjectedInverseTrace (P ω, G) :=
      gaussianProjectedInverseTrace_nonneg (P ω) hω.1 hω.2.1 hω.2.2 G
    change (k : ℝ) / ((ℓ : ℝ) - k - 1) = ∫ G, ‖gaussianProjectedInverseTrace (P ω, G)‖
      ∂gaussianMatrixLaw n k
    simp only [Real.norm_of_nonneg (h0 _)]
    exact (gaussianMatrix_projectedGram_inv_trace_mean hℓn hkℓ (P ω) hω.1 hω.2.1 hω.2.2).2.symm

/-- Joint integrability for every law supported on rank-ℓ projectors. -/
theorem integrable_gaussianProjectedInverseTrace (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (ν : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ P ∂ν, Pᵀ = P ∧ P * P = P ∧ P.rank = ℓ) :
    Integrable (@gaussianProjectedInverseTrace n k) (ν.prod (gaussianMatrixLaw n k)) :=
  integrable_gaussianProjectedInverseTrace_comp hℓn hkℓ ν id measurable_id hν

/-- Equivalent observation pair of sketch and Gaussian polar frame. -/
noncomputable def gaussianPolarSketchObservation (p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin k) ℝ) :=
  (p.1, gaussianPolarFrame p.2)

private theorem measurable_gaussianPolarSketchObservation :
    Measurable (@gaussianPolarSketchObservation n k) :=
  measurable_fst.prodMk (measurable_gaussianPolarFrame.comp measurable_snd)

set_option maxHeartbeats 1000000 in
/-- Exact radial conditioning identity from Section 2.4. -/
theorem gaussianPolar_projectedInverseTrace_condExp_comp (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (P : Ω → Matrix (Fin n) (Fin n) ℝ) (hP : Measurable P)
    (hν : ∀ᵐ ω ∂ν, (P ω)ᵀ = P ω ∧ P ω * P ω = P ω ∧ (P ω).rank = ℓ) :
    let μ := ν.prod (gaussianMatrixLaw n k)
    μ[(gaussianProjectedInverseTrace ∘ Prod.map P id) |
      MeasurableSpace.comap (Prod.map id gaussianPolarFrame) inferInstance] =ᵐ[μ]
      (fun p =>
        ((gaussianPolarFrame p.2)ᵀ * P p.1 * gaussianPolarFrame p.2)⁻¹.trace / ((n : ℝ) - k - 1)) := by
  let μ := ν.prod (gaussianMatrixLaw n k)
  let X : Ω × Matrix (Fin n) (Fin k) ℝ → Ω × Matrix (Fin n) (Fin k) ℝ :=
    Prod.map id gaussianPolarFrame
  let H := fun p : Ω × Matrix (Fin n) (Fin k) ℝ => gaussianPolarRadial p.2
  let η := gaussianRadialFactorLaw n k
  let B := fun G : Matrix (Fin n) (Fin k) ℝ => (gaussianPolarFrame G, gaussianPolarRadial G)
  let F := fun z : (Ω × Matrix (Fin n) (Fin k) ℝ) ×
      Matrix (Fin k) (Fin k) ℝ =>
    (((z.1.2ᵀ * P z.1.1 * z.1.2)⁻¹) * (z.2 * z.2)⁻¹).trace
  have hkN : k ≤ n := by omega
  have hn : k + 1 < n := by omega
  have hX : Measurable X := measurable_id.prodMap measurable_gaussianPolarFrame
  have hH : Measurable H := continuous_gaussianPolarRadial.measurable.comp measurable_snd
  have hB : Measurable B := measurable_gaussianPolarFrame.prodMk continuous_gaussianPolarRadial.measurable
  have hF : Measurable F := by
    apply measurable_matrix_trace.comp
    apply measurable_matrix_product
    · exact measurable_matrix_nonsing_inv.comp (measurable_matrix_product
        (measurable_matrix_product
          (measurable_matrix_transpose (measurable_snd.comp measurable_fst))
          (hP.comp (measurable_fst.comp measurable_fst)))
        (measurable_snd.comp measurable_fst))
    · exact measurable_matrix_nonsing_inv.comp (measurable_matrix_product measurable_snd measurable_snd)
  have hXM : μ.map X = ν.prod (gaussianHaarFrameLaw hkN) := by
    change μ.map (Prod.map id gaussianPolarFrame) = _
    rw [← Measure.map_prod_map _ _ measurable_id measurable_gaussianPolarFrame, Measure.map_id,
      gaussianPolarFrameLaw_eq_haar hkN]
  have hProd : μ.map (fun p => (X p, H p)) = (μ.map X).prod η := by
    rw [hXM]
    let e := MeasurableEquiv.prodAssoc (α := Ω)
      (β := Matrix (Fin n) (Fin k) ℝ) (γ := Matrix (Fin k) (Fin k) ℝ)
    change μ.map (e.symm ∘ Prod.map id B) = _
    rw [← Measure.map_map e.symm.measurable (measurable_id.prodMap hB),
      ← Measure.map_prod_map _ _ measurable_id hB, Measure.map_id, gaussianPolarLaw_eq_prod hkN]
    exact (measurePreserving_prodAssoc ν (gaussianHaarFrameLaw hkN) η).symm.map_eq
  have he : gaussianProjectedInverseTrace ∘ Prod.map P id =ᵐ[μ] fun p => F (X p, H p) := by
    have hfull := (measurePreserving_snd (μ := ν) (ν := gaussianMatrixLaw n k)).quasiMeasurePreserving.ae
      (ae_gaussianMatrix_injective hkN)
    filter_upwards [hfull] with p hp
    exact gaussianPolar_inv_projectedGram_trace p.2 hp (P p.1)
  have hInt : Integrable (fun p => F (X p, H p)) μ :=
    (integrable_gaussianProjectedInverseTrace_comp hℓn hkℓ ν P hP hν).congr he
  change μ[(gaussianProjectedInverseTrace ∘ Prod.map P id) | MeasurableSpace.comap X inferInstance] =ᵐ[μ] _
  refine (condExp_congr_ae he).trans
    ((condExp_of_product_image μ η X H hX hH hProd F hF hInt).trans ?_)
  filter_upwards [] with p
  let A := ((gaussianPolarFrame p.2)ᵀ * P p.1 * gaussianPolarFrame p.2)⁻¹
  exact (gaussianPolarRadial_weightedInverse_mean (n := n) hn A).2

/-- Exact radial conditioning identity on the law of the sketch matrix. -/
theorem gaussianPolar_projectedInverseTrace_condExp (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (ν : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ P ∂ν, Pᵀ = P ∧ P * P = P ∧ P.rank = ℓ) :
    let μ := ν.prod (gaussianMatrixLaw n k)
    μ[gaussianProjectedInverseTrace | MeasurableSpace.comap gaussianPolarSketchObservation inferInstance]
      =ᵐ[μ] (fun p =>
        ((gaussianPolarFrame p.2)ᵀ * p.1 * gaussianPolarFrame p.2)⁻¹.trace / ((n : ℝ) - k - 1)) :=
  gaussianPolar_projectedInverseTrace_condExp_comp hℓn hkℓ ν id measurable_id hν

end SketchOrientation
