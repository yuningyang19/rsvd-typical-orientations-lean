import TypicalOrientations.PaperConsequences
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {n k l : ℕ}

/-- Flip a coin of bias α to choose the first block or the uniform block law. -/
def firstBlockMixture (α : ℝ) (μ : Measure (OrthogonalProjector n l))
    (P₀ : OrthogonalProjector n l) : Measure (OrthogonalProjector n l) :=
  ENNReal.ofReal (1 - α) • μ + ENNReal.ofReal α • Measure.dirac P₀

theorem isProbabilityMeasure_firstBlockMixture
    {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (P₀ : OrthogonalProjector n l) : IsProbabilityMeasure (firstBlockMixture α μ P₀) := by
  constructor
  simp only [firstBlockMixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hα₁) hα, sub_add_cancel, ENNReal.ofReal_one]

private theorem integral_firstBlockMixture (μ : Measure (OrthogonalProjector n l))
    (P₀ : OrthogonalProjector n l) {f : OrthogonalProjector n l → ℝ}
    (hf : Integrable f μ) {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    (∫ P, f P ∂firstBlockMixture α μ P₀) = (1-α) * (∫ P, f P ∂μ) + α * f P₀ := by
  unfold firstBlockMixture
  have hdir : Integrable f (Measure.dirac P₀) := integrable_dirac (by simp)
  rw [integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
    (hdir.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hα₁), ENNReal.toReal_ofReal hα,
    integral_dirac]
  rfl

private theorem norm_scalar_identity_add_projector (P : OrthogonalProjector n l)
    (hl : 0 < l) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a • (1 : Matrix (Fin n) (Fin n) ℝ) + b • P.val)‖ = a + b := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) P.val
  let T := a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + b • L
  have hL (u : EuclideanSpace ℝ (Fin n)) : L u = (orientationRowSpace P).starProjection u :=
    (orientationRowSpace_starProjection P u).symm
  have hT (u : EuclideanSpace ℝ (Fin n)) : T u = a • u + b • L u := rfl
  rw [map_add, map_smul, map_smul, map_one]
  change ‖T‖ = a + b
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (add_nonneg ha hb) fun u => ?_) ?_
  · rw [hT]
    calc
      _ ≤ ‖a • u‖ + ‖b • L u‖ := norm_add_le _ _
      _ = a * ‖u‖ + b * ‖L u‖ := by
        simp [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ _ := by
        rw [add_mul, hL]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          ((orientationRowSpace P).norm_starProjection_apply_le u) hb)
  · have hP : P.val ≠ 0 := by
      intro h
      have hr := P.property.2.2
      rw [h, Matrix.rank_zero] at hr
      omega
    have hL₀ : L ≠ 0 := by
      intro h
      apply hP
      apply (Matrix.toEuclideanCLM (𝕜 := ℝ)).injective
      rw [map_zero]
      exact h
    obtain ⟨u, hu⟩ : ∃ u, L u ≠ 0 := by
      by_contra! h
      exact hL₀ (ContinuousLinearMap.ext h)
    have hLu : L (L u) = L u := by
      rw [hL]
      apply Submodule.starProjection_eq_self_iff.mpr
      rw [hL]
      exact (orientationRowSpace P).starProjection_apply_mem u
    have heval : T (L u) = (a + b) • L u := by rw [hT, hLu, add_smul]
    have hn : ‖T (L u)‖ = (a + b) * ‖L u‖ := by
      rw [heval, norm_smul, Real.norm_of_nonneg (add_nonneg ha hb)]
    have h := T.le_opNorm (L u)
    rw [hn] at h
    exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hu)

/-- Equation (4.2), with ℓ/n = 1/B for B equally sized blocks.
The input is any isotropic base law and actual positive-rank first block. -/
theorem blockMixture_meanProjectorNorm_and_conditionalMean
    {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hl : 0 < l)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (P₀ : OrthogonalProjector n l)
    (hμ : meanSketchProjector μ = ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (σ : Spectra n k) (U : Matrix (Fin n) (Fin n) ℝ) :
    meanProjectorNorm (firstBlockMixture α μ P₀) = α + (1-α) * ((l : ℝ) / n) ∧
    conditionalMean k σ.val (firstBlockMixture α μ P₀) U =
      (1-α) * conditionalMean k σ.val μ U +
        α * (squaredResidual (diagonal σ.val) (U * P₀.val) / optimalSquaredTail k σ.val) := by
  have hMean : meanSketchProjector (firstBlockMixture α μ P₀) =
      (1-α) • meanSketchProjector μ + α • P₀.val := by
    ext i j
    exact integral_firstBlockMixture μ P₀ (integrable_sketchProjector_entry μ i j) hα hα₁
  constructor
  · unfold meanProjectorNorm
    rw [hMean, hμ, smul_smul]
    change ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (((1-α) * ((l : ℝ) / n)) • (1 : Matrix (Fin n) (Fin n) ℝ) + α • P₀.val)‖ = _
    exact (norm_scalar_identity_add_projector P₀ hl
      (mul_nonneg (sub_nonneg.mpr hα₁) (by positivity)) hα).trans (add_comm _ _)
  · apply integral_firstBlockMixture μ P₀ _ hα hα₁
    let f (P : OrthogonalProjector n l) :=
      squaredResidual (diagonal σ.val) (U * P.val) / optimalSquaredTail k σ.val
    have hf : Measurable f :=
      (measurable_rawResidual measurable_const
        (measurable_matrix_product measurable_const measurable_subtype_coe)).div_const _
    refine Integrable.of_bound hf.aestronglyMeasurable
      (squaredFrobenius (diagonal σ.val) / optimalSquaredTail k σ.val) (ae_of_all _ fun P => ?_)
    rw [show ‖f P‖ = f P from Real.norm_of_nonneg
      (residual_div_tail_nonneg k σ.val σ.property.2.2 _)]
    exact residual_div_tail_le k σ.val σ.property.2.2 _

/-- Two conditionally independent replicates with the same conditional mean.
The conditional joint law given the common input is the product of their kernels. -/
theorem replicate_covariance_eq_conditionalMean_variance
    {A : Type*} [MeasurableSpace A] (η : Measure A) [IsProbabilityMeasure η]
    (κ₁ κ₂ : Kernel A ℝ) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
    (F : A → ℝ) (hF : MemLp F 2 η)
    (h₁ : ∀ᵐ a ∂η, (∫ y, y ∂κ₁ a) = F a)
    (h₂ : ∀ᵐ a ∂η, (∫ y, y ∂κ₂ a) = F a)
    (hY₁ : MemLp (fun z : A × (ℝ × ℝ) => z.2.1) 2 (η ⊗ₘ (κ₁ ×ₖ κ₂)))
    (hY₂ : MemLp (fun z : A × (ℝ × ℝ) => z.2.2) 2 (η ⊗ₘ (κ₁ ×ₖ κ₂))) :
    cov[fun z => z.2.1, fun z => z.2.2; η ⊗ₘ (κ₁ ×ₖ κ₂)] = Var[F; η] := by
  let μ := η ⊗ₘ (κ₁ ×ₖ κ₂)
  let Y₁ (z : A × (ℝ × ℝ)) := z.2.1
  let Y₂ (z : A × (ℝ × ℝ)) := z.2.2
  change cov[Y₁, Y₂; μ] = _
  rw [covariance_eq_sub hY₁ hY₂, variance_eq_sub hF]
  have e₁ : (∫ z, Y₁ z ∂μ) = ∫ a, F a ∂η := by
    rw [Measure.integral_compProd (hY₁.integrable (by norm_num))]
    apply integral_congr_ae
    filter_upwards [h₁] with a ha
    rw [Kernel.prod_apply]
    change (∫ z : ℝ × ℝ, z.1 ∂(κ₁ a).prod (κ₂ a)) = F a
    rw [integral_fun_fst (fun x : ℝ => x), probReal_univ, one_smul]
    exact ha
  have e₂ : (∫ z, Y₂ z ∂μ) = ∫ a, F a ∂η := by
    rw [Measure.integral_compProd (hY₂.integrable (by norm_num))]
    apply integral_congr_ae
    filter_upwards [h₂] with a ha
    rw [Kernel.prod_apply]
    change (∫ z : ℝ × ℝ, z.2 ∂(κ₁ a).prod (κ₂ a)) = F a
    rw [integral_fun_snd (fun x : ℝ => x), probReal_univ, one_smul]
    exact ha
  have e₁₂ : (∫ z, (Y₁ * Y₂) z ∂μ) = ∫ a, F a ^ 2 ∂η := by
    rw [Measure.integral_compProd (hY₁.integrable_mul hY₂)]
    apply integral_congr_ae
    filter_upwards [h₁, h₂] with a ha₁ ha₂
    rw [Kernel.prod_apply]
    change (∫ z : ℝ × ℝ, z.1 * z.2 ∂(κ₁ a).prod (κ₂ a)) = F a ^ 2
    rw [integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x), ha₁, ha₂, pow_two]
  rw [e₁, e₂, e₁₂]
  simp [pow_two]

end
end TypicalOrientations
