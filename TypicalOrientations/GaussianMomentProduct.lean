import TypicalOrientations.GaussianMomentDeterministic
import TypicalOrientations.GaussianMomentRows
import SketchOrientation.GaussianTailGram
import SketchOrientation.GaussianPolarConditional

namespace TypicalOrientations

open Matrix SketchOrientation MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {k ℓ m : ℕ}

/-- The leading block is stored transposed to use the Gaussian inverse Gram law. -/
abbrev gaussianSplitLaw (k ℓ m : ℕ) :
    Measure (Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin m) (Fin ℓ) ℝ) :=
  (gaussianMatrixLaw ℓ k).prod (gaussianMatrixLaw m ℓ)

/-- Squared Euclidean length of tail row (i) after multiplying by (B^\dagger). -/
def gaussianTailRowEnergy (i : Fin m)
    (w : Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin m) (Fin ℓ) ℝ) : ℝ :=
  ∑ j, (w.2 * leadingRightInverse w.1ᵀ) i j ^ 2

theorem gaussianTailRowEnergy_nonneg (i : Fin m)
    (w : Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin m) (Fin ℓ) ℝ) :
    0 ≤ gaussianTailRowEnergy i w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem measurable_leadingRightInverse_transpose :
    Measurable (fun B : Matrix (Fin ℓ) (Fin k) ℝ => leadingRightInverse Bᵀ) := by
  have hm : Measurable (fun B : Matrix (Fin ℓ) (Fin k) ℝ => gaussianGram B) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  simp only [leadingRightInverse, transpose_transpose]
  exact measurable_matrix_product measurable_id (measurable_matrix_nonsing_inv.comp hm)

theorem measurable_gaussianTailRowEnergy (i : Fin m) :
    Measurable (@gaussianTailRowEnergy k ℓ m i) := by
  have hp := measurable_matrix_product (measurable_snd (β := Matrix (Fin m) (Fin ℓ) ℝ))
    (measurable_leadingRightInverse_transpose (k := k) (ℓ := ℓ) |>.comp measurable_fst)
  exact Finset.measurable_sum _ fun j _ =>
    ((continuous_id.matrix_elem i j).measurable.comp hp).pow_const (2 : ℕ)

/-- The row map is a marginal of the independent Gaussian matrix law. -/
theorem gaussianMatrixLaw_row_measurePreserving (i : Fin m) :
    MeasurePreserving (fun Z : Matrix (Fin m) (Fin ℓ) ℝ => Z i)
      (gaussianMatrixLaw m ℓ) (gaussianRowLaw ℓ) := by
  rw [gaussianMatrixLaw_eq_row_product]
  exact measurePreserving_eval _ i

/-- All transformed tail rows have the same marginal law even though they
share the leading block. This makes the second step of (3.5) an equality. -/
theorem gaussianTailRowEnergy_identDistrib (i j : Fin m) :
    IdentDistrib (@gaussianTailRowEnergy k ℓ m i) (@gaussianTailRowEnergy k ℓ m j)
      (gaussianSplitLaw k ℓ m) (gaussianSplitLaw k ℓ m) := by
  let μ := gaussianSplitLaw k ℓ m
  let ν := (gaussianMatrixLaw ℓ k).prod (gaussianRowLaw ℓ)
  let g (x : Matrix (Fin ℓ) (Fin k) ℝ × (Fin ℓ → ℝ)) : ℝ :=
    ∑ j, (x.2 ᵥ* leadingRightInverse x.1ᵀ) j ^ 2
  have hg : Measurable g := by
    refine Finset.measurable_sum _ fun j _ => ?_
    change Measurable (fun x : Matrix (Fin ℓ) (Fin k) ℝ × (Fin ℓ → ℝ) =>
      (∑ t, x.2 t * leadingRightInverse x.1ᵀ t j) ^ (2 : ℕ))
    refine (Finset.measurable_sum _ fun t _ => ?_).pow_const _
    exact ((measurable_pi_apply t).comp measurable_snd).mul
      ((continuous_id.matrix_elem t j).measurable.comp
        (measurable_leadingRightInverse_transpose.comp measurable_fst))
  have hLaw (i : Fin m) : μ.map (gaussianTailRowEnergy i) = ν.map g := by
    let f := Prod.map (id : Matrix (Fin ℓ) (Fin k) ℝ → Matrix (Fin ℓ) (Fin k) ℝ)
      (fun Z : Matrix (Fin m) (Fin ℓ) ℝ => Z i)
    have hf : MeasurePreserving f μ ν :=
      (MeasurePreserving.id (gaussianMatrixLaw ℓ k)).prod
        (gaussianMatrixLaw_row_measurePreserving i)
    change μ.map (g ∘ f) = ν.map g
    rw [← Measure.map_map hg hf.measurable, hf.map_eq]
  exact ⟨(measurable_gaussianTailRowEnergy i).aemeasurable,
    (measurable_gaussianTailRowEnergy j).aemeasurable, (hLaw i).trans (hLaw j).symm⟩

/-- Paper's inverse-Wishart moment estimate with its unnormalized trace. -/
theorem gaussianLeading_inverse_trace_moment (hk : 0 < k) (hkl : k ≤ ℓ)
    {r : ℝ} (hr : 1 ≤ r) (hℓ : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    Integrable (fun B => (gaussianGram B)⁻¹.trace ^ r) (gaussianMatrixLaw ℓ k) ∧
    (∫ B, (gaussianGram B)⁻¹.trace ^ r ∂gaussianMatrixLaw ℓ k) ≤
      (k : ℝ) ^ r * chiSquareNegativeMoment (ℓ - k + 1) r := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := gaussianGram_inv_trace_moment hk hkl (zero_lt_one.trans_le hr) hℓ
  have he : (fun B => (gaussianGram B)⁻¹.trace ^ r) =ᵐ[gaussianMatrixLaw ℓ k]
      (fun B => (k : ℝ) ^ r * ((gaussianGram B)⁻¹.trace / k) ^ r) := by
    filter_upwards [ae_gaussianMatrix_injective hkl] with B hB
    have hp := (gaussianGram_posDef B hB).inv
    have hnn : 0 ≤ (gaussianGram B)⁻¹.trace :=
      Finset.sum_nonneg fun i _ => hp.diag_pos.le
    rw [← Real.mul_rpow hk'.le (div_nonneg hnn hk'.le),
      mul_div_cancel₀ (gaussianGram B)⁻¹.trace hk'.ne']
  refine ⟨(h.1.const_mul _).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hk'.le _)
  simpa only [if_pos hr, one_mul] using h.2

/-- The uniform bound on a single transformed tail row, obtained by
conditioning on the leading block and applying its inverse-Wishart bound. -/
theorem gaussianTailRowEnergy_moment (hk : 0 < k) (hkl : k ≤ ℓ) (i : Fin m)
    {r : ℝ} (hr : 1 ≤ r) (hℓ : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    Integrable (fun w => gaussianTailRowEnergy i w ^ r) (gaussianSplitLaw k ℓ m) ∧
    (∫ w, gaussianTailRowEnergy i w ^ r ∂gaussianSplitLaw k ℓ m) ≤
      (k : ℝ) ^ r * (standardNormalMoment r * chiSquareNegativeMoment (ℓ - k + 1) r) := by
  let f (w : Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin m) (Fin ℓ) ℝ) :=
    gaussianTailRowEnergy i w ^ r
  let μ := gaussianMatrixLaw ℓ k
  let ν := gaussianMatrixLaw m ℓ
  let g (B : Matrix (Fin ℓ) (Fin k) ℝ) := (gaussianGram B)⁻¹.trace ^ r * standardNormalMoment r
  have h := gaussianLeading_inverse_trace_moment hk hkl hr hℓ
  have hg : Integrable g μ := h.1.mul_const _
  have hf : Measurable f := (measurable_gaussianTailRowEnergy i).pow_const _
  have hC (B : Matrix (Fin ℓ) (Fin k) ℝ) :
      Integrable (fun Z => f (B, Z)) ν ∧
      (∫ Z, f (B, Z) ∂ν) ≤ (∑ j, ∑ x, leadingRightInverse Bᵀ x j ^ 2) ^ r *
        standardNormalMoment r := by
    let R := leadingRightInverse Bᵀ
    let G := fun z : Fin ℓ → ℝ => (∑ j, (z ᵥ* R) j ^ 2) ^ r
    have hL : MeasurePreserving (fun Z : Matrix (Fin m) (Fin ℓ) ℝ => Z i) ν (gaussianRowLaw ℓ) :=
      gaussianMatrixLaw_row_measurePreserving i
    have hEq (Z : Matrix (Fin m) (Fin ℓ) ℝ) : f (B, Z) = G (Z i) := rfl
    simp_rw [hEq]
    have hR' := gaussianRow_vecMul_moment R hr
    refine ⟨hL.integrable_comp_of_integrable hR'.1, ?_⟩
    rw [← integral_map hL.measurable.aemeasurable, hL.map_eq]
    · exact hR'.2
    · rw [hL.map_eq]
      exact hR'.1.aestronglyMeasurable
  have hnn (w : Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin m) (Fin ℓ) ℝ) : 0 ≤ f w :=
    Real.rpow_nonneg (gaussianTailRowEnergy_nonneg i w) r
  have hB : (fun B => ∫ Z, f (B, Z) ∂ν) ≤ᵐ[μ] g := by
    filter_upwards [ae_gaussianMatrix_injective hkl] with B hB
    have hTr := leadingRightInverse_sum_column_sq Bᵀ (by simpa only [transpose_transpose] using hB)
    rw [transpose_transpose] at hTr
    exact (hC B).2.trans_eq (by simp only [hTr, g])
  have hI : Integrable (fun B => ∫ Z, f (B, Z) ∂ν) μ := by
    have hm : StronglyMeasurable (fun B => ∫ Z, f (B, Z) ∂ν) :=
      hf.stronglyMeasurable.integral_prod_right
    refine hg.mono' hm.aestronglyMeasurable ?_
    filter_upwards [hB] with B hB
    rw [Real.norm_of_nonneg (integral_nonneg fun Z => hnn (B, Z))]
    exact hB
  have hF : Integrable f (μ.prod ν) := by
    apply (integrable_prod_iff hf.aestronglyMeasurable).2
    refine ⟨ae_of_all _ fun B => (hC B).1, ?_⟩
    simpa only [Real.norm_of_nonneg (hnn _)] using hI
  refine ⟨hF, ?_⟩
  change (∫ w, f w ∂μ.prod ν) ≤ _
  rw [integral_prod _ hF]
  refine (integral_mono_ae hI hg hB).trans ?_
  unfold g
  rw [integral_mul_const, mul_comm (standardNormalMoment r) (chiSquareNegativeMoment _ r), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h.2 (standardNormalMoment_nonneg r)

/-- Exact constant (K_{k,p,r}) in Lemma 3.2. -/
def gaussianTailMomentConstant (k p : ℕ) (r : ℝ) : ℝ :=
  1 + k * (standardNormalMoment r * chiSquareNegativeMoment (p + 1) r) ^ (1 / r)

end

end TypicalOrientations
