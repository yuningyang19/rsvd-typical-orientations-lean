import SketchOrientation.GaussianLiftEnergyCovarianceRadial
import SketchOrientation.GaussianOrientationScore
import SketchOrientation.GaussianTailGram
import SketchOrientation.GaussianGramMean

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory Submodule
open scoped ENNReal

noncomputable section

variable {n k ℓ : ℕ}

def gaussianLiftProjectedGram (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ := Gᵀ * P.val * G

def gaussianLiftComplementGram (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ := Gᵀ * (1 - P.val) * G

def gaussianLiftCapturedEnergy (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : ℝ := (gaussianLiftProjectedGram P G).trace

theorem measurable_gaussianLiftProjectedGram (P : OrthogonalProjector n ℓ) :
    Measurable (gaussianLiftProjectedGram (k := k) P) :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable

theorem measurable_gaussianLiftComplementGram (P : OrthogonalProjector n ℓ) :
    Measurable (gaussianLiftComplementGram (k := k) P) :=
  ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable

theorem measurable_gaussianLiftCapturedEnergy (P : OrthogonalProjector n ℓ) :
    Measurable (gaussianLiftCapturedEnergy (k := k) P) :=
  measurable_matrix_trace.comp (measurable_gaussianLiftProjectedGram P)

theorem gaussianLiftProjectedGram_eq_gram (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianLiftProjectedGram P G = gaussianGram (P.val * G) := by
  calc
    _ = Gᵀ * (P.val * P.val) * G := by
      rw [P.property.2.1]
      rfl
    _ = _ := by
      unfold gaussianGram
      rw [transpose_mul, P.property.1]
      simp only [Matrix.mul_assoc]

private theorem complement_transpose (P : OrthogonalProjector n ℓ) :
    (1 - P.val)ᵀ = 1 - P.val := by simp [P.property.1]

private theorem complement_idempotent (P : OrthogonalProjector n ℓ) :
    (1 - P.val) * (1 - P.val) = 1 - P.val := by
  simp [Matrix.sub_mul, Matrix.mul_sub, P.property.2.1]

theorem gaussianLiftComplementGram_eq_gram (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianLiftComplementGram P G = gaussianGram ((1 - P.val) * G) := by
  calc
    _ = Gᵀ * ((1 - P.val) * (1 - P.val)) * G := by
      rw [complement_idempotent]
      rfl
    _ = _ := by
      unfold gaussianGram
      rw [transpose_mul, complement_transpose]
      simp only [Matrix.mul_assoc]

theorem gaussianLift_gram_add (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) :
    gaussianLiftProjectedGram P G + gaussianLiftComplementGram P G = gaussianGram G := by
  unfold gaussianLiftProjectedGram gaussianLiftComplementGram gaussianGram
  rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]

theorem gaussianLift_projected_indep_complement (P : OrthogonalProjector n ℓ) :
    IndepFun (fun G : Matrix (Fin n) (Fin k) ℝ => P.val * G)
      (fun G => (1 - P.val) * G) (gaussianMatrixLaw n k) := by
  let X := GaussianColumnHilbert n k
  let γ := stdGaussian X
  let R : Submodule ℝ X := columnwiseSubspace (orientationRowSpace P)
  let F := @gaussianHilbertMatrix n k
  let L := fun G : Matrix (Fin n) (Fin k) ℝ => P.val * G
  let M := fun G : Matrix (Fin n) (Fin k) ℝ => (1 - P.val) * G
  have hF : Measurable F := measurable_gaussianHilbertMatrix
  have hL : Measurable L := (continuous_const.matrix_mul continuous_id).measurable
  have hM : Measurable M := (continuous_const.matrix_mul continuous_id).measurable
  have hR : IndepFun (L ∘ F) (M ∘ F) γ := by
    have hi := (stdGaussian_orthogonal_split_indep R).comp
      (hF.comp measurable_subtype_coe) (hF.comp measurable_subtype_coe)
    apply hi.congr
    · exact ae_of_all _ fun z => gaussianHilbertMatrix_columnwise_projection P z
    · apply ae_of_all
      intro z
      change F (Rᗮ.starProjection z) = (1 - P.val) * F z
      rw [Submodule.starProjection_orthogonal_val]
      have hsub : F (z - R.starProjection z) = F z - F (R.starProjection z) := by
        ext i j
        rfl
      rw [hsub, show F (R.starProjection z) = P.val * F z from
        gaussianHilbertMatrix_columnwise_projection P z, Matrix.sub_mul, Matrix.one_mul]
  rw [indepFun_iff_map_prod_eq_prod_map_map (hL.comp hF).aemeasurable
    (hM.comp hF).aemeasurable] at hR
  change γ.map ((fun z => (L z, M z)) ∘ F) =
    (γ.map (L ∘ F)).prod (γ.map (M ∘ F)) at hR
  rw [← Measure.map_map (hL.prodMk hM) hF, ← Measure.map_map hL hF,
    ← Measure.map_map hM hF, gaussianHilbertMatrix_map] at hR
  exact (indepFun_iff_map_prod_eq_prod_map_map hL.aemeasurable hM.aemeasurable).2 hR

/-- The two native orthogonal Gaussian blocks give independent Gram matrices. -/
theorem gaussianLift_projectedGram_indep_complementGram (P : OrthogonalProjector n ℓ) :
    IndepFun (gaussianLiftProjectedGram (k := k) P) (gaussianLiftComplementGram P)
      (gaussianMatrixLaw n k) := by
  have hG : Measurable (@gaussianGram n k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  have h := (gaussianLift_projected_indep_complement (k := k) P).comp hG hG
  exact h.congr (ae_of_all _ fun G => (gaussianLiftProjectedGram_eq_gram P G).symm)
    (ae_of_all _ fun G => (gaussianLiftComplementGram_eq_gram P G).symm)

private theorem gaussianLift_normalized_joint {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → A} {C : Ω → B}
    (hW : Measurable W) (hC : Measurable C) (hWC : IndepFun W C μ)
    {N : A → A} {S : A → ℝ} (hN : Measurable N) (hS : Measurable S)
    (hNS : IndepFun N S (μ.map W)) :
    IndepFun (fun x => (N (W x), C x)) (S ∘ W) μ := by
  let α := (μ.map W).map N
  let β := (μ.map W).map S
  let χ := μ.map C
  let E := fun x => ((N (W x), S (W x)), C x)
  let T := fun (p : (A × ℝ) × B) => ((p.1.1, p.2), p.1.2)
  let : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  let : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map hN.aemeasurable
  let : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map hS.aemeasurable
  let : IsProbabilityMeasure χ := Measure.isProbabilityMeasure_map hC.aemeasurable
  have hE : Measurable E := ((hN.comp hW).prodMk (hS.comp hW)).prodMk hC
  have hT : Measurable T := by fun_prop
  have hMap : μ.map E = (α.prod β).prod χ := by
    have he : E = Prod.map (fun w => (N w, S w)) id ∘ (fun x => (W x, C x)) := rfl
    rw [he, ← Measure.map_map ((hN.prodMk hS).prodMap measurable_id) (hW.prodMk hC),
      hWC.map_prod_eq_prod_map_map hW.aemeasurable hC.aemeasurable,
      ← Measure.map_prod_map _ _ (hN.prodMk hS) measurable_id,
      hNS.map_prod_eq_prod_map_map hN.aemeasurable hS.aemeasurable, Measure.map_id]
  have hPerm : MeasurePreserving T ((α.prod β).prod χ) ((α.prod χ).prod β) := by
    have hSwap : MeasurePreserving (Prod.map (id : A → A) (Prod.swap : ℝ × B → B × ℝ))
        (α.prod (β.prod χ)) (α.prod (χ.prod β)) :=
      (MeasurePreserving.id α).prod Measure.measurePreserving_swap
    exact (measurePreserving_prodAssoc α χ β).symm.comp
      (hSwap.comp (measurePreserving_prodAssoc α β χ))
  let H := fun x => (N (W x), C x)
  let R := S ∘ W
  have hH : Measurable H := (hN.comp hW).prodMk hC
  have hR : Measurable R := hS.comp hW
  have he : μ.map (fun x => (H x, R x)) = (α.prod χ).prod β := by
    change μ.map (T ∘ E) = _
    rw [← Measure.map_map hT hE, hMap, hPerm.map_eq]
  have hα : μ.map H = α.prod χ := by
    have hh := congrArg (Measure.map Prod.fst) he
    rw [Measure.map_map measurable_fst (hH.prodMk hR), Measure.map_fst_prod, measure_univ, one_smul] at hh
    exact hh
  have hβ : μ.map R = β := (Measure.map_map hS hW).symm
  exact (indepFun_iff_map_prod_eq_prod_map_map hH.aemeasurable hR.aemeasurable).2
    (by rw [hα, hβ]; exact he)

/-- The normalized projected Gram and the complementary Gram together
are independent of the scalar projected energy. -/
theorem gaussianLift_normalizedGram_complement_indep_energy (hℓn : ℓ ≤ n)
    (h : 0 < k * ℓ) (P : OrthogonalProjector n ℓ) :
    IndepFun (fun G : Matrix (Fin n) (Fin k) ℝ =>
      ((gaussianLiftCapturedEnergy P G)⁻¹ • gaussianLiftProjectedGram P G, gaussianLiftComplementGram P G))
      (gaussianLiftCapturedEnergy P) (gaussianMatrixLaw n k) := by
  let W := gaussianLiftProjectedGram (k := k) P
  let C := gaussianLiftComplementGram (k := k) P
  let N := fun A : Matrix (Fin k) (Fin k) ℝ => A.trace⁻¹ • A
  let S := fun A : Matrix (Fin k) (Fin k) ℝ => A.trace
  have hS : Measurable S := measurable_matrix_trace
  have hN : Measurable N := hS.inv.smul measurable_id
  have hW : Measurable W := measurable_gaussianLiftProjectedGram P
  have hC : Measurable C := measurable_gaussianLiftComplementGram P
  apply gaussianLift_normalized_joint hW hC (gaussianLift_projectedGram_indep_complementGram P) hN hS
  have hm : Measurable (@gaussianGram ℓ k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  have hLaw : (gaussianMatrixLaw n k).map W = (gaussianMatrixLaw ℓ k).map gaussianGram :=
    gaussianMatrixLaw_map_projectedGram hℓn P.val P.property.1 P.property.2.1 P.property.2.2
  rw [hLaw]
  have hNS := gaussianGram_normalized_indep_trace h
  change IndepFun (N ∘ gaussianGram) (S ∘ gaussianGram) (gaussianMatrixLaw ℓ k) at hNS
  rw [indepFun_iff_map_prod_eq_prod_map_map (hN.comp hm).aemeasurable
    (hS.comp hm).aemeasurable] at hNS
  rw [indepFun_iff_map_prod_eq_prod_map_map hN.aemeasurable hS.aemeasurable,
    Measure.map_map (hN.prodMk hS) hm, Measure.map_map hN hm, Measure.map_map hS hm]
  exact hNS

/-- The energy observed through a fixed sketch has the genuine chi-square law. -/
theorem gaussianLiftCapturedEnergy_law (hℓn : ℓ ≤ n) (h : 0 < k * ℓ)
    (P : OrthogonalProjector n ℓ) :
    (gaussianMatrixLaw n k).map (gaussianLiftCapturedEnergy P) = chiSquareLaw (k * ℓ) := by
  change (gaussianMatrixLaw n k).map (Matrix.trace ∘ gaussianLiftProjectedGram P) = _
  rw [← Measure.map_map measurable_matrix_trace (measurable_gaussianLiftProjectedGram P)]
  unfold gaussianLiftProjectedGram
  rw [gaussianMatrixLaw_map_projectedGram hℓn P.val P.property.1 P.property.2.1 P.property.2.2]
  have hm : Measurable (@gaussianGram ℓ k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  rw [Measure.map_map measurable_matrix_trace hm]
  exact gaussianGram_trace_law h

end

end SketchOrientation
