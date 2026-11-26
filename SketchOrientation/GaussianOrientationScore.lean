import SketchOrientation.GaussianOrientationTruncation
import SketchOrientation.GaussianPolarConditional
import SketchOrientation.AtomTheorem

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

variable {n k ℓ : ℕ}

/-- The Euclidean subspace observed by a sketch projector. -/
noncomputable def orientationRowSpace (P : OrthogonalProjector n ℓ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range P.val.toEuclideanLin

theorem orientationRowSpace_starProjection (P : OrthogonalProjector n ℓ)
    (u : EuclideanSpace ℝ (Fin n)) :
    (orientationRowSpace P).starProjection u = P.val.toEuclideanLin u := by
  have h := congrArg Matrix.toEuclideanLin
    (rangeProjector_of_projector P.val P.property.1 P.property.2.1)
  rw [euclidean_projector] at h
  exact LinearMap.congr_fun h u

theorem measurable_orientationRowSpace_projection (u : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun P : OrthogonalProjector n ℓ => (orientationRowSpace P).starProjection u) := by
  simp_rw [orientationRowSpace_starProjection]
  change Measurable (fun P : OrthogonalProjector n ℓ =>
    WithLp.toLp 2 (P.val *ᵥ WithLp.ofLp u))
  exact (WithLp.measurable_toLp _ _).comp
    ((continuous_id.matrix_mulVec continuous_const).measurable.comp measurable_subtype_coe)

private theorem orientationRowSpace_basis_energy (P : OrthogonalProjector n ℓ) (i : Fin n) :
    ‖(orientationRowSpace P).starProjection (EuclideanSpace.single i 1)‖ ^ 2 = P.val i i := by
  let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have h := (orientationRowSpace P).re_inner_starProjection_eq_normSq u
  change inner ℝ ((orientationRowSpace P).starProjection u) u =
    ‖(orientationRowSpace P).starProjection u‖ ^ 2 at h
  rw [orientationRowSpace_starProjection, EuclideanSpace.inner_single_right] at h
  rw [orientationRowSpace_starProjection]
  simpa [u, Matrix.toLpLin_apply, EuclideanSpace.single, Matrix.mulVec_single_one] using h.symm

/-- Mean projected energy dominates the dimension fraction. -/
theorem sketchRank_le_dim_mul_meanProjectedEnergy
    (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν] :
    (ℓ : ℝ) ≤ (n : ℝ) * meanProjectedEnergy ν orientationRowSpace := by
  have hTrace (P : OrthogonalProjector n ℓ) : P.val.trace = (ℓ : ℝ) := by
    calc
      P.val.trace = (rangeProjector P.val).trace := congrArg Matrix.trace
        (rangeProjector_of_projector P.val P.property.1 P.property.2.1).symm
      _ = (P.val.rank : ℝ) := trace_rangeProjector _
      _ = (ℓ : ℝ) := congrArg Nat.cast P.property.2.2
  have hSum (P : OrthogonalProjector n ℓ) :
      (∑ i, ‖(orientationRowSpace P).starProjection (EuclideanSpace.single i 1)‖ ^ 2) = (ℓ : ℝ) := by
    simp_rw [orientationRowSpace_basis_energy]
    exact hTrace P
  have hInt (i : Fin n) := integrable_projected_energy ν orientationRowSpace
    (EuclideanSpace.single i 1) (measurable_orientationRowSpace_projection _)
  calc
    (ℓ : ℝ) = ∫ P, ∑ i, ‖(orientationRowSpace P).starProjection
        (EuclideanSpace.single i 1)‖ ^ 2 ∂ν := by simp_rw [hSum, integral_const]; simp
    _ = ∑ i, ∫ P, ‖(orientationRowSpace P).starProjection
        (EuclideanSpace.single i 1)‖ ^ 2 ∂ν := integral_finsetSum _ fun i _ => hInt i
    _ ≤ ∑ _ : Fin n, meanProjectedEnergy ν orientationRowSpace := by
      apply Finset.sum_le_sum
      intro i _
      simpa [EuclideanSpace.single, PiLp.norm_single] using
        projectedEnergy_le_meanProjectedEnergy ν orientationRowSpace
          measurable_orientationRowSpace_projection (EuclideanSpace.single i 1)
    _ = _ := by simp

/-- The matrix with the indicated Gaussian Hilbert columns. -/
def gaussianHilbertMatrix (x : GaussianColumnHilbert n k) : Matrix (Fin n) (Fin k) ℝ :=
  matrixOfGaussianColumns x.ofLp

theorem measurable_gaussianHilbertMatrix : Measurable (@gaussianHilbertMatrix n k) :=
  measurable_matrixOfGaussianColumns.comp (WithLp.measurable_ofLp _ _)

theorem gaussianHilbertMatrix_map :
    (stdGaussian (GaussianColumnHilbert n k)).map gaussianHilbertMatrix = gaussianMatrixLaw n k := by
  rw [← gaussianColumnLaw_map_toLp,
    Measure.map_map measurable_gaussianHilbertMatrix (WithLp.measurable_toLp _ _)]
  rfl

theorem gaussianHilbertMatrix_columnwise_projection (P : OrthogonalProjector n ℓ)
    (x : GaussianColumnHilbert n k) :
    gaussianHilbertMatrix ((columnwiseSubspace (orientationRowSpace P)).starProjection x) =
      P.val * gaussianHilbertMatrix x := by
  rw [columnwiseSubspace_starProjection]
  ext i j
  change ((orientationRowSpace P).starProjection (x j)) i =
    ∑ a, P.val i a * (x j) a
  rw [orientationRowSpace_starProjection]
  rfl

/-- Normalized inverse trace in the Gaussian lift of Theorem 1.1. -/
noncomputable def gaussianOrientationScore (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  gaussianProjectedInverseTrace (P.val, G) / k

theorem measurable_gaussianOrientationScore :
    Measurable (Function.uncurry (@gaussianOrientationScore n k ℓ)) :=
  (measurable_gaussianProjectedInverseTrace.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)).div_const _

theorem measurable_gaussianOrientationScore_fixed (P : OrthogonalProjector n ℓ) :
    Measurable (gaussianOrientationScore (k := k) P) := by
  have hP : Measurable (fun _ : Matrix (Fin n) (Fin k) ℝ => P) := measurable_const
  have h := (@measurable_gaussianOrientationScore n k ℓ).comp (hP.prodMk measurable_id)
  exact h

theorem gaussianOrientationScore_nonneg (P : OrthogonalProjector n ℓ)
    (G : Matrix (Fin n) (Fin k) ℝ) : 0 ≤ gaussianOrientationScore P G :=
  div_nonneg (gaussianProjectedInverseTrace_nonneg P.val P.property.1 P.property.2.1 P.property.2.2 G)
    (Nat.cast_nonneg _)

theorem gaussianOrientationScore_observation (P : OrthogonalProjector n ℓ) :
    Measurable[MeasurableSpace.comap
      (columnwiseSubspace (orientationRowSpace P) (k := k)).orthogonalProjectionOnto inferInstance]
      (fun x => gaussianOrientationScore P (gaussianHilbertMatrix x)) := by
  let F := fun G : Matrix (Fin n) (Fin k) ℝ => ((gaussianGram G)⁻¹.trace) / (k : ℝ)
  have hG : Measurable (@gaussianGram n k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  have hF : Measurable F :=
    (measurable_matrix_trace.comp (measurable_matrix_nonsing_inv.comp hG)).div_const _
  let S : Submodule ℝ (GaussianColumnHilbert n k) := columnwiseSubspace (orientationRowSpace P)
  have he : (fun x => gaussianOrientationScore P (gaussianHilbertMatrix x)) =
      F ∘ gaussianHilbertMatrix ∘ Subtype.val ∘ S.orthogonalProjectionOnto := by
    funext x
    change (_ : ℝ) = F (gaussianHilbertMatrix (S.starProjection x))
    unfold gaussianOrientationScore gaussianProjectedInverseTrace F
    rw [gaussianHilbertMatrix_columnwise_projection]
    congr 2
    apply congrArg Inv.inv
    change (gaussianHilbertMatrix x)ᵀ * P.val * gaussianHilbertMatrix x =
      (P.val * gaussianHilbertMatrix x)ᵀ * (P.val * gaussianHilbertMatrix x)
    rw [transpose_mul, P.property.1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P.val P.val, P.property.2.1]
  rw [he]
  exact hF.comp (measurable_gaussianHilbertMatrix.comp
    (measurable_subtype_coe.comp (measurable_iff_comap_le.mpr le_rfl)))

/-- Every fixed sketch induces the same law of the normalized inverse trace. -/
theorem gaussianOrientationScore_map_eq (hℓn : ℓ ≤ n) (P Q : OrthogonalProjector n ℓ) :
    (gaussianMatrixLaw n k).map (gaussianOrientationScore P) =
      (gaussianMatrixLaw n k).map (gaussianOrientationScore Q) := by
  let f := fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹.trace / (k : ℝ)
  have hf : Measurable f :=
    (measurable_matrix_trace.comp measurable_matrix_nonsing_inv).div_const _
  have hm (P : OrthogonalProjector n ℓ) :
      Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => Gᵀ * P.val * G) :=
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable
  have he (P : OrthogonalProjector n ℓ) :
      (gaussianMatrixLaw n k).map (gaussianOrientationScore P) =
      ((gaussianMatrixLaw ℓ k).map gaussianGram).map f := by
    change (gaussianMatrixLaw n k).map (f ∘ fun G => Gᵀ * P.val * G) = _
    rw [← Measure.map_map hf (hm P),
      gaussianMatrixLaw_map_projectedGram hℓn _ P.property.1 P.property.2.1 P.property.2.2]
  rw [he P, he Q]

/-- The first moment of the normalized Gaussian lift is independent of the
chosen projector. -/
theorem gaussianOrientationScore_mean (hℓn : ℓ ≤ n) (hk : 0 < k) (hkℓ : k + 1 < ℓ)
    (P : OrthogonalProjector n ℓ) :
    Integrable (gaussianOrientationScore (k := k) P) (gaussianMatrixLaw n k) ∧
      (∫ G, gaussianOrientationScore P G ∂gaussianMatrixLaw n k) =
        1 / ((ℓ : ℝ) - k - 1) := by
  have h := gaussianMatrix_projectedGram_inv_trace_mean hℓn hkℓ _
    P.property.1 P.property.2.1 P.property.2.2
  refine ⟨h.1.div_const _, ?_⟩
  unfold gaussianOrientationScore gaussianProjectedInverseTrace
  rw [integral_div, h.2]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

private theorem measurable_gaussianOrientationHilbertScore :
    Measurable (fun p : OrthogonalProjector n ℓ × GaussianColumnHilbert n k =>
      gaussianOrientationScore p.1 (gaussianHilbertMatrix p.2)) := by
  have hm : Measurable (Prod.map (id : OrthogonalProjector n ℓ → OrthogonalProjector n ℓ)
      (@gaussianHilbertMatrix n k)) := measurable_id.prodMap measurable_gaussianHilbertMatrix
  have h := (@measurable_gaussianOrientationScore n k ℓ).comp hm
  exact h

/-- Positive uniform moment constant in the quantitative orientation bound. -/
noncomputable def gaussianOrientationMomentConstant (p : ℕ) (r : ℝ) : ℝ :=
  chiSquareNegativeMoment (p + 1) r ^ (1 / r)

set_option maxHeartbeats 350000 in
/-- The Gaussian endpoint estimate for the genuine lift of every projector law. -/
theorem gaussianOrientationScore_centered_bound (hℓn : ℓ ≤ n) (hk : 0 < k)
    (hkℓ : k + 1 < ℓ) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 < r) (hr₂ : r ≤ 2) (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2) :
    (∫ G, |(∫ P, gaussianOrientationScore P G ∂ν) - 1 / ((ℓ : ℝ) - k - 1)|
       ∂gaussianMatrixLaw n k) ≤
      3 * gaussianOrientationMomentConstant (ℓ - k) r *
        meanProjectedEnergy ν orientationRowSpace ^ (1 - 1 / r) := by
  let γ := stdGaussian (GaussianColumnHilbert n k)
  let S := fun P : OrthogonalProjector n ℓ =>
    columnwiseSubspace (orientationRowSpace P) (k := k)
  let Y := fun (P : OrthogonalProjector n ℓ) (x : GaussianColumnHilbert n k) =>
    gaussianOrientationScore P (gaussianHilbertMatrix x)
  obtain ⟨P₀, _⟩ : ∃ P : OrthogonalProjector n ℓ, True := (ae_of_all ν fun _ => True.intro).exists
  let ρ := meanProjectedEnergy ν orientationRowSpace
  let M := chiSquareNegativeMoment (ℓ - k + 1) r
  let K := gaussianOrientationMomentConstant (ℓ - k) r
  have hρ : 0 < ρ := by
    apply pos_of_mul_pos_right _ (Nat.cast_nonneg n)
    exact (Nat.cast_pos.mpr (show 0 < ℓ by omega)).trans_le
      (sketchRank_le_dim_mul_meanProjectedEnergy ν)
  have hM : 0 < M := by
    unfold M chiSquareNegativeMoment
    have h₁ := Real.Gamma_pos_of_pos (sub_pos.mpr hr')
    have h₂ := Real.Gamma_pos_of_pos ((zero_lt_one.trans hr).trans hr')
    positivity
  have hK : 0 < K := Real.rpow_pos_of_pos hM _
  have hMK : K ^ r = M := by
    change (M ^ (1 / r)) ^ r = M
    rw [← Real.rpow_mul hM.le, div_mul_cancel₀ _ (zero_lt_one.trans hr).ne', Real.rpow_one]
  have hY : Measurable (Function.uncurry Y) :=
    @measurable_gaussianOrientationHilbertScore n k ℓ
  have hScore (P : OrthogonalProjector n ℓ) :
      Measurable (gaussianOrientationScore (k := k) P) :=
    measurable_gaussianOrientationScore_fixed P
  have hLaw (P : OrthogonalProjector n ℓ) : IdentDistrib (Y P) (Y P₀) γ γ := by
    refine ⟨((hScore P).comp measurable_gaussianHilbertMatrix).aemeasurable,
      ((hScore P₀).comp measurable_gaussianHilbertMatrix).aemeasurable, ?_⟩
    change γ.map (gaussianOrientationScore P ∘ gaussianHilbertMatrix) =
      γ.map (gaussianOrientationScore P₀ ∘ gaussianHilbertMatrix)
    rw [← Measure.map_map (hScore P) measurable_gaussianHilbertMatrix,
      ← Measure.map_map (hScore P₀) measurable_gaussianHilbertMatrix,
      gaussianHilbertMatrix_map]
    exact gaussianOrientationScore_map_eq hℓn P P₀
  have hMean := gaussianOrientationScore_mean (k := k) hℓn hk hkℓ P₀
  have hInt : Integrable (Y P₀) γ := by
    change Integrable (gaussianOrientationScore P₀ ∘ gaussianHilbertMatrix) γ
    rw [← integrable_map_measure (hScore P₀).aestronglyMeasurable
      measurable_gaussianHilbertMatrix.aemeasurable, gaussianHilbertMatrix_map]
    exact hMean.1
  have hMean' : (∫ x, Y P₀ x ∂γ) = 1 / ((ℓ : ℝ) - k - 1) := by
    change (∫ x, gaussianOrientationScore P₀ (gaussianHilbertMatrix x) ∂γ) = _
    rw [← integral_map measurable_gaussianHilbertMatrix.aemeasurable (hScore P₀).aestronglyMeasurable,
      gaussianHilbertMatrix_map, hMean.2]
  have hMoment := gaussianMatrix_projectedGram_inv_trace_moment hℓn hk (by omega)
    hr.le hr' P₀.val P₀.property.1 P₀.property.2.1 P₀.property.2.2
  have hPower : Measurable (fun G => gaussianOrientationScore (k := k) P₀ G ^ r) :=
    (hScore P₀).pow_const _
  have hMomentInt : Integrable (fun x => Y P₀ x ^ r) γ := by
    change Integrable ((fun G => gaussianOrientationScore P₀ G ^ r) ∘ gaussianHilbertMatrix) γ
    rw [← integrable_map_measure hPower.aestronglyMeasurable
      measurable_gaussianHilbertMatrix.aemeasurable, gaussianHilbertMatrix_map]
    exact hMoment.1
  have hMoment' : (∫ x, Y P₀ x ^ r ∂γ) ≤ K ^ r := by
    change (∫ x, gaussianOrientationScore P₀ (gaussianHilbertMatrix x) ^ r ∂γ) ≤ _
    rw [← integral_map measurable_gaussianHilbertMatrix.aemeasurable hPower.aestronglyMeasurable,
      gaussianHilbertMatrix_map, hMK]
    exact hMoment.2
  let a := K * ρ ^ (-1 / r)
  have ha : 0 < a := mul_pos hK (Real.rpow_pos_of_pos hρ _)
  have hSm (u : GaussianColumnHilbert n k) : Measurable (fun P => (S P).starProjection u) := by
    change Measurable (fun P : OrthogonalProjector n ℓ =>
      (columnwiseSubspace (orientationRowSpace P)).starProjection u)
    simp_rw [columnwiseSubspace_starProjection]
    exact (WithLp.measurable_toLp _ _).comp
      (measurable_pi_iff.mpr fun _ => measurable_orientationRowSpace_projection _)
  have h := gaussianProjection_truncation_bound ν S hSm ρ hρ.le
    (projected_columns_le_meanProjectedEnergy ν orientationRowSpace
      measurable_orientationRowSpace_projection) Y hY
    (fun P x => gaussianOrientationScore_nonneg P _) gaussianOrientationScore_observation
    (Y P₀) hInt (fun x => gaussianOrientationScore_nonneg P₀ _) hLaw ha hr hr₂ hMomentInt hMoment'
  rw [gaussianOrientation_cutoff_bound_eq hρ hK hr, hMean'] at h
  have hm : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ =>
      |(∫ P, gaussianOrientationScore P G ∂ν) - 1 / ((ℓ : ℝ) - k - 1)|) :=
    (measurable_gaussianOrientationScore.stronglyMeasurable.integral_prod_left
      |>.measurable.sub measurable_const).abs
  rw [← gaussianHilbertMatrix_map (n := n) (k := k),
    integral_map measurable_gaussianHilbertMatrix.aemeasurable hm.aestronglyMeasurable]
  exact h

end SketchOrientation
