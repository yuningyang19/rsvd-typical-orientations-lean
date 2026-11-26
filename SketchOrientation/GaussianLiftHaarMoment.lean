import SketchOrientation.GaussianLiftStabilizer
import SketchOrientation.GaussianHaarQuadratic

namespace SketchOrientation

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {n k ℓ : ℕ}

private theorem frameProjector_entry_abs_le (V : Matrix (Fin n) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) (i j : Fin n) : |(V * Vᵀ) i j| ≤ 1 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  let S := V.toEuclideanLin.range
  have hMap := congrArg Matrix.toEuclideanLin (rangeProjector_of_frame V hV)
  rw [euclidean_projector] at hMap
  have hVec : S.starProjection e = (V * Vᵀ).toEuclideanLin e := LinearMap.congr_fun hMap e
  have he : (S.starProjection e) i = (V * Vᵀ) i j := by
    rw [hVec]
    change (toLpLin 2 2 (V * Vᵀ) e) i = _
    simp [e, Matrix.toLpLin_apply, EuclideanSpace.single, Matrix.mulVec_apply, dotProduct,
      Matrix.mul_apply]
  rw [← he]
  calc
    _ ≤ ‖S.starProjection e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖e‖ := S.norm_starProjection_apply_le _
    _ = 1 := by simp [e, EuclideanSpace.single, PiLp.norm_single]

/-- The Haar average of the target projector with a scalar weight. -/
noncomputable def haarWeightedTargetProjector (hkn : k ≤ n)
    (w : Matrix (Fin n) (Fin k) ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ V, w V * (V * Vᵀ) i j ∂gaussianHaarFrameLaw hkn

private theorem integrable_weightedTargetProjector_entry (hkn : k ≤ n)
    {w : Matrix (Fin n) (Fin k) ℝ → ℝ}
    (hw : Integrable w (gaussianHaarFrameLaw hkn)) (i j : Fin n) :
    Integrable (fun V => w V * (V * Vᵀ) i j) (gaussianHaarFrameLaw hkn) := by
  have hEntry : Continuous (fun V : Matrix (Fin n) (Fin k) ℝ => (V * Vᵀ) i j) :=
    (continuous_id.matrix_elem i j).comp (continuous_id.matrix_mul continuous_id.matrix_transpose)
  refine hw.norm.mono' (hw.aestronglyMeasurable.mul hEntry.measurable.aestronglyMeasurable) ?_
  filter_upwards [ae_gaussianHaarFrame_orthonormal hkn] with V hV
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [Real.norm_eq_abs]
  exact frameProjector_entry_abs_le V hV i j

theorem trace_mul_haarWeightedTargetProjector (hkn : k ≤ n)
    {w : Matrix (Fin n) (Fin k) ℝ → ℝ}
    (hw : Integrable w (gaussianHaarFrameLaw hkn)) (D : Matrix (Fin n) (Fin n) ℝ) :
    (D * haarWeightedTargetProjector hkn w).trace =
      ∫ V, w V * (D * (V * Vᵀ)).trace ∂gaussianHaarFrameLaw hkn := by
  let η := gaussianHaarFrameLaw hkn
  let f (i j : Fin n) (V : Matrix (Fin n) (Fin k) ℝ) := D i j * (w V * (V * Vᵀ) j i)
  have hI (i j : Fin n) : Integrable (f i j) η :=
    (integrable_weightedTargetProjector_entry hkn hw j i).const_mul _
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, D i j * ∫ V, w V * (V * Vᵀ) j i ∂η := rfl
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ V, f i j V ∂η := by
      simp_rw [f, integral_const_mul]
    _ = ∫ V, ∑ i : Fin n, ∑ j : Fin n, f i j V ∂η := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
      simp_rw [integral_finsetSum _ (fun j _ => hI _ j)]
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ fun V => ?_)
      change (∑ i : Fin n, ∑ j : Fin n, D i j * (w V * (V * Vᵀ) j i)) =
        w V * (∑ i : Fin n, ∑ j : Fin n, D i j * (V * Vᵀ) j i)
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_left_comm (D i j) (w V) ((V * Vᵀ) j i)

private theorem trace_conjugated_product (R D X : Matrix (Fin n) (Fin n) ℝ) :
    ((Rᵀ * D * R) * X).trace = (D * (R * X * Rᵀ)).trace := by
  rw [Matrix.mul_assoc Rᵀ D R, Matrix.mul_assoc Rᵀ (D * R) X, trace_mul_comm Rᵀ]
  simp only [Matrix.mul_assoc]

/-- A scalar weight invariant under the rotations preserving the sketch
gives a weighted Haar mean that commutes with every such rotation. -/
theorem haarWeightedTargetProjector_stabilizer (hkn : k ≤ n)
    (P : OrthogonalProjector n ℓ) {w : Matrix (Fin n) (Fin k) ℝ → ℝ}
    (hm : Measurable w) (hw : Integrable w (gaussianHaarFrameLaw hkn))
    (hi : ∀ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = 1 → P.val * R = R * P.val →
      ∀ V, w (R * V) = w V)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : Rᵀ * R = 1) (hPR : P.val * R = R * P.val) :
    haarWeightedTargetProjector hkn w * R = R * haarWeightedTargetProjector hkn w := by
  let N := haarWeightedTargetProjector hkn w
  let η := gaussianHaarFrameLaw hkn
  have hRN : R * N * Rᵀ = N := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro D
    let F (V : Matrix (Fin n) (Fin k) ℝ) := w V * (D * (V * Vᵀ)).trace
    have hF : Measurable F := hm.mul (measurable_matrix_trace.comp
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_id.matrix_transpose)).measurable)
    have hRot : Measurable (fun V : Matrix (Fin n) (Fin k) ℝ => R * V) :=
      (continuous_const.matrix_mul continuous_id).measurable
    calc
      _ = ((Rᵀ * D * R) * N).trace := (trace_conjugated_product R D N).symm
      _ = ∫ V, w V * ((Rᵀ * D * R) * (V * Vᵀ)).trace ∂η :=
        trace_mul_haarWeightedTargetProjector hkn hw _
      _ = ∫ V, F (R * V) ∂η := by
        apply integral_congr_ae (ae_of_all _ fun V => ?_)
        rw [trace_conjugated_product]
        simp only [F, hi R hR hPR V, transpose_mul, Matrix.mul_assoc]
      _ = ∫ V, F V ∂η := by
        rw [← integral_map hRot.aemeasurable hF.aestronglyMeasurable,
          gaussianHaarFrameLaw_map_left hkn R hR]
      _ = _ := (trace_mul_haarWeightedTargetProjector hkn hw D).symm
  change N * R = R * N
  calc
    N * R = (R * N * Rᵀ) * R := congrArg (· * R) hRN.symm
    _ = R * N := by rw [Matrix.mul_assoc (R * N), hR, Matrix.mul_one]

/-- A centered weight produces a trace-zero weighted projector. -/
theorem trace_haarWeightedTargetProjector_eq_zero (hkn : k ≤ n)
    {w : Matrix (Fin n) (Fin k) ℝ → ℝ} (hw : Integrable w (gaussianHaarFrameLaw hkn))
    (hZero : (∫ V, w V ∂gaussianHaarFrameLaw hkn) = 0) :
    (haarWeightedTargetProjector hkn w).trace = 0 := by
  have h := trace_mul_haarWeightedTargetProjector hkn hw (1 : Matrix (Fin n) (Fin n) ℝ)
  simp only [Matrix.one_mul] at h
  rw [h]
  have he : (fun V : Matrix (Fin n) (Fin k) ℝ => w V * (V * Vᵀ).trace)
      =ᵐ[gaussianHaarFrameLaw hkn] fun V => w V * (k : ℝ) := by
    filter_upwards [ae_gaussianHaarFrame_orthonormal hkn] with V hV
    rw [trace_mul_comm, hV, trace_one, Fintype.card_fin]
  rw [integral_congr_ae he, integral_mul_const, hZero, zero_mul]

theorem trace_projector_mul_haarWeightedTargetProjector (hkn : k ≤ n)
    (P : OrthogonalProjector n ℓ) {w : Matrix (Fin n) (Fin k) ℝ → ℝ}
    (hw : Integrable w (gaussianHaarFrameLaw hkn)) :
    (P.val * haarWeightedTargetProjector hkn w).trace =
      ∫ V, w V * (Vᵀ * P.val * V).trace ∂gaussianHaarFrameLaw hkn := by
  rw [trace_mul_haarWeightedTargetProjector hkn hw]
  apply integral_congr_ae (ae_of_all _ fun V => ?_)
  rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]

end SketchOrientation
