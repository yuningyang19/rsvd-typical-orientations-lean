import SketchOrientation.GaussianHaarColumnSchur

namespace SketchOrientation

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {n k : ℕ}

/-- The projected energy of a direction onto the span of a fixed frame. -/
noncomputable def haarFrameQuadratic (u : EuclideanSpace ℝ (Fin n))
    (V : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ‖Vᵀ.toEuclideanLin u‖ ^ 2

theorem measurable_haarFrameQuadratic (u : EuclideanSpace ℝ (Fin n)) :
    Measurable (haarFrameQuadratic (k := k) u) := by
  have h : Continuous (fun V : Matrix (Fin n) (Fin k) ℝ => Vᵀ.toEuclideanLin u) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_transpose.matrix_mulVec continuous_const)
  exact h.measurable.norm.pow_const _

theorem haarFrameQuadratic_eq_projection (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (u : EuclideanSpace ℝ (Fin n)) :
    haarFrameQuadratic u V = ‖V.toEuclideanLin.range.starProjection u‖ ^ 2 := by
  have h := congrArg Matrix.toEuclideanLin (rangeProjector_of_frame V hV)
  rw [euclidean_projector, euclidean_mul] at h
  have he : V.toEuclideanLin (Vᵀ.toEuclideanLin u) = V.toEuclideanLin.range.starProjection u :=
    (LinearMap.congr_fun h u).symm
  have hP := V.toEuclideanLin.range.re_inner_starProjection_eq_normSq u
  change inner ℝ (V.toEuclideanLin.range.starProjection u) u =
    ‖V.toEuclideanLin.range.starProjection u‖ ^ 2 at hP
  rw [haarFrameQuadratic, ← real_inner_self_eq_norm_sq, euclidean_transpose, LinearMap.adjoint_inner_left, ← euclidean_transpose]
  change inner ℝ u (V.toEuclideanLin (Vᵀ.toEuclideanLin u)) = _
  rw [he, real_inner_comm]
  exact hP

theorem haarFrameQuadratic_le (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (u : EuclideanSpace ℝ (Fin n)) : haarFrameQuadratic u V ≤ ‖u‖ ^ 2 := by
  rw [haarFrameQuadratic_eq_projection V hV]
  exact pow_le_pow_left₀ (norm_nonneg _) (V.toEuclideanLin.range.norm_starProjection_apply_le u) _

end SketchOrientation
