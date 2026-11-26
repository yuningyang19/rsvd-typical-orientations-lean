import SketchOrientation.GaussianLiftEnergyCovariance
import SketchOrientation.GaussianLiftEnergyBridge
import SketchOrientation.GaussianLiftHaarMoment

namespace SketchOrientation

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {n k ℓ : ℕ}

/-- The centered Haar target-projector average in the necessity proof.
The Gaussian lift computes its trace against the sketch projector, and
the orthogonal stabilizer determines the entire centered matrix. -/
theorem haarProjectedInverseTrace_centeredProjector_lift (hℓn : ℓ ≤ n)
    (hkℓ : k + 1 < ℓ) (hk : 0 < k) (P : OrthogonalProjector n ℓ) :
    haarWeightedTargetProjector (show k ≤ n by omega)
      (fun V => (Vᵀ * P.val * V)⁻¹.trace -
        (k : ℝ) * (((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1))) =
      (-2 * (k : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - k - 1))) •
        (P.val - ((ℓ : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have hkn : k ≤ n := by omega
  let η := gaussianHaarFrameLaw hkn
  let a := (ℓ : ℝ) - k - 1
  let mean := (k : ℝ) * (((n : ℝ) - k - 1) / a)
  let w (V : Matrix (Fin n) (Fin k) ℝ) := (Vᵀ * P.val * V)⁻¹.trace - mean
  let c := -2 * (k : ℝ) / ((ℓ : ℝ) * a)
  have hG := haarProjectedInverseTrace_mean hℓn hk hkℓ P
  have hI : Integrable w η := hG.1.sub (integrable_const _)
  have hMean : (∫ V, w V ∂η) = 0 := by
    unfold w
    rw [integral_sub hG.1 (integrable_const mean), hG.2, integral_const, probReal_univ,
      one_smul, sub_self]
  have hm : Measurable w := (measurable_matrix_trace.comp (measurable_matrix_nonsing_inv.comp
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable)).sub_const _
  have hw (R : Matrix (Fin n) (Fin n) ℝ) (hR : Rᵀ * R = 1)
      (hP : P.val * R = R * P.val) (V : Matrix (Fin n) (Fin k) ℝ) : w (R * V) = w V := by
    have hConj : Rᵀ * P.val * R = P.val := by
      rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hR, Matrix.one_mul]
    have hT : (R * V)ᵀ * P.val * (R * V) = Vᵀ * P.val * V := by
      rw [transpose_mul]
      calc
        _ = Vᵀ * (Rᵀ * P.val * R) * V := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hConj]
    simp only [w, hT]
  refine centered_stabilizer_matrix_eq (by omega) hℓn P _ c
    (haarWeightedTargetProjector_stabilizer hkn P hm hI hw)
    (trace_haarWeightedTargetProjector_eq_zero hkn hI hMean) ?_
  rw [trace_projector_mul_haarWeightedTargetProjector hkn P hI]
  have hLift := gaussianPolar_projectedInverseTrace_centered_energy hℓn hk hkℓ P
  have hGaussian := (gaussianPolar_projectedInverseTrace_energy_covariance hℓn hk hkℓ P).2
  have hScale : (n : ℝ) * (∫ V, w V * (Vᵀ * P.val * V).trace ∂η) =
      -2 * (k : ℝ) * ((n : ℝ) - ℓ) / a := by
    refine hLift.symm.trans ?_
    simpa only [mul_div_assoc] using hGaussian
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hℓ : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (by omega)
  have ha : 0 < a := by
    have h : (k : ℝ) + 1 < ℓ := by exact_mod_cast hkℓ
    dsimp [a]
    linarith
  apply mul_left_cancel₀ hn.ne'
  rw [hScale]
  dsimp only [c]
  field_simp [hℓ.ne', ha.ne', hn.ne']

private theorem trace_outer_mul (u : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) :
    (vecMulVec u.ofLp u.ofLp * A).trace = inner ℝ (A.toEuclideanLin u) u := by
  rw [trace_mul_comm, mul_vecMulVec, trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct]
  change (A *ᵥ u.ofLp) ⬝ᵥ u.ofLp = u.ofLp ⬝ᵥ star (A *ᵥ u.ofLp)
  simp only [star_trivial]
  exact dotProduct_comm _ _

private theorem frame_projector_inner (V : Matrix (Fin n) (Fin k) ℝ)
    (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((V * Vᵀ).toEuclideanLin u) u = haarFrameQuadratic u V := by
  rw [euclidean_mul, LinearMap.comp_apply, haarFrameQuadratic, ← real_inner_self_eq_norm_sq,
    euclidean_transpose, LinearMap.adjoint_inner_left, real_inner_comm]

/-- The fixed-projector covariance, evaluated against a quadratic test
direction. This is the Gaussian-lift route used in the revised manuscript. -/
theorem integral_haarProjectedInverseTrace_covariance_lift (hℓn : ℓ ≤ n)
    (hkℓ : k + 1 < ℓ) (hk : 0 < k) (P : OrthogonalProjector n ℓ)
    (u : EuclideanSpace ℝ (Fin n)) :
    (∫ V : Matrix (Fin n) (Fin k) ℝ,
      ((Vᵀ * P.val * V)⁻¹.trace -
        (k : ℝ) * (((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1))) *
        haarFrameQuadratic u V ∂gaussianHaarFrameLaw (show k ≤ n by omega)) =
      (-2 * (k : ℝ)) / ((ℓ : ℝ) * ((ℓ : ℝ) - k - 1)) *
        (‖P.val.toEuclideanLin u‖ ^ 2 - ((ℓ : ℝ) / (n : ℝ)) * ‖u‖ ^ 2) := by
  have hkn : k ≤ n := by omega
  let w (V : Matrix (Fin n) (Fin k) ℝ) := (Vᵀ * P.val * V)⁻¹.trace -
    (k : ℝ) * (((n : ℝ) - k - 1) / ((ℓ : ℝ) - k - 1))
  let D := vecMulVec u.ofLp u.ofLp
  have hI : Integrable w (gaussianHaarFrameLaw hkn) :=
    (haarProjectedInverseTrace_mean hℓn hk hkℓ P).1.sub (integrable_const _)
  have hPair := trace_mul_haarWeightedTargetProjector hkn hI D
  have hDP : (D * P.val).trace = ‖P.val.toEuclideanLin u‖ ^ 2 := by
    rw [trace_outer_mul, ← orientationRowSpace_starProjection]
    exact (orientationRowSpace P).re_inner_starProjection_eq_normSq u
  have hD : D.trace = ‖u‖ ^ 2 := by
    rw [← Matrix.mul_one D, trace_outer_mul]
    change inner ℝ ((toLpLin 2 2 (1 : Matrix (Fin n) (Fin n) ℝ)) u) u = _
    rw [Matrix.toLpLin_one, LinearMap.id_apply, real_inner_self_eq_norm_sq]
  change (∫ V, w V * haarFrameQuadratic u V ∂gaussianHaarFrameLaw hkn) = _
  calc
    _ = (D * haarWeightedTargetProjector hkn w).trace := by
      rw [hPair]
      simp only [D, trace_outer_mul, frame_projector_inner]
    _ = _ := by
      rw [haarProjectedInverseTrace_centeredProjector_lift hℓn hkℓ hk P,
        Matrix.mul_smul, trace_smul, smul_eq_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
        trace_sub, trace_smul, smul_eq_mul, hDP, hD]

end SketchOrientation
