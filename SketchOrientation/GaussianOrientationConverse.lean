import SketchOrientation.GaussianOrientationCovariance
import SketchOrientation.GaussianOrientationConverseMoments
import SketchOrientation.GaussianOrientationGapConvergence
import SketchOrientation.GaussianMixedExpectationConvergence

namespace SketchOrientation

open MeasureTheory Filter Matrix
open scoped InnerProductSpace Topology

variable {n k p : ℕ}

private theorem integral_centered_endpoint_times_directionTest
    (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n)
    (ν : Measure (OrthogonalProjector n (k + p))) [IsProbabilityMeasure ν]
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (huρ : inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u =
      ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖) :
    let η := gaussianHaarFrameLaw (show k ≤ n by omega)
    (∫ V, (haarOrientationEndpoint ν V - haarOrientationBenchmark n k (k + p)) *
      ((n : ℝ) * haarFrameQuadratic u V - (k : ℝ)) ∂η) =
        -2 * (n : ℝ) / (((k + p : ℕ) : ℝ) * ((p : ℝ) - 1) * ((n : ℝ) - k)) *
          (‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖ -
            ((k + p : ℕ) : ℝ) / n) := by
  intro η
  have hkp : k + 1 < k + p := by omega
  let Z := fun V => haarOrientationEndpoint (k := k) ν V - haarOrientationBenchmark n k (k + p)
  let Q := @haarFrameQuadratic n k u
  have hZI : Integrable Z η :=
    (haarOrientationEndpoint_mean hn hk hkp ν).1.sub (integrable_const _)
  have hZM : (∫ V, Z V ∂η) = 0 := by
    unfold Z
    rw [integral_sub (haarOrientationEndpoint_mean hn hk hkp ν).1 (integrable_const _),
      (haarOrientationEndpoint_mean hn hk hkp ν).2, integral_const, probReal_univ, one_smul,
      sub_self]
  have hZI' : Integrable (fun V => Z V * Q V) η := by
    have hm : Measurable Z := (measurable_haarOrientationEndpoint ν).sub_const _
    refine (hZI.norm.mul_const (‖u‖ ^ 2)).mono'
      (hm.mul (measurable_haarFrameQuadratic u)).aestronglyMeasurable ?_
    filter_upwards [ae_gaussianHaarFrame_orthonormal (show k ≤ n by omega)] with V hV
    have h0 : 0 ≤ Q V := sq_nonneg _
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (haarFrameQuadratic_le V hV u) (norm_nonneg _)
  have he (V : Matrix (Fin n) (Fin k) ℝ) :
      Z V * ((n : ℝ) * Q V - (k : ℝ)) = (n : ℝ) * (Z V * Q V) - Z V * (k : ℝ) :=
    by ring
  change (∫ V, Z V * ((n : ℝ) * Q V - (k : ℝ)) ∂η) = _
  simp_rw [he]
  rw [integral_sub (hZI'.const_mul _) (hZI.mul_const _), integral_const_mul, integral_mul_const,
    hZM, zero_mul, sub_zero]
  have hc := haarOrientationEndpoint_rankOne_covariance hn hkp hk ν u
  change (n : ℝ) * (∫ V, Z V * haarFrameQuadratic u V ∂η) = _
  rw [hc, huρ, hu, one_pow, mul_one]
  push_cast
  rw [show (k : ℝ) + p - k - 1 = (p : ℝ) - 1 by ring]
  ring

set_option maxHeartbeats 1800000 in
/-- Necessity in Theorem 1.1. Probability convergence of the loss forces
the Euclidean operator norm of the mean sketch projector to vanish. -/
theorem haarOrientationDiffuse_of_probability (hk : 0 < k) (hp : 2 ≤ p)
    (D : ℕ → ℕ) (hD : ∀ i, k + p ≤ D i) (hDt : Tendsto D atTop atTop)
    (ν : ∀ i, Measure (OrthogonalProjector (D i) (k + p)))
    [∀ i, IsProbabilityMeasure (ν i)] (Γ : ℕ → WithTop ℝ)
    (hΓ : Tendsto (fun i => orientationGapScale (D i) k (Γ i)) atTop (𝓝 ⊤))
    (hP : ∀ ε : ℝ, 0 < ε → Tendsto (fun i =>
      (gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))).real
        {V | ε ≤ |haarOrientationMeanAt (k := k) (ν i) (Γ i) V -
          haarOrientationBenchmark (D i) k (k + p)|}) atTop (𝓝 0)) :
    Tendsto (fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖)
      atTop (𝓝 0) := by
  have hn (i : ℕ) : 0 < D i := by have := hD i; omega
  have hkD (i : ℕ) : k < D i := by have := hD i; omega
  let ρ := fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖
  let η (i : ℕ) := gaussianHaarFrameLaw (show k ≤ D i from le_trans (Nat.le_add_right _ _) (hD i))
  let X (i : ℕ) := fun V : Matrix (Fin (D i)) (Fin k) ℝ =>
    haarOrientationEndpoint (ν i) V - haarOrientationBenchmark (D i) k (k + p)
  choose u hu huρ using fun i => exists_unit_meanSketchProjector_rayleigh_eq_norm (hn i) (ν i)
  let Y (i : ℕ) := fun V : Matrix (Fin (D i)) (Fin k) ℝ =>
    (D i : ℝ) * haarFrameQuadratic (u i) V - (k : ℝ)
  have hX (i : ℕ) : Measurable (X i) :=
    (measurable_haarOrientationEndpoint (ν i)).sub_const _
  have hY (i : ℕ) : Measurable (Y i) :=
    ((measurable_haarFrameQuadratic (u i)).const_mul _).sub_const _
  let C := chiSquareNegativeMoment (p + 1) ((5 : ℝ) / 4) + 1
  let K := (∏ j ∈ Finset.range 10, ((k : ℝ) + 2 * j)) + (k : ℝ) ^ (10 : ℕ)
  have hMX (i : ℕ) : Integrable (fun V => (|X i V| : ℝ) ^ ((5 : ℝ) / 4)) (η i) ∧
      (∫ V, (|X i V| : ℝ) ^ ((5 : ℝ) / 4) ∂η i) ≤ C :=
    haarOrientationEndpoint_centered_rpow_bound (hD i) hk hp (ν i)
  have hMY (i : ℕ) : Integrable (fun V => (|Y i V| : ℝ) ^ (10 : ℝ)) (η i) ∧
      (∫ V, (|Y i V| : ℝ) ^ (10 : ℝ) ∂η i) ≤ K :=
    haarFrameDirectionTest_moment hk (hkD i) (u i) (hu i)
  have hC0 : 0 ≤ C := (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)).trans (hMX 0).2
  have hK0 : 0 ≤ K := (integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)).trans (hMY 0).2
  have hProb : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (η i).real {z | ε ≤ |X i z|}) atTop (𝓝 0) :=
    haarOrientationEndpointProbability_of_observed hk hp D hD ν Γ hΓ hP
  let Z := fun i => ∫ V, X i V * Y i V ∂η i
  have hZt : Tendsto Z atTop (𝓝 0) :=
    mixed_expectation_tendsto_zero η X Y hX hY hC0 hK0 hMX hMY hProb
  let L := ((k + p : ℕ) : ℝ)
  have hL : 0 < L := Nat.cast_pos.mpr (by omega)
  have hp1 : 0 < (p : ℝ) - 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hCov (i : ℕ) : Z i =
      -2 * (D i : ℝ) / (L * ((p : ℝ) - 1) * ((D i : ℝ) - k)) *
        (ρ i - L / (D i : ℝ)) :=
    integral_centered_endpoint_times_directionTest hk hp (hD i) (ν i) (u i) (hu i) (huρ i)
  have hR (i : ℕ) : ρ i = L / (D i : ℝ) -
        (L * ((p : ℝ) - 1) / 2 * (1 - (k : ℝ) / (D i : ℝ))) * Z i := by
    have hi : (0 : ℝ) < D i := Nat.cast_pos.mpr (hn i)
    have hi' : (0 : ℝ) < (D i : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkD i)
    rw [hCov]
    field_simp [hL.ne', hp1.ne', hi.ne', hi'.ne']
    ring
  have hDn : Tendsto (fun i => (D i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDt
  have hDinv : Tendsto (fun i => (D i : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hDn
  have hQ (a : ℝ) : Tendsto (fun i => a / (D i : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hDinv.const_mul a
  have hZ' := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hQ k)).const_mul
    (L * ((p : ℝ) - 1) / 2)
  have hh := (hQ L).sub (hZ'.mul hZt)
  simp only [sub_zero, mul_zero] at hh
  exact hh.congr (fun i => (hR i).symm)

end SketchOrientation
