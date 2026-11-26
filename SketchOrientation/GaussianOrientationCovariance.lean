import SketchOrientation.GaussianLiftHaarCovariance
import Mathlib.Probability.Moments.Covariance

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {n k ℓ : ℕ}

set_option maxHeartbeats 1500000 in
/-- Equation (3.9) evaluated against a rank-one quadratic test matrix.
The sketch law is arbitrary and the target orientation is genuine Haar. -/
theorem haarOrientationEndpoint_rankOne_covariance (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (hk : 0 < k) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    (u : EuclideanSpace ℝ (Fin n)) :
    (∫ V : Matrix (Fin n) (Fin k) ℝ,
        (haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ) * haarFrameQuadratic u V
      ∂gaussianHaarFrameLaw (show k ≤ n by omega)) =
      -2 / ((ℓ : ℝ) * ((ℓ : ℝ) - k - 1) * ((n : ℝ) - k)) *
        (inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u - (ℓ : ℝ) / n * ‖u‖ ^ 2) := by
  let η := gaussianHaarFrameLaw (show k ≤ n by omega)
  let b := (n : ℝ) - k - 1
  let c := (n : ℝ) - k
  let a := (ℓ : ℝ) - k - 1
  let F := Function.uncurry (@gaussianOrientationScore n k ℓ)
  let g := @haarFrameQuadratic n k u
  let Z := fun z : OrthogonalProjector n ℓ × Matrix (Fin n) (Fin k) ℝ =>
    (F z - b / a) * g z.2
  have hZ : Measurable Z :=
    (measurable_gaussianOrientationScore.sub_const (b / a)).mul
      ((measurable_haarFrameQuadratic u).comp measurable_snd)
  have hη : ∀ᵐ z ∂ν.prod η, z.2ᵀ * z.2 = (1 : Matrix (Fin k) (Fin k) ℝ) :=
    (measurePreserving_snd (μ := ν) (ν := η)).quasiMeasurePreserving.ae
      (ae_gaussianHaarFrame_orthonormal (show k ≤ n by omega))
  have hF : Integrable F (ν.prod η) := by
    have har : (1 : ℝ) < ((ℓ - k + 1 : ℕ) : ℝ) / 2 := by
      have h : (2 : ℝ) < ((ℓ - k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 2 < ℓ - k + 1 by omega)
      linarith
    simpa only [F, Real.rpow_one, Function.uncurry_def] using
      (haarOrientationScore_moment_prod hℓn hk hkℓ ν le_rfl har).1
  have hI : Integrable Z (ν.prod η) := by
    refine ((hF.sub (integrable_const (b / a))).norm.mul_const (‖u‖ ^ 2)).mono'
      hZ.aestronglyMeasurable ?_
    filter_upwards [hη] with z hz
    change ‖(F z - b / a) * g z.2‖ ≤ ‖F z - b / a‖ * ‖u‖ ^ 2
    have h0 : 0 ≤ g z.2 := sq_nonneg _
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (haarFrameQuadratic_le z.2 hz u) (norm_nonneg _)
  have hY : (fun V => (haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ) * g V)
      =ᵐ[η] fun V => (∫ P, Z (P, V) ∂ν) / c := by
    filter_upwards [hF.prod_left_ae] with V hV
    change ((haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ) * g V) =
      (∫ P, (F (P, V) - b / a) * g V ∂ν) / c
    rw [integral_mul_const, integral_sub hV (integrable_const (b / a)),
      integral_const, probReal_univ, one_smul]
    unfold haarOrientationEndpoint haarOrientationBenchmark
    change (((∫ P, F (P, V) ∂ν) - (ℓ : ℝ) / k) / c -
      (b * (1 / a) - (ℓ : ℝ) / k) / c) * g V =
      ((∫ P, F (P, V) ∂ν) - b / a) * g V / c
    ring
  have hP (P : OrthogonalProjector n ℓ) :
      (∫ V, Z (P, V) ∂η) =
        -2 / ((ℓ : ℝ) * a) *
          (‖P.val.toEuclideanLin u‖ ^ 2 - (ℓ : ℝ) / n * ‖u‖ ^ 2) := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have he (V : Matrix (Fin n) (Fin k) ℝ) : Z (P, V) =
        (((Vᵀ * P.val * V)⁻¹.trace - (k : ℝ) * (b / a)) * g V) / k := by
      change ((Vᵀ * P.val * V)⁻¹.trace / (k : ℝ) - b / a) * g V = _
      field_simp [hk']
    simp_rw [he]
    rw [integral_div, integral_haarProjectedInverseTrace_covariance_lift hℓn hkℓ hk P u]
    change ((-2 * (k : ℝ)) / ((ℓ : ℝ) * a) *
      (‖P.val.toEuclideanLin u‖ ^ 2 - (ℓ : ℝ) / n * ‖u‖ ^ 2)) / (k : ℝ) = _
    field_simp [hk']
  change (∫ V, (haarOrientationEndpoint ν V - haarOrientationBenchmark n k ℓ) * g V ∂η) = _
  rw [integral_congr_ae hY, integral_div, ← integral_prod_symm _ hI, integral_prod _ hI]
  simp_rw [hP]
  have hProjI : Integrable (fun P : OrthogonalProjector n ℓ => ‖P.val.toEuclideanLin u‖ ^ 2) ν := by
    simpa only [orientationRowSpace_starProjection] using
      integrable_projected_energy ν orientationRowSpace u (measurable_orientationRowSpace_projection u)
  rw [integral_const_mul, integral_sub hProjI (integrable_const _), integral_const, probReal_univ, one_smul]
  have hm : (∫ P : OrthogonalProjector n ℓ, ‖P.val.toEuclideanLin u‖ ^ 2 ∂ν) =
      inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u := by
    simpa only [orientationRowSpace_starProjection] using (meanSketchProjector_inner ν u).symm
  rw [hm]
  let x := inner ℝ ((meanSketchProjector ν).toEuclideanLin u) u - (ℓ : ℝ) / n * ‖u‖ ^ 2
  change (-2 / ((ℓ : ℝ) * a) * x) / c = -2 / ((ℓ : ℝ) * a * c) * x
  calc
    _ = (-2 * x) / ((ℓ : ℝ) * a * c) := by rw [div_mul_eq_mul_div, div_div]
    _ = _ := by rw [div_mul_eq_mul_div]

private theorem trace_mul_eigenvectorQuadratic (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    (A * B).trace =
      ∑ j, hA.eigenvalues j * inner ℝ (B.toEuclideanLin (hA.eigenvectorBasis j))
        (hA.eigenvectorBasis j) := by
  let E := EuclideanSpace ℝ (Fin n)
  let b := hA.eigenvectorBasis
  have hTr : (A * B).trace = LinearMap.trace ℝ E (A * B).toEuclideanLin := by
    change (A * B).trace = LinearMap.trace ℝ E (toLpLin 2 2 (A * B))
    rw [Matrix.toLpLin_eq_toLin, Matrix.trace_toLin_eq]
  have hAdj : A.toEuclideanLin.adjoint = A.toEuclideanLin := by
    rw [← euclidean_transpose]
    simpa only [conjTranspose_eq_transpose_of_trivial] using congrArg Matrix.toEuclideanLin hA.eq
  have hEig (j : Fin n) : A.toEuclideanLin (b j) = hA.eigenvalues j • (b j) := by
    ext i
    exact congrFun (hA.mulVec_eigenvectorBasis j) i
  rw [hTr, euclidean_mul, LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.comp_apply]
  change b.toBasis.repr (A.toEuclideanLin (B.toEuclideanLin (b i))) i = _
  rw [show b.toBasis.repr (A.toEuclideanLin (B.toEuclideanLin (b i))) i =
      inner ℝ (b i) (A.toEuclideanLin (B.toEuclideanLin (b i))) from b.repr_apply_apply _ _]
  rw [← LinearMap.adjoint_inner_left, hAdj, hEig, real_inner_smul_left, real_inner_comm]

private theorem matrix_frameQuadratic_pair (V : Matrix (Fin n) (Fin k) ℝ)
    (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((V * Vᵀ).toEuclideanLin u) u = haarFrameQuadratic u V := by
  rw [euclidean_mul, LinearMap.comp_apply, haarFrameQuadratic, ← real_inner_self_eq_norm_sq,
    euclidean_transpose, LinearMap.adjoint_inner_left, real_inner_comm]

set_option maxHeartbeats 1600000 in
/-- The manuscript's full covariance identity for every real symmetric
test matrix and every law of sketch projectors. -/
theorem haarOrientationEndpoint_covariance (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (hk : 0 < k) (ν : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure ν]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    covariance (haarOrientationEndpoint (k := k) ν) (fun V => (A * (V * Vᵀ)).trace)
        (gaussianHaarFrameLaw (show k ≤ n by omega)) =
      -2 / ((ℓ : ℝ) * ((ℓ : ℝ) - k - 1) * ((n : ℝ) - k)) *
        ((meanSketchProjector ν - ((ℓ : ℝ) / n) • 1) * A).trace := by
  let η := gaussianHaarFrameLaw (show k ≤ n by omega)
  let b := hA.eigenvectorBasis
  let B := meanSketchProjector ν - ((ℓ : ℝ) / n) • 1
  let h := haarOrientationBenchmark n k ℓ
  let F := haarOrientationEndpoint (k := k) ν
  let Z := fun V : Matrix (Fin n) (Fin k) ℝ => F V - h
  let d := -2 / ((ℓ : ℝ) * ((ℓ : ℝ) - k - 1) * ((n : ℝ) - k))
  let Q := fun V : Matrix (Fin n) (Fin k) ℝ => (A * (V * Vᵀ)).trace
  have hF := haarOrientationEndpoint_mean hℓn hk hkℓ ν
  have hZI : Integrable Z η := hF.1.sub (integrable_const h)
  have hZ0 : (∫ V, Z V ∂η) = 0 := by
    change (∫ V, F V - h ∂η) = 0
    rw [integral_sub hF.1 (integrable_const h), hF.2, integral_const, probReal_univ, one_smul]
    exact sub_self _
  have hQ (V : Matrix (Fin n) (Fin k) ℝ) : Q V =
      ∑ j, hA.eigenvalues j * haarFrameQuadratic (b j) V := by
    dsimp only [Q]
    rw [trace_mul_eigenvectorQuadratic A _ hA]
    simp only [matrix_frameQuadratic_pair]
    rfl
  have hTermI (j : Fin n) : Integrable (fun V => Z V * haarFrameQuadratic (b j) V) η := by
    have hm : Measurable Z := (measurable_haarOrientationEndpoint ν).sub_const h
    refine (hZI.norm.mul_const (‖b j‖ ^ 2)).mono'
      (hm.mul (measurable_haarFrameQuadratic (b j))).aestronglyMeasurable ?_
    filter_upwards [ae_gaussianHaarFrame_orthonormal (show k ≤ n by omega)] with V hV
    have h0 : 0 ≤ haarFrameQuadratic (b j) V := sq_nonneg _
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (haarFrameQuadratic_le V hV _) (norm_nonneg _)
  have hI (j : Fin n) : Integrable (fun V => hA.eigenvalues j * (Z V * haarFrameQuadratic (b j) V)) η :=
    (hTermI j).const_mul _
  have hProd : Integrable (fun V => Z V * Q V) η := by
    have he (V : Matrix (Fin n) (Fin k) ℝ) :
        Z V * Q V = ∑ j, hA.eigenvalues j * (Z V * haarFrameQuadratic (b j) V) := by
      rw [hQ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he]
    exact integrable_finsetSum _ fun j _ => hI j
  have hB (j : Fin n) : inner ℝ (B.toEuclideanLin (b j)) (b j) =
      inner ℝ ((meanSketchProjector ν).toEuclideanLin (b j)) (b j) -
        (ℓ : ℝ) / n * ‖b j‖ ^ 2 := by
    unfold B
    rw [map_sub, map_smul, Matrix.toLpLin_one]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  change covariance F Q η = d * (B * A).trace
  unfold covariance
  rw [hF.2]
  change (∫ V, Z V * (Q V - ∫ W, Q W ∂η) ∂η) = _
  simp_rw [mul_sub]
  rw [integral_sub hProd (hZI.mul_const _), integral_mul_const, hZ0, zero_mul, sub_zero,
    Matrix.trace_mul_comm B A, trace_mul_eigenvectorQuadratic A B hA]
  simp_rw [hQ, Finset.mul_sum]
  have hFub (j : Fin n) : Integrable (fun V => Z V * (hA.eigenvalues j * haarFrameQuadratic (b j) V)) η := by
    simpa only [mul_left_comm] using hI j
  rw [integral_finsetSum _ (fun j _ => hFub j)]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_left_comm (Z _), integral_const_mul]
  rw [haarOrientationEndpoint_rankOne_covariance hℓn hkℓ hk ν (b j), hB]
  change hA.eigenvalues j * (d * _) = d * (hA.eigenvalues j * _)
  ring

end SketchOrientation
