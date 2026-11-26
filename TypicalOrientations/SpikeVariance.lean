import TypicalOrientations.SpikeCovariance
import SketchOrientation.GaussianOrientationConverseMoments

namespace TypicalOrientations

open MeasureTheory ProbabilityTheory SketchOrientation
open scoped InnerProductSpace

private abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem measurable_directionalTest {n : ℕ} (u : Ambient n) :
    Measurable (spikeDirectionalTest u) :=
  ((measurable_sphere_inner_sq u).const_mul (n : ℝ)).sub_const 1

private theorem directionalTest_norm_le {n : ℕ} (u x : Ambient n) (hu : ‖u‖ = 1) :
    ‖spikeDirectionalTest u x‖ ≤ (n : ℝ) + 1 := by
  let t := (inner ℝ u (sphereNormalize x)) ^ 2
  have ht : t ≤ 1 := by simpa only [hu, one_pow] using sphere_inner_sq_le u x
  change ‖(n : ℝ) * t - 1‖ ≤ (n : ℝ) + 1
  calc
    _ ≤ ‖(n : ℝ) * t‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
    _ = (n : ℝ) * t + 1 := by rw [Real.norm_of_nonneg (by positivity), norm_one]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)]

theorem spikeDirectionalTest_square_mean {n : ℕ} (hn : 1 < n)
    (u : Ambient n) (hu : ‖u‖ = 1) :
    (∫ x, spikeDirectionalTest u x ^ 2 ∂stdGaussian (Ambient n)) =
      2 * ((n : ℝ) - 1) / ((n : ℝ) + 2) := by
  let R := (ℝ ∙ u)
  let q := fun x : Ambient n => (inner ℝ u (sphereNormalize x)) ^ 2
  let γ := stdGaussian (Ambient n)
  let a : ℝ := 1 / 2
  let b : ℝ := ((n : ℝ) - 1) / 2
  let β := betaMeasure a b
  have hu' : u ≠ 0 := by rintro rfl; simp at hu
  have hR : Module.finrank ℝ R = 1 := finrank_span_singleton hu'
  have hC : Module.finrank ℝ Rᗮ = n - 1 := by
    have h := R.finrank_add_finrank_orthogonal
    rw [hR, finrank_euclideanSpace_fin] at h
    omega
  have hProj : sphereProjectionEnergy R = q := by
    funext x
    rw [sphereProjectionEnergy, show R = (ℝ ∙ u) from rfl,
      Submodule.starProjection_unit_singleton ℝ hu, norm_smul, hu, mul_one,
      Real.norm_eq_abs, sq_abs]
  have hLaw : γ.map q = β := by
    have h := stdGaussian_sphere_projected_sq_beta R (by omega) (by omega)
    change γ.map (sphereProjectionEnergy R) = _ at h
    rw [hR, hC, Nat.cast_sub (by omega), Nat.cast_one, hProj] at h
    exact h
  have hM : Measurable q := measurable_sphere_inner_sq u
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hA : 0 < a := by norm_num [a]
  have hB : 0 < b := half_pos (sub_pos.mpr hn')
  have h1 := beta_mean hA hB
  have h2 := beta_nat_moment hA hB 2
  have hId : Measurable (fun t : ℝ => t) := measurable_id
  have hSq : Measurable (fun t : ℝ => t ^ 2) := measurable_id.pow_const _
  have hI1 : Integrable q γ :=
    (MeasurePreserving.mk hM hLaw).integrable_comp_of_integrable h1.1
  have hI2 : Integrable (fun x => q x ^ 2) γ :=
    (MeasurePreserving.mk hM hLaw).integrable_comp_of_integrable h2.1
  have hN : (0 : ℝ) < n := by linarith
  have hMean1 : (∫ x, q x ∂γ) = 1 / (n : ℝ) := by
    rw [← integral_map hM.aemeasurable hId.aestronglyMeasurable, hLaw, h1.2]
    dsimp [a, b]
    field_simp [hN.ne']
    ring
  have hMean2 : (∫ x, q x ^ 2 ∂γ) = 3 / ((n : ℝ) * ((n : ℝ) + 2)) := by
    rw [← integral_map hM.aemeasurable hSq.aestronglyMeasurable, hLaw, h2.2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      add_zero, one_mul, a, b]
    have hD : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    field_simp [hN.ne', hD.ne']
    ring
  have hExpand (x : Ambient n) :
      spikeDirectionalTest u x ^ 2 = ((n : ℝ)^2 * q x ^ 2 - (2 * (n : ℝ)) * q x) + 1 := by
    unfold spikeDirectionalTest q
    ring
  simp_rw [hExpand]
  have hFirst : Integrable (fun x => (n : ℝ)^2 * q x ^ 2) γ := hI2.const_mul _
  have hSecond : Integrable (fun x => (2 * (n : ℝ)) * q x) γ := hI1.const_mul _
  have hSum := integral_add (hFirst.sub hSecond) (integrable_const (μ := γ) (1 : ℝ))
  simp only [Pi.sub_apply] at hSum
  rw [hSum, integral_sub hFirst hSecond, integral_const_mul, integral_const_mul,
    hMean1, hMean2, integral_const, probReal_univ, one_smul]
  field_simp [hN.ne', (show (0 : ℝ) < (n : ℝ) + 2 by positivity).ne']
  ring

set_option maxHeartbeats 1500000 in
/-- Cauchy–Schwarz with the manuscript's centered quadratic test. Boundedness
of the conditional reciprocal changes its variance into absolute deviation. -/
theorem spike_covariance_sq_le_twice_deviation {n ℓ : ℕ} (hn : 1 < n)
    (μ : Measure (OrthogonalProjector n ℓ)) [IsProbabilityMeasure μ]
    (u : Ambient n) (hu : ‖u‖ = 1) :
    covariance (spikeConditionalAverage μ) (spikeDirectionalTest u)
      (stdGaussian (Ambient n)) ^ 2 ≤
      2 * (∫ x, |spikeConditionalAverage μ x -
        ∫ y, spikeConditionalAverage μ y ∂stdGaussian (Ambient n)| ∂stdGaussian (Ambient n)) := by
  let γ := stdGaussian (Ambient n)
  let J := spikeConditionalAverage μ
  let H := spikeDirectionalTest u
  let m := ∫ x, J x ∂γ
  let X := fun x => J x - m
  let Jvar := ∫ x, X x ^ 2 ∂γ
  let Hvar := ∫ x, H x ^ 2 ∂γ
  let A := ∫ x, |X x| ∂γ
  have hJ (x : Ambient n) : J x ∈ Set.Icc (0 : ℝ) 1 :=
    spikeConditionalAverage_mem_Icc μ x
  have hJM : Measurable J := measurable_spikeConditionalAverage μ
  have hJI : Integrable J γ := (integrable_const (1 : ℝ)).mono' hJM.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hJ x).1]; exact (hJ x).2)
  have hM0 : 0 ≤ m := integral_nonneg fun x => (hJ x).1
  have hM1 : m ≤ 1 := by
    have hm := integral_mono hJI (integrable_const (1 : ℝ)) (fun x => (hJ x).2)
    simpa only [integral_const, probReal_univ, one_smul] using hm
  have hXM : Measurable X := hJM.sub_const _
  have hX (x : Ambient n) : |X x| ≤ 1 := by
    apply abs_le.mpr
    change -1 ≤ J x - m ∧ J x - m ≤ 1
    exact ⟨by linarith [(hJ x).1], by linarith [(hJ x).2]⟩
  have hNormX (x : Ambient n) : ‖X x‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hX x
  have hL2X : MemLp X (ENNReal.ofReal 2) γ :=
    MemLp.of_bound hXM.aestronglyMeasurable 1 (ae_of_all _ hNormX)
  have hL2H : MemLp H (ENNReal.ofReal 2) γ :=
    MemLp.of_bound (measurable_directionalTest u).aestronglyMeasurable ((n : ℝ) + 1)
      (ae_of_all _ fun x => directionalTest_norm_le u x hu)
  have hX2 := hL2X
  have hH2 := hL2H
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [h2] at hX2 hH2
  have hHH : (∫ x, H x ∂γ) = 0 := by
    have h0 := integral_radial_weighted_sphere_inner_sq (E := Ambient n)
      (by simp; omega) (fun _ => 1) measurable_const (integrable_const 1) u
    simp only [one_mul, finrank_euclideanSpace_fin, hu, one_pow,
      integral_const, probReal_univ, one_smul, mul_one] at h0
    have hQ : Integrable (fun x : Ambient n => (inner ℝ u (sphereNormalize x)) ^ (2 : ℕ)) γ := by
      simpa using integrable_radial_weighted_sphere_inner_sq (E := Ambient n)
        (fun _ => 1) measurable_const (integrable_const 1) u
    unfold H spikeDirectionalTest
    rw [integral_sub (hQ.const_mul _) (integrable_const _), integral_const_mul, h0,
      integral_const, probReal_univ, one_smul, mul_one_div,
      div_self (Nat.cast_ne_zero.mpr (by omega)), sub_self]
  have hCov : covariance J H γ = ∫ x, X x * H x ∂γ := by
    simp only [covariance, hHH, sub_zero, X, m]
  have hJvar0 : 0 ≤ Jvar := integral_nonneg fun _ => sq_nonneg _
  have hHvar0 : 0 ≤ Hvar := integral_nonneg fun _ => sq_nonneg _
  have hVars : Jvar ≤ A := by
    apply integral_mono (hX2.integrable_mul hX2 |>.congr (ae_of_all _ fun _ => by simp only [Pi.mul_apply, pow_two]))
      (hJI.sub (integrable_const m)).abs
    intro x
    change X x ^ 2 ≤ |X x|
    rw [← sq_abs]
    nlinarith [abs_nonneg (X x), hX x]
  have hHvar : Hvar ≤ 2 := by
    change (∫ x, spikeDirectionalTest u x ^ 2 ∂stdGaussian (Ambient n)) ≤ 2
    rw [spikeDirectionalTest_square_mean hn u hu]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := γ) Real.HolderConjugate.two_two hL2X hL2H
  have hC : |covariance J H γ| ≤ Real.sqrt Jvar * Real.sqrt Hvar := by
    rw [hCov]
    calc
      _ ≤ ∫ x, |X x * H x| ∂γ := abs_integral_le_integral_abs
      _ = ∫ x, ‖X x‖ * ‖H x‖ ∂γ := by simp only [abs_mul, Real.norm_eq_abs]
      _ ≤ _ := by
        simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow,
          Jvar, Hvar] using hHolder
  have hSq := pow_le_pow_left₀ (abs_nonneg (covariance J H γ)) hC 2
  rw [sq_abs, mul_pow, Real.sq_sqrt hJvar0, Real.sq_sqrt hHvar0] at hSq
  exact hSq.trans ((mul_le_mul_of_nonneg_left hHvar hJvar0).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hVars (show (0 : ℝ) ≤ 2 by norm_num)))

end TypicalOrientations
