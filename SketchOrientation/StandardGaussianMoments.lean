import Mathlib.Probability.Distributions.Gaussian.Real

namespace SketchOrientation

open MeasureTheory ProbabilityTheory

private theorem standardGaussian_mgf_eq :
    mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
  rw [mgf_fun_id_gaussianReal]
  simp

/-- Integrability of every integer power under the scalar standard Gaussian. -/
theorem standardGaussian_power_integrable (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) n

private theorem gaussianMgfExp_deriv (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
  have h : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    apply (((hasDerivAt_id t).pow 2).div_const 2).congr_deriv
    simp
  apply h.exp.congr_deriv
  ring

private theorem gaussianMgfExp_second :
    iteratedDeriv 2 (fun s : ℝ => Real.exp (s ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one]
  simp_rw [funext fun t => (gaussianMgfExp_deriv t).deriv]
  funext t
  apply HasDerivAt.deriv
  apply ((hasDerivAt_id t).mul (gaussianMgfExp_deriv t)).congr_deriv
  simp only [id_eq]
  ring

/-- The native scalar Gaussian has second raw moment one. -/
theorem standardGaussian_second_moment :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 2
  change iteratedDeriv 2 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 =
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) at h
  rw [standardGaussian_mgf_eq, gaussianMgfExp_second] at h
  norm_num at h
  exact h.symm

/-- The fourth moment of the scalar standard Gaussian is three. -/
theorem standardGaussian_fourth_moment :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have h3 : iteratedDeriv 3 (fun s : ℝ => Real.exp (s ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    rw [show (3 : ℕ) = 2 + 1 by decide, iteratedDeriv_succ, gaussianMgfExp_second]
    funext t
    apply HasDerivAt.deriv
    have h : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).const_add 1
    apply (h.mul (gaussianMgfExp_deriv t)).congr_deriv
    ring
  have h4 : iteratedDeriv 4 (fun s : ℝ => Real.exp (s ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    change iteratedDeriv (3 + 1) (fun s : ℝ => Real.exp (s ^ 2 / 2)) = _
    rw [iteratedDeriv_succ, h3]
    funext t
    apply HasDerivAt.deriv
    have h : HasDerivAt (fun s : ℝ => 3 * s + s ^ 3) (3 + 3 * t ^ 2) t := by
      have h0 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      exact ((h0.const_mul 3).add (h0.pow 3)).congr_deriv (by simp)
    apply (h.mul (gaussianMgfExp_deriv t)).congr_deriv
    ring
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 4
  change iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 =
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) at h
  rw [standardGaussian_mgf_eq, h4] at h
  norm_num at h
  exact h.symm

end SketchOrientation
