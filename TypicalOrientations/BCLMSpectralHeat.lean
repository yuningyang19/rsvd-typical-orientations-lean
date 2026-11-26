import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace TypicalOrientations

open Filter
open scoped InnerProductSpace Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)

private abbrev basisIndex (E : Type*) [AddCommGroup E] [Module ℝ E] := Fin (Module.finrank ℝ E)

private def heatBasis : OrthonormalBasis (basisIndex E) ℝ E :=
  hA.eigenvectorBasis rfl

private def heatEigenvalues : basisIndex E → ℝ := hA.eigenvalues rfl

private theorem heatBasis_eigen (i : basisIndex E) :
    A (heatBasis hA i) = heatEigenvalues hA i • heatBasis hA i :=
  hA.apply_eigenvectorBasis rfl i

/-- Finite-dimensional heat evolution defined by the spectral theorem. -/
def spectralHeat (t : ℝ) : E →ₗ[ℝ] E :=
  ∑ i : basisIndex E, Real.exp (t * heatEigenvalues hA i) •
    (InnerProductSpace.rankOne ℝ (heatBasis hA i) (heatBasis hA i)).toLinearMap

theorem spectralHeat_apply (t : ℝ) (x : E) :
    spectralHeat hA t x =
      ∑ i : basisIndex E, (Real.exp (t * heatEigenvalues hA i) *
        ⟪heatBasis hA i, x⟫_ℝ) • heatBasis hA i := by
  simp only [spectralHeat, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, smul_smul]

@[simp] theorem spectralHeat_zero (x : E) : spectralHeat hA 0 x = x := by
  simp only [spectralHeat_apply, zero_mul, Real.exp_zero, one_mul]
  exact (heatBasis hA).sum_repr' x

theorem hasDerivAt_spectralHeat (t : ℝ) (x : E) :
    HasDerivAt (fun s => spectralHeat hA s x) (A (spectralHeat hA t x)) t := by
  simp only [spectralHeat_apply, map_sum, map_smul, heatBasis_eigen, smul_smul]
  apply HasDerivAt.fun_sum
  intro i _
  have he := ((hasDerivAt_id t).mul_const (heatEigenvalues hA i)).exp
  have hm := (he.mul_const ⟪heatBasis hA i, x⟫_ℝ).smul_const (heatBasis hA i)
  have heq : (Real.exp (t * heatEigenvalues hA i) * heatEigenvalues hA i *
        ⟪heatBasis hA i, x⟫_ℝ) =
      Real.exp (t * heatEigenvalues hA i) * ⟪heatBasis hA i, x⟫_ℝ * heatEigenvalues hA i := by
    ring
  simpa only [id_eq, one_mul, heq] using hm

theorem spectralHeat_jointContinuous :
    Continuous (fun z : ℝ × E => spectralHeat hA z.1 z.2) := by
  simp only [spectralHeat_apply]
  exact continuous_finsetSum _ fun i _ =>
    (((continuous_fst.mul continuous_const).rexp).mul
      (continuous_const.inner continuous_snd)).smul continuous_const

private theorem spectralHeat_eigen (t lam : ℝ) (x : E) (hx : A x = lam • x) :
    spectralHeat hA t x = Real.exp (t * lam) • x := by
  rw [spectralHeat_apply]
  conv_rhs => rw [← (heatBasis hA).sum_repr' x, Finset.smul_sum]
  have hcoord (i : basisIndex E) :
      heatEigenvalues hA i * ⟪heatBasis hA i, x⟫_ℝ =
        lam * ⟪heatBasis hA i, x⟫_ℝ := by
    have h := hA (heatBasis hA i) x
    rw [heatBasis_eigen, hx, real_inner_smul_left, real_inner_smul_right] at h
    exact h
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  by_cases h : ⟪heatBasis hA i, x⟫_ℝ = 0
  · simp only [h, mul_zero]
  · rw [mul_right_cancel₀ h (hcoord i)]

theorem spectralHeat_commutes (B : E →ₗ[ℝ] E) (hB : ∀ x, A (B x) = B (A x))
    (t : ℝ) (x : E) :
    B (spectralHeat hA t x) = spectralHeat hA t (B x) := by
  let b := heatBasis hA
  have hb (i : basisIndex E) : A (B (b i)) = heatEigenvalues hA i • B (b i) := by
    change A (B (heatBasis hA i)) = _
    rw [hB, heatBasis_eigen, map_smul]
  calc
    _ = ∑ i : basisIndex E, (Real.exp (t * heatEigenvalues hA i) *
        ⟪b i, x⟫_ℝ) • B (b i) := by
      rw [spectralHeat_apply, map_sum]
      simp only [b, map_smul]
    _ = spectralHeat hA t (B (∑ i : basisIndex E, ⟪b i, x⟫_ℝ • b i)) := by
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, map_smul, spectralHeat_eigen hA t _ _ (hb i), smul_smul, mul_comm]
    _ = _ := by rw [b.sum_repr']

/-- Heat preserves a linear functional which vanishes on the generator. -/
theorem spectralHeat_linear_invariant (I : E →ₗ[ℝ] ℝ) (hI : ∀ x, I (A x) = 0)
    (t : ℝ) (x : E) : I (spectralHeat hA t x) = I x := by
  have h (s : ℝ) : HasDerivAt (fun u => I (spectralHeat hA u x)) 0 s := by
    have hd := I.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_spectralHeat hA s x)
    change HasDerivAt (fun u => I (spectralHeat hA u x)) (I (A (spectralHeat hA s x))) s at hd
    rwa [hI] at hd
  have hconst := is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) t 0
  simpa only [spectralHeat_zero] using hconst

/-- Negative semidefiniteness makes the heat flow converge to a member of
the kernel, with every stationary linear functional retained. -/
theorem spectralHeat_tendsto_kernel
    (hneg : ∀ x, ⟪x, A x⟫_ℝ ≤ 0)
    (I : E →ₗ[ℝ] ℝ) (hI : ∀ x, I (A x) = 0) (x : E) :
    ∃ y, A y = 0 ∧ I y = I x ∧ Tendsto (fun t => spectralHeat hA t x) atTop (𝓝 y) := by
  let b := heatBasis hA
  let lam := heatEigenvalues hA
  let z (i : basisIndex E) := if lam i = 0 then ⟪b i, x⟫_ℝ • b i else 0
  let y := ∑ i, z i
  have hlam (i : basisIndex E) : lam i ≤ 0 := by
    have h := hneg (b i)
    change ⟪heatBasis hA i, A (heatBasis hA i)⟫_ℝ ≤ 0 at h
    rw [heatBasis_eigen, real_inner_smul_right, real_inner_self_eq_norm_sq,
      (heatBasis hA).orthonormal.norm_eq_one, one_pow, mul_one] at h
    exact h
  have hD : Tendsto (fun t => spectralHeat hA t x) atTop (𝓝 y) := by
    simp only [spectralHeat_apply, y]
    apply tendsto_finsetSum
    intro i _
    by_cases hi : lam i = 0
    · have h : heatEigenvalues hA i = 0 := hi
      simpa only [h, mul_zero, Real.exp_zero, one_mul, z, hi, if_true, b] using tendsto_const_nhds
    · have hh : heatEigenvalues hA i < 0 := lt_of_le_of_ne (hlam i) hi
      have ht : Tendsto (fun t : ℝ => t * heatEigenvalues hA i) atTop atBot :=
        tendsto_id.atTop_mul_const_of_neg hh
      have he := Real.tendsto_exp_atBot.comp ht
      simpa only [Function.comp_def, zero_mul, zero_smul, z, hi, if_false] using
        (he.mul_const ⟪heatBasis hA i, x⟫_ℝ).smul_const (heatBasis hA i)
  refine ⟨y, ?_, ?_, hD⟩
  · simp only [y, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : lam i = 0
    · simp only [z, hi, if_true, map_smul, b, heatBasis_eigen,
        show heatEigenvalues hA i = 0 from hi, zero_smul, smul_zero]
    · simp [z, hi]
  · have ht := (I.toContinuousLinearMap.continuous.tendsto y).comp hD
    have he : (fun t => I (spectralHeat hA t x)) = fun _ : ℝ => I x :=
      funext fun t => spectralHeat_linear_invariant hA I hI t x
    change Tendsto (fun t => I (spectralHeat hA t x)) atTop (𝓝 (I y)) at ht
    rw [he] at ht
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm

end

end TypicalOrientations
