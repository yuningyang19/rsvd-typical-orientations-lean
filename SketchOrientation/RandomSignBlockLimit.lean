import SketchOrientation.SignBlockLimit
import SketchOrientation.WalshGaussian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace SketchOrientation

open Edge.Walsh Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace

/-- Equivalent finite draw spaces produce the same uniform pushforward. -/
theorem finiteProbabilityLaw_reindex {A B E : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [MeasurableSpace E] (e : A ≃ B) (f : B → E) :
    finiteProbabilityLaw (fun a => f (e a)) = finiteProbabilityLaw f := by
  apply Subtype.ext
  change finiteLaw (fun a => f (e a)) = finiteLaw f
  simp only [finiteLaw, Fintype.card_congr e]
  exact congrArg (fun μ : Measure E => (Fintype.card B : ENNReal)⁻¹ • μ)
    (e.sum_comp (fun b => Measure.dirac (f b)))

private def fairSign (b : Bool) : ℝ := if b then 1 else -1

/-- Sum of independent signs after the draw of a coefficient array. -/
noncomputable def signedCoefficientSum {I E : Type*} [Fintype I]
    [AddCommMonoid E] [SMul ℝ E] (a : I → E) (ε : I → Bool) : E :=
  ∑ i, fairSign (ε i) • a i

private theorem signedCoefficient_exponential_mean {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : I → E) (t : E) :
    ((Fintype.card (I → Bool) : ℝ)⁻¹ : ℝ) •
        (∑ ε : I → Bool, Complex.exp ((⟪signedCoefficientSum a ε, t⟫ : ℝ) * Complex.I)) =
      ((∏ i, Real.cos ⟪a i, t⟫ : ℝ) : ℂ) := by
  classical
  let u (i : I) (b : Bool) := Complex.exp (((fairSign b * ⟪a i, t⟫ : ℝ) : ℂ) * Complex.I)
  simp_rw [signedCoefficientSum, sum_inner, real_inner_smul_left, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  change ((Fintype.card (I → Bool) : ℝ)⁻¹ : ℝ) • (∑ ε : I → Bool, ∏ i, u i (ε i)) = _
  rw [← Fintype.prod_sum (fun i b => u i b), Complex.real_smul]
  have hsum (i : I) : ∑ b, u i b = 2 * (Real.cos ⟪a i, t⟫ : ℂ) := by
    simp only [Fintype.sum_bool, u, fairSign, Bool.false_eq_true, ↓reduceIte,
      Complex.ofReal_neg, neg_mul, one_mul, Complex.ofReal_cos]
    rw [Complex.cos, add_comm]
    ring
  simp only [hsum, Fintype.card_pi, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_prod]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_mul]

/-- Conditional characteristic-function identity averaged over the actual
finite coefficient environment. -/
theorem charFun_signedCoefficientLaw {A I E : Type*} [Fintype A] [Nonempty A] [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a : A → I → E) (t : E) :
    charFun (finiteProbabilityLaw (fun q : A × (I → Bool) => signedCoefficientSum (a q.1) q.2) :
      Measure E) t =
      ((uniformMean fun q => ∏ i, Real.cos ⟪a q i, t⟫ : ℝ) : ℂ) := by
  classical
  change charFun (finiteLaw (fun q : A × (I → Bool) => signedCoefficientSum (a q.1) q.2)) t = _
  rw [charFun_apply, integral_finiteLaw, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    mul_inv, Complex.real_smul, Complex.ofReal_mul]
  simp only [uniformMean, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]
  rw [mul_assoc]
  rw [mul_comm (∑ q : A, ((∏ i, Real.cos ⟪a q i, t⟫ : ℝ) : ℂ))]
  apply congrArg (fun v : ℂ => ((Fintype.card A : ℝ) : ℂ)⁻¹ * v)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simpa only [Complex.real_smul, Complex.ofReal_inv] using signedCoefficient_exponential_mean (a q) t

private theorem abs_cos_product_sub_gaussian_global {I : Type*} [Fintype I] (b : I → ℝ) :
    |(∏ i, Real.cos (b i)) - Real.exp (-(∑ i, b i ^ 2) / 2)| ≤ 2 * ∑ i, b i ^ 4 := by
  by_cases h : ∀ i, |b i| ≤ 1
  · exact abs_cos_product_sub_gaussian b h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 : (1 : ℝ) ≤ ∑ i, b i ^ 4 := by
    calc
      _ ≤ |b i| ^ 4 := one_le_pow₀ hi.le
      _ = b i ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ _ := Finset.single_le_sum (f := fun i => b i ^ 4) (by intros; positivity) (Finset.mem_univ _)
  have hprod : |∏ i, Real.cos (b i)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one
    · intros; positivity
    · intros; exact Real.abs_cos_le_one _
  have hexp : |Real.exp (-(∑ i, b i ^ 2) / 2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (by norm_num)
  exact (abs_sub _ _).trans (by linarith)

private theorem abs_exp_neg_half_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x / 2) - Real.exp (-y / 2)| ≤ |x - y| / 2 := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hy hx (le_of_not_ge hxy)
  have hneg : -y / 2 ≤ -x / 2 := by linarith
  have hmono := Real.exp_le_exp.mpr hneg
  have htan := Real.add_one_le_exp ((-y / 2) - (-x / 2))
  have hp := mul_le_mul_of_nonneg_left htan (Real.exp_nonneg (-x / 2))
  rw [← Real.exp_add] at hp
  have he : -x / 2 + (-y / 2 - -x / 2) = -y / 2 := by ring
  rw [he] at hp
  have hb : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc := mul_le_mul_of_nonneg_right hb (show 0 ≤ (y - x) / 2 by positivity)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hxy)]
  linarith

/-- Conditional variance tending in mean to the identity and fourth-order
error tending to zero imply Gaussian convergence for finite draw spaces. -/
theorem tendsto_signedCoefficientLaw {A I : ℕ → Type*}
    [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (a : (j : ℕ) → A j → I j → E)
    (hVar : ∀ t : E, Tendsto (fun j => uniformMean fun q =>
      |(∑ i, ⟪a j q i, t⟫ ^ 2) - ‖t‖ ^ 2|) atTop (𝓝 0))
    (hFourth : ∀ t : E, Tendsto (fun j => uniformMean fun q =>
      ∑ i, ⟪a j q i, t⟫ ^ 4) atTop (𝓝 0)) :
    Tendsto (fun j => finiteProbabilityLaw (fun q : A j × (I j → Bool) =>
      signedCoefficientSum (a j q.1) q.2)) atTop
      (𝓝 (⟨stdGaussian E, inferInstance⟩ : ProbabilityMeasure E)) := by
  classical
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t => ?_
  simp_rw [charFun_signedCoefficientLaw]
  change Tendsto (fun j => ((uniformMean fun q => ∏ i, Real.cos ⟪a j q i, t⟫ : ℝ) : ℂ))
    atTop (𝓝 (charFun (stdGaussian E) t))
  rw [charFun_stdGaussian, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_div, ← Complex.ofReal_exp]
  apply Complex.continuous_ofReal.continuousAt.tendsto.comp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  refine squeeze_zero (g := fun j =>
    2 * (uniformMean fun q => ∑ i, ⟪a j q i, t⟫ ^ 4) +
      (uniformMean fun q => |(∑ i, ⟪a j q i, t⟫ ^ 2) - ‖t‖ ^ 2|) / 2)
    (fun _ => abs_nonneg _) ?_ ?_
  · intro j
    let c := Real.exp (-‖t‖ ^ 2 / 2)
    let f (q : A j) := ∏ i, Real.cos ⟪a j q i, t⟫
    change |uniformMean f - c| ≤
      2 * (uniformMean fun q => ∑ i, ⟪a j q i, t⟫ ^ 4) +
        (uniformMean fun q => |(∑ i, ⟪a j q i, t⟫ ^ 2) - ‖t‖ ^ 2|) / 2
    rw [← uniformMean_const (A := A j) c, ← uniformMean_sub]
    refine (abs_uniformMean_le _).trans ?_
    calc
      _ ≤ uniformMean (fun q => 2 * (∑ i, ⟪a j q i, t⟫ ^ 4) +
         (|(∑ i, ⟪a j q i, t⟫ ^ 2) - ‖t‖ ^ 2|) / 2) := by
        apply uniformMean_mono
        intro q
        have h₁ := abs_cos_product_sub_gaussian_global (fun i => ⟪a j q i, t⟫)
        have hNonneg : 0 ≤ ∑ i, ⟪a j q i, t⟫ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have h₂ := abs_exp_neg_half_sub_le hNonneg (sq_nonneg ‖t‖)
        exact (abs_sub_le (f q) (Real.exp (-(∑ i, ⟪a j q i, t⟫ ^ 2) / 2)) c).trans (add_le_add h₁ h₂)
      _ = _ := by
        simp_rw [uniformMean, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
        ring
  · simpa only [mul_zero, zero_div, add_zero] using
      ((hFourth t).const_mul 2).add ((hVar t).div_const 2)

end SketchOrientation
