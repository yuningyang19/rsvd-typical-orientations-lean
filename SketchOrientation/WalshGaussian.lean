import SketchOrientation.WalshGap
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Gaussian limit for equal-amplitude Walsh targets
The finite coupling reduces this specialization to the scalar iid central
limit theorem in each coordinate and Lévy's continuity theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace BoundedContinuousFunction

noncomputable section
namespace SketchOrientation.Edge.Walsh

/-- The law of a function of a uniform draw on a finite space. -/
def finiteLaw {A E : Type*} [Fintype A] [MeasurableSpace E] (f : A → E) : Measure E :=
  (Fintype.card A : ℝ≥0∞)⁻¹ • ∑ a, Measure.dirac (f a)

instance {A E : Type*} [Fintype A] [Nonempty A] [MeasurableSpace E] (f : A → E) :
    IsProbabilityMeasure (finiteLaw f) := by
  constructor
  rw [finiteLaw, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  simp [ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

theorem integral_finiteLaw {A E G : Type*} [Fintype A] [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : A → E) (g : E → G) :
    (∫ x, g x ∂finiteLaw f) = (Fintype.card A : ℝ)⁻¹ • ∑ a, g (f a) := by
  rw [finiteLaw, integral_smul_measure]
  rw [integral_finsetSum_measure (fun a _ => integrable_dirac (by simp))]
  simp

def finiteProbabilityLaw {A E : Type*} [Fintype A] [Nonempty A] [MeasurableSpace E]
    (f : A → E) : ProbabilityMeasure E :=
  ⟨finiteLaw f, inferInstance⟩

abbrev Block (ell : ℕ) := EuclideanSpace ℝ (Fin ell)

def tableBlock {s ell : ℕ} (T : Fin s → Fin ell → Bool) : Block ell :=
  WithLp.toLp 2 (fun j => (walshSignSum T j : ℝ) / Real.sqrt s)

def iidBlockLaw (s ell : ℕ) : ProbabilityMeasure (Block ell) :=
  finiteProbabilityLaw (tableBlock (s := s) (ell := ell))

def gaussianBlockLaw (ell : ℕ) : ProbabilityMeasure (Block ell) :=
  ⟨stdGaussian (Block ell), inferInstance⟩

/-- The limiting Gaussian vector has independent standard normal coordinates. -/
theorem gaussianBlockLaw_eq_pi (ell : ℕ) :
    (gaussianBlockLaw ell : Measure (Block ell)) =
      (Measure.pi (fun _ : Fin ell => gaussianReal 0 1)).map (WithLp.toLp 2) :=
  map_pi_eq_stdGaussian.symm

private def sampledBlockMeasure (m s ell : ℕ) : Measure (Block ell) :=
  if Fintype.card (Draw m s ell) = 0 then Measure.dirac 0
  else finiteLaw (tableBlock ∘ table : Draw m s ell → Block ell)

def sampledBlockLaw (m s ell : ℕ) : ProbabilityMeasure (Block ell) :=
  ⟨sampledBlockMeasure m s ell, by
    by_cases h : Fintype.card (Draw m s ell) = 0
    · rw [sampledBlockMeasure, if_pos h]
      infer_instance
    · rw [sampledBlockMeasure, if_neg h]
      haveI := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
      infer_instance⟩

theorem sampledBlockLaw_of_nonempty (m s ell : ℕ) [Nonempty (Draw m s ell)] :
    sampledBlockLaw m s ell =
      finiteProbabilityLaw (tableBlock ∘ table : Draw m s ell → Block ell) := by
  apply Subtype.ext
  change sampledBlockMeasure m s ell = _
  rw [sampledBlockMeasure, if_neg (Fintype.card_ne_zero (α := Draw m s ell))]
  rfl

private def rademacher (b : Bool) : ℝ := if b then 1 else -1

private def rademacherLaw : Measure ℝ := finiteLaw rademacher

private instance : IsProbabilityMeasure rademacherLaw := by
  unfold rademacherLaw
  infer_instance

private theorem rademacher_first_moment : (∫ x, x ∂rademacherLaw) = 0 := by
  rw [rademacherLaw, integral_finiteLaw]
  simp [rademacher]

private theorem rademacher_second_moment : (∫ x, x^2 ∂rademacherLaw) = 1 := by
  rw [rademacherLaw, integral_finiteLaw]
  norm_num [rademacher, Fintype.sum_bool]

private theorem rademacher_charCLT (t : ℝ) :
    Tendsto (fun s : ℕ => charFun rademacherLaw ((Real.sqrt s)⁻¹ * t) ^ s)
      atTop (𝓝 (Complex.exp (- (t : ℂ)^2 / 2))) := by
  simpa only [id_eq, Measure.map_id] using
    tendsto_charFun_inv_sqrt_mul_pow (P := rademacherLaw) (X := id)
      measurable_id.aemeasurable rademacher_first_moment rademacher_second_moment t

private theorem charFun_iidBlockLaw (s ell : ℕ) (t : Block ell) :
    charFun (iidBlockLaw s ell : Measure (Block ell)) t =
      ∏ j : Fin ell, charFun rademacherLaw ((Real.sqrt s)⁻¹ * t j) ^ s := by
  classical
  change charFun (finiteLaw (tableBlock (s := s) (ell := ell))) t = _
  rw [charFun_apply, integral_finiteLaw]
  have hinner (T : Fin s → Fin ell → Bool) :
      ⟪tableBlock T, t⟫ = ∑ i : Fin s, ∑ j : Fin ell,
        (Real.sqrt s)⁻¹ * t j * rademacher (T i j) := by
    simp only [PiLp.inner_apply, tableBlock, RCLike.inner_apply,
      conj_trivial, walshSignSum]
    push_cast
    simp only [rademacher, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split <;> ring
  simp_rw [hinner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  let v (j : Fin ell) (b : Bool) : ℂ := Complex.exp
    (((Real.sqrt s)⁻¹ * t j * rademacher b : ℝ) * Complex.I)
  change ((Fintype.card (Fin s → Fin ell → Bool) : ℝ)⁻¹ : ℝ) •
      (∑ T : Fin s → Fin ell → Bool, ∏ i : Fin s, ∏ j : Fin ell, v j (T i j)) = _
  rw [← Fintype.prod_sum (fun (_ : Fin s) (r : Fin ell → Bool) => ∏ j, v j (r j))]
  simp_rw [← Fintype.prod_sum (fun j b => v j b)]
  have hchar (j : Fin ell) :
      charFun rademacherLaw ((Real.sqrt s)⁻¹ * t j) =
        (2 : ℂ)⁻¹ * ∑ b, v j b := by
    rw [charFun_apply_real, rademacherLaw, integral_finiteLaw]
    simp [Complex.real_smul, v, mul_add]
  simp_rw [hchar]
  simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_ofNat, mul_pow, Finset.prod_mul_distrib]
  simp only [inv_pow, ← Finset.prod_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Product standard Gaussian limit for a table of independent fair signs. -/
theorem tendsto_iidBlockLaw (ell : ℕ) :
    Tendsto (fun s => iidBlockLaw s ell) atTop (𝓝 (gaussianBlockLaw ell)) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  simp_rw [charFun_iidBlockLaw]
  have h := tendsto_finsetProd Finset.univ (fun j _ => rademacher_charCLT (t j))
  have hlim : (∏ j : Fin ell, Complex.exp (- ((t j : ℝ) : ℂ)^2 / 2)) =
      charFun (gaussianBlockLaw ell : Measure (Block ell)) t := by
    change _ = charFun (stdGaussian (Block ell)) t
    rw [charFun_stdGaussian, ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq, ← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, ← Finset.sum_neg_distrib, ← Finset.sum_div,
      Complex.ofReal_pow]
  rwa [hlim] at h


theorem integral_finiteLaw_eq_uniformMean {A E : Type*} [Fintype A] [MeasurableSpace E]
    [MeasurableSingletonClass E] (f : A → E) (g : E → ℝ) :
    (∫ x, g x ∂finiteLaw f) = uniformMean (fun a => g (f a)) := by
  rw [integral_finiteLaw, uniformMean, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem uniformMean_affine {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) (a b : ℝ) :
    uniformMean (fun x => a * f x + b) = a * uniformMean f + b := by
  have h : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformMean, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc,
    mul_div_cancel_left₀, h]

private theorem integral_coupling_bound {m s ell : ℕ} (h : Nonempty (Draw m s ell))
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)]
    (g : Block ell →ᵇ ℝ) :
    |(∫ x, g x ∂(sampledBlockLaw m s ell : Measure (Block ell))) -
      (∫ x, g x ∂(iidBlockLaw s ell : Measure (Block ell)))| ≤
      2 * (‖g‖ + 1) * (((s : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell) / (2 : ℝ)^m) := by
  haveI := h
  let C := ‖g‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let f (T : Fin s → Fin ell → Bool) := (2 * C)⁻¹ * g (tableBlock T) + 1 / 2
  have hb (x : Block ell) : |g x| ≤ C :=
    (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x : |g x| ≤ ‖g‖).trans
      (le_add_of_nonneg_right zero_le_one)
  have h₀ (T) : 0 ≤ f T := by
    have ht := mul_le_mul_of_nonneg_left (abs_le.mp (hb (tableBlock T))).1
      (inv_nonneg.2 (by positivity : 0 ≤ 2 * C))
    dsimp only [f]
    have ha : (2 * C)⁻¹ * (-C) = -1 / 2 := by field_simp
    linarith only [ht, ha]
  have h₁ (T) : f T ≤ 1 := by
    have ht := mul_le_mul_of_nonneg_left (abs_le.mp (hb (tableBlock T))).2
      (inv_nonneg.2 (by positivity : 0 ≤ 2 * C))
    dsimp only [f]
    have ha : (2 * C)⁻¹ * C = 1 / 2 := by field_simp
    linarith only [ht, ha]
  have hcmp := abs_uniformMean_table_sub (m := m) f h₀ h₁
  dsimp only [f] at hcmp
  rw [uniformMean_affine, uniformMean_affine] at hcmp
  simp only [add_sub_add_right_eq_sub, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.2 (by positivity : 0 < 2 * C))] at hcmp
  rw [← div_eq_inv_mul, div_le_iff₀ (by positivity : 0 < 2 * C)] at hcmp
  rw [sampledBlockLaw_of_nonempty]
  unfold iidBlockLaw
  change |(∫ x, g x ∂finiteLaw (tableBlock ∘ table : Draw m s ell → Block ell)) -
      (∫ x, g x ∂finiteLaw (tableBlock (s := s) (ell := ell)))| ≤ _
  rw [integral_finiteLaw_eq_uniformMean, integral_finiteLaw_eq_uniformMean, mul_comm (2 * C)]
  exact hcmp

/-- Under the growth condition for the miss estimate, the same coupled
finite laws converge weakly to the standard Gaussian vector. -/
theorem tendsto_sampledBlockLaw {m s : ℕ → ℕ} {ell : ℕ}
    (hs : Tendsto s atTop atTop)
    (hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i)
    (hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i)
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    Tendsto (fun i => sampledBlockLaw (m i) (s i) ell) atTop (𝓝 (gaussianBlockLaw ell)) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g => ?_
  let a (i : ℕ) := ∫ x, g x ∂(sampledBlockLaw (m i) (s i) ell : Measure (Block ell))
  let b (i : ℕ) := ∫ x, g x ∂(iidBlockLaw (s i) ell : Measure (Block ell))
  have hb := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    ((tendsto_iidBlockLaw ell).comp hs) g
  let C : ℝ := 1 + (ell : ℝ)^2 + (2 : ℝ)^ell
  have hbound : ∀ᶠ i in atTop, ‖a i - b i‖ ≤
      (2 * (‖g‖ + 1) * C) * ((s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i) := by
    filter_upwards [hs.eventually_ge_atTop 1, hr, hc] with i hsi hri hci
    letI := label_embedding_nonempty (m := m i) hri
    letI := label_embedding_nonempty (m := m i) hci
    have hs1 : (1 : ℝ) ≤ s i := by exact_mod_cast hsi
    have hs2 : (1 : ℝ) ≤ (s i : ℝ)^2 := by nlinarith
    have hq : 1 ≤ (s i : ℝ) ^ ((ell : ℝ) / 2) := Real.one_le_rpow hs1 (by positivity)
    have hC : (s i : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell ≤ C * (s i : ℝ)^2 := by
      have h₁ := mul_le_mul_of_nonneg_left hs2 (sq_nonneg (ell : ℝ))
      have h₂ := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ (2 : ℝ)^ell by positivity)
      dsimp [C]
      nlinarith
    have hC' : C * (s i : ℝ)^2 ≤ C * (s i : ℝ) ^ (2 + (ell : ℝ) / 2) := by
      rw [Real.rpow_add (by positivity), Real.rpow_two]
      calc
        _ ≤ (C * (s i : ℝ)^2) * (s i : ℝ) ^ ((ell : ℝ) / 2) :=
          le_mul_of_one_le_right (by dsimp [C]; positivity) hq
        _ = _ := by ring
    rw [Real.norm_eq_abs]
    dsimp only [a,b]
    calc
      _ ≤ _ := integral_coupling_bound (inferInstance : Nonempty (Draw (m i) (s i) ell)) g
      _ ≤ 2 * (‖g‖ + 1) * ((C * (s i : ℝ) ^ (2 + (ell : ℝ) / 2)) / (2 : ℝ)^m i) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hC.trans hC') (by positivity))
          (by positivity)
      _ = _ := by ring
  have hd : Tendsto (fun i => a i - b i) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound (by simpa only [mul_zero] using
      (hgrowth.const_mul (2 * (‖g‖ + 1) * C)))
  have h := hd.add hb
  simpa only [zero_add, sub_add_cancel, a, b, Function.comp_apply] using h


/-- Distribution of the normalized projected block from the two full
signed permutations, with prescribed support and output locations. -/
def signedPermBlockLaw {m s ell : ℕ} (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) :
    ProbabilityMeasure (Block ell) :=
  finiteProbabilityLaw (fun d : SignedPermDraw m => WithLp.toLp 2
    (fun j => normalizedProjection rows cols d j))

theorem signedPermBlockLaw_eq_sampledBlockLaw {m s ell : ℕ}
    (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) :
    signedPermBlockLaw rows cols = sampledBlockLaw m s ell := by
  classical
  letI : Nonempty (Fin s ↪ Label m) := ⟨rows⟩
  letI : Nonempty (Fin ell ↪ Label m) := ⟨cols⟩
  rw [sampledBlockLaw_of_nonempty]
  apply Subtype.ext
  change finiteLaw (fun d : SignedPermDraw m => WithLp.toLp 2
    (fun j => normalizedProjection rows cols d j)) =
      finiteLaw (tableBlock ∘ table : Draw m s ell → Block ell)
  apply Measure.ext_of_charFun
  funext t
  simp_rw [normalizedProjection_eq_signSum]
  let g (d : Draw m s ell) : ℂ := Complex.exp (⟪tableBlock (table d), t⟫ * Complex.I)
  rw [charFun_apply, charFun_apply, integral_finiteLaw, integral_finiteLaw]
  change (Fintype.card (SignedPermDraw m) : ℝ)⁻¹ • (∑ d, g (restrictSignedPerm rows cols d)) =
    (Fintype.card (Draw m s ell) : ℝ)⁻¹ • (∑ d, g d)
  apply Complex.ext
  · simpa only [uniformMean, Complex.smul_re, Complex.re_sum, smul_eq_mul, div_eq_inv_mul] using
      uniformMean_restrictSignedPerm rows cols (fun d => (g d).re)
  · simpa only [uniformMean, Complex.smul_im, Complex.im_sum, smul_eq_mul, div_eq_inv_mul] using
      uniformMean_restrictSignedPerm rows cols (fun d => (g d).im)

/-- Theorem 1.4 for the rank-one signed Walsh model, in support coordinates.
The support is available in the ambient space eventually. Every fixed choice
of distinct support and sampled output coordinates has the same block law
by the signed-permutation bridge above. -/
theorem prescribedGap_gaussian_divergence {ell : ℕ} (hell : 2 < ell) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    let s := fun i => walshSupport ell ((2 : ℝ)^m i) (L i)
    (∀ᶠ i in atTop, 0 < s i ∧ s i ≤ 2 ^ m i ∧ ell ≤ 2 ^ m i) ∧
    Tendsto (fun i => sampledBlockLaw (m i) (s i) ell) atTop (𝓝 (gaussianBlockLaw ell)) ∧
    Tendsto (fun i => meanLoss (m i) (s i) ell (L i)) atTop atTop := by
  dsimp only
  let n (i : ℕ) : ℝ := 2 ^ m i
  let s (i : ℕ) := walshSupport ell (n i) (L i)
  have hn : Tendsto n atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  have hL₀ : ∀ᶠ i in atTop, 0 ≤ L i := hL.eventually_ge_atTop 0
  have hs : Tendsto s atTop atTop := tendsto_walshSupport (by omega) hn hL
  have hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i := by
    filter_upwards [hL₀] with i hi
    have hni : 1 ≤ (2 : ℕ)^m i := Nat.one_le_pow _ _ (by decide)
    simpa only [s, n, Nat.cast_pow, Nat.cast_ofNat] using
      (walshSupport_le_dimension (ell := ell) hni hi)
  have hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i := by
    have hn' : Tendsto (fun i => (2 : ℕ)^m i) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2)).comp hm
    exact hn'.eventually_ge_atTop ell
  refine ⟨?_, tendsto_sampledBlockLaw hs hr hc (walshSupport_growth hn hL₀),
    tendsto_prescribedGap_meanLoss hell hm hL⟩
  filter_upwards [hs.eventually_ge_atTop 1, hr, hc] with i hsi hri hci
  exact ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one hsi, hri, hci⟩

end SketchOrientation.Edge.Walsh
