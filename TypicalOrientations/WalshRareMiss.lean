import SketchOrientation.WalshRSVD
import SketchOrientation.RandomSignBlockLimit
import SketchOrientation.GaussianMatrixSpace
import Mathlib.Analysis.SpecificLimits.Basic

namespace TypicalOrientations

open Matrix Filter MeasureTheory ProbabilityTheory Asymptotics SketchOrientation SketchOrientation.Edge.Walsh
open scoped Topology ENNReal

noncomputable section

variable {m ell : ℕ}

/-- Uniform distinct rows and an independent vector of fair signs. -/
abbrev FlatWalshDraw (m ell : ℕ) := (Fin ell ↪ Label m) × (Label m → ZMod 2)

/-- The transpose of (R_J H D), with no signed permutations on either side. -/
def flatWalshSketch (d : FlatWalshDraw m ell) : Matrix (Label m) (Fin ell) ℝ :=
  Matrix.of (fun x j => core m (d.1 j) x * signValue (d.2 x))

/-- The unit vector with all entries (1/\sqrt{2^m}). -/
def flatWalshTarget (m : ℕ) : Matrix (Label m) (Fin 1) ℝ :=
  Matrix.of (fun _ _ => (Real.sqrt ((2 : ℝ)^m))⁻¹)

private theorem walsh_core_symm (a b : Label m) : core m a b = core m b a := by
  have h : parity a b = parity b a := by
    unfold parity
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp only [core, h]

theorem flatWalshSketch_orthonormal (d : FlatWalshDraw m ell) :
    (flatWalshSketch d)ᵀ * flatWalshSketch d = 1 := by
  let e : SignedPermDraw m := (Equiv.refl _, Equiv.refl _, d.2, 0)
  have he : signedMatrix d.1 e = flatWalshSketch d := by
    ext x j
    rw [signedMatrix_apply]
    simp only [e, Equiv.refl_apply, Pi.zero_apply, signValue_zero, mul_one,
      flatWalshSketch, Matrix.of_apply]
    rw [walsh_core_symm (d.1 j) x, core]
    ring
  rw [← he]
  exact signedMatrix_orthonormal _ _

theorem flatWalshTarget_orthonormal :
    (flatWalshTarget m)ᵀ * flatWalshTarget m = 1 := by
  ext i j
  have h : i = j := Subsingleton.elim _ _
  have hn : (2 : ℝ)^m ≠ 0 := by positivity
  simp only [flatWalshTarget, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply, h, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← pow_two, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2^m),
    card_label, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_inv_cancel₀ hn

/-- All signs are (+1) and the sampled rows omit the constant Walsh row. -/
def flatWalshRareEvent (d : FlatWalshDraw m ell) : Prop :=
  (0 : Label m) ∉ Set.range d.1 ∧ d.2 = 0

private theorem uniformMean_const_mul_local {A : Type*} [Fintype A] (a : ℝ) (f : A → ℝ) :
    uniformMean (fun x => a * f x) = a * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum, mul_div_assoc]

private theorem uniformMean_mul_const_local {A : Type*} [Fintype A] (a : ℝ) (f : A → ℝ) :
    uniformMean (fun x => f x * a) = uniformMean f * a := by
  simp_rw [mul_comm _ a]
  exact uniformMean_const_mul_local a f

private def embeddingSwap (a b : Label m) : (Fin ell ↪ Label m) ≃ (Fin ell ↪ Label m) where
  toFun J := J.trans (Equiv.swap a b).toEmbedding
  invFun J := J.trans (Equiv.swap a b).toEmbedding
  left_inv J := by ext i; simp
  right_inv J := by ext i; simp

private theorem row_inclusion_probability (h : ell ≤ 2^m) (x : Label m) :
    uniformProbability (fun J : Fin ell ↪ Label m => x ∈ Set.range J) = (ell : ℝ) / (2 : ℝ)^m := by
  classical
  let : Nonempty (Fin ell ↪ Label m) := label_embedding_nonempty h
  let f (a : Label m) (J : Fin ell ↪ Label m) := indicator (a ∈ Set.range J)
  have hEqual (a b : Label m) : uniformMean (f a) = uniformMean (f b) := by
    have hmem (J : Fin ell ↪ Label m) : a ∈ Set.range J ↔ b ∈ Set.range (embeddingSwap a b J) := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨i, ?_⟩
        change Equiv.swap a b (J i) = b
        rw [hi, Equiv.swap_apply_left]
      · rintro ⟨i, hi⟩
        have hi' : Equiv.swap a b (J i) = b := hi
        refine ⟨i, (Equiv.swap a b).injective ?_⟩
        rwa [Equiv.swap_apply_left]
    refine (congrArg uniformMean (funext fun J => ?_)).trans
      (uniformMean_equiv (embeddingSwap a b) (f b))
    simp only [f, hmem J]
  have hSum (J : Fin ell ↪ Label m) : (∑ a, f a J) = ell := by
    have hmem (a : Label m) : a ∈ Set.range J ↔ a ∈ Finset.univ.map J := by simp [Set.mem_range]
    simp only [f, indicator, hmem]
    rw [← Finset.sum_filter, show (Finset.univ.filter (fun a => a ∈ Finset.univ.map J)) =
      Finset.univ.map J from by ext a; simp]
    simp
  have hN : (2 : ℝ)^m ≠ 0 := by positivity
  change uniformMean (f x) = _
  apply (eq_div_iff hN).2
  calc
    uniformMean (f x) * (2 : ℝ)^m = ∑ a : Label m, uniformMean (f a) := by
      simp_rw [fun a => hEqual a x]
      simp [mul_comm]
    _ = uniformMean (fun J : Fin ell ↪ Label m => ∑ a, f a J) := by
      unfold uniformMean
      rw [← Finset.sum_div, Finset.sum_comm]
    _ = ell := by simp_rw [hSum]; exact uniformMean_const _

private theorem first_row_omission_probability (h : ell ≤ 2^m) :
    uniformProbability (fun J : Fin ell ↪ Label m => (0 : Label m) ∉ Set.range J) =
      1 - (ell : ℝ) / (2 : ℝ)^m := by
  classical
  let : Nonempty (Fin ell ↪ Label m) := label_embedding_nonempty h
  rw [← row_inclusion_probability h (0 : Label m)]
  change uniformMean _ = 1 - uniformMean _
  have hI (J : Fin ell ↪ Label m) :
      indicator ((0 : Label m) ∉ Set.range J) = 1 - indicator ((0 : Label m) ∈ Set.range J) := by
    by_cases hJ : (0 : Label m) ∈ Set.range J <;> simp [indicator, hJ]
  simp_rw [hI]
  unfold uniformMean
  rw [Finset.sum_sub_distrib, sub_div]
  have h1 : (∑ _ : Fin ell ↪ Label m, (1 : ℝ)) / Fintype.card (Fin ell ↪ Label m) = 1 :=
    uniformMean_const _
  rw [h1]

private theorem all_positive_sign_probability :
    uniformProbability (fun z : Label m → ZMod 2 => z = 0) = ((2 : ℝ)^((2 : ℕ)^m))⁻¹ := by
  classical
  have hSum : (∑ z : Label m → ZMod 2, indicator (z = 0)) = 1 := by
    rw [Finset.sum_eq_single (0 : Label m → ZMod 2)]
    · simp [indicator]
    · intro z _ hz
      simp [indicator, hz]
    · simp
  unfold uniformProbability uniformMean
  rw [hSum, Fintype.card_pi]
  simp only [ZMod.card, Finset.prod_const, Finset.card_univ, card_label, Nat.cast_pow,
    Nat.cast_ofNat, one_div]

/-- The precise probability of the single event used to force divergence
in §5.2. Distinct rows are sampled uniformly, independently of the signs. -/
theorem flatWalshRareEvent_probability (h : ell ≤ 2^m) :
    uniformProbability (flatWalshRareEvent (m := m) (ell := ell)) =
      ((2 : ℝ)^((2 : ℕ)^m))⁻¹ * (1 - (ell : ℝ) / (2 : ℝ)^m) := by
  classical
  have he (J : Fin ell ↪ Label m) (z : Label m → ZMod 2) :
      indicator (flatWalshRareEvent (J, z)) =
        indicator ((0 : Label m) ∉ Set.range J) * indicator (z = 0) := by
    by_cases hJ : (0 : Label m) ∉ Set.range J <;> by_cases hz : z = 0 <;>
      simp [flatWalshRareEvent, indicator, hJ, hz]
  unfold uniformProbability
  rw [uniformMean_prod']
  simp_rw [he, uniformMean_const_mul_local, uniformMean_mul_const_local]
  change uniformProbability (fun J : Fin ell ↪ Label m => (0 : Label m) ∉ Set.range J) *
    uniformProbability (fun z : Label m → ZMod 2 => z = 0) = _
  rw [first_row_omission_probability h, all_positive_sign_probability, mul_comm]

/-- On the explicit event the SRHT misses the flat target in every sampled row. -/
theorem flatWalshRareEvent_miss (d : FlatWalshDraw m ell) (hd : flatWalshRareEvent d) :
    (flatWalshSketch d)ᵀ * flatWalshTarget m = 0 := by
  classical
  rcases d with ⟨J, z⟩
  rcases hd with ⟨hJ, hz⟩
  change z = 0 at hz
  subst z
  ext i j
  let n : ℝ := (2 : ℝ)^m
  have h0 : J i ≠ 0 := fun h => hJ ⟨i, h⟩
  have hS := sum_signValue_parity_mul (J i) (0 : Label m)
  have hParity (x : Label m) : parity x 0 = 0 := by simp [parity]
  simp only [h0, if_false, hParity, signValue_zero, mul_one] at hS
  rw [Matrix.mul_apply]
  have hTerm (x : Label m) :
      (flatWalshSketch (J, 0))ᵀ i x * flatWalshTarget m x j =
        (Real.sqrt n)⁻¹ ^ 2 * signValue (parity x (J i)) := by
    simp only [flatWalshSketch, flatWalshTarget, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply, signValue_zero, mul_one]
    rw [walsh_core_symm (J i) x, core]
    dsimp [n]
    ring
  simp_rw [hTerm, ← Finset.mul_sum, hS, mul_zero]
  rfl


/-- The actual residual is at least the energy of the missed spike, in
units of the optimal rank-one squared tail. -/
theorem flatWalshRareEvent_relativeLoss {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hm : 0 < m) (hWidth : ell < 2^m)
    (d : FlatWalshDraw m ell) (hd : flatWalshRareEvent d) :
    Γ / ((2 : ℝ)^m - 1) ≤
      tailRelativeError 1 (twoLevelInput (flatWalshTarget m) Γ) (flatWalshSketch d) := by
  let V := flatWalshTarget m
  let U := flatWalshSketch d
  let A := twoLevelInput V Γ
  have hV : Vᵀ * V = 1 := flatWalshTarget_orthonormal
  have hU : Uᵀ * U = 1 := flatWalshSketch_orthonormal d
  have hGram : Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ) :=
    twoLevelInput_gram V hV (zero_le_one.trans hΓ)
  have hUV : Uᵀ * V = 0 := flatWalshRareEvent_miss d hd
  have hComp : Vᵀ * (U * Uᵀ) * V = 0 := by
    simp only [Matrix.mul_assoc, hUV, Matrix.mul_zero]
  have hRes := twoLevel_squaredResidual A U V hU hV hΓ hGram
  rw [hComp, smul_zero, add_zero, inv_one, trace_one] at hRes
  have hTail := twoLevel_optimalTail A V hV hΓ hGram
  simp only [card_label, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_one] at hRes hTail
  have hN : (1 : ℝ) < (2 : ℝ)^m := one_lt_pow₀ (by norm_num) hm.ne'
  have hRest : 0 ≤ (2 : ℝ)^m - 1 - (ell : ℝ) := by
    have h : (ell : ℝ) + 1 ≤ (2 : ℝ)^m := by exact_mod_cast (show ell + 1 ≤ 2^m from hWidth)
    linarith
  change _ ≤ tailRelativeError 1 A U
  rw [tailRelativeError, hTail, hRes]
  exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hN.le)

/-- The standard SRHT law for the prescribed flat-target example. -/
def flatWalshSketchMeasure (m ell : ℕ) : Measure (Matrix (Label m) (Fin ell) ℝ) :=
  finiteLaw (@flatWalshSketch m ell)

theorem isProbabilityMeasure_flatWalshSketchMeasure (h : ell ≤ 2^m) :
    IsProbabilityMeasure (flatWalshSketchMeasure m ell) := by
  let : Nonempty (Fin ell ↪ Label m) := label_embedding_nonempty h
  unfold flatWalshSketchMeasure
  infer_instance

/-- Mean normalized residual for the actual two-level input and SRHT,
before averaging over any orientation of that input. -/
def flatWalshRelativeMean (m ell : ℕ) (Γ : ℝ) : ℝ :=
  ∫ Ω, tailRelativeError 1 (twoLevelInput (flatWalshTarget m) Γ) Ω ∂flatWalshSketchMeasure m ell

/-- The bound in §5.2 using exactly the event of all positive signs and
omission of the first row. -/
theorem flatWalshRelativeMean_rareMiss_lower {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hm : 0 < m) (hWidth : ell < 2^m) :
    ((2 : ℝ)^((2 : ℕ)^m))⁻¹ * (1 - (ell : ℝ) / (2 : ℝ)^m) *
        Γ / ((2 : ℝ)^m - 1) ≤ flatWalshRelativeMean m ell Γ := by
  let K := Γ / ((2 : ℝ)^m - 1)
  let F := fun d : FlatWalshDraw m ell =>
    tailRelativeError 1 (twoLevelInput (flatWalshTarget m) Γ) (flatWalshSketch d)
  have hTail : optimalTail 1 (twoLevelInput (flatWalshTarget m) Γ) = (2 : ℝ)^m - 1 := by
    have hV : (flatWalshTarget m)ᵀ * flatWalshTarget m = 1 := flatWalshTarget_orthonormal
    have h := twoLevel_optimalTail _ _ hV hΓ
      (twoLevelInput_gram _ hV (zero_le_one.trans hΓ))
    simpa only [Fintype.card_fin, card_label, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h
  have hN : (1 : ℝ) ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
  have hN0 (d : FlatWalshDraw m ell) : 0 ≤ F d := by
    unfold F tailRelativeError
    rw [hTail]
    exact div_nonneg (squaredFrobenius_nonneg _) (sub_nonneg.mpr hN)
  have hP := flatWalshRareEvent_probability (m := m) (ell := ell) hWidth.le
  rw [mul_div_assoc, ← hP, flatWalshRelativeMean, flatWalshSketchMeasure,
    integral_finiteLaw_eq_uniformMean]
  change uniformMean (fun d => indicator (flatWalshRareEvent d)) * K ≤ uniformMean F
  rw [← uniformMean_mul_const_local]
  apply uniformMean_mono
  intro d
  by_cases hd : flatWalshRareEvent d
  · simpa only [indicator, if_pos hd, one_mul] using flatWalshRareEvent_relativeLoss hΓ hm hWidth d hd
  · simpa only [indicator, if_neg hd, zero_mul] using hN0 d

/-- For the exact scale Γ=n²·2ⁿ the event bound simplifies to the paper's
dimension-sized lower bound. -/
theorem flatWalshRelativeMean_exponential_lower (hm : 0 < m) (hWidth : ell < 2^m) :
    (1 - (ell : ℝ) / (2 : ℝ)^m) * ((2 : ℝ)^m)^2 / ((2 : ℝ)^m - 1) ≤
      flatWalshRelativeMean m ell (((2 : ℝ)^m)^2 * (2 : ℝ)^((2 : ℕ)^m)) := by
  let n : ℝ := (2 : ℝ)^m
  let q : ℝ := (2 : ℝ)^((2 : ℕ)^m)
  have hn : 1 ≤ n := one_le_pow₀ (by norm_num)
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hg : 1 ≤ n^2 * q :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) hq
  have h := flatWalshRelativeMean_rareMiss_lower (Γ := n^2 * q) hg hm hWidth
  have hEq : q⁻¹ * (1 - (ell : ℝ)/n) * (n^2*q) / (n-1) =
      (1 - (ell : ℝ)/n) * n^2 / (n-1) := by
    rw [show q⁻¹ * (1 - (ell : ℝ)/n) * (n^2*q) =
        (q⁻¹ * q) * ((1 - (ell : ℝ)/n) * n^2) by ring,
      inv_mul_cancel₀ (zero_lt_one.trans_le hq).ne', one_mul]
  change _ ≤ flatWalshRelativeMean m ell (n^2 * q)
  exact hEq ▸ h

/-- The lower bound obtained from the explicit miss is asymptotic to the
ambient dimension, as stated after the choice Γ=n²·2ⁿ. -/
theorem flatWalsh_exponential_lower_isEquivalent_dim {digits : ℕ → ℕ}
    (hm : Tendsto digits atTop atTop) :
    (fun i => (1 - (ell : ℝ) / (2 : ℝ)^(digits i)) * ((2 : ℝ)^(digits i))^2 /
      ((2 : ℝ)^(digits i) - 1)) ~[atTop] (fun i => (2 : ℝ)^(digits i)) := by
  let N := fun i => (2 : ℝ)^(digits i)
  have hn : Tendsto N atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  have hn0 (i : ℕ) : 0 < N i := by unfold N; positivity
  apply (isEquivalent_iff_tendsto_one (Eventually.of_forall fun i => (hn0 i).ne')).2
  have hA : Tendsto (fun i => 1 - (ell : ℝ) / N i) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (ell : ℝ))).div_atTop hn).const_sub 1
  have hB : Tendsto (fun i => 1 - (1 : ℝ) / N i) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hn).const_sub 1
  have ht := hA.div hB one_ne_zero
  rw [div_one] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_gt_atTop (1 : ℝ)] with i hi
  change (1 - (ell : ℝ) / N i) / (1 - 1 / N i) =
    ((1 - (ell : ℝ) / N i) * (N i)^2 / (N i - 1)) / N i
  have h1N : 1 - (1 : ℝ) / N i ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt ((div_lt_iff₀ (hn0 i)).mpr (by simpa only [one_mul] using hi)))
  field_simp [(hn0 i).ne', (sub_pos.mpr hi).ne', h1N]

/-- Divergence on the prescribed flat spike for the paper's exact sequence
Γ=n²·2ⁿ. The sketch is the fixed-width genuine SRHT throughout. -/
theorem flatWalshRelativeMean_exponential_tendsto_atTop {digits : ℕ → ℕ}
    (hm : Tendsto digits atTop atTop) :
    Tendsto (fun i => flatWalshRelativeMean (digits i) ell
      (((2 : ℝ)^(digits i))^2 * (2 : ℝ)^((2 : ℕ)^(digits i)))) atTop atTop := by
  let N := fun i => (2 : ℝ)^(digits i)
  have hn : Tendsto N atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  refine tendsto_atTop_mono' atTop (f₁ := fun i => N i / 2) ?_ ?_
  · filter_upwards [hm.eventually_ge_atTop 1, hn.eventually_gt_atTop (ell : ℝ),
      hn.eventually_gt_atTop 1, hn.eventually_ge_atTop (2 * (ell : ℝ))] with i hi hw hn1 hw2
    have hWidth : ell < 2^(digits i) := by
      exact_mod_cast (show (ell : ℝ) < (2 : ℝ)^digits i from hw)
    have hN0 : 0 < N i := zero_lt_one.trans hn1
    have hOmit : (1 : ℝ) / 2 ≤ 1 - (ell : ℝ) / N i := by
      have hLess : (ell : ℝ) / N i ≤ 1 / 2 := (div_le_iff₀ hN0).2 (by linarith)
      linarith
    have hSize : N i ≤ (N i)^2 / (N i - 1) := by
      apply (le_div_iff₀ (sub_pos.mpr hn1)).2
      nlinarith
    have hBound := flatWalshRelativeMean_exponential_lower (ell := ell)
      (show 0 < digits i by omega) hWidth
    calc
      N i / 2 = (1 / 2 : ℝ) * N i := by ring
      _ ≤ (1 - (ell : ℝ) / N i) * ((N i)^2 / (N i - 1)) :=
        mul_le_mul hOmit hSize hN0.le (by linarith)
      _ = (1 - (ell : ℝ) / N i) * (N i)^2 / (N i - 1) := by rw [mul_div_assoc]
      _ ≤ _ := hBound
  · simpa only [div_eq_mul_inv, mul_comm _ ((2 : ℝ)⁻¹)] using
      hn.const_mul_atTop (show 0 < (2 : ℝ)⁻¹ by positivity)


/-- The projected vector of the prescribed flat target, scaled by √n. -/
def flatWalshScaledProjection (d : FlatWalshDraw m ell) : Block ell :=
  WithLp.toLp 2 (fun j => Real.sqrt ((2 : ℝ)^m) *
    ((flatWalshSketch d)ᵀ * flatWalshTarget m) j 0)

/-- The vector multiplying one sign when the selected rows are held fixed. -/
def flatWalshCoefficient (J : Fin ell ↪ Label m) (x : Label m) : Block ell :=
  WithLp.toLp 2 (fun j => core m (J j) x)

private def boolWalshSign : Bool ≃ ZMod 2 where
  toFun b := if b then 0 else 1
  invFun z := decide (z = 0)
  left_inv := by intro b; cases b <;> decide
  right_inv := by
    intro z
    have h : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases h z with rfl | rfl <;> decide

private theorem flatWalshScaledProjection_signedSum (J : Fin ell ↪ Label m)
    (z : Label m → Bool) :
    flatWalshScaledProjection (J, fun x => boolWalshSign (z x)) =
      signedCoefficientSum (flatWalshCoefficient J) z := by
  ext j
  let p : Block ell →ₗ[ℝ] ℝ := EuclideanSpace.projₗ j
  change _ = p (∑ x, _ • flatWalshCoefficient J x)
  rw [map_sum]
  change Real.sqrt ((2 : ℝ)^m) *
    ((flatWalshSketch (J, fun x => boolWalshSign (z x)))ᵀ * flatWalshTarget m) j 0 = _
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hn : Real.sqrt ((2 : ℝ)^m) ≠ 0 := by positivity
  change Real.sqrt ((2 : ℝ)^m) *
      (core m (J j) x * signValue (boolWalshSign (z x)) * (Real.sqrt ((2 : ℝ)^m))⁻¹) = _
  rw [map_smul]
  cases hz : z x
  · change Real.sqrt ((2 : ℝ)^m) *
      (core m (J j) x * signValue (boolWalshSign false) * (Real.sqrt ((2 : ℝ)^m))⁻¹) =
      (-1 : ℝ) * core m (J j) x
    rw [show boolWalshSign false = 1 from rfl, signValue_one]
    field_simp
  · change Real.sqrt ((2 : ℝ)^m) *
      (core m (J j) x * signValue (boolWalshSign true) * (Real.sqrt ((2 : ℝ)^m))⁻¹) =
      (1 : ℝ) * core m (J j) x
    rw [show boolWalshSign true = 0 from rfl, signValue_zero]
    field_simp

open scoped InnerProductSpace in
/-- Exact conditional variance, from orthogonality of the sampled Walsh rows. -/
theorem flatWalshCoefficient_inner_squares (J : Fin ell ↪ Label m) (t : Block ell) :
    (∑ x, (inner ℝ (flatWalshCoefficient J x) t)^2) = ‖t‖ ^ 2 := by
  let U := flatWalshSketch (J, (0 : Label m → ZMod 2))
  have hU : Uᵀ * U = 1 := flatWalshSketch_orthonormal _
  have he (x : Label m) :
      inner ℝ (flatWalshCoefficient J x) t = (U.toEuclideanLin t) x := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, flatWalshCoefficient,
      U, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, flatWalshSketch, Matrix.of_apply,
      Pi.zero_apply, signValue_zero, mul_one]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  simp_rw [he]
  rw [← EuclideanSpace.real_norm_sq_eq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq t, ← LinearMap.adjoint_inner_left,
    ← euclidean_transpose, ← LinearMap.comp_apply, ← euclidean_mul,
    hU, Matrix.toLpLin_one, LinearMap.id_apply]

private theorem flatWalshCoefficient_norm (J : Fin ell ↪ Label m) (x : Label m) :
    ‖flatWalshCoefficient J x‖ = Real.sqrt ((ell : ℝ) / (2 : ℝ)^m) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), EuclideanSpace.real_norm_sq_eq]
  have hcore (j : Fin ell) : core m (J j) x ^ 2 = ((2 : ℝ)^m)⁻¹ := by
    rw [core, mul_pow, signValue_sq, mul_one, inv_pow, Real.sq_sqrt (by positivity)]
  change (∑ j : Fin ell, core m (J j) x ^ 2) = _
  simp_rw [hcore]
  simp [div_eq_mul_inv]

open scoped InnerProductSpace in
/-- Every scalar coefficient is uniformly small over the choice of rows,
with the manuscript's `√(ℓ/n)` factor for a unit test vector. -/
theorem flatWalshCoefficient_inner_bound (J : Fin ell ↪ Label m) (x : Label m) (t : Block ell) :
    |inner ℝ (flatWalshCoefficient J x) t| ≤ Real.sqrt ((ell : ℝ) / (2 : ℝ)^m) * ‖t‖ := by
  rw [← Real.norm_eq_abs, ← flatWalshCoefficient_norm J x]
  exact norm_inner_le_norm _ _

open scoped InnerProductSpace in
/-- The Lindeberg tail vanishes uniformly over all sets of distinct rows,
because every coefficient is eventually smaller than the fixed cutoff. -/
theorem flatWalshCoefficient_lindeberg_tail_zero {digits : ℕ → ℕ}
    (hm : Tendsto digits atTop atTop) (t : Block ell) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ J : Fin ell ↪ Label (digits i),
      (∑ x : Label (digits i),
        if ε ≤ |inner ℝ (flatWalshCoefficient J x) t| then
          (inner ℝ (flatWalshCoefficient J x) t)^2 else 0) = 0 := by
  have hN : Tendsto (fun i => (2 : ℝ)^(digits i)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
  have hr : Tendsto (fun i => (ell : ℝ) / (2 : ℝ)^(digits i)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (ell : ℝ))).div_atTop hN
  have hB : Tendsto (fun i => Real.sqrt ((ell : ℝ) / (2 : ℝ)^(digits i)) * ‖t‖) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp hr).mul_const ‖t‖
    rw [Real.sqrt_zero, zero_mul] at h
    exact h
  filter_upwards [hB.eventually_lt_const hε] with i hi J
  apply Finset.sum_eq_zero
  intro x _
  exact if_neg (not_le_of_gt ((flatWalshCoefficient_inner_bound J x t).trans_lt hi))

open scoped InnerProductSpace in
private theorem flatWalshCoefficient_inner_fourth (J : Fin ell ↪ Label m) (t : Block ell) :
    (∑ x, (inner ℝ (flatWalshCoefficient J x) t)^4) ≤ (ell : ℝ) / (2 : ℝ)^m * ‖t‖^4 := by
  let q := (ell : ℝ) / (2 : ℝ)^m
  have hB (x : Label m) : (inner ℝ (flatWalshCoefficient J x) t)^2 ≤ q * ‖t‖ ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (flatWalshCoefficient_inner_bound J x t) 2
    rwa [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at h
  calc
    _ ≤ ∑ x, (q * ‖t‖ ^ 2) * (inner ℝ (flatWalshCoefficient J x) t)^2 := by
      apply Finset.sum_le_sum
      intro x _
      have hx := mul_le_mul_of_nonneg_right (hB x) (sq_nonneg (inner ℝ (flatWalshCoefficient J x) t))
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, flatWalshCoefficient_inner_squares]; unfold q; ring


set_option maxHeartbeats 1100000 in
open scoped InnerProductSpace in
/-- The CLT is uniform in the row choice. The environment is any finite
row selection made before drawing the independent signs. -/
theorem flatWalshScaledProjection_environment_tendsto {digits : ℕ → ℕ} {A : ℕ → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (J : ∀ i, A i → Fin ell ↪ Label (digits i)) (hm : Tendsto digits atTop atTop) :
    Tendsto (fun i => finiteProbabilityLaw (fun q : A i × (Label (digits i) → ZMod 2) =>
      flatWalshScaledProjection (J i q.1, q.2))) atTop (𝓝 (gaussianBlockLaw ell)) := by
  classical
  let coef (i : ℕ) (q : A i) (x : Label (digits i)) := flatWalshCoefficient (J i q) x
  have hVar (t : Block ell) : Tendsto (fun i => uniformMean fun q =>
      |(∑ x, (inner ℝ (coef i q x) t)^2) - ‖t‖^2|) atTop (𝓝 0) := by
    change Tendsto (fun i => uniformMean fun q : A i =>
      |(∑ x, (inner ℝ (flatWalshCoefficient (J i q) x) t)^2) - ‖t‖^2|) atTop (𝓝 0)
    simp only [flatWalshCoefficient_inner_squares, sub_self, abs_zero, uniformMean_const]
    exact tendsto_const_nhds
  have hFourth (t : Block ell) : Tendsto (fun i => uniformMean fun q =>
      ∑ x, (inner ℝ (coef i q x) t)^4) atTop (𝓝 0) := by
    have hN : Tendsto (fun i => (2 : ℝ)^(digits i)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hm
    have hBound : Tendsto (fun i => (ell : ℝ) / (2 : ℝ)^(digits i) * ‖t‖^4) atTop (𝓝 0) := by
      have h := ((tendsto_const_nhds (x := (ell : ℝ))).div_atTop hN).mul_const (‖t‖^4)
      rw [zero_mul] at h
      exact h
    refine squeeze_zero (g := fun i => (ell : ℝ) / (2 : ℝ)^(digits i) * ‖t‖^4) ?_ ?_ hBound
    · intro i
      unfold uniformMean
      exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
        (Nat.cast_nonneg _)
    · intro i
      rw [← uniformMean_const (A := A i) ((ell : ℝ) / (2 : ℝ)^(digits i) * ‖t‖^4)]
      exact uniformMean_mono fun q => flatWalshCoefficient_inner_fourth (J i q) t
  have h := tendsto_signedCoefficientLaw coef hVar hFourth
  apply h.congr
  intro i
  let e : (A i × (Label (digits i) → Bool)) ≃ A i × (Label (digits i) → ZMod 2) :=
    (Equiv.refl (A i)).prodCongr (Equiv.piCongrRight fun _ => boolWalshSign)
  let f (q : A i × (Label (digits i) → ZMod 2)) := flatWalshScaledProjection (J i q.1, q.2)
  change _ = finiteProbabilityLaw f
  rw [← finiteProbabilityLaw_reindex e f]
  congr 1
  funext q
  exact (flatWalshScaledProjection_signedSum (J i q.1) q.2).symm

/-- For every deterministic sequence of distinct sampled row sets, the
standard signed Walsh projection converges to the Gaussian vector. -/
theorem flatWalshScaledProjection_fixedRows_tendsto {digits : ℕ → ℕ}
    (J : ∀ i, Fin ell ↪ Label (digits i)) (hm : Tendsto digits atTop atTop) :
    Tendsto (fun i => finiteProbabilityLaw (fun z : Label (digits i) → ZMod 2 =>
      flatWalshScaledProjection (J i, z))) atTop (𝓝 (gaussianBlockLaw ell)) := by
  have h := flatWalshScaledProjection_environment_tendsto
    (A := fun _ => PUnit.{1}) (fun i _ => J i) hm
  apply h.congr
  intro i
  exact finiteProbabilityLaw_reindex (Equiv.punitProd (Label (digits i) → ZMod 2))
    (fun z => flatWalshScaledProjection (J i, z))

/-- With genuinely uniform distinct rows, the prescribed flat direction
has the same Gaussian projection limit. -/
theorem flatWalshScaledProjection_uniformRows_tendsto {digits : ℕ → ℕ}
    (hWidth : ∀ i, ell ≤ 2^(digits i)) (hm : Tendsto digits atTop atTop) :
    letI : ∀ i, Nonempty (Fin ell ↪ Label (digits i)) := fun i => label_embedding_nonempty (hWidth i)
    Tendsto (fun i => finiteProbabilityLaw (@flatWalshScaledProjection (digits i) ell)) atTop
      (𝓝 (gaussianBlockLaw ell)) := by
  let : ∀ i, Nonempty (Fin ell ↪ Label (digits i)) := fun i => label_embedding_nonempty (hWidth i)
  exact flatWalshScaledProjection_environment_tendsto (fun _ J => J) hm

end

end TypicalOrientations
