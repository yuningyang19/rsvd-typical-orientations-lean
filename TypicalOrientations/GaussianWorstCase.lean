import TypicalOrientations.RankDeficiency

namespace TypicalOrientations

open Matrix MeasureTheory SketchOrientation Filter
open scoped Topology MatrixOrder

noncomputable section

variable {n k l p : ℕ}

/-- The sharp finite-dimensional Gaussian worst-case mean from (1.2). -/
def gaussianWorstCaseValue (n k p : ℕ) : ℝ :=
  ((n : ℝ) - (k + p : ℕ)) / ((n : ℝ) - k) * (1 + (k : ℝ) / ((p : ℝ) - 1))

/-- The Gaussian polar decomposition identifies the reference mean with the
same residual under the Haar Stiefel-frame law. -/
theorem gaussianMean_eq_haarFrame (hl : l ≤ n) (k : ℕ) (σ : Fin n → ℝ) :
    gaussianMean k l σ = ∫ U, squaredResidual (diagonal σ) U / optimalSquaredTail k σ
      ∂gaussianHaarFrameLaw hl := by
  rw [gaussianMean_eq_haarProjector hl, haarSketchProjectorLaw,
    integral_map (measurable_haarFrameProjector hl).aemeasurable
      (measurable_subspaceLoss k σ).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_gaussianHaarFrame_orthonormal hl] with U hU
  rw [subspaceLoss, haarFrameProjector_val hl hU,
    squaredResidual_frame_projector _ _ hU]

private theorem leadingFrame_twoLevel_eq_diagonal (hkn : k ≤ n) (Γ : ℝ) :
    twoLevelInput (rowSelector (Fin.castLEEmb hkn))ᵀ Γ =
      diagonal (equalSpikeSpectrum (n := n) k Γ) := by
  let Q := rowSelector (Fin.castLEEmb hkn)
  have hP (i j : Fin n) : (Qᵀ * Q) i j = if i = j ∧ i.val < k then 1 else 0 := by
    rw [Matrix.mul_apply]
    simp only [Q, transpose_apply, rowSelector, Fin.castLEEmb_apply]
    by_cases hij : i = j
    · subst j
      simp only [true_and]
      by_cases hi : i.val < k
      · let s : Fin k := ⟨i.val, hi⟩
        have he (a : Fin k) : Fin.castLE hkn a = i ↔ a = s := by
          constructor
          · intro ha
            exact Fin.ext (congrArg (fun x : Fin n => x.val) ha)
          · rintro rfl
            exact Fin.ext rfl
        simp [he, hi]
      · have he (a : Fin k) : ¬ Fin.castLE hkn a = i := by
          intro ha
          exact hi (congrArg Fin.val ha ▸ a.isLt)
        simp [he, hi]
    · rw [if_neg (fun h => hij h.1)]
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : Fin.castLE hkn a = i
      · simp [ha, hij]
      · simp [ha]
  ext i j
  have he := hP i j
  change ((1 : Matrix (Fin n) (Fin n) ℝ) + (Real.sqrt Γ - 1) • (Qᵀ * Qᵀᵀ)) i j = _
  rw [transpose_transpose, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, he]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k <;> simp [equalSpikeSpectrum, hi]
  · simp [hij]

/-- A two-level input with its spike on the leading coordinate frame has
exactly the finite-gap Gaussian mean computed by the Haar frame formulas. -/
theorem gaussianMean_equalSpike_eq_haarFiniteMean (hk : 0 < k) (hkn : k < n)
    (hl : l ≤ n) {L : ℝ} (hL : 0 < L) (hΓ : 1 ≤ (n : ℝ) * k * L) :
    gaussianMean k l (equalSpikeSpectrum (n := n) k ((n : ℝ) * k * L)) =
      1 + (k : ℝ) * Cosine.haarSketchFiniteMean hl ((n : ℝ) * k * L)
        (rowSelector (Fin.castLEEmb hkn.le))ᵀ := by
  let V := (rowSelector (Fin.castLEEmb hkn.le))ᵀ
  have hV : Vᵀ * V = 1 := by
    dsimp [V]
    rw [transpose_transpose, rowSelector_orthonormal]
  let Γ := (n : ℝ) * k * L
  have hInput : twoLevelInput V Γ = diagonal (equalSpikeSpectrum (n := n) k Γ) :=
    leadingFrame_twoLevel_eq_diagonal hkn.le Γ
  have hTail : optimalTail k (twoLevelInput V Γ) = (n : ℝ) - k := by
    simpa only [Fintype.card_fin] using
      twoLevel_optimalTail (twoLevelInput V Γ) V hV hΓ
        (twoLevelInput_gram V hV (zero_le_one.trans hΓ))
  change gaussianMean k l (equalSpikeSpectrum (n := n) k Γ) =
    1 + (k : ℝ) * Cosine.haarSketchFiniteMean hl Γ V
  rw [gaussianMean_eq_haarFrame hl, equalSpikeSpectrum_optimalSquaredTail hkn.le,
    ← hInput, ← hTail]
  exact Cosine.haarSketchTailRelativeMean_eq hl hk hkn hL hΓ V hV

private theorem gaussianWorstCaseValue_eq_haarBenchmark (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k + p ≤ n) :
    gaussianWorstCaseValue n k p = 1 + (k : ℝ) * haarOrientationBenchmark n k (k + p) := by
  rw [haarOrientationBenchmark_eq_paper hk hp hn]
  unfold gaussianWorstCaseValue
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hk']
  ring

/-- The normalized mean at the exact two-level spectrum approaches the
sharp constant as the gap grows at a fixed ambient dimension. -/
theorem gaussianMean_equalSpike_tendsto (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n) :
    Tendsto (fun Γ : ℝ => gaussianMean k (k + p) (equalSpikeSpectrum (n := n) k Γ))
      atTop (𝓝 (gaussianWorstCaseValue n k p)) := by
  have hkn : k < n := by omega
  let V := (rowSelector (Fin.castLEEmb hkn.le))ᵀ
  have hV : Vᵀ * V = 1 := by
    dsimp [V]
    rw [transpose_transpose, rowSelector_orthonormal]
  let a := (n : ℝ) * k
  have ha : 0 < a := mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hk)
  let L := fun Γ : ℝ => Γ / a
  have hL : Tendsto L atTop atTop := by
    simpa only [L, div_eq_inv_mul, id_eq] using tendsto_id.const_mul_atTop (inv_pos.mpr ha)
  have hGap (Γ : ℝ) : (n : ℝ) * k * L Γ = Γ := by
    change a * (Γ / a) = Γ
    field_simp
  have hd : Tendsto (fun Γ => 2 / L Γ) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hL
  have hPow := (Real.continuous_rpow_const (show 0 ≤ (1 / 4 : ℝ) by norm_num)).continuousAt
    (x := 0) |>.tendsto.comp hd
  rw [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] at hPow
  have hBound := hPow.const_mul (chiSquareNegativeMoment (p + 1) (5 / 4 : ℝ))
  simp only [mul_zero] at hBound
  have hFeasible : ∀ᶠ Γ in atTop, 0 < L Γ ∧ 2 ≤ (n : ℝ) * k * L Γ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Γ hΓ
    exact ⟨div_pos (by linarith) ha, by rw [hGap]; exact hΓ⟩
  have hErr : Tendsto (fun Γ => haarOrientationBenchmark n k (k + p) -
      Cosine.haarSketchFiniteMean hn ((n : ℝ) * k * L Γ) V) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hBound
    · filter_upwards [hFeasible] with Γ hΓ
      exact (Cosine.haarSketchFiniteMean_window_difference hk hp hn hΓ.1 hΓ.2 V hV).1
    · filter_upwards [hFeasible] with Γ hΓ
      exact (Cosine.haarSketchFiniteMean_window_difference hk hp hn hΓ.1 hΓ.2 V hV).2
  have hCenter := tendsto_const_nhds (x := haarOrientationBenchmark n k (k + p)) |>.sub hErr
  simp only [sub_zero, sub_sub_cancel] at hCenter
  have hFull := (hCenter.const_mul (k : ℝ)).const_add 1
  rw [← gaussianWorstCaseValue_eq_haarBenchmark hk hp hn] at hFull
  refine hFull.congr' ?_
  filter_upwards [hFeasible] with Γ hΓ
  rw [← gaussianMean_equalSpike_eq_haarFiniteMean hk hkn hn hΓ.1 (by linarith [hΓ.2]), hGap]

/-- Every finite feasible gap gives a mean below the sharp Gaussian value. -/
theorem gaussianMean_equalSpike_le_worstCase (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    gaussianMean k (k + p) (equalSpikeSpectrum (n := n) k Γ) ≤ gaussianWorstCaseValue n k p := by
  have hkn : k < n := by omega
  let V := (rowSelector (Fin.castLEEmb hkn.le))ᵀ
  have hV : Vᵀ * V = 1 := by
    dsimp [V]
    rw [transpose_transpose, rowSelector_orthonormal]
  let a := (n : ℝ) * k
  have ha : 0 < a := mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hk)
  let G := max 2 Γ
  let L := G / a
  have hL : 0 < L := div_pos (by unfold G; linarith [le_max_left (2 : ℝ) Γ]) ha
  have hGap : (n : ℝ) * k * L = G := by
    change a * (G / a) = G
    field_simp
  have h2 : 2 ≤ (n : ℝ) * k * L := hGap ▸ le_max_left _ _
  have hHigh : gaussianMean k (k + p) (equalSpikeSpectrum (n := n) k G) ≤
      gaussianWorstCaseValue n k p := by
    rw [← hGap, gaussianMean_equalSpike_eq_haarFiniteMean hk hkn hn hL (by linarith),
      gaussianWorstCaseValue_eq_haarBenchmark hk hp hn]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (sub_nonneg.mp (Cosine.haarSketchFiniteMean_window_difference hk hp hn hL h2 V hV).1)
      (Nat.cast_nonneg k)) 1
  let S := equalSpikeSpectrum (n := n) k Γ
  let T := equalSpikeSpectrum (n := n) k G
  have hGram : (diagonal S)ᵀ * diagonal S ≤ (diagonal T)ᵀ * diagonal T := by
    rw [diagonal_transpose, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal,
      Matrix.le_iff]
    rw [show diagonal (fun i => T i * T i) - diagonal (fun i => S i * S i) =
      diagonal (fun i => T i * T i - S i * S i) by
        exact diagonal_sub (fun i => T i * T i) (fun i => S i * S i)]
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i.val < k
    · simp only [S, T, equalSpikeSpectrum, if_pos hi, ← pow_two,
        Real.sq_sqrt (show 0 ≤ Γ by linarith),
        Real.sq_sqrt (show 0 ≤ G by unfold G; linarith [le_max_left (2 : ℝ) Γ])]
      exact sub_nonneg.mpr (le_max_right _ _)
    · simp [S, T, equalSpikeSpectrum, hi]
  have hTail : 0 < (n : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkn)
  have hComp : gaussianMean k (k + p) S ≤ gaussianMean k (k + p) T := by
    have hInt (σ : Fin n → ℝ) (hσ : 0 < optimalSquaredTail k σ) :
        Integrable (fun M : Matrix (Fin n) (Fin (k + p)) ℝ =>
          squaredResidual (diagonal σ) M / optimalSquaredTail k σ) (gaussianMatrixLaw n (k + p)) := by
      apply Integrable.of_bound
        ((measurable_rawResidual measurable_const measurable_id).div_const _).aestronglyMeasurable
        (squaredFrobenius (diagonal σ) / optimalSquaredTail k σ)
      exact ae_of_all _ fun M => by
        simp only [id_eq]
        rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ hσ M)]
        exact residual_div_tail_le k σ hσ M
    have hS : optimalSquaredTail k S = (n : ℝ) - k := equalSpikeSpectrum_optimalSquaredTail hkn.le Γ
    have hT : optimalSquaredTail k T = (n : ℝ) - k := equalSpikeSpectrum_optimalSquaredTail hkn.le G
    exact integral_mono (hInt S (hS ▸ hTail)) (hInt T (hT ▸ hTail)) (fun M => by
      change squaredResidual (diagonal S) M / optimalSquaredTail k S ≤
        squaredResidual (diagonal T) M / optimalSquaredTail k T
      rw [hS, hT]
      exact div_le_div_of_nonneg_right (squaredResidual_mono_gram _ _ M hGram) hTail.le)
  exact hComp.trans hHigh

private theorem diagonal_residual_attains_sampled_approximation
    (σ : Fin n → ℝ) (G : Matrix (Fin n) (Fin l) ℝ) :
    ∃ R : Matrix (Fin l) (Fin n) ℝ, squaredResidual (diagonal σ) G =
      squaredFrobenius (diagonal σ * (1 - G * R)) := by
  let A := diagonal σ
  let Y := A * G
  have hS : (Yᵀ * Y).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self Y
  let R := symmetricPseudoInverse (Yᵀ * Y) hS * Yᵀ * A
  have hR : Y * R = rangeProjector Y * A := by
    rw [rangeProjector_eq_gram_pseudoInverse]
    simp only [R, Matrix.mul_assoc]
  refine ⟨R, ?_⟩
  change squaredFrobenius ((1 - rangeProjector Y) * A) = squaredFrobenius (A * (1 - G * R))
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, show A * G = Y from rfl, hR,
    Matrix.sub_mul, Matrix.one_mul]

private theorem squaredFrobenius_diagonal_mul (σ : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    squaredFrobenius (diagonal σ * Q) = ∑ i, σ i ^ 2 * (∑ j, Q i j ^ 2) := by
  simp only [Cosine.squaredFrobenius_eq_sum_entries, Matrix.diagonal_mul, mul_pow, Finset.mul_sum]

/-- Concavity in a diagonal Gram matrix, from the common minimizing
least-squares coefficient for the averaged weights. -/
theorem sum_squaredResidual_le_card_mul_of_gramAverage {ι : Type*} [Fintype ι]
    (T : ι → Fin n → ℝ) (S : Fin n → ℝ) (G : Matrix (Fin n) (Fin l) ℝ)
    (hAverage : ∀ i, (∑ a, T a i ^ 2) = (Fintype.card ι : ℝ) * S i ^ 2) :
    (∑ a, squaredResidual (diagonal (T a)) G) ≤
      (Fintype.card ι : ℝ) * squaredResidual (diagonal S) G := by
  classical
  obtain ⟨R, hR⟩ := diagonal_residual_attains_sampled_approximation S G
  let Q := (1 : Matrix (Fin n) (Fin n) ℝ) - G * R
  let f (i : Fin n) := ∑ j, Q i j ^ 2
  have hOpt (a : ι) : squaredResidual (diagonal (T a)) G ≤ squaredFrobenius (diagonal (T a) * Q) := by
    simpa only [Q, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc] using
      squaredResidual_le_sampled_approximation (diagonal (T a)) G R
  calc
    _ ≤ ∑ a, squaredFrobenius (diagonal (T a) * Q) := Finset.sum_le_sum (fun a _ => hOpt a)
    _ = ∑ i, ∑ a, T a i ^ 2 * f i := by
      simp only [squaredFrobenius_diagonal_mul, f]
      exact Finset.sum_comm
    _ = ∑ i, ((Fintype.card ι : ℝ) * S i ^ 2) * f i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hAverage]
    _ = _ := by
      rw [hR, squaredFrobenius_diagonal_mul]
      simp only [f, Q, mul_assoc, Finset.mul_sum]

private theorem integrable_gaussian_diagonalResidual (σ : Fin n → ℝ) :
    Integrable (fun G : Matrix (Fin n) (Fin l) ℝ => squaredResidual (diagonal σ) G)
      (gaussianMatrixLaw n l) := by
  apply Integrable.of_bound (measurable_rawResidual measurable_const measurable_id).aestronglyMeasurable
    (squaredFrobenius (diagonal σ))
  exact ae_of_all _ fun G => by
    simp only [id_eq]
    rw [Real.norm_of_nonneg (show 0 ≤ squaredResidual (diagonal σ) G from squaredFrobenius_nonneg _)]
    simpa only [Matrix.mul_zero, sub_zero] using
      squaredResidual_le_sampled_approximation (diagonal σ) G (0 : Matrix (Fin l) (Fin n) ℝ)

private theorem gaussian_diagonalResidual_mean_perm (π : Equiv.Perm (Fin n)) (σ : Fin n → ℝ) :
    (∫ G, squaredResidual (diagonal (σ ∘ π)) G ∂gaussianMatrixLaw n l) =
      ∫ G, squaredResidual (diagonal σ) G ∂gaussianMatrixLaw n l := by
  let Q := π.permMatrix ℝ
  have hQ : Qᵀ * Q = 1 := by
    dsimp [Q]
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  have hRot := gaussianMatrixLaw_map_left_orthogonal (k := l) Q hQ
  have hm : Measurable (fun G : Matrix (Fin n) (Fin l) ℝ => Q * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hR : Measurable (fun G : Matrix (Fin n) (Fin l) ℝ => squaredResidual (diagonal (σ ∘ π)) G) :=
    measurable_rawResidual measurable_const measurable_id
  calc
    _ = ∫ G, squaredResidual (diagonal (σ ∘ π)) (Q * G) ∂gaussianMatrixLaw n l := by
      rw [← integral_map (f := fun G => squaredResidual (diagonal (σ ∘ π)) G)
        hm.aemeasurable hR.aestronglyMeasurable, hRot]
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun G => by
        have hSub : Q * G = G.submatrix π id := by
          ext i j
          change (Q *ᵥ fun r => G r j) i = G (π i) j
          rw [Matrix.permMatrix_mulVec]
          rfl
        change squaredResidual (diagonal (σ ∘ π)) (Q * G) = squaredResidual (diagonal σ) G
        rw [hSub, ← Matrix.submatrix_diagonal_equiv]
        exact squaredResidual_submatrix_equiv π (diagonal σ) G

/-- Permute the two blocks independently, keeping the first k coordinates
and the remaining coordinates in their respective blocks. -/
private def blockPermutation (hkn : k ≤ n) [NeZero k] [NeZero (n-k)]
    (s : Fin k × Fin (n-k)) : Equiv.Perm (Fin n) :=
  (leadingTailEquiv hkn).symm.trans <|
    (Equiv.sumCongr (Equiv.addRight s.1) (Equiv.addRight s.2)).trans (leadingTailEquiv hkn)

set_option maxHeartbeats 800000 in
private theorem blockPermutation_average (hkn : k ≤ n) [NeZero k] [NeZero (n-k)]
    (σ : Fin n → ℝ) (a b : ℝ)
    (ha : (∑ j : Fin k, σ (leadingTailEquiv hkn (Sum.inl j)) ^ 2) = (k : ℝ) * a)
    (hb : (∑ j : Fin (n-k), σ (leadingTailEquiv hkn (Sum.inr j)) ^ 2) = ((n-k : ℕ) : ℝ) * b)
    (i : Fin n) :
    (∑ s : Fin k × Fin (n-k), σ (blockPermutation hkn s i) ^ 2) =
      (Fintype.card (Fin k × Fin (n-k)) : ℝ) * (if i.val < k then a else b) := by
  let e := leadingTailEquiv hkn
  obtain ⟨j, rfl⟩ := e.surjective i
  cases j with
  | inl j =>
    have hj : (e (Sum.inl j)).val < k := by
      dsimp only [e]
      rw [leadingTailEquiv_leading_val]
      exact j.isLt
    rw [if_pos hj, Fintype.sum_prod_type]
    have hApply (x : Fin k) (y : Fin (n-k)) :
        blockPermutation hkn (x, y) (e (Sum.inl j)) = e (Sum.inl (j + x)) := by
      simp [blockPermutation, e, Equiv.addRight]
    simp_rw [hApply]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
      Fintype.card_fin, Nat.cast_mul]
    have hsum : (∑ x : Fin k, σ (e (Sum.inl (j + x))) ^ 2) =
        ∑ x : Fin k, σ (e (Sum.inl x)) ^ 2 :=
      Fintype.sum_equiv (Equiv.addLeft j) _ _ (fun _ => rfl)
    rw [← Finset.mul_sum, hsum, ha]
    ring
  | inr j =>
    have hj : ¬ (e (Sum.inr j)).val < k := by
      dsimp only [e]
      rw [leadingTailEquiv_tail_val]
      omega
    rw [if_neg hj, Fintype.sum_prod_type]
    have hApply (x : Fin k) (y : Fin (n-k)) :
        blockPermutation hkn (x, y) (e (Sum.inr j)) = e (Sum.inr (j + y)) := by
      simp [blockPermutation, e, Equiv.addRight]
    simp_rw [hApply]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
      Fintype.card_fin, Nat.cast_mul]
    have hsum : (∑ y : Fin (n-k), σ (e (Sum.inr (j + y))) ^ 2) =
        ∑ y : Fin (n-k), σ (e (Sum.inr y)) ^ 2 :=
      Fintype.sum_equiv (Equiv.addLeft j) _ _ (fun _ => rfl)
    rw [hsum, hb]
    ring

/-- The trace of the Schur complement increases on averaging the squared
weights over the leading and trailing blocks of the Gaussian sketch. -/
theorem gaussian_diagonalResidual_mean_le_blockAverage (hk : 0 < k) (hkn : k < n)
    (σ : Fin n → ℝ) (a b : ℝ) (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (ha : (∑ j : Fin k, σ (leadingTailEquiv hkn.le (Sum.inl j)) ^ 2) = (k : ℝ) * a)
    (hb : (∑ j : Fin (n-k), σ (leadingTailEquiv hkn.le (Sum.inr j)) ^ 2) = ((n-k : ℕ) : ℝ) * b) :
    (∫ G, squaredResidual (diagonal σ) G ∂gaussianMatrixLaw n l) ≤
      ∫ G, squaredResidual (diagonal (fun i : Fin n => if i.val < k then Real.sqrt a else Real.sqrt b)) G
        ∂gaussianMatrixLaw n l := by
  let : NeZero k := ⟨hk.ne'⟩
  let : NeZero (n-k) := ⟨Nat.sub_ne_zero_of_lt hkn⟩
  let I := Fin k × Fin (n-k)
  let T (s : I) := σ ∘ blockPermutation hkn.le s
  let S (i : Fin n) := if i.val < k then Real.sqrt a else Real.sqrt b
  let C := (Fintype.card I : ℝ)
  have hC : 0 < C := Nat.cast_pos.mpr Fintype.card_pos
  have havg (i : Fin n) : (∑ s, T s i ^ 2) = C * S i ^ 2 := by
    have h := blockPermutation_average hkn.le σ a b ha hb i
    by_cases hi : i.val < k <;> simpa [T, S, C, I, hi, Real.sq_sqrt ha₀, Real.sq_sqrt hb₀] using h
  apply le_of_mul_le_mul_left ?_ hC
  calc
    C * (∫ G, squaredResidual (diagonal σ) G ∂gaussianMatrixLaw n l) =
        ∑ s : I, ∫ G, squaredResidual (diagonal (T s)) G ∂gaussianMatrixLaw n l := by
      simp only [T, gaussian_diagonalResidual_mean_perm, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, C]
    _ = ∫ G, ∑ s : I, squaredResidual (diagonal (T s)) G ∂gaussianMatrixLaw n l := by
      symm
      exact integral_finsetSum _ (fun s _ => integrable_gaussian_diagonalResidual (T s))
    _ ≤ ∫ G, C * squaredResidual (diagonal S) G ∂gaussianMatrixLaw n l := by
      exact integral_mono (integrable_finsetSum _ (fun s _ => integrable_gaussian_diagonalResidual (T s)))
        ((integrable_gaussian_diagonalResidual S).const_mul C)
        (fun G => sum_squaredResidual_le_card_mul_of_gramAverage T S G havg)
    _ = _ := integral_const_mul _ _

private theorem squaredFrobenius_real_smul {m d : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin d) ℝ) :
    squaredFrobenius (c • A) = c ^ 2 * squaredFrobenius A := by
  simp only [Cosine.squaredFrobenius_eq_sum_entries, Matrix.smul_apply, smul_eq_mul, mul_pow,
    Finset.mul_sum]

private theorem squaredResidual_real_smul {m : ℕ} (c : ℝ) (hc : c ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (G : Matrix (Fin n) (Fin l) ℝ) :
    squaredResidual (c • A) G = c ^ 2 * squaredResidual A G := by
  have hP : rangeProjector (c • (A * G)) = rangeProjector (A * G) := by
    apply rangeProjector_eq_of_range_eq
    rw [map_smul, LinearMap.range_smul _ _ hc]
  rw [squaredResidual, squaredResidual, Matrix.smul_mul, hP, Matrix.mul_smul,
    squaredFrobenius_real_smul]

/-- Averaging first within the two spectral blocks reduces the worst-case
upper bound to the two-level mean at the ratio of the two averaged weights. -/
theorem gaussianMean_le_worstCase (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n)
    (σ : Spectra n k) : gaussianMean k (k + p) σ.val ≤ gaussianWorstCaseValue n k p := by
  have hkn : k < n := by omega
  let e := leadingTailEquiv hkn.le
  let D := optimalSquaredTail k σ.val
  let u (i : Fin k) := σ.val (e (Sum.inl i)) ^ 2
  let v (j : Fin (n-k)) := σ.val (e (Sum.inr j)) ^ 2
  let a := (∑ i, u i) / (k : ℝ)
  let b := D / ((n-k : ℕ) : ℝ)
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hm : 0 < ((n-k : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hkn)
  have hD : 0 < D := σ.property.2.2
  have hD' : D = ∑ j, v j := optimalSquaredTail_eq_sum_tail hkn.le σ.val
  have hb : 0 < b := div_pos hD hm
  have haMean : (∑ i, u i) = (k : ℝ) * a := by unfold a; field_simp
  have hbMean : (∑ j, v j) = ((n-k : ℕ) : ℝ) * b := by rw [←hD']; unfold b; field_simp
  have hba : b ≤ a := by
    have hEach (i : Fin k) : b ≤ u i := by
      apply (div_le_iff₀ hm).2
      rw [hD']
      calc
        (∑ j, v j) ≤ ∑ _j : Fin (n-k), u i := by
          refine Finset.sum_le_sum fun j _ => ?_
          apply pow_le_pow_left₀ (σ.property.2.1 _) (σ.property.1 ?_) 2
          show (e (Sum.inl i)).val ≤ (e (Sum.inr j)).val
          change (leadingTailEquiv hkn.le _).val ≤ (leadingTailEquiv hkn.le _).val
          rw [leadingTailEquiv_leading_val, leadingTailEquiv_tail_val]
          omega
        _ = _ := by simp [mul_comm]
    apply (le_div_iff₀ hk').2
    calc
      b * k = ∑ _i : Fin k, b := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hEach i)
  have ha : 0 ≤ a := hb.le.trans hba
  let S : Fin n → ℝ := fun i => if i.val < k then Real.sqrt a else Real.sqrt b
  have hAvg := gaussian_diagonalResidual_mean_le_blockAverage (l := k+p) hk hkn σ.val a b ha
    hb.le haMean hbMean
  let Γ := a / b
  have hΓ : 1 ≤ Γ := (one_le_div hb).2 hba
  let T := equalSpikeSpectrum (n := n) k Γ
  have hScale : diagonal S = Real.sqrt b • diagonal T := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    have hb' : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
    by_cases hi : i.val < k
    · simp only [S, T, equalSpikeSpectrum, Pi.smul_apply, smul_eq_mul, if_pos hi, Γ,
        Real.sqrt_div ha]
      field_simp
    · simp [S, T, equalSpikeSpectrum, hi]
  have hScaleR (G : Matrix (Fin n) (Fin (k+p)) ℝ) :
      squaredResidual (diagonal S) G = b * squaredResidual (diagonal T) G := by
    rw [hScale, squaredResidual_real_smul _ (Real.sqrt_pos.2 hb).ne', Real.sq_sqrt hb.le]
  have hT : optimalSquaredTail k T = (n : ℝ) - k := equalSpikeSpectrum_optimalSquaredTail hkn.le Γ
  have hDScale : D = b * ((n : ℝ) - k) := by
    rw [← Nat.cast_sub hkn.le]
    unfold b
    field_simp
  have hCompare : gaussianMean k (k+p) σ.val ≤ gaussianMean k (k+p) T := by
    unfold gaussianMean
    rw [integral_div]
    calc
      _ ≤ (∫ G, squaredResidual (diagonal S) G ∂gaussianMatrixLaw n (k+p)) / D :=
        div_le_div_of_nonneg_right hAvg hD.le
      _ = _ := by
        simp_rw [hScaleR]
        rw [integral_const_mul, integral_div, hT, hDScale]
        field_simp
  exact hCompare.trans (gaussianMean_equalSpike_le_worstCase hk hp hn hΓ)

/-- Full-column-rank spectral data are precisely the positive sorted spectra. -/
def PositiveSpectra (n k : ℕ) := {σ : Spectra n k // ∀ i, 0 < σ.val i}

/-- The first equality of (1.2) in spectral coordinates, with the supremum
restricted to full-column-rank spectra. -/
theorem gaussianMean_sup_eq_worstCase (hk : 0 < k) (hp : 2 ≤ p) (hn : k + p ≤ n) :
    sSup (Set.range fun σ : PositiveSpectra n k => gaussianMean k (k+p) σ.val.val) =
      gaussianWorstCaseValue n k p := by
  have hkn : k < n := by omega
  let E := Set.range fun σ : PositiveSpectra n k => gaussianMean k (k+p) σ.val.val
  have hMem {Γ : ℝ} (hΓ : 1 ≤ Γ) :
      gaussianMean k (k+p) (equalSpikeSpectrum (n := n) k Γ) ∈ E := by
    let σ := equalSpikeSpectra hkn Γ hΓ
    have hpos (i : Fin n) : 0 < σ.val i := by
      change 0 < equalSpikeSpectrum k Γ i
      by_cases hi : i.val < k <;> simp [equalSpikeSpectrum, hi, Real.sqrt_pos.2 (show 0 < Γ by linarith)]
    exact ⟨⟨σ, hpos⟩, rfl⟩
  have hBound : BddAbove E := ⟨gaussianWorstCaseValue n k p,
    by rintro _ ⟨σ, rfl⟩; exact gaussianMean_le_worstCase hk hp hn σ.val⟩
  refine le_antisymm (csSup_le ⟨_, hMem le_rfl⟩ ?_) ?_
  · rintro _ ⟨σ, rfl⟩
    exact gaussianMean_le_worstCase hk hp hn σ.val
  · apply le_of_tendsto (gaussianMean_equalSpike_tendsto hk hp hn)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Γ hΓ
    exact le_csSup hBound (hMem hΓ)

private theorem projector_entry_nonneg (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : Pᵀ = P) (hi : P * P = P) (i : Fin n) : 0 ≤ P i i := by
  rw [← congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hi, Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro j _
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hs
  change P j i = P i j at h
  rw [h, ← pow_two]
  exact sq_nonneg _

private theorem leadingMask_sum (hkn : k ≤ n) :
    (∑ i : Fin n, if i.val < k then (1 : ℝ) else 0) = k := by
  rw [← Finset.sum_filter, Finset.sum_const, Fin.card_filter_val_lt, min_eq_right hkn]
  simp

private theorem trace_diagonal_mul_complement (σ : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) :
    (diagonal (fun i => σ i ^ 2) * (1-P)).trace = ∑ i, σ i ^ 2 * (1 - P i i) := by
  simp [Matrix.trace, Matrix.diagonal_mul]

private theorem leadingMask_weighted_complement (σ : Fin n → ℝ) :
    (∑ i, σ i ^ 2 * (1 - if (i : Fin n).val < k then (1 : ℝ) else 0)) = optimalSquaredTail k σ := by
  rw [optimalSquaredTail, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k <;> simp [hi, Nat.not_le_of_lt, Nat.le_of_not_gt]

private theorem sorted_trace_diagonal_mul_projection_bound (hkn : k < n) (σ : Fin n → ℝ)
    (hσ : Antitone σ) (hσ₀ : ∀ i, 0 ≤ σ i)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hPi : P * P = P)
    (hTrace : P.trace ≤ (k : ℝ)) :
    optimalSquaredTail k σ ≤ (diagonal (fun i => σ i ^ 2) * (1-P)).trace := by
  let c := σ ⟨k, hkn⟩ ^ 2
  let M (i : Fin n) : ℝ := if i.val < k then 1 else 0
  have h0 (i : Fin n) : 0 ≤ P i i := projector_entry_nonneg P hP hPi i
  have h1 (i : Fin n) : P i i ≤ 1 := by
    have h := projector_entry_nonneg (1-P) (by simp [hP]) (projector_complement P hPi) i
    simpa only [Matrix.sub_apply, Matrix.one_apply_eq, sub_nonneg] using h
  have hTerm (i : Fin n) : σ i ^ 2 * (P i i - M i) ≤ c * (P i i - M i) := by
    by_cases hi : i.val < k
    · have hc : c ≤ σ i ^ 2 :=
        pow_le_pow_left₀ (hσ₀ _) (hσ (show i.val ≤ k from hi.le)) 2
      exact mul_le_mul_of_nonpos_right hc (by simpa [M, hi] using h1 i)
    · have hc : σ i ^ 2 ≤ c :=
        pow_le_pow_left₀ (hσ₀ _) (hσ (show k ≤ i.val by omega)) 2
      exact mul_le_mul_of_nonneg_right hc (by simpa [M, hi] using h0 i)
  have hSum : ∑ i, σ i ^ 2 * (P i i - M i) ≤ 0 := by
    calc
      _ ≤ ∑ i, c * (P i i - M i) := Finset.sum_le_sum (fun i _ => hTerm i)
      _ = c * (P.trace - k) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, show (∑ i, M i) = k from leadingMask_sum hkn.le]
        rfl
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (sub_nonpos.mpr hTrace)
  rw [trace_diagonal_mul_complement, ← leadingMask_weighted_complement (k := k) σ]
  change (∑ i, σ i ^ 2 * (1 - M i)) ≤ ∑ i, σ i ^ 2 * (1 - P i i)
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one] at hSum ⊢
  linarith

/-- Eckart–Young tail equality for any input whose column Gram is diagonal
with the prescribed nonincreasing nonnegative singular values. -/
theorem optimalTail_eq_of_sorted_diagonal_gram {m : ℕ} (hkn : k < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (σ : Fin n → ℝ) (hσ : Antitone σ) (hσ₀ : ∀ i, 0 ≤ σ i)
    (hGram : Aᵀ * A = diagonal (fun i => σ i ^ 2)) :
    optimalTail k A = optimalSquaredTail k σ := by
  classical
  let M (i : Fin n) : ℝ := if i.val < k then 1 else 0
  let P := diagonal M
  have hP : Pᵀ = P := diagonal_transpose _
  have hPi : P * P = P := by
    rw [show P = diagonal M from rfl, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i.val < k <;> simp [M, hi]
  have hrank : P.rank = k := by
    rw [show P = diagonal M from rfl, rank_diagonal]
    have he : { i : Fin n // M i ≠ 0} ≃ Fin k :=
      { toFun := fun i => ⟨i.val.val, by
          by_contra hi
          exact i.property (by simp [M, hi])⟩
        invFun := fun i => ⟨Fin.castLE hkn.le i, by simp [M, i.isLt]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_fin] using Fintype.card_congr he
  let Z := A * P
  have hZ : Z.rank ≤ k := (rank_mul_le_right A P).trans hrank.le
  have hZVal : squaredFrobenius (A - Z) = optimalSquaredTail k σ := by
    rw [show A - Z = A * (1-P) by rw [Matrix.mul_sub, Matrix.mul_one],
      squaredFrobenius_mul_projector_right _ _ (by simp [hP]) (projector_complement P hPi),
      hGram, trace_diagonal_mul_complement, ← leadingMask_weighted_complement (k := k) σ]
    congr 1
    funext i
    rw [show P i i = M i from diagonal_apply_eq _ _]
  have hMin (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank ≤ k) :
      squaredFrobenius (A - Z) ≤ squaredFrobenius (A - B) := by
    let S := rangeProjector Bᵀ
    have hS : Sᵀ = S := rangeProjector_transpose _
    have hSi : S * S = S := rangeProjector_mul_self _
    have hBS : B * S = B := by
      have h := congrArg Matrix.transpose (rangeProjector_mul_sample Bᵀ)
      change (S * Bᵀ)ᵀ = Bᵀᵀ at h
      simpa only [transpose_mul, transpose_transpose, hS] using h
    have hTrace : S.trace ≤ (k : ℝ) := by
      rw [show S = rangeProjector Bᵀ from rfl, trace_rangeProjector, rank_transpose]
      exact_mod_cast hB
    calc
      _ = optimalSquaredTail k σ := hZVal
      _ ≤ (diagonal (fun i => σ i ^ 2) * (1-S)).trace :=
        sorted_trace_diagonal_mul_projection_bound hkn σ hσ hσ₀ S hS hSi hTrace
      _ = squaredFrobenius (A * (1-S)) := by
        rw [squaredFrobenius_mul_projector_right _ _ (by simp [hS]) (projector_complement S hSi), hGram]
      _ = squaredFrobenius ((A-B) * (1-S)) := by
        rw [Matrix.sub_mul, show B * (1-S) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, hBS, sub_self], sub_zero]
      _ ≤ _ := squaredFrobenius_mul_projector_right_le _ _ hS hSi
  rw [← hZVal, squaredFrobenius_eq_norm_sq]
  exact optimalTail_eq_of_best_approximation k A Z hZ (fun B hB => by
    simpa only [squaredFrobenius_eq_norm_sq] using hMin B hB)

private theorem mulVec_injective_of_full_column_rank {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) : Function.Injective A.mulVec := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [← Matrix.rank, hA, Module.finrank_pi, Fintype.card_fin] at h
  have hker : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

private theorem exists_sorted_column_gram {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ), Qᵀ * Q = 1 ∧ Antitone σ ∧
      (∀ i, 0 < σ i) ∧ (A * Q)ᵀ * (A * Q) = diagonal (fun i => σ i ^ 2) := by
  let H := Aᵀ * A
  have hH : H.PosDef := by
    simpa only [H, conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self A (mulVec_injective_of_full_column_rank A hA)
  let Q₀ : Matrix (Fin n) (Fin n) ℝ := hH.1.eigenvectorUnitary
  have hQ₀ : Q₀ᵀ * Q₀ = 1 := by
    simpa only [Q₀, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hH.1.eigenvectorUnitary
  let c : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let t : Fin n ≃o Fin (Fintype.card (Fin n)) := Fin.castOrderIso (Fintype.card_fin n).symm
  let π : Equiv.Perm (Fin n) := t.toEquiv.trans c
  let Q := Q₀.submatrix id π
  have hDiag₀ : Q₀ᵀ * H * Q₀ = diagonal hH.1.eigenvalues := by
    simpa only [Q₀, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] using
      hH.1.conjStarAlgAut_star_eigenvectorUnitary
  have hConj (B : Matrix (Fin n) (Fin n) ℝ) :
      Qᵀ * B * Q = (Q₀ᵀ * B * Q₀).submatrix π π := by
    dsimp only [Q]
    rw [transpose_submatrix]
    nth_rewrite 1 [← Matrix.submatrix_id_id B]
    change Q₀ᵀ.submatrix π (Equiv.refl _) * B.submatrix (Equiv.refl _) (Equiv.refl _) *
      Q₀.submatrix (Equiv.refl _) π = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  have hDiag : Qᵀ * H * Q = diagonal (hH.1.eigenvalues ∘ π) := by
    rw [hConj H, hDiag₀, Matrix.submatrix_diagonal_equiv]
  have hQ : Qᵀ * Q = 1 := by
    have h := hConj (1 : Matrix (Fin n) (Fin n) ℝ)
    simpa only [Matrix.mul_one, hQ₀, Matrix.submatrix_one_equiv] using h
  let σ (i : Fin n) := Real.sqrt (hH.1.eigenvalues (π i))
  have hEigen (i : Fin n) : hH.1.eigenvalues (π i) = hH.1.eigenvalues₀ (t i) := by
    change hH.1.eigenvalues₀ (c.symm (c (t i))) = _
    rw [Equiv.symm_apply_apply]
  have hσ : Antitone σ := by
    intro i j hij
    change Real.sqrt (hH.1.eigenvalues (π j)) ≤ Real.sqrt (hH.1.eigenvalues (π i))
    rw [hEigen, hEigen]
    exact Real.sqrt_le_sqrt (hH.1.eigenvalues₀_antitone (t.monotone hij))
  have hσ' (i : Fin n) : 0 < σ i := Real.sqrt_pos.2 (hH.eigenvalues_pos _)
  refine ⟨Q, σ, hQ, hσ, hσ', ?_⟩
  rw [transpose_mul, Matrix.mul_assoc Qᵀ, ← Matrix.mul_assoc Aᵀ, ← Matrix.mul_assoc Qᵀ,
    show Aᵀ * A = H from rfl, hDiag]
  congr 1
  funext i
  exact (Real.sq_sqrt (hH.eigenvalues_pos (π i)).le).symm

/-- The Gaussian expectation of the actual tail-relative residual of any
full-column-rank rectangular input has the same positive spectral model. -/
theorem gaussian_tailRelativeMean_eq_positiveSpectrum {m : ℕ} (hkn : k < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) :
    ∃ σ : PositiveSpectra n k, (∫ G, tailRelativeError k A G ∂gaussianMatrixLaw n l) =
      gaussianMean k l σ.val.val := by
  obtain ⟨Q, σ, hQ, hσ, hσpos, hGram⟩ := exists_sorted_column_gram A hA
  have hQt : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hT : 0 < optimalSquaredTail k σ := by
    unfold optimalSquaredTail
    apply Finset.sum_pos' (fun i _ => sq_nonneg (σ i))
    exact ⟨⟨k, hkn⟩, by simp, sq_pos_of_pos (hσpos ⟨k, hkn⟩)⟩
  refine ⟨⟨⟨σ, hσ, fun i => (hσpos i).le, hT⟩, hσpos⟩, ?_⟩
  have hOpt : optimalTail k A = optimalSquaredTail k σ :=
    (optimalTail_mul_orthogonal_right k A Q hQt hQ).symm.trans
      (optimalTail_eq_of_sorted_diagonal_gram hkn (A*Q) σ hσ (fun i => (hσpos i).le) hGram)
  have hDiag : (diagonal σ)ᵀ * diagonal σ = diagonal (fun i => σ i ^ 2) := by
    rw [diagonal_transpose, diagonal_mul_diagonal]
    simp only [pow_two]
  have hDraw (G : Matrix (Fin n) (Fin l) ℝ) :
      squaredResidual A G = squaredResidual (diagonal σ) (Qᵀ * G) := by
    calc
      _ = squaredResidual (A * Q) (Qᵀ * G) := by
        unfold squaredResidual
        rw [Matrix.mul_assoc A Q, ← Matrix.mul_assoc Q Qᵀ G, hQt, Matrix.one_mul,
          ← Matrix.mul_assoc, squaredFrobenius_mul_orthogonal_right _ _ hQt]
      _ = _ := le_antisymm
        (squaredResidual_mono_gram _ _ _ (by rw [hGram, hDiag]))
        (squaredResidual_mono_gram _ _ _ (by rw [hGram, hDiag]))
  change (∫ G, tailRelativeError k A G ∂gaussianMatrixLaw n l) = gaussianMean k l σ
  unfold tailRelativeError gaussianMean
  rw [hOpt]
  simp_rw [hDraw]
  have hR : Measurable (fun G : Matrix (Fin n) (Fin l) ℝ =>
      squaredResidual (diagonal σ) G / optimalSquaredTail k σ) :=
    (measurable_rawResidual measurable_const measurable_id).div_const _
  have hm : Measurable (fun G : Matrix (Fin n) (Fin l) ℝ => Qᵀ * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hrot := gaussianMatrixLaw_map_left_orthogonal (k := l) Qᵀ (by simpa only [transpose_transpose] using hQt)
  rw [← integral_map (f := fun G => squaredResidual (diagonal σ) G / optimalSquaredTail k σ)
    hm.aemeasurable hR.aestronglyMeasurable, hrot]

/-- Full-column-rank inputs with n columns, allowing every number of rows. -/
def FullColumnRankInputs (n : ℕ) := Σ m : ℕ, {A : Matrix (Fin m) (Fin n) ℝ // A.rank = n}

/-- Equation (1.2), first equality, for the actual Gaussian range finder
on full-column-rank matrices. -/
theorem gaussian_tailRelativeMean_sup_eq_worstCase (hk : 0 < k) (hp : 2 ≤ p) (hn : k+p ≤ n) :
    sSup (Set.range fun A : FullColumnRankInputs n =>
      ∫ G, tailRelativeError k A.2.val G ∂gaussianMatrixLaw n (k+p)) = gaussianWorstCaseValue n k p := by
  have hkn : k < n := by omega
  let E := Set.range fun A : FullColumnRankInputs n =>
    ∫ G, tailRelativeError k A.2.val G ∂gaussianMatrixLaw n (k+p)
  let F := Set.range fun σ : PositiveSpectra n k => gaussianMean k (k+p) σ.val.val
  have hEF : E = F := by
    ext x
    constructor
    · rintro ⟨⟨m, ⟨A, hA⟩⟩, rfl⟩
      obtain ⟨σ, hσ⟩ := gaussian_tailRelativeMean_eq_positiveSpectrum (l := k+p) hkn A hA
      exact ⟨σ, hσ.symm⟩
    · rintro ⟨σ, rfl⟩
      let s := σ.val.val
      have hRank : (diagonal s).rank = n := by
        classical
        rw [rank_diagonal]
        have he : {i : Fin n // s i ≠ 0} ≃ Fin n :=
          { toFun := Subtype.val
            invFun := fun i => ⟨i, (σ.property i).ne'⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        simpa only [Fintype.card_fin] using Fintype.card_congr he
      refine ⟨⟨n, ⟨diagonal s, hRank⟩⟩, ?_⟩
      have hGram : (diagonal s)ᵀ * diagonal s = diagonal (fun i => s i ^ 2) := by
        rw [diagonal_transpose, diagonal_mul_diagonal]
        simp only [pow_two]
      change (∫ G, squaredResidual (diagonal s) G / optimalTail k (diagonal s)
        ∂gaussianMatrixLaw n (k+p)) = gaussianMean k (k+p) s
      rw [optimalTail_eq_of_sorted_diagonal_gram hkn _ s σ.val.property.1 σ.val.property.2.1 hGram]
      rfl
  change sSup E = _
  rw [hEF]
  exact gaussianMean_sup_eq_worstCase hk hp hn

end

end TypicalOrientations
