import SketchOrientation.WalshPositiveLoss
import SketchOrientation.WalshFrame
import SketchOrientation.TwoLevelResidual

/-!
# Actual rank-one RSVD loss for signed Walsh frames
-/

open Matrix Filter Asymptotics
open scoped Topology BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

/-- A rank-one frame with equal amplitudes on the prescribed support. -/
def targetFrame {m s : ℕ} (rows : Fin s ↪ Label m) : Matrix (Label m) (Fin 1) ℝ :=
  fun i _ => supportTarget rows i

theorem targetFrame_orthonormal {m s : ℕ} (rows : Fin s ↪ Label m) (hs : 0 < s) :
    (targetFrame rows)ᵀ * targetFrame rows = 1 := by
  ext i j
  have hij : i = j := Subsingleton.elim i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, targetFrame, Matrix.one_apply, hij, if_true,
    ← pow_two]
  exact supportTarget_unit rows hs

theorem normalizedProjection_eq_targetFrame {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) (j : Fin ell) :
    normalizedProjection rows cols d j = Real.sqrt ((2 : ℝ)^m) *
      ((targetFrame rows)ᵀ * signedMatrix cols d) 0 j := by
  rw [normalizedProjection_eq_supportTarget]
  rfl

/-- The rank-one scalar formula measures the actual residual of the two-level
input under the signed Walsh sketch. -/
theorem centeredRankLoss_eq_walshTable {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (d : SignedPermDraw m) (hs : 0 < s) (hm : 0 < m) {L : ℝ}
    (hΓ : 1 ≤ (2 : ℝ)^m * L) :
    centeredRankLoss 1 (twoLevelInput (targetFrame rows) ((2 : ℝ)^m * L)) (signedMatrix cols d) =
      rankOneLoss ((2 : ℝ)^m) L ell (walshTableEnergy (table (restrictSignedPerm rows cols d))) := by
  let n : ℝ := (2 : ℝ)^m
  let V := targetFrame rows
  let U := signedMatrix cols d
  let B := Vᵀ * U
  let Y := walshTableEnergy (table (restrictSignedPerm rows cols d))
  have hV : Vᵀ * V = 1 := targetFrame_orthonormal rows hs
  have hU : Uᵀ * U = 1 := signedMatrix_orthonormal cols d
  have hdim : 1 < Fintype.card (Label m) := by
    rw [card_label]
    exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hm.ne'
  have hLoss := twoLevel_centeredRankLoss (twoLevelInput V (n*L)) U V hU hV hΓ
    (twoLevelInput_gram V hV (zero_le_one.trans hΓ))
    (by decide : 0 < Fintype.card (Fin 1))
    (by simpa only [Fintype.card_fin] using hdim)
  simp only [Fintype.card_fin, card_label, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat,
    one_mul] at hLoss
  change centeredRankLoss 1 (twoLevelInput V (n * L)) U = rankOneLoss n L ell Y
  rw [hLoss]
  have hGram : Vᵀ * (U * Uᵀ) * V = B * Bᵀ := by
    simp [B, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hGram, Matrix.trace_fin_one, Matrix.inv_subsingleton, Matrix.diagonal_apply_eq,
    Ring.inverse_eq_inv, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
  have hY : Y = n * (B * Bᵀ) 0 0 := by
    change walshTableEnergy (table (restrictSignedPerm rows cols d)) = _
    rw [← projectionEnergy_eq_tableEnergy]
    simp_rw [normalizedProjection_eq_targetFrame, mul_pow,
      Real.sq_sqrt (show 0 ≤ (2 : ℝ)^m by positivity)]
    rw [← Finset.mul_sum]
    change n * (∑ j, B 0 j ^ 2) = n * (B * Bᵀ) 0 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hn : n ≠ 0 := by dsimp [n]; positivity
  have hY' : (B * Bᵀ) 0 0 = Y / n := by rw [hY, mul_comm, mul_div_cancel_right₀ _ hn]
  rw [hY', rankOneLoss]
  have hden : 1 + (n * L - 1) * (Y / n) = 1 + (L - 1 / n) * Y := by
    field_simp
  change (n * L * (1 + (n * L - 1) * (Y / n))⁻¹ - (ell : ℝ)) / (n - 1) = _
  rw [hden]
  ring

theorem meanLoss_eq_actual {m s ell : ℕ} (rows : Fin s ↪ Label m)
    (cols : Fin ell ↪ Label m) (hs : 0 < s) (hm : 0 < m) {L : ℝ}
    (hΓ : 1 ≤ (2 : ℝ)^m * L) :
    (uniformMean fun d : SignedPermDraw m =>
      centeredRankLoss 1 (twoLevelInput (targetFrame rows) ((2 : ℝ)^m * L)) (signedMatrix cols d)) =
        meanLoss m s ell L := by
  simp_rw [centeredRankLoss_eq_walshTable rows cols _ hs hm hΓ]
  exact uniformMean_restrictSignedPerm rows cols (fun d =>
    rankOneLoss ((2 : ℝ)^m) L ell (walshTableEnergy (table d)))


/-- Theorem 1.4 for the actual centered rank-one RSVD loss and signed Walsh
sketch. The index shift drops the initial sizes where the prescribed sketch
width, support, or spectral gap is infeasible. -/
theorem prescribedGap_actual {ell : ℕ} (hell : 2 < ell) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    let s := fun i => walshSupport ell ((2 : ℝ)^m i) (L i)
    ∃ N : ℕ,
      ∃ rows : ∀ i : ℕ, Fin (s (i + N)) ↪ Label (m (i + N)),
      ∃ cols : ∀ i : ℕ, Fin ell ↪ Label (m (i + N)),
        (∀ i, (targetFrame (rows i))ᵀ * targetFrame (rows i) = 1) ∧
        Tendsto (fun i => signedPermBlockLaw (rows i) (cols i)) atTop (𝓝 (gaussianBlockLaw ell)) ∧
        Tendsto (fun i => uniformMean (fun d : SignedPermDraw (m (i + N)) =>
          centeredRankLoss 1 (twoLevelInput (targetFrame (rows i))
            ((2 : ℝ)^m (i + N) * L (i + N))) (signedMatrix (cols i) d))) atTop atTop := by
  classical
  dsimp only
  let s (i : ℕ) := walshSupport ell ((2 : ℝ)^m i) (L i)
  obtain ⟨hsize, hblock, hloss⟩ := prescribedGap_gaussian_divergence hell hm hL
  have htail : ∀ᶠ i in atTop, (0 < s i ∧ s i ≤ 2 ^ m i ∧ ell ≤ 2 ^ m i) ∧
      1 ≤ m i ∧ 1 ≤ L i :=
    hsize.and ((hm.eventually_ge_atTop 1).and (hL.eventually_ge_atTop 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have h (i : ℕ) := hN (i + N) (by omega)
  let rows (i : ℕ) : Fin (s (i + N)) ↪ Label (m (i + N)) :=
    Classical.choice (label_embedding_nonempty (h i).1.2.1)
  let cols (i : ℕ) : Fin ell ↪ Label (m (i + N)) :=
    Classical.choice (label_embedding_nonempty (h i).1.2.2)
  refine ⟨N, rows, cols, (fun i => targetFrame_orthonormal _ (h i).1.1), ?_, ?_⟩
  · simp_rw [signedPermBlockLaw_eq_sampledBlockLaw]
    exact hblock.comp (tendsto_add_atTop_nat N)
  · have hΓ (i : ℕ) : 1 ≤ (2 : ℝ)^m (i + N) * L (i + N) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (h i).2.2
    simp_rw [fun i => meanLoss_eq_actual (rows i) (cols i) (h i).1.1
      (Nat.zero_lt_one.trans_le (h i).2.1) (hΓ i)]
    exact hloss.comp (tendsto_add_atTop_nat N)


/-- Probability that the actual rank-one target is orthogonal to every
sampled column of the signed Walsh sketch. -/
def actualMissProbability {m s ell : ℕ} (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) : ℝ :=
  uniformProbability fun d : SignedPermDraw m =>
    ∀ j : Fin ell, ((targetFrame rows)ᵀ * signedMatrix cols d) 0 j = 0

theorem actualMissProbability_eq {m s ell : ℕ}
    (rows : Fin s ↪ Label m) (cols : Fin ell ↪ Label m) :
    actualMissProbability rows cols = missProbability m s ell := by
  rw [← missProbability_eq_signedPerm rows cols]
  apply congrArg uniformProbability
  funext d
  apply propext
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    sq_nonneg (normalizedProjection rows cols d j))]
  have hn : Real.sqrt ((2 : ℝ)^m) ≠ 0 := by positivity
  simp [normalizedProjection_eq_targetFrame, hn]

/-- Proposition 6.4 for the actual signed Walsh sketch and centered RSVD
residual. The asymptotic miss term retains its exact finite-dimensional
coefficient for every growing gap. -/
theorem proposition_6_4_actual {m s : ℕ → ℕ} {ell : ℕ} (hell : 2 < ell)
    (rows : ∀ i : ℕ, Fin (s i) ↪ Label (m i)) (cols : ∀ i : ℕ, Fin ell ↪ Label (m i))
    (hs : Tendsto s atTop atTop) (he : ∀ᶠ i in atTop, Even (s i))
    (hgrowth : Tendsto (fun i => (s i : ℝ) ^ (2 + (ell : ℝ) / 2) / (2 : ℝ) ^ m i)
      atTop (𝓝 0)) :
    ((fun i => actualMissProbability (rows i) (cols i)) ~[atTop]
      (fun i => (2 / Real.pi) ^ ((ell : ℝ) / 2) * (s i : ℝ) ^ (-(ell : ℝ) / 2))) ∧
    ∀ L : ℕ → ℝ, Tendsto L atTop atTop →
      Tendsto (fun i => (uniformMean fun d : SignedPermDraw (m i) =>
        centeredRankLoss 1 (twoLevelInput (targetFrame (rows i)) ((2 : ℝ)^m i * L i))
          (signedMatrix (cols i) d)) -
        (2 : ℝ)^m i / ((2 : ℝ)^m i - 1) * L i * actualMissProbability (rows i) (cols i))
        atTop (𝓝 (1 / ((ell : ℝ) - 2))) := by
  have hr' (i : ℕ) : s i ≤ 2 ^ m i := by
    simpa only [Fintype.card_fin, card_label] using
      Fintype.card_le_of_injective (rows i) (rows i).injective
  have hc' (i : ℕ) : ell ≤ 2 ^ m i := by
    simpa only [Fintype.card_fin, card_label] using
      Fintype.card_le_of_injective (cols i) (cols i).injective
  have hr : ∀ᶠ i in atTop, s i ≤ 2 ^ m i := Eventually.of_forall hr'
  have hc : ∀ᶠ i in atTop, ell ≤ 2 ^ m i := Eventually.of_forall hc'
  have hm : Tendsto m atTop atTop := by
    refine tendsto_atTop.2 fun k => ?_
    filter_upwards [hs.eventually_ge_atTop ((2 : ℕ)^k)] with i hi
    by_contra! h
    exact (not_lt_of_ge (hi.trans (hr' i))) (Nat.pow_lt_pow_right (by decide) h)
  simp_rw [actualMissProbability_eq]
  refine ⟨missProbability_isEquivalent hs he hr hc hgrowth, fun L hL => ?_⟩
  refine (tendsto_meanLoss_sub_miss hell hm hs he hr hc hgrowth hL).congr' ?_
  filter_upwards [hs.eventually_ge_atTop 1, hm.eventually_ge_atTop 1, hL.eventually_ge_atTop 1]
    with i hsi hmi hLi
  have hΓ : 1 ≤ (2 : ℝ)^m i * L i := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) hLi
  rw [meanLoss_eq_actual (rows i) (cols i) (Nat.zero_lt_one.trans_le hsi)
    (Nat.zero_lt_one.trans_le hmi) hΓ]

end SketchOrientation.Edge.Walsh
