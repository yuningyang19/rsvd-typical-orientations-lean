import TypicalOrientations.BenchmarkBound
import TypicalOrientations.SamplingGeometry
import Mathlib.Probability.ConditionalProbability

namespace TypicalOrientations

open Matrix MeasureTheory SketchOrientation ProbabilityTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

variable {n k l : ℕ}

/-- The squared singular values are Γ in the leading k positions and
one in the remaining positions. -/
def equalSpikeSpectrum (k : ℕ) (Γ : ℝ) (i : Fin n) : ℝ :=
  if i.val < k then Real.sqrt Γ else 1

theorem equalSpikeSpectrum_optimalSquaredTail (hkn : k ≤ n) (Γ : ℝ) :
    optimalSquaredTail k (equalSpikeSpectrum (n := n) k Γ) = (n : ℝ) - k := by
  unfold optimalSquaredTail
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_, Finset.sum_const, nsmul_eq_mul, mul_one]
  · have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => i.val < k)
    have hsmall := Fin.card_filter_val_lt (n := n) (m := k)
    simp only [Nat.not_lt, Fintype.card_fin, Finset.card_univ, hsmall, min_eq_right hkn] at hcard
    have h := show (Finset.univ.filter (fun i : Fin n => k ≤ i.val)).card = n - k by omega
    rw [h, Nat.cast_sub hkn]
  · intro i hi
    have hik := (Finset.mem_filter.mp hi).2
    simp [equalSpikeSpectrum, Nat.not_lt.mpr hik]

def equalSpikeSpectra (hkn : k < n) (Γ : ℝ) (hΓ : 1 ≤ Γ) : Spectra n k := by
  refine ⟨equalSpikeSpectrum k Γ, ?_, ?_, ?_⟩
  · intro i j hij
    have h : i.val ≤ j.val := hij
    have hΓs : 1 ≤ Real.sqrt Γ := (Real.le_sqrt zero_le_one (by linarith)).2 (by linarith)
    by_cases hj : j.val < k
    · have hi : i.val < k := by omega
      simp [equalSpikeSpectrum, hi, hj]
    · by_cases hi : i.val < k <;> simp [equalSpikeSpectrum, hi, hj, hΓs]
  · intro i
    by_cases hi : i.val < k <;> simp [equalSpikeSpectrum, hi, Real.sqrt_nonneg]
  · rw [equalSpikeSpectrum_optimalSquaredTail hkn.le]
    exact sub_pos.mpr (by exact_mod_cast hkn)

private theorem rank_lt_width_exists_unit_kernel_column (B : Matrix (Fin l) (Fin k) ℝ)
    (hB : B.rank < k) :
    ∃ Z : Matrix (Fin k) (Fin 1) ℝ, Zᵀ * Z = 1 ∧ B * Z = 0 := by
  have hNI : ¬ Function.Injective B.mulVecLin := by
    intro h
    have hRank : B.rank = k := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj h, Module.finrank_pi,
        Fintype.card_fin]
    omega
  have hNB : LinearMap.ker B.mulVecLin ≠ ⊥ := fun h => hNI (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v, hv, hv₀⟩ := (Submodule.ne_bot_iff _).mp hNB
  let Z₀ : Matrix (Fin k) (Fin 1) ℝ := Matrix.replicateCol _ v
  have hZ₀ : Z₀ ≠ 0 := by
    intro he
    apply hv₀
    funext i
    exact congrArg (fun M : Matrix (Fin k) (Fin 1) ℝ => M i 0) he
  have hBZ₀ : B * Z₀ = 0 := by
    ext i j
    exact congrFun (LinearMap.mem_ker.mp hv) i
  let Z := ‖Z₀‖⁻¹ • Z₀
  have hZN : ‖Z‖ = 1 := by
    rw [show Z = ‖Z₀‖⁻¹ • Z₀ from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hZ₀)]
  have hZ : Zᵀ * Z = 1 := by
    have h := squaredFrobenius_eq_norm_sq Z
    rw [hZN, one_pow] at h
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simpa only [squaredFrobenius, Matrix.trace, Matrix.diag_apply, Fintype.sum_unique,
      Fin.default_eq_zero, Matrix.one_apply_eq] using h
  exact ⟨Z, hZ, by rw [show Z = ‖Z₀‖⁻¹ • Z₀ from rfl, Matrix.mul_smul, hBZ₀, smul_zero]⟩

/-- A below-target-rank draw misses a unit vector of the leading left
subspace. It leaves at least the full squared energy Γ of that vector. -/
theorem equalSpike_squaredResidual_ge_of_rank_lt (hkn : k ≤ n) (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (Ω : Matrix (Fin n) (Fin l) ℝ) (hRank : Ω.rank < k) :
    Γ ≤ squaredResidual (diagonal (equalSpikeSpectrum k Γ) * U) Ω := by
  let σ := equalSpikeSpectrum (n := n) k Γ
  let A := diagonal σ * U
  let V := (rowSelector (Fin.castLEEmb hkn))ᵀ
  let Y := A * Ω
  let P := rangeProjector Y
  let B := Yᵀ * V
  have hV : Vᵀ * V = 1 := by
    dsimp [V]
    rw [transpose_transpose, rowSelector_orthonormal]
  have hB : B.rank < k := calc
    B.rank ≤ Yᵀ.rank := rank_mul_le_left _ _
    _ = Y.rank := Matrix.rank_transpose _
    _ ≤ Ω.rank := rank_mul_le_right _ _
    _ < k := hRank
  obtain ⟨Z, hZ, hBZ⟩ := rank_lt_width_exists_unit_kernel_column B hB
  let W := V * Z
  have hW : Wᵀ * W = 1 := by
    dsimp [W]
    rw [transpose_mul, Matrix.mul_assoc Zᵀ, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, hZ]
  have hYN : Yᵀ * W = 0 := by
    rw [show W = V * Z from rfl, ← Matrix.mul_assoc]
    exact hBZ
  have hPW : P * W = 0 := by
    rw [show P = rangeProjector Y from rfl, rangeProjector_eq_gram_pseudoInverse,
      Matrix.mul_assoc, Matrix.mul_assoc, hYN, Matrix.mul_zero, Matrix.mul_zero]
  have hWP : Wᵀ * P = 0 := by
    have h := congrArg Matrix.transpose hPW
    simpa only [Matrix.transpose_mul, rangeProjector_transpose Y, Matrix.transpose_zero, P] using h
  have hGram : A * Aᵀ = diagonal (fun i => σ i * σ i) := by
    dsimp [A]
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U _ _,
      mul_eq_one_comm.mp hU, Matrix.one_mul, diagonal_mul_diagonal]
  have hLeft : diagonal (fun i => σ i * σ i) * V = Γ • V := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, V, transpose_apply, rowSelector]
    by_cases he : Fin.castLE hkn j = i
    · have hi : i.val < k := by
        rw [← he]
        exact j.isLt
      simp [he, σ, equalSpikeSpectrum, hi, ← pow_two,
        Real.sq_sqrt (show 0 ≤ Γ by linarith)]
    · simp [he]
  have hEnergy : squaredFrobenius (Wᵀ * A) = Γ := by
    unfold squaredFrobenius
    rw [transpose_mul, transpose_transpose, trace_mul_comm]
    have hG : diagonal (fun i => σ i * σ i) * W = Γ • W := by
      rw [show W = V * Z from rfl, ← Matrix.mul_assoc, hLeft, Matrix.smul_mul]
    calc
      ((Wᵀ * A) * (Aᵀ * W)).trace = (Wᵀ * ((A * Aᵀ) * W)).trace := by
        simp only [Matrix.mul_assoc]
      _ = Γ := by
        rw [hGram, hG, Matrix.mul_smul, hW,
          Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Nat.cast_one, smul_eq_mul, mul_one]
  let R := (1 - P) * A
  have hSame : Wᵀ * R = Wᵀ * A := by
    dsimp [R]
    rw [← Matrix.mul_assoc Wᵀ, Matrix.mul_sub, Matrix.mul_one, hWP, sub_zero]
  have hUnit : ‖W‖ = 1 := by
    have hN : ‖W‖ ^ 2 = 1 := by
      rw [← squaredFrobenius_eq_norm_sq, squaredFrobenius, hW, Matrix.trace_one,
        Fintype.card_fin, Nat.cast_one]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hN)
  have hF := Matrix.frobenius_norm_mul Wᵀ R
  rw [Matrix.frobenius_norm_transpose, hUnit, one_mul, hSame] at hF
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hF 2
  rw [← squaredFrobenius_eq_norm_sq, ← squaredFrobenius_eq_norm_sq, hEnergy] at hSq
  exact hSq

private theorem rank_eq_width_of_gram_det_ne_zero (Y : Matrix (Fin n) (Fin l) ℝ)
    (h : (gaussianGram Y).det ≠ 0) : Y.rank = l := by
  have hInj : Function.Injective Y.mulVecLin := (gaussianGram_det_ne_zero_iff _).1 h
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hInj, Module.finrank_pi, Fintype.card_fin]

private theorem rank_ge_iff_selectedGram (Ω : Matrix (Fin n) (Fin l) ℝ) (k : ℕ) :
    k ≤ Ω.rank ↔ ∃ J : Fin k ↪ Fin l, (gaussianGram (Ω.submatrix id J)).det ≠ 0 := by
  constructor
  · intro h
    rw [Matrix.rank_eq_finrank_span_cols] at h
    obtain ⟨v, hv, _, hV⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range Ω.col)
    let e := Fin.castLEEmb h
    choose j hj using hv
    let J : Fin k ↪ Fin l := ⟨j ∘ e, fun a b hab =>
      e.injective (hV.injective (by rw [← hj (e a), ← hj (e b), show j (e a) = j (e b) from hab]))⟩
    refine ⟨J, (gaussianGram_det_ne_zero_iff _).2 ?_⟩
    rw [Matrix.mulVec_injective_iff]
    have hc : (Ω.submatrix id J).col = v ∘ e := by
      funext i
      exact hj (e i)
    rw [hc]
    exact hV.comp e e.injective
  · rintro ⟨J, hJ⟩
    exact rank_eq_width_of_gram_det_ne_zero (Ω.submatrix id J) hJ ▸ Matrix.rank_submatrix_le Ω id J

private theorem measurableSet_selectedGram {r : ℕ} (J : Fin r ↪ Fin l) :
    MeasurableSet {Ω : Matrix (Fin n) (Fin l) ℝ | (gaussianGram (Ω.submatrix id J)).det ≠ 0} := by
  let f : Matrix (Fin n) (Fin l) ℝ → Matrix (Fin n) (Fin r) ℝ := fun Ω => Ω.submatrix id J
  have hf : Continuous f := continuous_id.matrix_submatrix id J
  have hG : Continuous (fun Ω => gaussianGram (f Ω)) := hf.matrix_transpose.matrix_mul hf
  exact (isClosed_singleton.preimage hG.matrix_det).measurableSet.compl

/-- Rank less than k is a Borel event, since rank at least k is the
presence of a k-column family with nonsingular Gram matrix. -/
theorem measurableSet_rank_lt (k : ℕ) :
    MeasurableSet {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank < k} := by
  classical
  let S := fun J : Fin k ↪ Fin l =>
    {Ω : Matrix (Fin n) (Fin l) ℝ | (gaussianGram (Ω.submatrix id J)).det ≠ 0}
  have he : {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank < k} = (⋃ J, S J)ᶜ := by
    ext Ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, S]
    change Ω.rank < k ↔ ¬ ∃ J : Fin k ↪ Fin l, (gaussianGram (Ω.submatrix id J)).det ≠ 0
    rw [← rank_ge_iff_selectedGram Ω k]
    omega
  rw [he]
  exact (MeasurableSet.iUnion (measurableSet_selectedGram (n := n))).compl

theorem measurableSet_rank_eq (r : ℕ) :
    MeasurableSet {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank = r} := by
  have he : {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank = r} =
      {Ω | Ω.rank < r+1} \ {Ω | Ω.rank < r} := by
    ext Ω
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    omega
  rw [he]
  exact (measurableSet_rank_lt (r+1)).diff (measurableSet_rank_lt r)

private theorem selectedColumns_range_eq (Ω : Matrix (Fin n) (Fin l) ℝ)
    {r : ℕ} (J : Fin r ↪ Fin l) (hR : Ω.rank = r)
    (hD : (gaussianGram (Ω.submatrix id J)).det ≠ 0) :
    LinearMap.range (Ω.submatrix id J).toEuclideanLin = LinearMap.range Ω.toEuclideanLin := by
  let X := Ω.submatrix id J
  have hSub : X = Ω * (rowSelector J)ᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, rowSelector, X, Matrix.submatrix_apply, id_eq,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hL : LinearMap.range X.toEuclideanLin ≤ LinearMap.range Ω.toEuclideanLin := by
    rw [hSub, euclidean_mul]
    exact LinearMap.range_comp_le_range _ _
  refine Submodule.eq_of_le_of_finrank_le hL ?_
  rw [← rank_eq_finrank_euclidean, ← rank_eq_finrank_euclidean, hR,
    rank_eq_width_of_gram_det_ne_zero X hD]

/-- Across rank changes, the range projector is Borel measurable by
covering the domain with countably many full-column-rank formulas. -/
theorem measurable_rangeProjector_of_matrix :
    Measurable (rangeProjector : Matrix (Fin n) (Fin l) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let I := Σ r : ℕ, Fin r ↪ Fin l
  let C (a : I) := {Ω : Matrix (Fin n) (Fin l) ℝ |
    Ω.rank = a.1 ∧ (gaussianGram (Ω.submatrix id a.2)).det ≠ 0}
  let R (a : I) (Ω : Matrix (Fin n) (Fin l) ℝ) :=
    let X := Ω.submatrix id a.2
    X * (gaussianGram X)⁻¹ * Xᵀ
  have hC (a : I) : MeasurableSet (C a) :=
    (measurableSet_rank_eq a.1).inter (measurableSet_selectedGram a.2)
  have hM (a : I) : Measurable (R a) := by
    let X : Matrix (Fin n) (Fin l) ℝ → Matrix (Fin n) (Fin a.1) ℝ :=
      fun Ω => Ω.submatrix id a.2
    have hX : Continuous X := continuous_id.matrix_submatrix id a.2
    have hg : Measurable (fun Ω => gaussianGram (X Ω)) :=
      (hX.matrix_transpose.matrix_mul hX).measurable
    exact measurable_matrix_product (measurable_matrix_product hX.measurable
      (measurable_matrix_nonsing_inv.comp hg)) hX.matrix_transpose.measurable
  have hE (a : I) {Ω : Matrix (Fin n) (Fin l) ℝ} (h : Ω ∈ C a) :
      rangeProjector Ω = R a Ω := by
    let X := Ω.submatrix id a.2
    have hRank : Ω.rank = a.1 := h.1
    have hD : (gaussianGram X).det ≠ 0 := h.2
    have hUnit := isUnit_iff_ne_zero.mpr hD
    have he : rangeProjector Ω = rangeProjector X :=
      rangeProjector_eq_of_range_eq _ _ (selectedColumns_range_eq Ω a.2 hRank hD).symm
    rw [he]
    apply rangeProjector_of_inner_inverse
    change gaussianGram X * (gaussianGram X)⁻¹ * gaussianGram X = gaussianGram X
    rw [Matrix.mul_nonsing_inv _ hUnit, Matrix.one_mul]
  intro T hT
  have he : (rangeProjector : Matrix (Fin n) (Fin l) ℝ → Matrix (Fin n) (Fin n) ℝ) ⁻¹' T =
      ⋃ a : I, C a ∩ (R a ⁻¹' T) := by
    ext Ω
    constructor
    · intro h
      obtain ⟨J,hJ⟩ := (rank_ge_iff_selectedGram Ω Ω.rank).1 le_rfl
      let a : I := ⟨Ω.rank,J⟩
      have hCa : Ω ∈ C a := ⟨rfl,hJ⟩
      refine Set.mem_iUnion.mpr ⟨a,hCa,?_⟩
      change R a Ω ∈ T
      rw [← hE a hCa]
      exact h
    · intro h
      obtain ⟨a, hCa, hA⟩ := Set.mem_iUnion.mp h
      change rangeProjector Ω ∈ T
      rw [hE a hCa]
      exact hA
  rw [he]
  exact MeasurableSet.iUnion fun a => (hC a).inter (hM a hT)

/-- The actual full-range residual at one sketch-matrix draw and one
orientation, expressed in singular coordinates. The sketch need not have
full column rank. -/
def matrixOrientationResidual (k : ℕ) (σ : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (Ω : Matrix (Fin n) (Fin l) ℝ) : ℝ :=
  squaredResidual (diagonal σ) (U * Ω) / optimalSquaredTail k σ

theorem matrixOrientationResidual_eq_rotatedInput (k : ℕ) (σ : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) (Ω : Matrix (Fin n) (Fin l) ℝ) :
    matrixOrientationResidual k σ U Ω =
      squaredResidual (diagonal σ * U) Ω / optimalSquaredTail k σ := by
  unfold matrixOrientationResidual squaredResidual
  rw [← Matrix.mul_assoc (diagonal σ) U Ω]
  let P := 1 - rangeProjector ((diagonal σ * U) * Ω)
  change squaredFrobenius (P * diagonal σ) / optimalSquaredTail k σ =
    squaredFrobenius (P * (diagonal σ * U)) / optimalSquaredTail k σ
  rw [← Matrix.mul_assoc P (diagonal σ) U,
    squaredFrobenius_mul_orthogonal_right _ _ (mul_eq_one_comm.mp hU)]

/-- Average the sketch law at the given orientation, including every draw. -/
def matrixConditionalResidual (k : ℕ) (σ : Fin n → ℝ)
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) (U : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ Ω, matrixOrientationResidual k σ U Ω ∂μ

theorem measurable_matrixOrientationResidual (k : ℕ) (σ : Fin n → ℝ) :
    Measurable (Function.uncurry (@matrixOrientationResidual n l k σ)) := by
  exact (measurable_rawResidual measurable_const
    (measurable_matrix_product measurable_fst measurable_snd)).div_const _

private theorem integrable_matrixOrientationResidual (k : ℕ) (σ : Fin n → ℝ)
    (htail : 0 < optimalSquaredTail k σ)
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) [IsProbabilityMeasure μ] :
    Integrable (Function.uncurry (matrixOrientationResidual k σ))
      ((gaussianRightOrthogonalLaw n).prod μ) := by
  apply Integrable.of_bound (measurable_matrixOrientationResidual k σ).aestronglyMeasurable
    (squaredFrobenius (diagonal σ) / optimalSquaredTail k σ)
  exact ae_of_all _ fun z => by
    change ‖squaredResidual (diagonal σ) (z.1 * z.2) / optimalSquaredTail k σ‖ ≤ _
    rw [Real.norm_of_nonneg (residual_div_tail_nonneg k σ htail _)]
    exact residual_div_tail_le k σ htail _

/-- The probability of a draw with rank below the target rank. -/
def rankDeficiencyProbability (k : ℕ) (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) : ℝ :=
  μ.real {Ω | Ω.rank < k}

/-- The joint Haar and sketch expectation keeps the exact probability factor
and the exact tail normalization in the paper's rank-deficiency bound. -/
theorem equalSpike_meanResidual_ge_rankDeficiency (hkn : k < n) (Γ : ℝ) (hΓ : 1 ≤ Γ)
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) [IsProbabilityMeasure μ] :
    rankDeficiencyProbability k μ * Γ / ((n : ℝ) - k) ≤
      ∫ z, matrixOrientationResidual k (equalSpikeSpectrum k Γ) z.1 z.2
        ∂(gaussianRightOrthogonalLaw n).prod μ := by
  let η := gaussianRightOrthogonalLaw n
  let σ := equalSpikeSpectrum (n := n) k Γ
  let S := {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank < k}
  let c := Γ / ((n : ℝ) - k)
  let I := S.indicator (fun _ => c)
  let R := Function.uncurry (@matrixOrientationResidual n l k σ)
  have hT : 0 < (n : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkn)
  have htail : 0 < optimalSquaredTail k σ := by rw [equalSpikeSpectrum_optimalSquaredTail hkn.le]; exact hT
  have hS : MeasurableSet S := measurableSet_rank_lt k
  have hI := (measurePreserving_snd : MeasurePreserving Prod.snd (η.prod μ) μ)
  have hInt : Integrable R (η.prod μ) := integrable_matrixOrientationResidual k σ htail μ
  have hIi : Integrable I μ := (integrable_const c).indicator hS
  have hIi' : Integrable (I ∘ Prod.snd) (η.prod μ) := hI.integrable_comp_of_integrable hIi
  have hBound : (I ∘ Prod.snd) ≤ᵐ[η.prod μ] R := by
    have hU := (measurePreserving_fst : MeasurePreserving Prod.fst (η.prod μ) η)
      |>.quasiMeasurePreserving.tendsto_ae (ae_gaussianRightOrthogonal n)
    filter_upwards [hU] with z hz
    change S.indicator (fun _ => c) z.2 ≤ matrixOrientationResidual k σ z.1 z.2
    by_cases he : z.2 ∈ S
    · rw [Set.indicator_of_mem he, matrixOrientationResidual_eq_rotatedInput k σ z.1 hz z.2,
        show optimalSquaredTail k σ = (n : ℝ) - k from equalSpikeSpectrum_optimalSquaredTail hkn.le Γ]
      exact div_le_div_of_nonneg_right
        (equalSpike_squaredResidual_ge_of_rank_lt hkn.le Γ hΓ z.1 hz z.2 he) hT.le
    · rw [Set.indicator_of_notMem he]
      exact residual_div_tail_nonneg k σ htail (z.1 * z.2)
  calc
    _ = ∫ Ω, I Ω ∂μ := by
      change _ = ∫ Ω, S.indicator (fun _ => c) Ω ∂μ
      rw [integral_indicator_const _ hS]
      change μ.real S * Γ / ((n : ℝ) - k) = μ.real S * c
      unfold c
      ring
    _ = ∫ z, (I ∘ Prod.snd) z ∂η.prod μ := by
      have hm : AEStronglyMeasurable I ((η.prod μ).map Prod.snd) := by
        rw [hI.map_eq]
        exact hIi.aestronglyMeasurable
      have h := integral_map hI.measurable.aemeasurable hm
      rw [hI.map_eq] at h
      exact h
    _ ≤ _ := integral_mono_ae hIi' hInt hBound

/-- Positive below-target rank probability makes the spectrum-uniform mean
absolute discrepancy unbounded at that dimension. The Gaussian comparison
uses the same spectrum and width. -/
theorem rankDeficiency_meanDiscrepancy_unbounded {p : ℕ} (hk : 0 < k) (hp : 2 ≤ p)
    (hn : k+p ≤ n) (μ : Measure (Matrix (Fin n) (Fin (k+p)) ℝ)) [IsProbabilityMeasure μ]
    (hδ : 0 < rankDeficiencyProbability k μ) :
    ¬ BddAbove (Set.range fun σ : Spectra n k =>
      ∫ U, |matrixConditionalResidual k σ.val μ U - gaussianMean k (k+p) σ.val|
        ∂gaussianRightOrthogonalLaw n) := by
  rintro ⟨M, hM⟩
  let δ := rankDeficiencyProbability k μ
  let T := (n : ℝ) - k
  let K := gaussianTailMomentConstant k p (5/4)
  let B := max 0 (M + K) + 1
  let Γ := B * T / δ + 1
  have hkn : k < n := by omega
  have hT : 0 < T := sub_pos.mpr (by exact_mod_cast hkn)
  have hB : 0 < B := by
    unfold B
    linarith [le_max_left (0 : ℝ) (M + K)]
  have hΓ : 1 ≤ Γ := by unfold Γ; linarith [div_nonneg (mul_nonneg hB.le hT.le) hδ.le]
  let σ := equalSpikeSpectra hkn Γ hΓ
  let F := matrixConditionalResidual k σ.val μ
  let g := gaussianMean k (k+p) σ.val
  let η := gaussianRightOrthogonalLaw n
  have hG : g ≤ K := gaussianMean_le_momentConstant hk hp hn σ
  have hI := integrable_matrixOrientationResidual k σ.val σ.property.2.2 μ
  have hF : Integrable F η := hI.integral_prod_left
  have hLow := equalSpike_meanResidual_ge_rankDeficiency hkn Γ hΓ μ
  have hMean : δ * Γ / T ≤ ∫ U, F U ∂η := by
    change _ ≤ ∫ z, Function.uncurry (matrixOrientationResidual k σ.val) z
      ∂η.prod μ at hLow
    rw [integral_prod _ hI] at hLow
    exact hLow
  have hGap : (∫ U, F U ∂η) - g ≤ ∫ U, |F U - g| ∂η := by
    calc
      _ = ∫ U, F U - g ∂η := by rw [integral_sub hF (integrable_const g)]; simp
      _ ≤ _ := integral_mono (hF.sub (integrable_const g)) (hF.sub (integrable_const g)).abs
        (fun U => le_abs_self (F U - g))
  have hCalc : δ * Γ / T = B + δ / T := by
    unfold Γ
    field_simp [show δ ≠ 0 from hδ.ne', hT.ne']
  have hContra : M < ∫ U, |F U - g| ∂η := by
    have hM' : M + K < B := by unfold B; linarith [le_max_right (0 : ℝ) (M + K)]
    have hB' : B < δ * Γ / T := by rw [hCalc]; linarith [div_pos hδ hT]
    linarith
  exact (not_le_of_gt hContra) (hM ⟨σ, rfl⟩)


private theorem rank_rangeProjector_eq (Y : Matrix (Fin n) (Fin l) ℝ) :
    (rangeProjector Y).rank = Y.rank := by
  apply Nat.cast_injective (R := ℝ)
  rw [← trace_rangeProjector Y, ← trace_rangeProjector (rangeProjector Y),
    rangeProjector_of_projector _ (rangeProjector_transpose Y) (rangeProjector_mul_self Y)]

private theorem rankDeficiency_diagonal_sign_orthogonal {s : Fin n → ℝ}
    (hs : ∀ i, s i = 1 ∨ s i = -1) : (diagonal s)ᵀ * diagonal s = 1 := by
  rw [diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases hs i with hi | hi <;> simp [hi]

private theorem rankDeficiency_permutation_orthogonal (π : Equiv.Perm (Fin n)) :
    (π.permMatrix ℝ)ᵀ * (π.permMatrix ℝ) = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

private theorem integrable_rangeProjector_entry_of_matrix
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) [IsProbabilityMeasure μ] (i j : Fin n) :
    Integrable (fun Y => rangeProjector Y i j) μ := by
  have hm : Measurable (fun Y : Matrix (Fin n) (Fin l) ℝ => rangeProjector Y i j) :=
    (continuous_id.matrix_elem i j).measurable.comp measurable_rangeProjector_of_matrix
  refine Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun Y => ?_)
  let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  let R := LinearMap.range Y.toEuclideanLin
  have hp : (rangeProjector Y).toEuclideanLin u = R.starProjection u :=
    congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => f u)
      (euclidean_projector Y)
  have he : (R.starProjection u) i = rangeProjector Y i j := by
    rw [← hp]
    change ((toLpLin 2 2 (rangeProjector Y)) u) i = _
    simp [u, Matrix.toLpLin_apply, EuclideanSpace.single]
  rw [← he]
  exact (PiLp.norm_apply_le _ _).trans
    ((R.norm_starProjection_apply_le u).trans_eq (by simp [u]))

private theorem rangeProjector_entry_integrals_eq_of_symmetry
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ * S = 1)
    (hLaw : (μ.map fun Ω => rangeProjector (S * Ω)) = μ.map rangeProjector)
    (i j : Fin n) :
    (∫ Ω, (S * rangeProjector Ω * Sᵀ) i j ∂μ) = ∫ Ω, rangeProjector Ω i j ∂μ := by
  let f : Matrix (Fin n) (Fin n) ℝ → ℝ := fun P => P i j
  have hf : Measurable f := (continuous_id.matrix_elem i j).measurable
  have hm : Measurable (fun Ω : Matrix (Fin n) (Fin l) ℝ => rangeProjector (S * Ω)) :=
    measurable_rangeProjector_of_matrix.comp (continuous_const.matrix_mul continuous_id).measurable
  have h := congrArg (fun ν : Measure (Matrix (Fin n) (Fin n) ℝ) => ∫ P, f P ∂ν) hLaw
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_rangeProjector_of_matrix.aemeasurable hf.aestronglyMeasurable] at h
  simpa only [f, rangeProjector_mul_orthogonal_left S hS] using h

/-- The trace argument for raw sign/permutation-invariant column-space laws
also keeps every rank-deficient draw. Its scalar is the expected rank divided by n. -/
theorem meanRangeProjector_eq_expected_rank_identity (hn : 0 < n)
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) [IsProbabilityMeasure μ]
    (hSign : ∀ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      (μ.map fun Ω => rangeProjector (diagonal s * Ω)) = μ.map rangeProjector)
    (hPerm : ∀ π : Equiv.Perm (Fin n),
      (μ.map fun Ω => rangeProjector (π.permMatrix ℝ * Ω)) = μ.map rangeProjector) :
    (Matrix.of fun i j => ∫ Ω, rangeProjector Ω i j ∂μ) =
      ((∫ Ω, ((Ω.rank : ℕ) : ℝ) ∂μ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => ∫ Ω, rangeProjector Ω i j ∂μ)
  have hOff (i j : Fin n) (hij : i ≠ j) : M i j = 0 := by
    let s : Fin n → ℝ := fun a => if a = i then -1 else 1
    have hs (a : Fin n) : s a = 1 ∨ s a = -1 := by by_cases ha : a = i <;> simp [s, ha]
    have h := rangeProjector_entry_integrals_eq_of_symmetry μ (diagonal s)
      (rankDeficiency_diagonal_sign_orthogonal hs) (hSign s hs) i j
    have he (P : Matrix (Fin n) (Fin n) ℝ) :
        (diagonal s * P * (diagonal s)ᵀ) i j = -(P i j) := by
      simp [s, diagonal_transpose, Ne.symm hij]
    simp_rw [he, integral_neg] at h
    change -(M i j) = M i j at h
    linarith
  have hPermEntry (P : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) (i j : Fin n) :
      (π.permMatrix ℝ * P * (π.permMatrix ℝ)ᵀ) i j = P (π i) (π j) := by
    have hL (a b : Fin n) : (π.permMatrix ℝ * P) a b = P (π a) b := by
      change (π.permMatrix ℝ *ᵥ fun r => P r b) a = _
      rw [Matrix.permMatrix_mulVec]
      rfl
    rw [Matrix.transpose_permMatrix]
    change ((fun r => (π.permMatrix ℝ * P) i r) ᵥ* (π⁻¹).permMatrix ℝ) j = _
    rw [Matrix.vecMul_permMatrix]
    simpa only [Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_symm] using hL i (π j)
  have hSame (i j : Fin n) : M i i = M j j := by
    let π := Equiv.swap i j
    have h := rangeProjector_entry_integrals_eq_of_symmetry μ (π.permMatrix ℝ)
      (rankDeficiency_permutation_orthogonal π) (hPerm π) i i
    simp only [hPermEntry, π, Equiv.swap_apply_left] at h
    exact h.symm
  have hTrace : M.trace = ∫ Ω, ((Ω.rank : ℕ) : ℝ) ∂μ := by
    change (∑ i, ∫ Ω, rangeProjector Ω i i ∂μ) = _
    rw [← integral_finsetSum _ (fun i _ => integrable_rangeProjector_entry_of_matrix μ i i)]
    exact integral_congr_ae (ae_of_all _ fun Ω => trace_rangeProjector Ω)
  have hDiag (i : Fin n) : M i i = (∫ Ω, ((Ω.rank : ℕ) : ℝ) ∂μ) / n := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr hn.ne')).2
    calc
      M i i * n = ∑ _j : Fin n, M i i := by simp [mul_comm]
      _ = ∑ j : Fin n, M j j := Finset.sum_congr rfl fun j _ => hSame i j
      _ = _ := hTrace
  ext i j
  change M i j = _
  by_cases h : i = j
  · subst j
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using hDiag i
  · simp [h, hOff i j h]

private theorem map_cond_eq_cond_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f) {E : Set Y} (hE : MeasurableSet E) :
    (ProbabilityTheory.cond μ (f ⁻¹' E)).map f = ProbabilityTheory.cond (μ.map f) E := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Measure.restrict_map hf hE, Measure.map_apply hf hE]

/-- Conditioning on rank l preserves an orthogonal symmetry of the
column-space law, even when the unconditioned matrix law has variable rank. -/
theorem fullRank_conditioned_preserves_column_space_symmetry
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ * S = 1)
    (hLaw : (μ.map fun Ω => rangeProjector (S * Ω)) = μ.map rangeProjector) :
    let ν := ProbabilityTheory.cond μ {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank = l}
    (ν.map fun Ω => rangeProjector (S * Ω)) = ν.map rangeProjector := by
  dsimp only
  let E := {P : Matrix (Fin n) (Fin n) ℝ | P.rank = l}
  let f := fun Ω : Matrix (Fin n) (Fin l) ℝ => rangeProjector (S * Ω)
  let g := fun Ω : Matrix (Fin n) (Fin l) ℝ => rangeProjector Ω
  let F := {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank = l}
  have hE : MeasurableSet E := measurableSet_rank_eq l
  have hg : Measurable g := measurable_rangeProjector_of_matrix
  have hf : Measurable f := measurable_rangeProjector_of_matrix.comp
    (continuous_const.matrix_mul continuous_id).measurable
  have hDet : S.det ≠ 0 := by
    have h := congrArg Matrix.det hS
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  have hfg : f ⁻¹' E = F := by
    ext Ω
    change (rangeProjector (S * Ω)).rank = l ↔ Ω.rank = l
    rw [rank_rangeProjector_eq, Matrix.rank_mul_eq_right_of_det_ne_zero S Ω hDet]
  have hgg : g ⁻¹' E = F := by
    ext Ω
    change (rangeProjector Ω).rank = l ↔ Ω.rank = l
    rw [rank_rangeProjector_eq]
  change (ProbabilityTheory.cond μ F).map f = (ProbabilityTheory.cond μ F).map g
  calc
    _ = ProbabilityTheory.cond (μ.map f) E := hfg ▸ map_cond_eq_cond_map μ hf hE
    _ = ProbabilityTheory.cond (μ.map g) E := congrArg (fun ν => ProbabilityTheory.cond ν E) hLaw
    _ = _ := (hgg ▸ map_cond_eq_cond_map μ hg hE).symm


/-- The full-rank conditional law is admissible for Corollary 4.2 whenever
the full-rank event has positive probability. -/
theorem meanSketchProjector_of_conditionedFullRank_symmetry (hn : 0 < n) (hl : l ≤ n)
    (μ : Measure (Matrix (Fin n) (Fin l) ℝ)) [IsProbabilityMeasure μ]
    (hMass : μ {Ω | Ω.rank = l} ≠ 0)
    (hSign : ∀ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
      (μ.map fun Ω => rangeProjector (diagonal s * Ω)) = μ.map rangeProjector)
    (hPerm : ∀ π : Equiv.Perm (Fin n),
      (μ.map fun Ω => rangeProjector (π.permMatrix ℝ * Ω)) = μ.map rangeProjector) :
    let ν := ProbabilityTheory.cond μ {Ω | Ω.rank = l}
    meanSketchProjector (ν.map (fullRankColumnProjector hl)) =
      ((l : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let E := {Ω : Matrix (Fin n) (Fin l) ℝ | Ω.rank = l}
  let ν := ProbabilityTheory.cond μ E
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hMass
  have hE : MeasurableSet E := measurableSet_rank_eq l
  have hA : ∀ᵐ Ω ∂ν, Ω ∈ E :=
    (ae_iff).2 ((prob_compl_eq_zero_iff hE).2 (cond_apply_self hMass (measure_ne_top μ E)))
  have hinj : ∀ᵐ Ω ∂ν, Function.Injective Ω.mulVec := by
    filter_upwards [hA] with Ω hΩ
    have hr : Ω.rank = l := hΩ
    have h := LinearMap.finrank_range_add_finrank_ker Ω.mulVecLin
    rw [← Matrix.rank, hr, Module.finrank_pi, Fintype.card_fin] at h
    have hker : Module.finrank ℝ (LinearMap.ker Ω.mulVecLin) = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  exact meanSketchProjector_of_fullRankColumnSpace_symmetry hn hl ν hinj
    (fun s hs => fullRank_conditioned_preserves_column_space_symmetry μ _
      (rankDeficiency_diagonal_sign_orthogonal hs) (hSign s hs))
    (fun π => fullRank_conditioned_preserves_column_space_symmetry μ _
      (rankDeficiency_permutation_orthogonal π) (hPerm π))


end

end TypicalOrientations
