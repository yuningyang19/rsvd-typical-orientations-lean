import SketchOrientation.GaussianProjectedGram
import SketchOrientation.GaussianPolarLaw

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace

variable {n k : ℕ}

/-- Insert one Euclidean column into an existing real matrix. -/
def insertFrameColumn (j : Fin (k + 1)) (W : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin (k + 1)) ℝ :=
  Matrix.of (fun i => j.insertNth (x i) (W i))

@[simp] theorem insertFrameColumn_same (j : Fin (k + 1)) (W : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    insertFrameColumn j W x i j = x i := by
  change j.insertNth (α := fun _ => ℝ) (x i) (W i) j = x i
  rw [Fin.insertNth_apply_same]

@[simp] theorem insertFrameColumn_succAbove (j : Fin (k + 1)) (W : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (a : Fin k) :
    insertFrameColumn j W x i (j.succAbove a) = W i a := by
  change j.insertNth (α := fun _ => ℝ) (x i) (W i) (j.succAbove a) = W i a
  rw [Fin.insertNth_apply_succAbove]

theorem continuous_insertFrameColumn (j : Fin (k + 1)) :
    Continuous (fun p : Matrix (Fin n) (Fin k) ℝ × EuclideanSpace ℝ (Fin n) =>
      insertFrameColumn j p.1 p.2) := by
  apply continuous_matrix
  intro i a
  by_cases ha : a = j
  · subst a
    simp only [insertFrameColumn_same]
    exact (PiLp.continuous_apply 2 _ i).comp continuous_snd
  · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
    simp only [insertFrameColumn_succAbove]
    exact continuous_fst.matrix_elem i b

theorem insertFrameColumn_orthonormal (j : Fin (k + 1)) (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) (x : EuclideanSpace ℝ (Fin n)) (hn : ‖x‖ = 1)
    (hWₓ : Wᵀ *ᵥ x.ofLp = 0) :
    (insertFrameColumn j W x)ᵀ * insertFrameColumn j W x = 1 := by
  ext a b
  have hE (a : Fin (k + 1)) : a = j ∨ ∃ i, j.succAbove i = a := by
    by_cases h : a = j
    · exact Or.inl h
    · exact Or.inr (Fin.exists_succAbove_eq h)
  have hnorm : (∑ i, x i * x i) = 1 := by
    have h := PiLp.norm_sq_eq_of_L2 _ x
    rw [hn, one_pow] at h
    simpa [pow_two, Real.norm_eq_abs, abs_mul_abs_self] using h.symm
  have horth (i : Fin k) : (∑ a, W a i * x a) = 0 := by
    exact congrFun hWₓ i
  rcases hE a with rfl | ⟨a, rfl⟩ <;> rcases hE b with rfl | ⟨b, rfl⟩
  · simpa only [Matrix.mul_apply, Matrix.transpose_apply, insertFrameColumn_same, Matrix.one_apply_eq]
      using hnorm
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, insertFrameColumn_same,
      insertFrameColumn_succAbove, Matrix.one_apply_ne (Fin.succAbove_ne a b).symm]
    simpa only [mul_comm] using horth b
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, insertFrameColumn_same,
      insertFrameColumn_succAbove, Matrix.one_apply_ne (Fin.succAbove_ne b a)]
    exact horth a
  · have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M a b) hW
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, insertFrameColumn_succAbove,
      Matrix.one_apply, Fin.succAbove_right_injective.eq_iff] using h

theorem mul_insertFrameColumn (Q : Matrix (Fin n) (Fin n) ℝ) (j : Fin (k + 1))
    (W : Matrix (Fin n) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Q * insertFrameColumn j W x = insertFrameColumn j (Q * W) (Q.toEuclideanLin x) := by
  ext i a
  by_cases ha : a = j
  · subst a
    simp only [Matrix.mul_apply, insertFrameColumn_same]
    rfl
  · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq ha
    rw [Matrix.mul_apply, insertFrameColumn_succAbove, Matrix.mul_apply]
    simp only [insertFrameColumn_succAbove]

/-- Residual used to append one direction to a frame. -/
noncomputable def haarResidualColumn (W : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 - W * Wᵀ).toEuclideanLin x

theorem continuous_haarResidualColumn :
    Continuous (Function.uncurry (@haarResidualColumn n k)) := by
  have hM : Continuous (fun p : Matrix (Fin n) (Fin k) ℝ × EuclideanSpace ℝ (Fin n) =>
      1 - p.1 * p.1ᵀ) := continuous_const.sub (continuous_fst.matrix_mul continuous_fst.matrix_transpose)
  exact (PiLp.continuous_toLp 2 _).comp
    (hM.matrix_mulVec ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

theorem continuous_haarResidualColumn_fixed_vector (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun W : Matrix (Fin n) (Fin k) ℝ => haarResidualColumn W x) := by
  have h : Continuous (fun W : Matrix (Fin n) (Fin k) ℝ => (W, x)) :=
    continuous_id.prodMk continuous_const
  have h' := (@continuous_haarResidualColumn n k).comp h
  exact h'

/-- A Gaussian vector projected onto the orthogonal complement and normalized. -/
noncomputable def haarCompletionColumn (W : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖haarResidualColumn W x‖⁻¹ • haarResidualColumn W x

theorem measurable_haarCompletionColumn :
    Measurable (Function.uncurry (@haarCompletionColumn n k)) := by
  have h := (@continuous_haarResidualColumn n k).measurable
  exact h.norm.inv.smul h

theorem haarResidualColumn_eq_projection (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) (x : EuclideanSpace ℝ (Fin n)) :
    haarResidualColumn W x = (W.toEuclideanLin.range)ᗮ.starProjection x := by
  unfold haarResidualColumn
  rw [← rangeProjector_of_frame W hW, map_sub, euclidean_projector, LinearMap.sub_apply]
  change (toLpLin 2 2 (1 : Matrix (Fin n) (Fin n) ℝ)) x -
    W.toEuclideanLin.range.starProjection x = _
  rw [Matrix.toLpLin_one]
  change x - W.toEuclideanLin.range.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val]

theorem ae_haarResidualColumn_ne_zero (hkn : k < n) (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) :
    ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin n)), haarResidualColumn W x ≠ 0 := by
  filter_upwards [ae_not_mem_proper_submodule _ (range_ne_top_of_width_lt W hkn)] with x hx
  rw [haarResidualColumn_eq_projection W hW]
  intro h
  rw [Submodule.starProjection_orthogonal_val, sub_eq_zero] at h
  apply hx
  rw [h]
  exact (W.toEuclideanLin.range.orthogonalProjectionOnto x).property

theorem haarCompletionColumn_norm (W : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : haarResidualColumn W x ≠ 0) :
    ‖haarCompletionColumn W x‖ = 1 := by
  unfold haarCompletionColumn
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem haarCompletionColumn_orthogonal (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) (x : EuclideanSpace ℝ (Fin n)) :
    Wᵀ *ᵥ (haarCompletionColumn W x).ofLp = 0 := by
  unfold haarCompletionColumn haarResidualColumn
  change Wᵀ *ᵥ (‖(1 - W * Wᵀ).toEuclideanLin x‖⁻¹ •
    ((1 - W * Wᵀ) *ᵥ WithLp.ofLp x)) = 0
  rw [Matrix.mulVec_smul, mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, hW, Matrix.one_mul, sub_self, Matrix.zero_mulVec, smul_zero]

theorem haarResidualColumn_mul_orthogonal (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (W : Matrix (Fin n) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    haarResidualColumn (Q * W) (Q.toEuclideanLin x) =
      Q.toEuclideanLin (haarResidualColumn W x) := by
  have e : (1 - (Q * W) * (Q * W)ᵀ) * Q = Q * (1 - W * Wᵀ) := by
    simp only [transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    have he : (Q * W) * (Wᵀ * Qᵀ) * Q = Q * (W * Wᵀ) := by
      simp only [Matrix.mul_assoc]
      simp [hQ]
    rw [he]
  unfold haarResidualColumn
  rw [← LinearMap.comp_apply, ← euclidean_mul, e, euclidean_mul]
  rfl

theorem haarCompletionColumn_mul_orthogonal (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (W : Matrix (Fin n) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    haarCompletionColumn (Q * W) (Q.toEuclideanLin x) =
      Q.toEuclideanLin (haarCompletionColumn W x) := by
  have he := haarResidualColumn_mul_orthogonal Q hQ W x
  have hn : ‖Q.toEuclideanLin (haarResidualColumn W x)‖ = ‖haarResidualColumn W x‖ := by
    rw [← orthogonalMatrixIsometry_apply Q hQ, LinearIsometryEquiv.norm_map]
  simp only [haarCompletionColumn, he, hn, map_smul]

/-- Complete independently drawn Haar columns by one spherical direction
in their orthogonal complement. -/
noncomputable def appendHaarColumn (j : Fin (k + 1))
    (p : Matrix (Fin n) (Fin k) ℝ × EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin (k + 1)) ℝ :=
  insertFrameColumn j p.1 (haarCompletionColumn p.1 p.2)

theorem measurable_appendHaarColumn (j : Fin (k + 1)) :
    Measurable (@appendHaarColumn n k j) := by
  have hf := measurable_fst.prodMk (@measurable_haarCompletionColumn n k)
  exact (continuous_insertFrameColumn j).measurable.comp hf

set_option maxHeartbeats 900000 in
/-- The conditional column construction used in Equation (3.9): discarding
one Haar column and completing by a normalized perpendicular Gaussian
recovers the original Haar frame law. -/
theorem gaussianHaarFrameLaw_append_column (hkn : k + 1 ≤ n) (j : Fin (k + 1)) :
    ((gaussianHaarFrameLaw (show k ≤ n by omega)).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (appendHaarColumn j) =
      gaussianHaarFrameLaw hkn := by
  let hkn' : k ≤ n := by omega
  let η := gaussianHaarFrameLaw hkn'
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := η.prod γ
  let F := @appendHaarColumn n k j
  let ν := μ.map F
  have hF := measurable_appendHaarColumn (n := n) j
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hF.aemeasurable
  refine gaussianHaarFrameLaw_unique hkn ν ?_ ?_
  · have hset : MeasurableSet {V : Matrix (Fin n) (Fin (k + 1)) ℝ |
        Vᵀ * V = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)} :=
      (isClosed_singleton.preimage (continuous_id.matrix_transpose.matrix_mul continuous_id)).measurableSet
    apply (ae_map_iff hF.aemeasurable hset).2
    have hset' : MeasurableSet {p : Matrix (Fin n) (Fin k) ℝ × EuclideanSpace ℝ (Fin n) |
        (F p)ᵀ * F p = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)} := hset.preimage hF
    apply (Measure.ae_prod_iff_ae_ae hset').2
    filter_upwards [ae_gaussianHaarFrame_orthonormal hkn'] with W hW
    filter_upwards [ae_haarResidualColumn_ne_zero (by omega) W hW] with x hx
    exact insertFrameColumn_orthonormal j W hW _ (haarCompletionColumn_norm W x hx)
      (haarCompletionColumn_orthogonal W hW x)
  · intro Q hQ
    let L := fun V : Matrix (Fin n) (Fin (k + 1)) ℝ => Q * V
    let R := fun W : Matrix (Fin n) (Fin k) ℝ => Q * W
    let e := orthogonalMatrixIsometry Q hQ
    have hL : Measurable L := (continuous_const.matrix_mul continuous_id).measurable
    have hR : Measurable R := (continuous_const.matrix_mul continuous_id).measurable
    have hE : Measurable e := e.continuous.measurable
    have he : L ∘ F = F ∘ Prod.map R e := by
      funext p
      change Q * insertFrameColumn j p.1 (haarCompletionColumn p.1 p.2) =
        insertFrameColumn j (Q * p.1) (haarCompletionColumn (Q * p.1) (e p.2))
      rw [mul_insertFrameColumn, orthogonalMatrixIsometry_apply,
        haarCompletionColumn_mul_orthogonal Q hQ]
    have hAct : μ.map (Prod.map R e) = μ := by
      rw [← Measure.map_prod_map _ _ hR hE]
      change (η.map R).prod (γ.map e) = η.prod γ
      rw [gaussianHaarFrameLaw_map_left hkn' Q hQ, stdGaussian_map e]
    change (μ.map F).map L = μ.map F
    rw [Measure.map_map hL hF, he, ← Measure.map_map hF (hR.prodMap hE), hAct]

end SketchOrientation
