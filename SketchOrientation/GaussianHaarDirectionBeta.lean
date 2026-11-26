import SketchOrientation.GaussianHaarQuadratic
import SketchOrientation.GaussianSphereIsotropy

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix

variable {n k : ℕ}

private def vectorColumn (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin 1) ℝ :=
  Matrix.of (fun i _ => x i)

private theorem continuous_vectorColumn : Continuous (@vectorColumn n) :=
  continuous_matrix fun i _ => PiLp.continuous_apply 2 _ i

private theorem vectorColumn_orthonormal (x : EuclideanSpace ℝ (Fin n)) (h : ‖x‖ = 1) :
    (vectorColumn x)ᵀ * vectorColumn x = 1 := by
  ext i j
  have e : i = j := Subsingleton.elim _ _
  subst j
  rw [Matrix.one_apply_eq]
  change (∑ a, x a * x a) = 1
  have hn := PiLp.norm_sq_eq_of_L2 _ x
  rw [h, one_pow] at hn
  simpa [pow_two, Real.norm_eq_abs, abs_mul_abs_self] using hn.symm

private theorem mul_vectorColumn (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Q * vectorColumn x = vectorColumn (Q.toEuclideanLin x) := by
  ext i j
  rfl

private theorem sphereNormalize_map_column_haar (hn : 0 < n) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (vectorColumn ∘ sphereNormalize) =
      gaussianHaarFrameLaw (show 1 ≤ n from hn) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let F := @vectorColumn n ∘ @sphereNormalize (EuclideanSpace ℝ (Fin n)) _ _
  let η := μ.map F
  have hF : Measurable F := continuous_vectorColumn.measurable.comp measurable_sphereNormalize
  have : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hF.aemeasurable
  apply gaussianHaarFrameLaw_unique (show 1 ≤ n from hn)
  · have hm : MeasurableSet {V : Matrix (Fin n) (Fin 1) ℝ | Vᵀ * V = 1} :=
      (isClosed_singleton.preimage (continuous_id.matrix_transpose.matrix_mul continuous_id)).measurableSet
    apply (ae_map_iff hF.aemeasurable hm).2
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using hn
    filter_upwards [ae_stdGaussian_ne_zero_of_finrank hdim] with x hx
    exact vectorColumn_orthonormal _ (sphereNormalize_norm hx)
  · intro Q hQ
    let e := orthogonalMatrixIsometry Q hQ
    let L := fun V : Matrix (Fin n) (Fin 1) ℝ => Q * V
    have hL : Measurable L := (continuous_const.matrix_mul continuous_id).measurable
    have hE : μ.map e = μ := stdGaussian_map e
    have he : L ∘ F = F ∘ e := by
      funext x
      change Q * vectorColumn (sphereNormalize x) = vectorColumn (sphereNormalize (e x))
      rw [mul_vectorColumn, ← orthogonalMatrixIsometry_apply Q hQ, sphereNormalize_map_linearIsometry]
    change (μ.map F).map L = _
    rw [Measure.map_map hL hF, he, ← Measure.map_map hF e.continuous.measurable, hE]

set_option maxHeartbeats 950000 in
/-- The transpose of a Haar orthogonal matrix sends any fixed unit direction
to the normalized Gaussian spherical law. -/
theorem gaussianRightOrthogonalLaw_map_transpose_direction (u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) :
    (gaussianRightOrthogonalLaw n).map (fun Q => Qᵀ.toEuclideanLin u) =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map sphereNormalize := by
  let μ := gaussianRightOrthogonalLaw n
  let H := fun Q : Matrix (Fin n) (Fin n) ℝ => Qᵀ.toEuclideanLin u
  let F := vectorColumn ∘ H
  have hn : 0 < n := by
    by_contra! h
    have hn₀ : n = 0 := by omega
    subst n
    have hz : u = 0 := Subsingleton.elim _ _
    simp [hz] at hu
  have hm : Continuous H :=
    (PiLp.continuous_toLp 2 _).comp
      (continuous_id.matrix_transpose.matrix_mulVec continuous_const)
  have hF : Measurable F := continuous_vectorColumn.measurable.comp hm.measurable
  have hLaw : μ.map F = gaussianHaarFrameLaw (show 1 ≤ n from hn) := by
    have : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    apply gaussianHaarFrameLaw_unique (show 1 ≤ n from hn)
    · have hset : MeasurableSet {V : Matrix (Fin n) (Fin 1) ℝ | Vᵀ * V = 1} :=
        (isClosed_singleton.preimage (continuous_id.matrix_transpose.matrix_mul continuous_id)).measurableSet
      apply (ae_map_iff hF.aemeasurable hset).2
      filter_upwards [ae_gaussianRightOrthogonal n] with Q hQ
      have hQ' : Qᵀᵀ * Qᵀ = 1 := by
        rw [transpose_transpose]
        exact mul_eq_one_comm.mp hQ
      apply vectorColumn_orthonormal
      change ‖Qᵀ.toEuclideanLin u‖ = 1
      rw [← orthogonalMatrixIsometry_apply Qᵀ hQ', LinearIsometryEquiv.norm_map, hu]
    · intro Q hQ
      let R := fun W : Matrix (Fin n) (Fin n) ℝ => W * Qᵀ
      let L := fun V : Matrix (Fin n) (Fin 1) ℝ => Q * V
      have hQ' : Qᵀᵀ * Qᵀ = 1 := by
        rw [transpose_transpose]
        exact mul_eq_one_comm.mp hQ
      have hR : Measurable R := (continuous_id.matrix_mul continuous_const).measurable
      have hL : Measurable L := (continuous_const.matrix_mul continuous_id).measurable
      have hRf : μ.map R = μ := gaussianRightOrthogonalLaw_map_right Qᵀ hQ'
      have he : L ∘ F = F ∘ R := by
        funext W
        change Q * vectorColumn (Wᵀ.toEuclideanLin u) = vectorColumn ((W * Qᵀ)ᵀ.toEuclideanLin u)
        rw [mul_vectorColumn, transpose_mul, transpose_transpose, euclidean_mul]
        rfl
      change (μ.map F).map L = _
      rw [Measure.map_map hL hF, he, ← Measure.map_map hF hR, hRf]
  let v := fun V : Matrix (Fin n) (Fin 1) ℝ => WithLp.toLp 2 (V.col 0)
  have hv : Measurable v := (WithLp.measurable_toLp _ _).comp
    (measurable_pi_iff.mpr fun i => (continuous_id.matrix_elem i (0 : Fin 1)).measurable)
  have hvx : v ∘ vectorColumn = id := by funext x; rfl
  have h' := congrArg (Measure.map v) (hLaw.trans (sphereNormalize_map_column_haar hn).symm)
  rw [Measure.map_map hv hF,
    Measure.map_map hv (continuous_vectorColumn.measurable.comp measurable_sphereNormalize),
    ← Function.comp_assoc, ← Function.comp_assoc, hvx, Function.id_comp, Function.id_comp] at h'
  exact h'

set_option maxHeartbeats 950000 in
/-- The Haar frame's energy in a fixed unit direction is beta with
parameters `k/2` and `(n-k)/2`. -/
theorem haarFrameQuadratic_beta (hk : 0 < k) (hkn : k < n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    (gaussianHaarFrameLaw hkn.le).map (haarFrameQuadratic u) =
      betaMeasure ((k : ℝ) / 2) (((n - k : ℕ) : ℝ) / 2) := by
  obtain ⟨U, hU⟩ := exists_stiefel_frame hkn.le
  let μ := gaussianRightOrthogonalLaw n
  let H := fun Q : Matrix (Fin n) (Fin n) ℝ => Qᵀ.toEuclideanLin u
  let V := fun Q : Matrix (Fin n) (Fin n) ℝ => Q * U
  let F := fun x : EuclideanSpace ℝ (Fin n) => haarFrameQuadratic x U
  have hM : Measurable F :=
    Uᵀ.toEuclideanLin.toContinuousLinearMap.continuous.measurable.norm.pow_const _
  have hV : Measurable V := (continuous_id.matrix_mul continuous_const).measurable
  have hH : Measurable H := by
    have h : Continuous H := (PiLp.continuous_toLp 2 _).comp
      (continuous_id.matrix_transpose.matrix_mulVec continuous_const)
    exact h.measurable
  have he : haarFrameQuadratic u ∘ V = F ∘ H := by
    funext Q
    change ‖(Q * U)ᵀ.toEuclideanLin u‖ ^ 2 = ‖Uᵀ.toEuclideanLin (Qᵀ.toEuclideanLin u)‖ ^ 2
    rw [transpose_mul, euclidean_mul]
    rfl
  rw [← gaussianHaarFrameLaw_eq_orbit hkn.le U hU,
    Measure.map_map (measurable_haarFrameQuadratic u) hV, he, ← Measure.map_map hM hH,
    gaussianRightOrthogonalLaw_map_transpose_direction u hu,
    Measure.map_map hM measurable_sphereNormalize]
  let S := U.toEuclideanLin.range
  have hS : Module.finrank ℝ S = k := by
    unfold S
    rw [LinearMap.finrank_range_of_inj (orthonormalFrame_toEuclideanLin_injective U hU),
      finrank_euclideanSpace, Fintype.card_fin]
  have hC : Module.finrank ℝ Sᗮ = n - k := finrank_orthonormalFrame_complement U hU
  have he' : F ∘ sphereNormalize = fun x => ‖S.starProjection (sphereNormalize x)‖ ^ 2 := by
    funext x
    exact haarFrameQuadratic_eq_projection U hU (sphereNormalize x)
  rw [he']
  have hz := stdGaussian_sphere_projected_sq_beta S (hS.symm ▸ hk)
    (hC.symm ▸ (show 0 < n - k by omega))
  rwa [hS, hC] at hz

end SketchOrientation
