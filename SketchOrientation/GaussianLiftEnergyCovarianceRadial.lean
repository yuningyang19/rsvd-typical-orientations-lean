import SketchOrientation.GaussianSphereIsotropy
import SketchOrientation.GaussianVectorization
import SketchOrientation.GaussianChiSquareMeans
import Mathlib.Probability.Independence.Integration

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Pulling back a pair along a measure-preserving map preserves independence. -/
theorem indepFun_comp_measurePreserving {A B U V : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace U] [MeasurableSpace V]
    {μ : Measure A} [IsProbabilityMeasure μ] {ν : Measure B} [IsProbabilityMeasure ν]
    {f : A → B} (hf : MeasurePreserving f μ ν)
    {x : B → U} {y : B → V} (hx : Measurable x) (hy : Measurable y)
    (hc : IndepFun x y ν) :
    IndepFun (x ∘ f) (y ∘ f) μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (hx.comp hf.measurable).aemeasurable
    (hy.comp hf.measurable).aemeasurable, ← Measure.map_map hx hf.measurable,
    ← Measure.map_map hy hf.measurable, hf.map_eq]
  have he : (fun z => ((x ∘ f) z, (y ∘ f) z)) = (fun z => (x z, y z)) ∘ f := rfl
  rw [he, ← Measure.map_map (hx.prodMk hy) hf.measurable, hf.map_eq]
  exact hc.map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable

private def energyVectorColumn {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin 1) ℝ := Matrix.of fun i _ => x i

private theorem continuous_energyVectorColumn {d : ℕ} :
    Continuous (@energyVectorColumn d) :=
  continuous_matrix fun i _ => PiLp.continuous_apply 2 _ i

private theorem energyVectorColumn_gram {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ = 1) : (energyVectorColumn x)ᵀ * energyVectorColumn x = 1 := by
  ext i j
  have h : i = j := Subsingleton.elim _ _
  subst j
  rw [Matrix.one_apply_eq]
  change (∑ a, x a * x a) = 1
  have hn := PiLp.norm_sq_eq_of_L2 _ x
  rw [hx, one_pow] at hn
  simpa [pow_two, Real.norm_eq_abs, abs_mul_abs_self] using hn.symm

private theorem stdGaussian_direction_normSq_indep_fin {d : ℕ} (hd : 0 < d) :
    IndepFun (sphereNormalize : EuclideanSpace ℝ (Fin d) → _)
      (fun x => ‖x‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let γ := stdGaussian E
  let F := @energyVectorColumn d ∘ @sphereNormalize E _ _
  let S := fun x : E => ‖x‖ ^ 2
  let j := fun x => (F x, S x)
  let J := γ.map j
  have hF : Measurable F := continuous_energyVectorColumn.measurable.comp measurable_sphereNormalize
  have hS : Measurable S := by fun_prop
  have hj : Measurable j := hF.prodMk hS
  let : IsProbabilityMeasure J := Measure.isProbabilityMeasure_map hj.aemeasurable
  have hFrame : ∀ᵐ z ∂J, z.1ᵀ * z.1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    have hm : MeasurableSet {z : Matrix (Fin d) (Fin 1) ℝ × ℝ | z.1ᵀ * z.1 = 1} :=
      (isClosed_singleton.preimage
        (continuous_fst.matrix_transpose.matrix_mul continuous_fst)).measurableSet
    apply (ae_map_iff hj.aemeasurable hm).2
    have hdim : 0 < Module.finrank ℝ E := by simpa only [E, finrank_euclideanSpace_fin] using hd
    filter_upwards [ae_stdGaussian_ne_zero_of_finrank hdim] with x hx
    exact energyVectorColumn_gram _ (sphereNormalize_norm hx)
  have hInv (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) :
      J.map (fun p => (Q * p.1, p.2)) = J := by
    let e := orthogonalMatrixIsometry Q hQ
    let L := fun p : Matrix (Fin d) (Fin 1) ℝ × ℝ => (Q * p.1, p.2)
    have hL : Measurable L := ((continuous_const.matrix_mul continuous_fst).prodMk
      continuous_snd).measurable
    have he : L ∘ j = j ∘ e := by
      funext x
      apply Prod.ext
      · change Q * energyVectorColumn (sphereNormalize x) =
          energyVectorColumn (sphereNormalize (e x))
        rw [sphereNormalize_map_linearIsometry]
        ext i a
        change (Q *ᵥ (sphereNormalize x).ofLp) i = (e (sphereNormalize x)) i
        rw [orthogonalMatrixIsometry_apply]
        rfl
      · change ‖x‖ ^ 2 = ‖e x‖ ^ 2
        rw [LinearIsometryEquiv.norm_map]
    change (γ.map j).map L = _
    rw [Measure.map_map hL hj, he, ← Measure.map_map hj e.continuous.measurable, stdGaussian_map]
  have hJ := haarFrame_joint_eq_prod_of_invariant (show 1 ≤ d from hd) J hFrame hInv
  have hFirst : J.map Prod.fst = γ.map F := by
    rw [Measure.map_map measurable_fst hj]
    rfl
  have hSecond : J.map Prod.snd = γ.map S := by
    rw [Measure.map_map measurable_snd hj]
    rfl
  let : IsProbabilityMeasure (J.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hFirst' : J.map Prod.fst = gaussianHaarFrameLaw (show 1 ≤ d from hd) := by
    conv_lhs => rw [hJ]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hi : IndepFun F S γ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hS.aemeasurable).2
    change J = _
    rw [← hFirst, hFirst', ← hSecond]
    exact hJ
  let col := fun V : Matrix (Fin d) (Fin 1) ℝ => (WithLp.toLp 2 (V.col 0) : E)
  have hcol : Measurable col :=
    (WithLp.measurable_toLp _ _).comp
      (measurable_pi_iff.mpr fun i => (continuous_id.matrix_elem i (0 : Fin 1)).measurable)
  exact hi.comp hcol measurable_id

/-- Spherical direction and squared radius of an actual standard Gaussian
are independent. This applies to the Euclidean space of all matrix entries. -/
theorem stdGaussian_direction_normSq_indep {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 0 < Module.finrank ℝ E) :
    IndepFun (sphereNormalize : E → E) (fun x => ‖x‖ ^ 2) (stdGaussian E) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  have he : MeasurePreserving e (stdGaussian E) (stdGaussian (EuclideanSpace ℝ _)) :=
    ⟨e.continuous.measurable, stdGaussian_map e⟩
  have h := indepFun_comp_measurePreserving he measurable_sphereNormalize
    (measurable_id.norm.pow_const (2 : ℕ)) (stdGaussian_direction_normSq_indep_fin hE)
  have h' := h.comp e.symm.continuous.measurable (measurable_id : Measurable (id : ℝ → ℝ))
  apply h'.congr
  · apply ae_of_all
    intro x
    change e.symm (sphereNormalize (e x)) = sphereNormalize x
    rw [sphereNormalize, sphereNormalize, LinearIsometryEquiv.norm_map, map_smul,
      LinearIsometryEquiv.symm_apply_apply]
  · exact ae_of_all _ fun x => by change ‖e x‖ ^ 2 = ‖x‖ ^ 2; rw [LinearIsometryEquiv.norm_map]

/-- The column-major entry isometry, presented as a matrix with these entries. -/
def gaussianEnergyMatrix {d k : ℕ} (x : EuclideanSpace ℝ (Fin k × Fin d)) :
    Matrix (Fin d) (Fin k) ℝ := (matrixOfBlockEuclidean x)ᵀ

theorem continuous_gaussianEnergyMatrix {d k : ℕ} : Continuous (@gaussianEnergyMatrix d k) :=
  continuous_matrixOfBlockEuclidean.matrix_transpose

theorem measurePreserving_gaussianEnergyMatrix (d k : ℕ) :
    MeasurePreserving (@gaussianEnergyMatrix d k)
      (stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))) (gaussianMatrixLaw d k) := by
  have h := gaussianRowBlock_eq_map_stdGaussian k d
  have ht : Measurable (Matrix.transpose : Matrix (Fin k) (Fin d) ℝ → _) :=
    continuous_id.matrix_transpose.measurable
  have hs : Measurable (Matrix.transpose : Matrix (Fin d) (Fin k) ℝ → _) :=
    continuous_id.matrix_transpose.measurable
  refine ⟨continuous_gaussianEnergyMatrix.measurable, ?_⟩
  change (stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))).map
    (Matrix.transpose ∘ matrixOfBlockEuclidean) = _
  rw [← Measure.map_map ht continuous_matrixOfBlockEuclidean.measurable, ← h]
  change ((gaussianMatrixLaw d k).map Matrix.transpose).map Matrix.transpose = _
  rw [Measure.map_map ht hs]
  simp only [Function.comp_def, Matrix.transpose_transpose, Measure.map_id']

/-- Squared Frobenius length is the trace of the Gaussian Gram. -/
theorem gaussianEnergyMatrix_gram_trace {d k : ℕ} (x : EuclideanSpace ℝ (Fin k × Fin d)) :
    (gaussianGram (gaussianEnergyMatrix x)).trace = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag_apply, gaussianGram, Matrix.mul_apply, Matrix.transpose_apply]
  simp [gaussianEnergyMatrix, matrixOfBlockEuclidean, pow_two]

/-- The normalized Gram is determined by the direction in the space of
all the entries. -/
theorem gaussianEnergyMatrix_normalizedGram {d k : ℕ} (x : EuclideanSpace ℝ (Fin k × Fin d)) :
    (‖x‖ ^ 2 : ℝ)⁻¹ • gaussianGram (gaussianEnergyMatrix x) =
      gaussianGram (gaussianEnergyMatrix (sphereNormalize x)) := by
  have h (a : ℝ) : gaussianEnergyMatrix (a • x) = a • gaussianEnergyMatrix x := by
    ext i j
    rfl
  rw [sphereNormalize, h]
  simp only [gaussianGram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← pow_two, inv_pow]

/-- Independence of normalized Gram and trace for a matrix of iid Gaussians. -/
theorem gaussianGram_normalized_indep_trace {d k : ℕ} (h : 0 < k * d) :
    IndepFun (fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z).trace⁻¹ • gaussianGram Z)
      (fun Z => (gaussianGram Z).trace) (gaussianMatrixLaw d k) := by
  let e := @gaussianEnergyMatrix d k
  let γ := stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))
  let N := fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z).trace⁻¹ • gaussianGram Z
  let S := fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z).trace
  have he := measurePreserving_gaussianEnergyMatrix d k
  have hG : Continuous (@gaussianGram d k) :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  have hS : Measurable S := hG.matrix_trace.measurable
  have hN : Measurable N := hS.inv.smul hG.measurable
  have hk : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin k × Fin d)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Fintype.card_prod] using h
  have hrad := (stdGaussian_direction_normSq_indep hk).comp
    (hG.measurable.comp continuous_gaussianEnergyMatrix.measurable)
    (measurable_id : Measurable (id : ℝ → ℝ))
  have hInd : IndepFun (N ∘ e) (S ∘ e) γ := by
    apply hrad.congr
    · exact ae_of_all _ fun x => by
        change gaussianGram (e (sphereNormalize x)) = (gaussianGram (e x)).trace⁻¹ • _
        rw [gaussianEnergyMatrix_gram_trace, gaussianEnergyMatrix_normalizedGram]
    · exact ae_of_all _ fun x => (gaussianEnergyMatrix_gram_trace x).symm
  rw [indepFun_iff_map_prod_eq_prod_map_map (hN.comp he.measurable).aemeasurable
    (hS.comp he.measurable).aemeasurable] at hInd
  rw [indepFun_iff_map_prod_eq_prod_map_map hN.aemeasurable hS.aemeasurable]
  have hNS : (fun x => ((N ∘ e) x, (S ∘ e) x)) = (fun x => (N x, S x)) ∘ e := rfl
  rw [hNS, ← Measure.map_map (hN.prodMk hS) he.measurable, ← Measure.map_map hN he.measurable,
    ← Measure.map_map hS he.measurable, he.map_eq] at hInd
  exact hInd

/-- The trace of a Gaussian Gram has one chi-square degree of freedom per entry. -/
theorem gaussianGram_trace_law {d k : ℕ} (h : 0 < k * d) :
    (gaussianMatrixLaw d k).map (fun Z => (gaussianGram Z).trace) = chiSquareLaw (k * d) := by
  let e := @gaussianEnergyMatrix d k
  have he := measurePreserving_gaussianEnergyMatrix d k
  have hG : Continuous (@gaussianGram d k) := continuous_id.matrix_transpose.matrix_mul continuous_id
  rw [← he.map_eq, Measure.map_map hG.matrix_trace.measurable he.measurable]
  have hEq : (fun Z : Matrix (Fin d) (Fin k) ℝ => (gaussianGram Z).trace) ∘ e =
      (fun x => ‖x‖ ^ 2) := funext gaussianEnergyMatrix_gram_trace
  rw [hEq, stdGaussian_norm_sq_map_finrank]
  · simp only [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin]
  · simpa only [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin] using h

end

end SketchOrientation
