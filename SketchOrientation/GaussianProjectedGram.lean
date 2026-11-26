import SketchOrientation.GaussianOrthogonal
import SketchOrientation.GaussianInput
import SketchOrientation.GaussianGramMoments
import SketchOrientation.GaussianGramTracePowers
import SketchOrientation.ProjectorFrame
import SketchOrientation.GaussianPolarAlgebra

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix Set

variable {n k ℓ : ℕ}

private theorem gaussian_pi_restrict (e : Fin ℓ ↪ Fin n) :
    MeasurePreserving (fun (x : Fin n → ℝ) (i : Fin ℓ) => x (e i))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) := by
  classical
  let p := fun i : Fin n => i ∈ Set.range e
  let : Fintype {i // p i} := Subtype.fintype p
  let : Fintype {i // ¬p i} := Subtype.fintype (fun i => ¬p i)
  let e' : Fin ℓ ≃ {i // p i} := Equiv.ofInjective e e.injective
  have h := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => gaussianReal 0 1) p
  have hp := measurePreserving_fst
    (μ := Measure.pi fun _ : {i // p i} => gaussianReal 0 1)
    (ν := Measure.pi fun _ : {i // ¬p i} => gaussianReal 0 1)
  have he := (measurePreserving_piCongrLeft (fun _ : {i // p i} => gaussianReal 0 1) e').symm
  exact he.comp (hp.comp h)

private theorem measurable_rawColumns (n k : ℕ) :
    Measurable (fun X : Fin k → Fin n → ℝ =>
      Matrix.of (fun (i : Fin n) (j : Fin k) => X j i)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact (measurable_pi_apply i).comp (measurable_pi_apply j)

/-- Restriction to any fixed subset of distinct rows preserves the iid scalar
Gaussian law with the corresponding dimension. -/
theorem gaussianMatrixLaw_map_submatrix_rows (e : Fin ℓ ↪ Fin n) :
    (gaussianMatrixLaw n k).map (fun G => G.submatrix e id) = gaussianMatrixLaw ℓ k := by
  let f (m : ℕ) := fun X : Fin k → Fin m → ℝ =>
    Matrix.of (fun (i : Fin m) (j : Fin k) => X j i)
  let r := fun (X : Fin k → Fin n → ℝ) (j : Fin k) (i : Fin ℓ) => X j (e i)
  have hR : MeasurePreserving r
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin ℓ => gaussianReal 0 1) :=
    measurePreserving_pi _ _ fun _ => gaussian_pi_restrict e
  have hs : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => G.submatrix e id) := by
    exact (continuous_matrix fun i j => continuous_id.matrix_elem (e i) j).measurable
  rw [gaussianMatrixLaw_eq_coordinate_product n k, gaussianMatrixLaw_eq_coordinate_product ℓ k]
  change ((Measure.pi _).map (f n)).map (fun G => G.submatrix e id) = (Measure.pi _).map (f ℓ)
  have he : (fun G : Matrix (Fin n) (Fin k) ℝ => G.submatrix e id) ∘ f n = f ℓ ∘ r := rfl
  rw [Measure.map_map hs (measurable_rawColumns n k), he,
    ← Measure.map_map (measurable_rawColumns ℓ k) hR.measurable, hR.map_eq]

/-- Projection on a fixed orthonormal frame produces an iid Gaussian block. -/
theorem gaussianMatrixLaw_map_frame_transpose (hℓn : ℓ ≤ n)
    (U : Matrix (Fin n) (Fin ℓ) ℝ) (hU : Uᵀ * U = 1) :
    (gaussianMatrixLaw n k).map (fun G => Uᵀ * G) = gaussianMatrixLaw ℓ k := by
  obtain ⟨Q, hQ, hQU⟩ := exists_orthogonal_extension hℓn U hU
  let e := Fin.castLEEmb hℓn
  have hQt : Qᵀᵀ * Qᵀ = 1 := by
    rw [transpose_transpose]
    exact mul_eq_one_comm.mp hQ
  have hM : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => Qᵀ * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hS : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => G.submatrix e id) :=
    (continuous_matrix fun i j => continuous_id.matrix_elem (e i) j).measurable
  have he : (fun G : Matrix (Fin n) (Fin k) ℝ => Uᵀ * G) =
      (fun G => G.submatrix e id) ∘ fun G => Qᵀ * G := by
    funext G
    ext i j
    rw [← hQU]
    simp [e, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [he, ← Measure.map_map hS hM, gaussianMatrixLaw_map_left_orthogonal _ hQt,
    gaussianMatrixLaw_map_submatrix_rows e]

/-- A Gaussian matrix compressed by a fixed rank-ℓ orthogonal projector
has exactly the ℓ-row Gaussian Gram law. -/
theorem gaussianMatrixLaw_map_projectedGram (hℓn : ℓ ≤ n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P) (hr : P.rank = ℓ) :
    (gaussianMatrixLaw n k).map (fun G => Gᵀ * P * G) =
      (gaussianMatrixLaw ℓ k).map gaussianGram := by
  obtain ⟨U, hU, hUP⟩ := exists_frame_of_projector P hs hi hr
  have hM : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => Uᵀ * G) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hGr : Measurable (@gaussianGram ℓ k) := (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  have he : (fun G : Matrix (Fin n) (Fin k) ℝ => Gᵀ * P * G) =
      gaussianGram ∘ fun G => Uᵀ * G := by
    funext G
    change Gᵀ * P * G = (Uᵀ * G)ᵀ * (Uᵀ * G)
    rw [transpose_mul, transpose_transpose, ← hUP]
    simp only [Matrix.mul_assoc]
  rw [he, ← Measure.map_map hGr hM, gaussianMatrixLaw_map_frame_transpose hℓn U hU]

/-- The inverse trace for a fixed rank-ℓ orthogonal observation is integrable
with the exact first moment of its ℓ-row Gram block. -/
theorem gaussianMatrix_projectedGram_inv_trace_mean (hℓn : ℓ ≤ n) (hkℓ : k + 1 < ℓ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P) (hr : P.rank = ℓ) :
    Integrable (fun G => (Gᵀ * P * G)⁻¹.trace) (gaussianMatrixLaw n k) ∧
      (∫ G, (Gᵀ * P * G)⁻¹.trace ∂gaussianMatrixLaw n k) =
        (k : ℝ) / ((ℓ : ℝ) - k - 1) := by
  let F := fun A : Matrix (Fin k) (Fin k) ℝ => A⁻¹.trace
  let G := fun X : Matrix (Fin n) (Fin k) ℝ => Xᵀ * P * X
  have hT : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.trace) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i
  have hF : Measurable F := hT.measurable.comp measurable_matrix_nonsing_inv
  have hG : Measurable G :=
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable
  have hGr : Measurable (@gaussianGram ℓ k) := (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  change Integrable (F ∘ G) (gaussianMatrixLaw n k) ∧
      (∫ X, F (G X) ∂gaussianMatrixLaw n k) = _
  rw [← integrable_map_measure hF.aestronglyMeasurable hG.aemeasurable,
    ← integral_map hG.aemeasurable hF.aestronglyMeasurable,
    gaussianMatrixLaw_map_projectedGram hℓn P hs hi hr,
    integrable_map_measure hF.aestronglyMeasurable hGr.aemeasurable,
    integral_map hGr.aemeasurable hF.aestronglyMeasurable]
  exact gaussianGram_inv_trace_mean hkℓ

/-- The normalized inverse trace power of a fixed sketch has a common
dimension-dependent Gaussian moment bound. -/
theorem gaussianMatrix_projectedGram_inv_trace_moment (hℓn : ℓ ≤ n) (hk : 0 < k)
    (hkℓ : k ≤ ℓ) {r : ℝ} (hr : 1 ≤ r) (hr' : r < ((ℓ - k + 1 : ℕ) : ℝ) / 2)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P) (hP : P.rank = ℓ) :
    Integrable (fun G => ((Gᵀ * P * G)⁻¹.trace / (k : ℝ)) ^ r) (gaussianMatrixLaw n k) ∧
      (∫ G, ((Gᵀ * P * G)⁻¹.trace / (k : ℝ)) ^ r ∂gaussianMatrixLaw n k) ≤
        chiSquareNegativeMoment (ℓ - k + 1) r := by
  let F := fun A : Matrix (Fin k) (Fin k) ℝ => (A⁻¹.trace / k) ^ r
  let G := fun X : Matrix (Fin n) (Fin k) ℝ => Xᵀ * P * X
  have hT : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.trace) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i
  have hF : Measurable F := ((hT.measurable.comp measurable_matrix_nonsing_inv).div_const _).pow_const _
  have hG : Measurable G :=
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable
  have hGr : Measurable (@gaussianGram ℓ k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  change Integrable (F ∘ G) (gaussianMatrixLaw n k) ∧
      (∫ X, F (G X) ∂gaussianMatrixLaw n k) ≤ _
  rw [← integrable_map_measure hF.aestronglyMeasurable hG.aemeasurable,
    ← integral_map hG.aemeasurable hF.aestronglyMeasurable,
    gaussianMatrixLaw_map_projectedGram hℓn P hs hi hP,
    integrable_map_measure hF.aestronglyMeasurable hGr.aemeasurable,
    integral_map hGr.aemeasurable hF.aestronglyMeasurable]
  simpa [F, Function.comp_def, hr] using gaussianGram_inv_trace_moment hk hkℓ (zero_lt_one.trans_le hr) hr'

/-- A fixed sketch gives an invertible Gaussian Gram matrix almost surely
when the observed dimension is at least the column count. -/
theorem ae_gaussianMatrix_projectedGram_invertible (hℓn : ℓ ≤ n) (hkℓ : k ≤ ℓ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : Pᵀ = P) (hi : P * P = P) (hP : P.rank = ℓ) :
    ∀ᵐ G ∂gaussianMatrixLaw n k, (Gᵀ * P * G).det ≠ 0 := by
  let G := fun X : Matrix (Fin n) (Fin k) ℝ => Xᵀ * P * X
  have hG : Measurable G :=
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id).measurable
  have hGr : Measurable (@gaussianGram ℓ k) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  have hdet : MeasurableSet {A : Matrix (Fin k) (Fin k) ℝ | A.det ≠ 0} :=
    (isClosed_singleton.preimage continuous_id.matrix_det).isOpen_compl.measurableSet
  change ∀ᵐ X ∂gaussianMatrixLaw n k, (G X).det ≠ 0
  rw [← ae_map_iff hG.aemeasurable hdet, gaussianMatrixLaw_map_projectedGram hℓn P hs hi hP,
      ae_map_iff hGr.aemeasurable hdet]
  filter_upwards [ae_gaussianMatrix_injective hkℓ] with Z hZ
  exact (gaussianGram_det_ne_zero_iff Z).2 hZ

end SketchOrientation
