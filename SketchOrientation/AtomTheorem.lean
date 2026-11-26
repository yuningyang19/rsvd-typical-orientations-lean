import SketchOrientation.Atom
import SketchOrientation.TwoLevelResidual
import SketchOrientation.ProjectorFrame
import SketchOrientation.SpectralGram
import SketchOrientation.GaussianMatrixSpace

namespace SketchOrientation

open Matrix MeasureTheory

/-- Rank-ℓ real orthogonal projectors, with the Borel structure inherited
from the space of all real matrices. -/
abbrev OrthogonalProjector (n l : ℕ) :=
  {P : Matrix (Fin n) (Fin n) ℝ // Pᵀ = P ∧ P * P = P ∧ P.rank = l}

theorem targetCompression_posSemidef {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n l) : (Vᵀ * P.val * V).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (P.val * V)
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_mul, P.property.1,
    Matrix.mul_assoc Vᵀ, ← Matrix.mul_assoc P.val P.val, P.property.2.1,
    ← Matrix.mul_assoc Vᵀ] at h

/-- The finite-gap loss realized by the actual RSVD residual. The columns
of P span the same sampled space as its orthonormal frame. -/
noncomputable def projectorTwoLevelLoss {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n l) (Γ : ℝ) : ℝ :=
  centeredRankLoss k (twoLevelInput V Γ) P.val

/-- Equation (2.3) for the loss defined on the law of projectors. -/
theorem projectorTwoLevelLoss_eq_angles {n k l : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) (P : OrthogonalProjector n l) {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (hk : 0 < k) (hkn : k < n) :
    projectorTwoLevelLoss V P Γ =
      ((∑ j, Γ / (1 + (Γ - 1) * orderedEigenvaluesFin
        (targetCompression_posSemidef V P).isHermitian j)) - l) / ((k : ℝ) * (n - k)) := by
  obtain ⟨U, hU, hP⟩ := exists_frame_of_projector P.val P.property.1
    P.property.2.1 P.property.2.2
  let A := twoLevelInput V Γ
  have hGram : Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ) :=
    twoLevelInput_gram V hV (zero_le_one.trans hΓ)
  have hRes : squaredResidual A P.val = squaredResidual A U :=
    hP ▸ squaredResidual_frame_projector A U hU
  have hLoss : centeredRankLoss k A P.val = centeredRankLoss k A U := by
    unfold centeredRankLoss tailRelativeError
    rw [hRes]
  rw [projectorTwoLevelLoss, hLoss]
  have h := twoLevel_centeredRankLoss A U V hU hV hΓ hGram
    (by simpa only [Fintype.card_fin] using hk)
    (by simpa only [Fintype.card_fin] using hkn)
  simp only [Fintype.card_fin, hP] at h
  rw [h, trace_inverse_one_add_smul_of_posSemidef (targetCompression_posSemidef V P)
    (Γ - 1) (sub_nonneg.mpr hΓ), Finset.mul_sum]
  simp only [div_eq_mul_inv]

private theorem orderedEigenvaluesFin_of_zero {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.IsHermitian) (hz : A = 0) (j : Fin k) :
    orderedEigenvaluesFin hA j = 0 := by
  subst A
  exact orderedEigenvaluesFin_zero hA j

/-- Theorem 6.2. The chosen frame is a function of the fixed atom and
works for all finite Γ ≥ 1 under the same projector law. -/
theorem theorem_6_2 {n k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) (hdim : k + l ≤ n)
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (P₀ : OrthogonalProjector n l) (_hα : 0 < μ.real {P₀}) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ,
      Vᵀ * V = 1 ∧ P₀.val * V = 0 ∧
      (∀ i, (∑ j, V i j ^ 2) ≤ ∑ j : Fin k, ((n - l - j.val : ℕ) : ℝ)⁻¹) ∧
      (∑ j : Fin k, ((n - l - j.val : ℕ) : ℝ)⁻¹) ≤
        (k : ℝ) / ((n - l - k + 1 : ℕ) : ℝ) ∧
      ∀ Γ : ℝ, 1 ≤ Γ →
        (μ.real {P₀} * Γ - (l : ℝ) / k) / (n - k) ≤
          ∫ P, projectorTwoLevelLoss V P Γ ∂μ := by
  classical
  have hkn : k < n := by omega
  obtain ⟨V, hNull, hV, hLev, hLev'⟩ := exists_flat_kernelFrame P₀.val P₀.property.2.2 hdim
  refine ⟨V, hV, hNull, hLev, hLev', ?_⟩
  intro Γ hΓ
  let C (P : OrthogonalProjector n l) : {S : Matrix (Fin k) (Fin k) ℝ // S.IsHermitian} :=
    ⟨Vᵀ * P.val * V, (targetCompression_posSemidef V P).isHermitian⟩
  let t (j : Fin k) (P : OrthogonalProjector n l) : ℝ :=
    orderedEigenvaluesFin (targetCompression_posSemidef V P).isHermitian j
  have hC : Continuous C := by
    apply Continuous.subtype_mk
    fun_prop
  have hmeas (j : Fin k) : Measurable (t j) := by
    apply Continuous.measurable
    exact (continuous_apply (Fin.cast (Fintype.card_fin k).symm j)).comp
      (continuous_orderedEigenvalues.comp hC)
  have hzero : ∀ P ∈ ({P₀} : Set (OrthogonalProjector n l)), ∀ j, t j P = 0 := by
    intro P hP j
    have hp : P = P₀ := hP
    subst P
    apply orderedEigenvaluesFin_of_zero
    rw [Matrix.mul_assoc, hNull, Matrix.mul_zero]
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  have h := atom_spectralLoss_lower (n := (n : ℝ)) (ℓ := (l : ℝ))
    μ hk hkn' hΓ t hmeas
    (fun j P => orderedEigenvaluesFin_nonneg (targetCompression_posSemidef V P) j)
    (measurableSet_singleton P₀) hzero
  calc
    _ ≤ _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with P using (projectorTwoLevelLoss_eq_angles V hV P hΓ hk hkn).symm

end SketchOrientation
