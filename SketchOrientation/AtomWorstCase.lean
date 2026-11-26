import SketchOrientation.UnequalSpikes
import SketchOrientation.GaussianOrientationGap
import SketchOrientation.DctSketchLaw

namespace SketchOrientation

open Matrix MeasureTheory Set Filter
open scoped MatrixOrder

private theorem orthogonal_extension_first {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (V₁ : Matrix (Fin n) (Fin 1) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * V = 1 ∧ V₁ * V₁ᵀ ≤ V * Vᵀ := by
  let h₁n : 1 ≤ n := (show 1 ≤ k from hk).trans hkn
  obtain ⟨U, hU, hU₁⟩ := exists_orthogonal_extension h₁n V₁ hV₁
  let E := (rowSelector (Fin.castLEEmb hkn))ᵀ
  let S := (rowSelector (Fin.castLEEmb (show 1 ≤ k from hk)))ᵀ
  let V := U * E
  have hE : Eᵀ * E = 1 := by
    simp only [E, transpose_transpose, rowSelector_orthonormal]
  have hS : Sᵀ * S = 1 := by
    simp only [S, transpose_transpose, rowSelector_orthonormal]
  have hSub {a b c : ℕ} (J : Fin b ↪ Fin c) (X : Matrix (Fin a) (Fin c) ℝ) :
      X * (rowSelector J)ᵀ = X.submatrix id J := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, rowSelector, submatrix_apply, id_eq, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hV : Vᵀ * V = 1 := by
    unfold V
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, hE]
  have hVS : V * S = V₁ := by
    unfold V E S
    rw [hSub, hSub, Matrix.submatrix_submatrix, ← hU₁]
    rfl
  have hSubPSD : (1 - S * Sᵀ).PosSemidef := by
    let Q := 1 - S * Sᵀ
    have hQ : Qᵀ = Q := by simp [Q, transpose_mul]
    have hPi : (S * Sᵀ) * (S * Sᵀ) = S * Sᵀ := by
      rw [Matrix.mul_assoc S, ← Matrix.mul_assoc Sᵀ, hS, Matrix.one_mul]
    have hIdem : Q * Q = Q := projector_complement _ hPi
    have hP := posSemidef_self_mul_conjTranspose Q
    rwa [conjTranspose_eq_transpose_of_trivial, hQ, hIdem] at hP
  refine ⟨V, hV, ?_⟩
  rw [Matrix.le_iff, ← hVS]
  rw [Matrix.transpose_mul V S]
  have he : V * Vᵀ - V * S * (Sᵀ * Vᵀ) = V * (1 - S * Sᵀ) * Vᵀ := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]
  rw [he]
  simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    hSubPSD.conjTranspose_mul_mul_same Vᵀ

set_option maxHeartbeats 1000000 in
/-- One missed direction is enough for an unbounded worst-case mean at
any positive-probability sketch atom, with no room for a full k-dimensional
kernel required. This is the argument after Proposition C.1. -/
theorem atom_tailRelativeMean_lowerBound {n k l : ℕ} (hk : 0 < k)
    (hkl : k < l) (hln : l < n) (μ : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure μ] (P₀ : OrthogonalProjector n l) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * V = 1 ∧
      ∀ Γ : ℝ, 1 ≤ Γ →
        (μ.real {P₀}) * Γ / ((n : ℝ) - k) ≤
          ∫ P, tailRelativeError k (twoLevelInput V Γ) P.val ∂μ := by
  classical
  have hkn : k < n := hkl.trans hln
  obtain ⟨V₁, hNull, hV₁, _, _⟩ :=
    exists_flat_kernelFrame (k := 1) P₀.val P₀.property.2.2 (by omega)
  obtain ⟨V, hV, hFrame⟩ := orthogonal_extension_first hk hkn.le V₁ hV₁
  refine ⟨V, hV, ?_⟩
  intro Γ hΓ
  let A := twoLevelInput V Γ
  let A₁ := twoLevelInput V₁ Γ
  let W (P : OrthogonalProjector n l) := tailRelativeError k A P.val
  let R := Γ / ((n : ℝ) - k)
  have hΓ₀ : 0 ≤ Γ := zero_le_one.trans hΓ
  have hGram : A₁ᵀ * A₁ ≤ Aᵀ * A := by
    rw [show A₁ᵀ * A₁ = 1 + (Γ - 1) • (V₁ * V₁ᵀ) from twoLevelInput_gram V₁ hV₁ hΓ₀,
      show Aᵀ * A = 1 + (Γ - 1) • (V * Vᵀ) from twoLevelInput_gram V hV hΓ₀,
      Matrix.le_iff, add_sub_add_left_eq_sub, ← smul_sub]
    exact (Matrix.le_iff.mp hFrame).smul (sub_nonneg.mpr hΓ)
  obtain ⟨U, hU, hP⟩ := exists_frame_of_projector P₀.val P₀.property.1
    P₀.property.2.1 P₀.property.2.2
  have hR₁ : Γ ≤ squaredResidual A₁ P₀.val := by
    have hZero : V₁ᵀ * P₀.val * V₁ = 0 := by
      rw [Matrix.mul_assoc, hNull, Matrix.mul_zero]
    have h1 := twoLevel_squaredResidual A₁ U V₁ hU hV₁ hΓ (twoLevelInput_gram V₁ hV₁ hΓ₀)
    rw [← squaredResidual_frame_projector A₁ U hU, hP, hZero, smul_zero, add_zero,
      inv_one, trace_one, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h1
    rw [h1]
    have hnl : ((l + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show l + 1 ≤ n from hln)
    push_cast at hnl
    norm_num only [Nat.cast_one]
    linarith
  have hTail : optimalTail k A = (n : ℝ) - k := by
    have h := twoLevel_optimalTail A V hV hΓ (twoLevelInput_gram V hV hΓ₀)
    simpa only [Fintype.card_fin] using h
  have hnk : 0 ≤ (n : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hkn.le)
  have hR : R ≤ W P₀ := by
    unfold R W tailRelativeError
    rw [hTail]
    exact div_le_div_of_nonneg_right (hR₁.trans (squaredResidual_mono_gram A₁ A _ hGram))
      hnk
  have hW0 (P : OrthogonalProjector n l) : 0 ≤ W P := by
    unfold W tailRelativeError
    rw [hTail]
    exact div_nonneg (squaredFrobenius_nonneg _) hnk
  have heq (P : OrthogonalProjector n l) :
      (k : ℝ) * orientationFiniteLoss Γ P V + 1 = W P := by
    rw [orientationFiniteLoss_eq_actual hk hkn Γ hΓ P V hV]
    unfold projectorTwoLevelLoss centeredRankLoss W
    have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp [hk₀]
    exact sub_add_cancel _ _
  have hWm : Measurable W := by
    have hm := (measurable_orientationFiniteLoss (n := n) (k := k) (ℓ := l) Γ).comp
      (measurable_id.prodMk (measurable_const (a := V)))
    have hA : (fun P : OrthogonalProjector n l => (k : ℝ) * orientationFiniteLoss Γ P V + 1) = W :=
      funext heq
    rw [← hA]
    exact (hm.const_mul (k : ℝ)).add_const 1
  have hWi : Integrable W μ := by
    refine Integrable.of_bound hWm.aestronglyMeasurable (squaredFrobenius A / ((n : ℝ) - k)) ?_
    exact Filter.Eventually.of_forall fun P => by
      rw [Real.norm_of_nonneg (hW0 P)]
      unfold W tailRelativeError
      rw [hTail]
      apply div_le_div_of_nonneg_right _ hnk
      have h := squaredResidual_le_sampled_approximation A P.val (0 : Matrix (Fin n) (Fin n) ℝ)
      simpa only [Matrix.mul_zero, sub_zero] using h
  let I := ({P₀} : Set (OrthogonalProjector n l)).indicator (fun _ => R)
  have his : MeasurableSet ({P₀} : Set (OrthogonalProjector n l)) := measurableSet_singleton _
  have hIi : Integrable I μ := (integrable_const R).indicator his
  have hIW (P : OrthogonalProjector n l) : I P ≤ W P := by
    by_cases he : P = P₀
    · subst P
      simpa [I] using hR
    · simpa [I, he] using hW0 P
  calc
    _ = ∫ P, I P ∂μ := by
      simp only [I, integral_indicator his, integral_const]
      simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
      unfold R
      ring
    _ ≤ _ := integral_mono hIi hWi hIW

/-- A positive sketch-space atom forces the mean tail-relative loss for
one fixed frame to diverge with the leading squared singular value. -/
theorem atom_tailRelativeMean_unbounded {n k l : ℕ} (hk : 0 < k)
    (hkl : k < l) (hln : l < n) (μ : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure μ] (P₀ : OrthogonalProjector n l) (hα : 0 < μ.real {P₀}) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * V = 1 ∧
      Tendsto (fun Γ => ∫ P, tailRelativeError k (twoLevelInput V Γ) P.val ∂μ) atTop atTop := by
  obtain ⟨V, hV, hBound⟩ := atom_tailRelativeMean_lowerBound hk hkl hln μ P₀
  refine ⟨V, hV, tendsto_atTop_mono' atTop
    (f₁ := fun Γ => μ.real {P₀} * Γ / ((n : ℝ) - k)) ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Γ hΓ
    exact hBound Γ hΓ
  · have hd : 0 < (n : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkl.trans hln)
    have hCoeff := tendsto_id.const_mul_atTop (div_pos hα hd)
    convert hCoeff using 1
    ext Γ
    simp only [id_eq]
    ring

end SketchOrientation
