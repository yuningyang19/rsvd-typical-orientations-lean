import SketchOrientation.Geometry
import SketchOrientation.AtomTheorem
import Mathlib.Analysis.MeanInequalitiesPow

namespace SketchOrientation

open Matrix

variable {n k ℓ : ℕ}

/-- Squared principal cosines of a Stiefel frame and a sketch projector. -/
noncomputable def orientationPrincipalCosines (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n ℓ) : Fin k → ℝ :=
  orderedEigenvaluesFin (targetCompression_posSemidef V P).isHermitian

theorem orientationPrincipalCosines_nonneg (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n ℓ) (i : Fin k) :
    0 ≤ orientationPrincipalCosines V P i :=
  orderedEigenvaluesFin_nonneg (targetCompression_posSemidef V P) i

theorem orientationPrincipalCosines_pos (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n ℓ) (h : (Vᵀ * P.val * V).det ≠ 0) (i : Fin k) :
    0 < orientationPrincipalCosines V P i :=
  orderedEigenvaluesFin_pos ((targetCompression_posSemidef V P).posDef_iff_det_ne_zero.mpr h) i

theorem orientationPrincipalCosines_le_one (V : Matrix (Fin n) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) (P : OrthogonalProjector n ℓ) (i : Fin k) :
    orientationPrincipalCosines V P i ≤ 1 := by
  let T := Vᵀ * P.val * V
  let hT := (targetCompression_posSemidef V P).isHermitian
  let j : Fin k := (Fintype.equivOfCardEq (Fintype.card_fin _))
    (Fin.cast (Fintype.card_fin k).symm i)
  let v : EuclideanSpace ℝ (Fin k) := hT.eigenvectorBasis j
  have hC : (1 - P.val).PosSemidef := by
    have ht : (1 - P.val)ᵀ = 1 - P.val := by rw [transpose_sub, transpose_one, P.property.1]
    have hi : (1 - P.val) * (1 - P.val) = 1 - P.val := by
      rw [sub_mul, one_mul, mul_sub, mul_one, P.property.2.1, sub_self, sub_zero]
    have h := posSemidef_conjTranspose_mul_self (1 - P.val)
    rw [conjTranspose_eq_transpose_of_trivial, ht, hi] at h
    exact h
  have hComp : (1 - T).PosSemidef := by
    have h := hC.conjTranspose_mul_mul_same V
    rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hV] at h
    exact h
  have hq := hComp.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  rw [sub_mulVec, one_mulVec, dotProduct_sub] at hq
  have hv : star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, real_inner_self_eq_norm_sq,
      hT.eigenvectorBasis.orthonormal.1 j]
    norm_num
  have he := hT.eigenvalues_eq j
  change hT.eigenvalues j = star (WithLp.ofLp v) ⬝ᵥ (T *ᵥ WithLp.ofLp v) at he
  rw [hv, ← he, sub_nonneg] at hq
  simpa [orientationPrincipalCosines, orderedEigenvaluesFin, j, hT, Matrix.IsHermitian.eigenvalues]
    using hq

theorem trace_inverse_orientationPrincipalCosines (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n ℓ) (h : (Vᵀ * P.val * V).det ≠ 0) :
    (Vᵀ * P.val * V)⁻¹.trace = ∑ j, (orientationPrincipalCosines V P j)⁻¹ := by
  have hspec (j : Fin k) : orientationPrincipalCosines V P j ≠ 0 :=
    (orientationPrincipalCosines_pos V P h j).ne'
  simpa only [orientationPrincipalCosines, zero_smul, one_smul, zero_add, one_mul] using
    trace_inverse_affine_orderedEigenvaluesFin (targetCompression_posSemidef V P).isHermitian
      1 0 (fun j => by simpa only [zero_add, one_mul] using (show orderedEigenvaluesFin (targetCompression_posSemidef V P).isHermitian j ≠ 0
        from hspec j))

/-- The endpoint loss of a fixed sketch projector. -/
noncomputable def projectorOrientationEndpoint (V : Matrix (Fin n) (Fin k) ℝ)
    (P : OrthogonalProjector n ℓ) : ℝ :=
  ((Vᵀ * P.val * V)⁻¹.trace - ℓ) / ((k : ℝ) * ((n : ℝ) - k))

private theorem sum_rpow_le_rpow_sum {r : ℝ} (hr : 1 ≤ r)
    (f : Fin k → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i ^ r) ≤ (∑ i, f i) ^ r := by
  have h (s : Finset (Fin k)) : (∑ i ∈ s, f i ^ r) ≤ (∑ i ∈ s, f i) ^ r := by
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow (zero_lt_one.trans_le hr).ne']
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add (le_refl (f i ^ r)) ih).trans
        (Real.add_rpow_le_rpow_add (hf i) (Finset.sum_nonneg fun j _ => hf j) hr)
  exact h Finset.univ

set_option maxHeartbeats 600000 in
/-- Pointwise domination of the gap deficit for actual two-level RSVD residuals. -/
theorem projectorOrientationGap_bound (hk : 0 < k) (hkn : k < n)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (P : OrthogonalProjector n ℓ) (hT : (Vᵀ * P.val * V).det ≠ 0)
    {Γ r : ℝ} (hΓ : 1 < Γ) (hr : 1 < r) (hr₂ : r ≤ 2) :
    0 ≤ projectorOrientationEndpoint V P - projectorTwoLevelLoss V P Γ ∧
      projectorOrientationEndpoint V P - projectorTwoLevelLoss V P Γ ≤
        (Γ - 1) ^ (1 - r) / ((k : ℝ) * ((n : ℝ) - k)) *
          ((Vᵀ * P.val * V)⁻¹.trace) ^ r := by
  let t := orientationPrincipalCosines V P
  let d := (k : ℝ) * ((n : ℝ) - k)
  have hd : 0 < d := mul_pos (Nat.cast_pos.mpr hk)
    (sub_pos.mpr (by exact_mod_cast hkn))
  have ht (i : Fin k) := orientationPrincipalCosines_pos V P hT i
  have h1 (i : Fin k) := orientationPrincipalCosines_le_one V hV P i
  have hdef (i : Fin k) := angleSummand_defect_bounds hΓ (ht i) (h1 i) hr hr₂
  have hTrace := trace_inverse_orientationPrincipalCosines V P hT
  rw [projectorOrientationEndpoint, projectorTwoLevelLoss_eq_angles V hV P hΓ.le hk hkn, hTrace]
  change 0 ≤ ((∑ i, (t i)⁻¹) - ℓ) / d - ((∑ i, angleSummand Γ (t i)) - ℓ) / d ∧
    ((∑ i, (t i)⁻¹) - ℓ) / d - ((∑ i, angleSummand Γ (t i)) - ℓ) / d ≤
      (Γ - 1) ^ (1 - r) / d * (∑ i, (t i)⁻¹) ^ r
  rw [← sub_div, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => (hdef i).1) hd.le, ?_⟩
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ∑ i, (Γ - 1) ^ (1 - r) * (t i) ^ (-r) :=
      Finset.sum_le_sum fun i _ => (hdef i).2
    _ = (Γ - 1) ^ (1 - r) * ∑ i, ((t i)⁻¹) ^ r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.inv_rpow (ht i).le, Real.rpow_neg (ht i).le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_rpow_le_rpow_sum hr.le _ (fun i => inv_nonneg.mpr (ht i).le))
        (Real.rpow_nonneg (sub_nonneg.mpr hΓ.le) _)

/-- Actual two-level RSVD loss is monotone over finite gaps on every frame. -/
theorem projectorTwoLevelLoss_monotone (hk : 0 < k) (hkn : k < n)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : Vᵀ * V = 1)
    (P : OrthogonalProjector n ℓ) :
    MonotoneOn (projectorTwoLevelLoss V P) (Set.Ici 1) := by
  intro Γ₀ h₀ Γ₁ h₁ hΓ
  have h₀' : 1 ≤ Γ₀ := h₀
  have h₁' : 1 ≤ Γ₁ := h₁
  rw [projectorTwoLevelLoss_eq_angles V hV P h₀' hk hkn,
    projectorTwoLevelLoss_eq_angles V hV P h₁' hk hkn]
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hkn'))
  · apply sub_le_sub_right
    exact Finset.sum_le_sum fun i _ => angleSummand_monotone
      (orientationPrincipalCosines_nonneg V P i) (orientationPrincipalCosines_le_one V hV P i)
      h₀ h₁ hΓ

end SketchOrientation
