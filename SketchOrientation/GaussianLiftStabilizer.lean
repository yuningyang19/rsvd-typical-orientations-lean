import SketchOrientation.ProjectorOverlap
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace SketchOrientation

open Matrix MeasureTheory Unitary

variable {n ℓ : ℕ}

private theorem stabilizer_diagonal_form (d : Fin n → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hComm : ∀ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = 1 →
      diagonal d * R = R * diagonal d → A * R = R * A) :
    ∃ a b : ℝ, A = a • diagonal d + b • (1 - diagonal d) := by
  classical
  have hOff (i j : Fin n) (hij : i ≠ j) : A i j = 0 := by
    let s (q : Fin n) : ℝ := if q = i then -1 else 1
    let R := diagonal s
    have hR : Rᵀ * R = 1 := by
      rw [show R = diagonal s from rfl, diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext q
      by_cases h : q = i <;> simp [s, h]
    have hD : diagonal d * R = R * diagonal d := by
      simp only [R, diagonal_mul_diagonal]
      congr 1
      funext q
      exact mul_comm _ _
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X i j) (hComm R hR hD)
    simp only [R, mul_diagonal, diagonal_mul, s, if_true, if_neg hij.symm, mul_one] at h
    linarith
  have hSame (i j : Fin n) (hij : d i = d j) : A i i = A j j := by
    let σ := Equiv.swap i j
    let R := σ.permMatrix ℝ
    have hR : Rᵀ * R = 1 := by
      rw [show R = σ.permMatrix ℝ from rfl, transpose_permMatrix, ← permMatrix_mul,
        mul_inv_cancel, permMatrix_one]
    have hdσ (q : Fin n) : d (σ q) = d q := by
      by_cases hi : q = i
      · subst q
        simp [σ, hij]
      by_cases hj : q = j
      · subst q
        simp [σ, hij]
      exact congrArg d (Equiv.swap_apply_of_ne_of_ne hi hj)
    have hD : diagonal d * R = R * diagonal d := by
      ext u v
      simp only [diagonal_mul, mul_diagonal]
      by_cases h : σ u = v
      · subst v
        rw [hdσ, mul_comm]
      · have h0 : R u v = 0 := by simpa [R, Equiv.Perm.permMatrix] using h
        simp [h0]
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ => X i j) (hComm R hR hD)
    have hleft : (A * R) i j = A i i := by
      change ((fun r => A i r) ᵥ* σ.permMatrix ℝ) j = _
      rw [vecMul_permMatrix, Function.comp_apply]
      simp [σ]
    have hright : (R * A) i j = A j j := by
      change (σ.permMatrix ℝ *ᵥ fun r => A r j) i = _
      rw [permMatrix_mulVec, Function.comp_apply]
      simp [σ]
    exact hleft.symm.trans (h.trans hright)
  let entry (x : ℝ) : ℝ := if h : ∃ i, d i = x then A h.choose h.choose else 0
  have hEntry (i : Fin n) : A i i = entry (d i) := by
    have hi : ∃ j, d j = d i := ⟨i, rfl⟩
    unfold entry
    rw [dif_pos hi]
    exact hSame i hi.choose hi.choose_spec.symm
  refine ⟨entry 1, entry 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    rw [hEntry]
    rcases hd i with h | h <;> simp [h]
  · simp [hOff i j hij, hij, one_apply_ne]

/-- The orthogonal stabilizer of a real projector forces a commuting
matrix to be scalar on its range and on its kernel. -/
theorem matrix_eq_projector_smul_add_complement_of_stabilizer
    (P : OrthogonalProjector n ℓ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hComm : ∀ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = 1 →
      P.val * R = R * P.val → A * R = R * A) :
    ∃ a b : ℝ, A = a • P.val + b • (1 - P.val) := by
  have hP : P.val.IsHermitian := by
    change P.valᴴ = P.val
    simpa only [conjTranspose_eq_transpose_of_trivial] using P.property.1
  let K := conjStarAlgAut ℝ _ hP.eigenvectorUnitary
  let d := hP.eigenvalues
  let D := diagonal d
  have hD : K D = P.val := hP.spectral_theorem.symm
  have hDD : D * D = D := by
    apply K.injective
    calc
      K (D * D) = K D * K D := map_mul K _ _
      _ = K D := by rw [hD, P.property.2.1]
  have hd (i : Fin n) : d i = 0 ∨ d i = 1 := by
    rw [show D = diagonal d from rfl, diagonal_mul_diagonal] at hDD
    have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hDD
    simp only [diagonal_apply_eq] at hi
    have h := (mul_eq_zero.mp (show d i * (d i - 1) = 0 by linarith [hi]))
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  let B := K.symm A
  have hB : K B = A := K.apply_symm_apply _
  have hBD (R : Matrix (Fin n) (Fin n) ℝ) (hR : Rᵀ * R = 1)
      (hDR : D * R = R * D) : B * R = R * B := by
    have hKR : (K R)ᵀ * (K R) = 1 := by
      have hStar : star R * R = 1 := by
        simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hR
      have he := congrArg K hStar
      rw [map_mul, map_star, map_one] at he
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using he
    have hRD : P.val * K R = K R * P.val := by
      simpa only [map_mul, hD] using congrArg K hDR
    apply K.injective
    calc
      K (B * R) = A * K R := by rw [map_mul]; change K B * K R = _; rw [hB]
      _ = K R * A := hComm (K R) hKR hRD
      _ = K (R * B) := by rw [map_mul]; change _ = K R * K B; rw [hB]
  obtain ⟨a, b, h⟩ := stabilizer_diagonal_form d hd B hBD
  refine ⟨a, b, ?_⟩
  change B = a • D + b • (1 - D) at h
  calc
    A = K B := hB.symm
    _ = K (a • D + b • (1 - D)) := congrArg K h
    _ = _ := by
      simp only [map_add, map_smul, map_sub, map_one]
      change a • K D + b • (1 - K D) = _
      rw [hD]

/-- Centering determines the range/kernel coefficients from the single
pairing with the sketch projector. -/
theorem centered_stabilizer_matrix_eq (hℓ : 0 < ℓ) (hℓn : ℓ ≤ n)
    (P : OrthogonalProjector n ℓ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hComm : ∀ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = 1 →
      P.val * R = R * P.val → A * R = R * A)
    (hCenter : A.trace = 0)
    (hEnergy : (P.val * A).trace = c * ((ℓ : ℝ) * ((n : ℝ) - ℓ) / n)) :
    A = c • (P.val - ((ℓ : ℝ) / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  obtain ⟨a, b, hA⟩ := matrix_eq_projector_smul_add_complement_of_stabilizer P A hComm
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (hℓ.trans_le hℓn)
  by_cases hFull : ℓ = n
  · subst ℓ
    obtain ⟨U, hU, hP⟩ := exists_frame_of_projector P.val P.property.1 P.property.2.1 P.property.2.2
    have hId : P.val = 1 := hP.symm.trans (mul_eq_one_comm.mp hU)
    simp only [hId, sub_self, smul_zero, add_zero] at hA
    rw [hA, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at hCenter
    have ha : a = 0 := (mul_eq_zero.mp hCenter).resolve_right hn.ne'
    rw [hA, ha, hId, div_self hn.ne', one_smul, sub_self, zero_smul, smul_zero]
  have hGap : 0 < (n : ℝ) - ℓ := sub_pos.mpr (by exact_mod_cast lt_of_le_of_ne hℓn hFull)
  have hℓ' : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ
  have hTrace : P.val.trace = (ℓ : ℝ) := by
    calc
      _ = (rangeProjector P.val).trace := congrArg trace
        (rangeProjector_of_projector P.val P.property.1 P.property.2.1).symm
      _ = (P.val.rank : ℝ) := trace_rangeProjector _
      _ = _ := by rw [P.property.2.2]
  have hPPc : P.val * (1 - P.val) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, P.property.2.1, sub_self]
  rw [hA, trace_add, trace_smul, trace_smul, trace_sub, trace_one,
    Fintype.card_fin, hTrace, smul_eq_mul, smul_eq_mul] at hCenter
  rw [hA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, P.property.2.1, hPPc,
    smul_zero, add_zero, trace_smul, hTrace, smul_eq_mul] at hEnergy
  have ha : a = c * (1 - (ℓ : ℝ) / n) := by
    apply mul_right_cancel₀ hℓ'.ne'
    rw [hEnergy]
    field_simp
  have hb : b = -(c * ((ℓ : ℝ) / n)) := by
    apply mul_right_cancel₀ hGap.ne'
    have hb' : b * ((n : ℝ) - ℓ) = -(a * (ℓ : ℝ)) := by linarith only [hCenter]
    rw [hb', hEnergy]
    ring
  rw [hA, ha, hb]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end SketchOrientation
