import SketchOrientation.Dct
import SketchOrientation.Residual

namespace SketchOrientation

open Matrix

/-- The ordered sample of distinct DCT rows. -/
def rowSelector {n l : ℕ} (rows : Fin l ↪ Fin n) : Matrix (Fin l) (Fin n) ℝ :=
  fun i j => if rows i = j then 1 else 0

/-- The orthogonal DCT-II of Section 4 uses frequency rows and spatial columns. -/
noncomputable def pairedDctII (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (cosineCore n)ᵀ

/-- One pass with prescribed sampled rows and signs, as in (4.1). -/
noncomputable def onePassDct {n l : ℕ} (rows : Fin l ↪ Fin n)
    (signs : Fin n → ℝ) : Matrix (Fin n) (Fin l) ℝ :=
  (rowSelector rows * pairedDctII n * diagonal signs)ᵀ

/-- Two passes with the same prescribed rows and first-pass signs. -/
noncomputable def twoPassDct {n l : ℕ} (rows : Fin l ↪ Fin n)
    (signs₁ signs₂ : Fin n → ℝ) : Matrix (Fin n) (Fin l) ℝ :=
  (rowSelector rows * pairedDctII n * diagonal signs₁ *
    pairedDctII n * diagonal signs₂)ᵀ

/-- The coupling equality specified in Proposition C.1. -/
theorem twoPassDct_pairing {n l : ℕ} (rows : Fin l ↪ Fin n)
    (signs₁ signs₂ : Fin n → ℝ) :
    twoPassDct rows signs₁ signs₂ =
      diagonal signs₂ * (pairedDctII n)ᵀ * onePassDct rows signs₁ := by
  simp only [twoPassDct, onePassDct, transpose_mul, diagonal_transpose, Matrix.mul_assoc]

/-- Proposition C.1, for every draw at each sampled width. -/
theorem proposition_C_1 {n l : ℕ} (k : ℕ) (σ : Fin n → ℝ)
    (_hσ : ∀ j, 0 ≤ σ j) (rows : Fin l ↪ Fin n) (signs₁ signs₂ : Fin n → ℝ)
    (_hsigns₁ : ∀ j, signs₁ j = -1 ∨ signs₁ j = 1)
    (hsigns₂ : ∀ j, signs₂ j = -1 ∨ signs₂ j = 1)
    (htail : 0 < optimalTail k (diagonal σ)) :
    tailRelativeError k (diagonal σ) (twoPassDct rows signs₁ signs₂) =
      tailRelativeError k (diagonal σ * (pairedDctII n)ᵀ) (onePassDct rows signs₁) := by
  rw [twoPassDct_pairing]
  apply pairedDraw_orthogonal k σ signs₂ _ _ _ _ hsigns₂ htail
  · simpa [pairedDctII] using cosineCore_mul_transpose n
  · simpa [pairedDctII] using cosineCore_transpose_mul n

end SketchOrientation
