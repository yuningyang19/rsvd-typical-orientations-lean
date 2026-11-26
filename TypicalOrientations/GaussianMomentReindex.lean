import TypicalOrientations.GaussianMomentDeterministic
import TypicalOrientations.GaussianMomentProduct

namespace TypicalOrientations

open Matrix SketchOrientation MeasureTheory

noncomputable section

variable {n k ℓ : ℕ}

private theorem submatrix_submatrix_transpose_prod {m m' p : Type*}
    [Fintype m] [Fintype m'] (Y : Matrix m p ℝ) (e : m' ≃ m) :
    (Y.submatrix e id)ᵀ * (Y.submatrix e id) = Yᵀ * Y := by
  rw [transpose_submatrix, Matrix.submatrix_mul_equiv Yᵀ Y id e id, Matrix.submatrix_id_id]

private theorem squaredFrobenius_submatrix_equiv {i i' j j' : Type*}
    [Fintype i] [Fintype i'] [Fintype j] [Fintype j']
    (e : i' ≃ i) (f : j' ≃ j) (A : Matrix i j ℝ) :
    squaredFrobenius (A.submatrix e f) = squaredFrobenius A := by
  simp only [Cosine.squaredFrobenius_eq_sum_entries, submatrix_apply]
  calc
    (∑ x, ∑ y, A (e x) (f y) ^ 2) = ∑ x, ∑ j, A (e x) j ^ 2 :=
      Finset.sum_congr rfl fun x _ => Fintype.sum_equiv f _ _ fun _ => rfl
    _ = _ := Fintype.sum_equiv e _ _ fun _ => rfl

/-- Relabeling both input and output basis indices preserves the entire residual,
including at rank changes of the sampled matrix. -/
theorem squaredResidual_submatrix_equiv {i i' : Type*}
    [Fintype i] [Fintype i'] [DecidableEq i] [DecidableEq i']
    (e : i' ≃ i) (A : Matrix i i ℝ) (G : Matrix i (Fin ℓ) ℝ) :
    squaredResidual (A.submatrix e e) (G.submatrix e id) = squaredResidual A G := by
  have hP (Y : Matrix i (Fin ℓ) ℝ) :
      rangeProjector (Y.submatrix e id) = (rangeProjector Y).submatrix e e := by
    let S := Yᵀ * Y
    let Q := symmetricPseudoInverse S
      (by simpa only [S, conjTranspose_eq_transpose_of_trivial] using
        isHermitian_conjTranspose_mul_self Y)
    have hSq : S * Q * S = S := symmetricPseudoInverse_penrose S _
    have hS := submatrix_submatrix_transpose_prod Y e
    have hSq' : (Y.submatrix e id)ᵀ * (Y.submatrix e id) * Q *
        ((Y.submatrix e id)ᵀ * (Y.submatrix e id)) =
          (Y.submatrix e id)ᵀ * (Y.submatrix e id) := by rw [hS]; exact hSq
    rw [rangeProjector_of_inner_inverse _ Q hSq',
      rangeProjector_of_inner_inverse _ Q hSq, transpose_submatrix]
    have he : Q = Q.submatrix (⇑(Equiv.refl (Fin ℓ))) (⇑(Equiv.refl (Fin ℓ))) := rfl
    conv_lhs => rw [he]
    simp only [show id = ⇑(Equiv.refl (Fin ℓ)) by rfl]
    rw [Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin ℓ)) _,
      Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin ℓ)) _]
  rw [squaredResidual, squaredResidual, Matrix.submatrix_mul_equiv A G e e id, hP]
  have hs :
      ((1 : Matrix i i ℝ) - rangeProjector (A * G)).submatrix e e =
        (1 : Matrix i i ℝ).submatrix e e - (rangeProjector (A * G)).submatrix e e := rfl
  rw [← show (1 : Matrix i i ℝ).submatrix e e = 1 from Matrix.submatrix_one_equiv e,
    ← hs, Matrix.submatrix_mul_equiv _ _ _ e _, squaredFrobenius_submatrix_equiv]

/-- The ordered identification of the leading k indices and the remaining indices. -/
def leadingTailEquiv (hkn : k ≤ n) : Fin k ⊕ Fin (n - k) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkn))

theorem leadingTailEquiv_leading_val (hkn : k ≤ n) (i : Fin k) :
    (leadingTailEquiv hkn (Sum.inl i)).val = i.val := by
  simp [leadingTailEquiv, finSumFinEquiv_apply_left]

theorem leadingTailEquiv_tail_val (hkn : k ≤ n) (i : Fin (n - k)) :
    (leadingTailEquiv hkn (Sum.inr i)).val = k + i.val := by
  simp [leadingTailEquiv, finSumFinEquiv_apply_right]

theorem gaussianMatrixLaw_map_transpose (m ℓ : ℕ) :
    (gaussianMatrixLaw m ℓ).map (fun B => Bᵀ) = gaussianMatrixLaw ℓ m := by
  let f (X : Fin ℓ → Fin m → ℝ) : Matrix (Fin m) (Fin ℓ) ℝ := Matrix.of fun i j => X j i
  let g (B : Matrix (Fin m) (Fin ℓ) ℝ) : Matrix (Fin ℓ) (Fin m) ℝ := Bᵀ
  have hf : Measurable f := measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hg : Measurable g :=
    (continuous_id.matrix_transpose : Continuous (fun B : Matrix (Fin m) (Fin ℓ) ℝ => Bᵀ)).measurable
  rw [gaussianMatrixLaw_eq_coordinate_product, gaussianMatrixLaw_eq_row_product]
  change Measure.map g (Measure.map f _) = _
  rw [Measure.map_map hg hf]
  change Measure.map id _ = _
  exact Measure.map_id

/-- Split rows of the standard Gaussian matrix into the leading and tail
blocks, with the leading block transposed. -/
def splitGaussianMatrix (hkn : k ≤ n) (G : Matrix (Fin n) (Fin ℓ) ℝ) :
    Matrix (Fin ℓ) (Fin k) ℝ × Matrix (Fin (n - k)) (Fin ℓ) ℝ :=
  ((G.submatrix (leadingTailEquiv hkn ∘ Sum.inl) id)ᵀ,
    G.submatrix (leadingTailEquiv hkn ∘ Sum.inr) id)

theorem gaussianSplit_measurePreserving (hkn : k ≤ n) :
    MeasurePreserving (splitGaussianMatrix (ℓ := ℓ) hkn) (gaussianMatrixLaw n ℓ)
      (gaussianSplitLaw k ℓ (n - k)) := by
  let R := Fin ℓ → ℝ
  let ν := gaussianRowLaw ℓ
  have h₁ := measurePreserving_piCongrLeft (α := fun _ : Fin k ⊕ Fin (n - k) => R)
    (fun _ => ν) (leadingTailEquiv hkn).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (X := fun _ : Fin k ⊕ Fin (n - k) => R) (fun _ => ν)
  have hT : MeasurePreserving (fun B : Matrix (Fin k) (Fin ℓ) ℝ => Bᵀ)
      (gaussianMatrixLaw k ℓ) (gaussianMatrixLaw ℓ k) :=
    ⟨continuous_id.matrix_transpose.measurable, gaussianMatrixLaw_map_transpose _ _⟩
  have h₃ := hT.prod (MeasurePreserving.id (gaussianMatrixLaw (n-k) ℓ))
  rw [gaussianMatrixLaw_eq_row_product, gaussianMatrixLaw_eq_row_product] at h₃
  have h := h₃.comp (h₂.comp h₁)
  have he : splitGaussianMatrix (ℓ := ℓ) hkn =
      Prod.map (fun B : Matrix (Fin k) (Fin ℓ) ℝ => Bᵀ) id ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (n-k) => R)) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin (n-k) => R) (leadingTailEquiv hkn).symm) := by
    funext G
    apply Prod.ext
    · ext i j
      change G (leadingTailEquiv hkn (Sum.inl j)) i =
        (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin (n-k) => R)
          (leadingTailEquiv hkn).symm G (Sum.inl j)) i
      have hj := MeasurableEquiv.piCongrLeft_apply_apply (leadingTailEquiv hkn).symm
        (β := fun _ => R) G (leadingTailEquiv hkn (Sum.inl j))
      simpa only [Equiv.symm_apply_apply] using congrArg (fun z : R => z i) hj.symm
    · ext i j
      change G (leadingTailEquiv hkn (Sum.inr i)) j =
        (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin (n-k) => R)
          (leadingTailEquiv hkn).symm G (Sum.inr i)) j
      have hi := MeasurableEquiv.piCongrLeft_apply_apply (leadingTailEquiv hkn).symm
        (β := fun _ => R) G (leadingTailEquiv hkn (Sum.inr i))
      simpa only [Equiv.symm_apply_apply] using congrArg (fun z : R => z j) hi.symm
  simp only [he, gaussianMatrixLaw_eq_row_product n ℓ, gaussianSplitLaw,
    gaussianMatrixLaw_eq_row_product (n - k) ℓ]
  exact h

theorem diagonal_residual_eq_split (hkn : k ≤ n) (σ : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin ℓ) ℝ) :
    squaredResidual (diagonal σ) G =
      squaredResidual
        (fromBlocks (diagonal (σ ∘ leadingTailEquiv hkn ∘ Sum.inl)) 0 0
          (diagonal (σ ∘ leadingTailEquiv hkn ∘ Sum.inr)))
        (fromRows (splitGaussianMatrix hkn G).1ᵀ (splitGaussianMatrix hkn G).2) := by
  let e := leadingTailEquiv hkn
  rw [← squaredResidual_submatrix_equiv e (diagonal σ) G,
    Matrix.submatrix_diagonal _ e e.injective]
  congr 1
  · ext i j
    cases i <;> cases j <;>
      simp [Matrix.diagonal_apply, Function.comp_def, e]
  · ext i j
    cases i <;> rfl

end

end TypicalOrientations
