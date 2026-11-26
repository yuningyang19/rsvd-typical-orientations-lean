import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace SketchOrientation

open Matrix

variable {d k : ℕ}

/-- The unnormalized Gram of the columns of a real matrix. -/
def gaussianGram (Z : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Zᵀ * Z

/-- The remaining columns in their original order. -/
def dropGramColumn (Z : Matrix (Fin d) (Fin (k + 1)) ℝ) (j : Fin (k + 1)) :
    Matrix (Fin d) (Fin k) ℝ :=
  Z.submatrix id j.succAbove

/-- Squared distance of a vector to the space spanned by a rectangular matrix's columns. -/
noncomputable def columnResidualSq (Y : Matrix (Fin d) (Fin k) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖z - (LinearMap.range Y.toEuclideanLin).starProjection z‖ ^ 2

lemma gaussianGram_posDef (Z : Matrix (Fin d) (Fin k) ℝ)
    (hZ : Function.Injective Z.mulVec) : (gaussianGram Z).PosDef := by
  simpa [gaussianGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self Z hZ

private lemma gram_mulVec_insertNth (Z : Matrix (Fin d) (Fin (k + 1)) ℝ)
    (j : Fin (k + 1)) (a : ℝ) (v : Fin k → ℝ) :
    Z *ᵥ j.insertNth a v = a • Z.col j + dropGramColumn Z j *ᵥ v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same, mul_comm (Z i j)]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Fin.insertNth_apply_succAbove]
  rfl

private lemma gram_mulVec_transpose_apply (Z : Matrix (Fin d) (Fin k) ℝ)
    (r : EuclideanSpace ℝ (Fin d)) (j : Fin k) :
    (Zᵀ *ᵥ WithLp.ofLp r) j = inner ℝ (WithLp.toLp 2 (Z.col j)) r := by
  simp [Matrix.mulVec, dotProduct, PiLp.inner_apply, Matrix.col_apply, RCLike.inner_apply,
    mul_comm]

/-- The Schur complement for one column. The positive-definite case gives
the diagonal of the inverse as the reciprocal squared orthogonal residual. -/
theorem gaussianGram_inv_diag (Z : Matrix (Fin d) (Fin (k + 1)) ℝ)
    (hZ : Function.Injective Z.mulVec) (j : Fin (k + 1)) :
    (gaussianGram Z)⁻¹ j j =
      (columnResidualSq (dropGramColumn Z j) (WithLp.toLp 2 (Z.col j)))⁻¹ := by
  let Y := dropGramColumn Z j
  let S := LinearMap.range Y.toEuclideanLin
  let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Z.col j)
  let r := z - S.starProjection z
  let s := ‖r‖ ^ 2
  have hr : r ∈ Sᗮ := S.sub_starProjection_mem_orthogonal z
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (S.orthogonalProjectionOnto z).property
  let u : Fin (k + 1) → ℝ := j.insertNth 1 (-WithLp.ofLp v)
  have hu : Z *ᵥ u = WithLp.ofLp r := by
    rw [gram_mulVec_insertNth, one_smul, Matrix.mulVec_neg]
    change Z.col j - (Y *ᵥ WithLp.ofLp v) = Z.col j - WithLp.ofLp (S.starProjection z)
    change Y.toEuclideanLin v = S.starProjection z at hv
    rw [← hv]
    rfl
  have hcol (l : Fin k) : WithLp.toLp 2 (Z.col (j.succAbove l)) ∈ S := by
    refine LinearMap.mem_range.mpr ⟨WithLp.toLp 2 (Pi.single l 1), ?_⟩
    rw [Matrix.toLpLin_apply 2 2, WithLp.ofLp_toLp, Matrix.mulVec_single_one]
    rfl
  have hinner : inner ℝ z r = s := by
    have hp : S.starProjection z ∈ S := (S.orthogonalProjectionOnto z).property
    have hh := hr _ hp
    have hz : z = r + S.starProjection z := by simp [r]
    calc
      inner ℝ z r = inner ℝ (r + S.starProjection z) r := congrArg (fun t => inner ℝ t r) hz
      _ = s := by rw [inner_add_left, hh, add_zero, real_inner_self_eq_norm_sq]
  have hGram : gaussianGram Z *ᵥ u = Pi.single j s := by
    rw [gaussianGram, ← Matrix.mulVec_mulVec, hu]
    funext l
    rw [gram_mulVec_transpose_apply]
    have h : ∀ i : Fin (k + 1),
        inner ℝ (WithLp.toLp 2 (Z.col i)) r = (Pi.single j s : Fin (k + 1) → ℝ) i :=
      (j.forall_iff_succAbove).2 ⟨by simpa [z] using hinner, fun i => by
        rw [hr _ (hcol i), Pi.single_eq_of_ne (Fin.succAbove_ne j i)]⟩
    exact h l
  have hi := (gaussianGram_posDef Z hZ).isUnit
  have hleft := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hi)
  have hsolve : (gaussianGram Z)⁻¹ *ᵥ Pi.single j s = u := by
    rw [← hGram, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hj := congrFun hsolve j
  rw [Matrix.mulVec_single, Pi.smul_apply] at hj
  have huj : u j = 1 := Fin.insertNth_apply_same _ _ _
  change (gaussianGram Z)⁻¹ j j * s = u j at hj
  rw [huj] at hj
  have hs : s ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hj
    exact zero_ne_one hj
  change (gaussianGram Z)⁻¹ j j = s⁻¹
  apply (eq_div_iff hs).2 ?_ |>.trans (one_div s)
  exact hj


/-- Injectivity of the columns is the nonvanishing Gram determinant condition. -/
theorem gaussianGram_det_ne_zero_iff (Z : Matrix (Fin d) (Fin k) ℝ) :
    (gaussianGram Z).det ≠ 0 ↔ Function.Injective Z.mulVec := by
  constructor
  · intro h a b hab
    apply Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr h))
    simp only [gaussianGram, ← Matrix.mulVec_mulVec, hab]
  · intro h
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (gaussianGram_posDef Z h).isUnit).ne_zero

/-- Adding a column outside the span of the other independent columns
preserves injectivity. -/
theorem gramColumns_injective_of_drop (Z : Matrix (Fin d) (Fin (k + 1)) ℝ)
    (j : Fin (k + 1)) (hY : Function.Injective (dropGramColumn Z j).mulVec)
    (hz : WithLp.toLp 2 (Z.col j) ∉ LinearMap.range (dropGramColumn Z j).toEuclideanLin) :
    Function.Injective Z.mulVec := by
  let Y := dropGramColumn Z j
  let S := LinearMap.range Y.toEuclideanLin
  let z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Z.col j)
  change Function.Injective Z.mulVecLin
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro v hv
  change Z *ᵥ v = 0 at hv
  rw [← Fin.insertNth_self_removeNth j v, gram_mulVec_insertNth] at hv
  have he : v j • z + Y.toEuclideanLin (WithLp.toLp 2 (j.removeNth v)) = 0 := by
    exact congrArg (WithLp.toLp 2) hv
  have hj : v j = 0 := by
    by_contra h
    have hmem : v j • z ∈ S := by
      rw [eq_neg_of_add_eq_zero_left he]
      exact S.neg_mem (LinearMap.mem_range_self _ _)
    have hmem' := S.smul_mem (v j)⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ h, one_smul] at hmem'
    exact hz hmem'
  have hrem : j.removeNth v = 0 := by
    apply hY
    simpa [hj] using hv
  calc
    v = j.insertNth (v j) (j.removeNth v) := (Fin.insertNth_self_removeNth j v).symm
    _ = 0 := Fin.insertNth_eq_iff.mpr ⟨hj, hrem⟩

end SketchOrientation
