import SketchOrientation.GaussianGramAlgebra
import SketchOrientation.GramResidual

namespace SketchOrientation

open Matrix Submodule
open scoped RealInnerProductSpace

noncomputable section

variable {d k : ℕ}

/-- The column dual in the Euclidean column space of a rectangular matrix. -/
def gaussianGramDualColumn (Y : Matrix (Fin d) (Fin k) ℝ) (i : Fin k) :
    EuclideanSpace ℝ (Fin d) :=
  Y.toEuclideanLin ((gaussianGram Y)⁻¹.toEuclideanLin (EuclideanSpace.single i 1))

theorem gaussianGramDualColumn_mem_range (Y : Matrix (Fin d) (Fin k) ℝ) (i : Fin k) :
    gaussianGramDualColumn Y i ∈ LinearMap.range Y.toEuclideanLin :=
  LinearMap.mem_range_self _ _

private theorem transpose_map_dualColumn (Y : Matrix (Fin d) (Fin k) ℝ)
    (hY : Function.Injective Y.mulVec) (i : Fin k) :
    Yᵀ.toEuclideanLin (gaussianGramDualColumn Y i) = EuclideanSpace.single i 1 := by
  have hInv := (Matrix.isUnit_iff_isUnit_det _).mp (gaussianGram_posDef Y hY).isUnit
  calc
    _ = (gaussianGram Y * (gaussianGram Y)⁻¹).toEuclideanLin (EuclideanSpace.single i 1) := by
      simp only [gaussianGramDualColumn, gaussianGram, euclidean_mul, LinearMap.comp_apply]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hInv]; simp [Matrix.toEuclideanLin]

private theorem euclideanLin_single_column (Y : Matrix (Fin d) (Fin k) ℝ) (i : Fin k) :
    Y.toEuclideanLin (EuclideanSpace.single i 1) = WithLp.toLp 2 (Y.col i) := by
  rw [Matrix.toEuclideanLin_apply]
  congr 1
  have he : (EuclideanSpace.single i (1 : ℝ)).ofLp = Pi.single i 1 := by
    ext j
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [he, Matrix.mulVec_single_one]

private theorem transpose_map_entry_inner (Y : Matrix (Fin d) (Fin k) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    (Yᵀ.toEuclideanLin z) i = ⟪WithLp.toLp 2 (Y.col i), z⟫ := by
  calc
    _ = ⟪EuclideanSpace.single i 1, Yᵀ.toEuclideanLin z⟫ := by
      simp [EuclideanSpace.inner_single_left]
    _ = _ := by
      rw [euclidean_transpose, LinearMap.adjoint_inner_right, euclideanLin_single_column]

/-- The squared norm of the dual equals the corresponding inverse diagonal. -/
theorem gaussianGramDualColumn_norm_sq (Y : Matrix (Fin d) (Fin k) ℝ)
    (hY : Function.Injective Y.mulVec) (i : Fin k) :
    ‖gaussianGramDualColumn Y i‖ ^ 2 = (gaussianGram Y)⁻¹ i i := by
  let v := (gaussianGram Y)⁻¹.toEuclideanLin (EuclideanSpace.single i 1)
  calc
    _ = ⟪Y.toEuclideanLin v, gaussianGramDualColumn Y i⟫ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ⟪v, EuclideanSpace.single i 1⟫ := by
      rw [← LinearMap.adjoint_inner_right, ← euclidean_transpose, transpose_map_dualColumn Y hY]
    _ = _ := by
      rw [EuclideanSpace.inner_single_right]
      simp [v, euclideanLin_single_column, Matrix.col_apply]

private theorem eq_dualColumn_of_transpose_eq (Y : Matrix (Fin d) (Fin k) ℝ)
    (hY : Function.Injective Y.mulVec) (i : Fin k) (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ LinearMap.range Y.toEuclideanLin)
    (hEq : Yᵀ.toEuclideanLin z = EuclideanSpace.single i 1) :
    z = gaussianGramDualColumn Y i := by
  obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hz
  let b := (gaussianGram Y)⁻¹.toEuclideanLin (EuclideanSpace.single i 1)
  have hb := transpose_map_dualColumn Y hY i
  change Yᵀ.toEuclideanLin (Y.toEuclideanLin b) = _ at hb
  have hAB : (gaussianGram Y).toEuclideanLin a = (gaussianGram Y).toEuclideanLin b := by
    simpa only [gaussianGram, euclidean_mul, LinearMap.comp_apply] using hEq.trans hb.symm
  have hInj := Matrix.mulVec_injective_of_isUnit (gaussianGram_posDef Y hY).isUnit
  have hAB' : a = b := WithLp.ofLp_injective 2 (hInj (congrArg WithLp.ofLp hAB))
  exact congrArg Y.toEuclideanLin hAB'

private theorem mulVec_insert_drop (Z : Matrix (Fin d) (Fin (k + 1)) ℝ)
    (j : Fin (k + 1)) (a : ℝ) (v : Fin k → ℝ) :
    Z *ᵥ j.insertNth a v = a • Z.col j + dropGramColumn Z j *ᵥ v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same, mul_comm (Z i j)]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [Fin.insertNth_apply_succAbove]
  rfl

private theorem range_dropGramColumn_le (Z : Matrix (Fin d) (Fin (k + 1)) ℝ) (j : Fin (k + 1)) :
    LinearMap.range (dropGramColumn Z j).toEuclideanLin ≤ LinearMap.range Z.toEuclideanLin := by
  rintro _ ⟨v, rfl⟩
  refine ⟨WithLp.toLp 2 (j.insertNth 0 v.ofLp), ?_⟩
  rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, mulVec_insert_drop, zero_smul, zero_add,
    Matrix.toEuclideanLin_apply]

/-- Appending one column adds the squared regression coefficient divided by
its Schur residual to every other inverse diagonal. -/
theorem gaussianGram_inv_succAbove_diag (Z : Matrix (Fin d) (Fin (k + 1)) ℝ)
    (j : Fin (k + 1)) (i : Fin k) (hZ : Function.Injective Z.mulVec)
    (hY : Function.Injective (dropGramColumn Z j).mulVec) :
    let Y := dropGramColumn Z j
    let x := (WithLp.toLp 2 (Z.col j) : EuclideanSpace ℝ (Fin d))
    (gaussianGram Z)⁻¹ (j.succAbove i) (j.succAbove i) =
      (gaussianGram Y)⁻¹ i i + ⟪gaussianGramDualColumn Y i, x⟫ ^ 2 / columnResidualSq Y x := by
  let Y := dropGramColumn Z j
  let S := LinearMap.range Y.toEuclideanLin
  let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Z.col j)
  let r := x - S.starProjection x
  let s := ‖r‖ ^ 2
  let u := gaussianGramDualColumn Y i
  let θ := ⟪u, x⟫
  let w := u - (θ / s) • r
  have hu : u ∈ S := gaussianGramDualColumn_mem_range Y i
  have hr : r ∈ Sᗮ := S.sub_starProjection_mem_orthogonal x
  have hπ : S.starProjection x ∈ S := (S.orthogonalProjectionOnto x).property
  have hx : x ∈ LinearMap.range Z.toEuclideanLin :=
    ⟨EuclideanSpace.single j 1, euclideanLin_single_column Z j⟩
  have hR := range_dropGramColumn_le Z j
  have hrZ : r ∈ LinearMap.range Z.toEuclideanLin :=
    (LinearMap.range Z.toEuclideanLin).sub_mem hx (hR hπ)
  have hw : w ∈ LinearMap.range Z.toEuclideanLin :=
    (LinearMap.range Z.toEuclideanLin).sub_mem (hR hu)
      ((LinearMap.range Z.toEuclideanLin).smul_mem _ hrZ)
  have hs : s ≠ 0 := by
    have hPos : 0 < (gaussianGram Z)⁻¹ j j := (gaussianGram_posDef Z hZ).inv.diag_pos
    rw [gaussianGram_inv_diag Z hZ j] at hPos
    exact fun hz => by simpa [columnResidualSq, Y, S, x, r, s, hz] using hPos
  have hxr : ⟪x, r⟫ = s := by
    calc
      _ = ⟪r + S.starProjection x, r⟫ := by rw [show r + S.starProjection x = x from sub_add_cancel ..]
      _ = s := by rw [inner_add_left, inner_right_of_mem_orthogonal hπ hr, add_zero,
        real_inner_self_eq_norm_sq]
  have hTw : Zᵀ.toEuclideanLin w = EuclideanSpace.single (j.succAbove i) 1 := by
    ext a
    apply (j.forall_iff_succAbove).2 ?_ a
    constructor
    · rw [transpose_map_entry_inner, EuclideanSpace.single_apply, if_neg (Fin.succAbove_ne j i).symm]
      change ⟪x, w⟫ = 0
      unfold w
      rw [inner_sub_right, real_inner_smul_right, hxr, show ⟪x, u⟫ = θ from real_inner_comm u x]
      field_simp
      ring
    · intro t
      rw [transpose_map_entry_inner, EuclideanSpace.single_apply]
      have hy : WithLp.toLp 2 (Y.col t) ∈ S :=
        ⟨EuclideanSpace.single t 1, euclideanLin_single_column Y t⟩
      change ⟪WithLp.toLp 2 (Y.col t), u - (θ / s) • r⟫ = _
      rw [inner_sub_right, real_inner_smul_right, inner_right_of_mem_orthogonal hy hr, mul_zero, sub_zero,
        ← transpose_map_entry_inner, transpose_map_dualColumn Y hY, EuclideanSpace.single_apply]
      simp only [Fin.succAbove_right_inj]
  have he := eq_dualColumn_of_transpose_eq Z hZ (j.succAbove i) w hw hTw
  change _ = _ + θ ^ 2 / s
  rw [← gaussianGramDualColumn_norm_sq Z hZ, ← he]
  change ‖u - (θ / s) • r‖ ^ 2 = _
  rw [norm_sub_sq_real, real_inner_smul_right, inner_right_of_mem_orthogonal hu hr,
    mul_zero, mul_zero, sub_zero, gaussianGramDualColumn_norm_sq Y hY, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  change _ + (θ / s) ^ 2 * s = _
  field_simp
  change (gaussianGram Y)⁻¹ i i * s + θ ^ 2 = s * (gaussianGram Y)⁻¹ i i + θ ^ 2
  ring

end

end SketchOrientation
