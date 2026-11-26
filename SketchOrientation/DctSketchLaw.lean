import SketchOrientation.PairedDct
import SketchOrientation.GaussianMatrixSpace
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace SketchOrientation

open Matrix MeasureTheory

/-- The ordered row sample and the two independent arrays of fair signs. -/
abbrev DctDraw (n l : ℕ) := (Fin l ↪ Fin n) × (Fin n → Bool) × (Fin n → Bool)

inductive DctPasses
  | one
  | two

/-- Boolean coordinate of a fair Rademacher sign. -/
noncomputable def rademacherValue (b : Bool) : ℝ := if b then 1 else -1

/-- Actual one- and two-pass DCT sketches driven by an independent finite draw. -/
noncomputable def DctPasses.sketch {n l : ℕ} (mode : DctPasses) (draw : DctDraw n l) :
    Matrix (Fin n) (Fin l) ℝ :=
  match mode with
  | .one => onePassDct draw.1 (rademacherValue ∘ draw.2.1)
  | .two => twoPassDct draw.1 (rademacherValue ∘ draw.2.1) (rademacherValue ∘ draw.2.2)

/-- The law assigns the same weight to each ordered choice of distinct
rows and each of the two sign arrays. One pass ignores the second array. -/
noncomputable def DctPasses.sketchPMF {n l : ℕ} (mode : DctPasses) (h : l ≤ n) :
    PMF (Matrix (Fin n) (Fin l) ℝ) := by
  classical
  letI : Nonempty (DctDraw n l) :=
    ⟨(Fin.castLEEmb h, fun _ => false, fun _ => false)⟩
  exact (PMF.uniformOfFintype (DctDraw n l)).map mode.sketch

noncomputable def DctPasses.sketchLaw {n l : ℕ} (mode : DctPasses) (h : l ≤ n) :
    ProbabilityMeasure (Matrix (Fin n) (Fin l) ℝ) :=
  ⟨(mode.sketchPMF h).toMeasure, inferInstance⟩

theorem rowSelector_orthonormal {n l : ℕ} (rows : Fin l ↪ Fin n) :
    rowSelector rows * (rowSelector rows)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [transpose_apply, rowSelector]
  rw [Finset.sum_eq_single (rows i)]
  · simp [Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem rademacherDiagonal_orthogonal {n : ℕ} (signs : Fin n → Bool) :
    diagonal (rademacherValue ∘ signs) * (diagonal (rademacherValue ∘ signs))ᵀ = 1 := by
  have h (i : Fin n) : rademacherValue (signs i) * rademacherValue (signs i) = 1 := by
    cases signs i <;> norm_num [rademacherValue]
  rw [diagonal_transpose, diagonal_mul_diagonal]
  simp [h]

private theorem rowOrthonormal_mul {n l : ℕ} (A : Matrix (Fin l) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q * Qᵀ = 1) :
    (A * Q) * (A * Q)ᵀ = A * Aᵀ := by
  rw [transpose_mul, Matrix.mul_assoc A, ← Matrix.mul_assoc Q, hQ, Matrix.one_mul]

/-- Both sketch models have orthonormal columns on every draw. -/
theorem DctPasses.sketch_orthonormal {n l : ℕ} (mode : DctPasses) (draw : DctDraw n l) :
    (mode.sketch draw)ᵀ * mode.sketch draw = 1 := by
  have hF : pairedDctII n * (pairedDctII n)ᵀ = 1 := by
    simpa only [pairedDctII, transpose_transpose] using cosineCore_transpose_mul n
  cases mode
  · simp only [DctPasses.sketch, onePassDct, transpose_transpose]
    rw [rowOrthonormal_mul _ _ (rademacherDiagonal_orthogonal _),
      rowOrthonormal_mul _ _ hF, rowSelector_orthonormal]
  · simp only [DctPasses.sketch, twoPassDct, transpose_transpose]
    rw [rowOrthonormal_mul _ _ (rademacherDiagonal_orthogonal _),
      rowOrthonormal_mul _ _ hF, rowOrthonormal_mul _ _ (rademacherDiagonal_orthogonal _),
      rowOrthonormal_mul _ _ hF, rowSelector_orthonormal]

end SketchOrientation
