import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

namespace SketchOrientation

open Matrix
open scoped Matrix

variable {ι : Type*}

/-- The entrywise power of a matrix, with the all-ones matrix at degree zero. -/
def schurPower (M : Matrix ι ι ℝ) (q : ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (M i j) ^ q

@[simp] theorem schurPower_apply (M : Matrix ι ι ℝ) (q : ℕ) (i j : ι) :
    schurPower M q i j = (M i j) ^ q := rfl

private theorem schurPower_succ (M : Matrix ι ι ℝ) (q : ℕ) :
    schurPower M (q + 1) = schurPower M q ⊙ M := by
  ext i j
  simp [pow_succ, hadamard_apply]

variable [Fintype ι]

/-- Schur powers of a positive semidefinite matrix are positive semidefinite. -/
theorem posSemidef_schurPower {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (q : ℕ) :
    (schurPower M q).PosSemidef := by
  induction q with
  | zero =>
    classical
    have hc : schurPower M 0 = vecMulVec (fun _ => (1 : ℝ)) (star (fun _ => (1 : ℝ))) := by
      ext i j
      simp [vecMulVec_apply]
    rw [hc]
    exact posSemidef_vecMulVec_self_star _
  | succ q ih =>
    rw [schurPower_succ]
    exact ih.hadamard hM

/-- For a positive semidefinite Gram kernel, compressing every factor costs
no more than compressing its first factor. This is the Schur-product form of
the degree-by-degree comparison in Lemma 3.2. -/
theorem posSemidef_schurPower_compress_first {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : (A - B).PosSemidef) (q : ℕ) :
    ((schurPower A q ⊙ B) - schurPower B (q + 1)).PosSemidef := by
  induction q with
  | zero =>
    have hc : (schurPower A 0 ⊙ B) - schurPower B (0 + 1) = 0 := by
      ext i j
      simp [hadamard_apply]
    rw [hc]
    exact Matrix.PosSemidef.zero
  | succ q ih =>
    have he :
        (schurPower A (q + 1) ⊙ B) - schurPower B (q + 1 + 1) =
          ((schurPower A q ⊙ B) - schurPower B (q + 1)) ⊙ B +
            (schurPower A q ⊙ B) ⊙ (A - B) := by
      ext i j
      simp only [schurPower_apply, hadamard_apply, Matrix.add_apply, Matrix.sub_apply, pow_succ]
      ring
    rw [he]
    exact (ih.hadamard hB).add ((posSemidef_schurPower hA q |>.hadamard hB).hadamard hAB)

end SketchOrientation
