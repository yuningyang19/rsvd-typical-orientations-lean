import TypicalOrientations.RotationProduct
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic

namespace TypicalOrientations

open Matrix MvPolynomial

noncomputable section

abbrev RotationCoordinate (n : ℕ) := Fin n × Fin n
abbrev RotationPolynomial (n : ℕ) := MvPolynomial (RotationCoordinate n) ℝ

variable {n : ℕ}

/-- Evaluate a polynomial in the matrix entries. -/
def rotationEval (p : RotationPolynomial n) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  p.eval fun ij => A ij.1 ij.2

/-- Polynomial substitution for the entries of A L. -/
def rightVectorComponent (L : Matrix (Fin n) (Fin n) ℝ) (ij : RotationCoordinate n) :
    RotationPolynomial n :=
  ∑ j, X (ij.1, j) * C (L j ij.2)

theorem rotationEval_rightVectorComponent (L A : Matrix (Fin n) (Fin n) ℝ)
    (ij : RotationCoordinate n) :
    rotationEval (rightVectorComponent L ij) A = (A * L) ij.1 ij.2 := by
  simp [rotationEval, rightVectorComponent, Matrix.mul_apply]

/-- The formal derivation differentiating along the matrix field A ↦ A L. -/
def polynomialDirection (L : Matrix (Fin n) (Fin n) ℝ) :
    Derivation ℝ (RotationPolynomial n) (RotationPolynomial n) :=
  MvPolynomial.mkDerivation ℝ (rightVectorComponent L)

@[simp] theorem polynomialDirection_X (L : Matrix (Fin n) (Fin n) ℝ)
    (ij : RotationCoordinate n) : polynomialDirection L (X ij) = rightVectorComponent L ij := by
  exact MvPolynomial.mkDerivation_X _ _ _

private def derivationAt (p : RotationPolynomial n) :
    Derivation ℝ (RotationPolynomial n) (RotationPolynomial n) →ₗ[ℝ] RotationPolynomial n where
  toFun D := D p
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem polynomialDirection_eq_sum (L : Matrix (Fin n) (Fin n) ℝ)
    (p : RotationPolynomial n) :
    polynomialDirection L p = ∑ ij, rightVectorComponent L ij * MvPolynomial.pderiv ij p := by
  classical
  let D (ij : RotationCoordinate n) : Derivation ℝ (RotationPolynomial n) (RotationPolynomial n) := rightVectorComponent L ij • MvPolynomial.pderiv ij
  have he (q : RotationPolynomial n) : (∑ ij : RotationCoordinate n, D ij) q = ∑ ij : RotationCoordinate n, rightVectorComponent L ij * pderiv ij q :=
    map_sum (derivationAt q) D _
  have h : polynomialDirection L = ∑ ij, D ij := by
    apply MvPolynomial.derivation_ext
    intro ij
    rw [polynomialDirection_X, he]
    simp [MvPolynomial.pderiv_X, Pi.single_apply]
  rw [h, he]

theorem rotationEval_continuous (p : RotationPolynomial n) : Continuous (rotationEval p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : (rotationEval (n := n) (C a)) = fun _ => a := funext fun A => by simp [rotationEval]
    rw [h]
    exact continuous_const
  | add p q hp hq =>
    have h : rotationEval (p + q) = (fun A => rotationEval p A + rotationEval q A) :=
      funext fun _ => map_add _ _ _
    rw [h]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A i.1 i.2) :=
      continuous_id.matrix_elem _ _
    have h : rotationEval (p * X i) = fun A => rotationEval p A * A i.1 i.2 := by
      funext A
      simp [rotationEval]
    rw [h]
    exact hp.mul hi

/-- Chain rule for a polynomial along a curve whose entry derivatives at
the current matrix are the entries of A L. -/
theorem rotationEval_hasDerivAt (p : RotationPolynomial n)
    (L : Matrix (Fin n) (Fin n) ℝ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) ((A t * L) i j) t) :
    HasDerivAt (fun s => rotationEval p (A s))
      (rotationEval (polynomialDirection L p) (A t)) t := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [rotationEval, eval_C, MvPolynomial.derivation_C, map_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    have h := hp.add hq
    change HasDerivAt (fun s => rotationEval p (A s) + rotationEval q (A s)) _ _ at h
    simpa only [rotationEval, map_add] using h
  | mul_X p ij hp =>
    have h := hp.mul (hA ij.1 ij.2)
    change HasDerivAt (fun s => rotationEval p (A s) * A s ij.1 ij.2) _ _ at h
    have hd : rotationEval (polynomialDirection L (p * X ij)) (A t) =
        rotationEval (polynomialDirection L p) (A t) * A t ij.1 ij.2 +
          rotationEval p (A t) * (A t * L) ij.1 ij.2 := by
      rw [Derivation.leibniz, polynomialDirection_X, ← rotationEval_rightVectorComponent]
      simp [rotationEval, smul_eq_mul, mul_comm, add_comm]
    rw [hd]
    simpa [rotationEval] using h

theorem polynomialDirection_add (L K : Matrix (Fin n) (Fin n) ℝ) :
    polynomialDirection (L + K) = polynomialDirection L + polynomialDirection K := by
  apply MvPolynomial.derivation_ext
  intro ij
  simp [rightVectorComponent, mul_add, Finset.sum_add_distrib]

theorem polynomialDirection_smul (a : ℝ) (L : Matrix (Fin n) (Fin n) ℝ) :
    polynomialDirection (a • L) = a • polynomialDirection L := by
  apply MvPolynomial.derivation_ext
  intro ij
  simp only [polynomialDirection_X, Derivation.smul_apply, rightVectorComponent, Matrix.smul_apply,
    smul_eq_mul, MvPolynomial.C_mul, ← C_mul']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pderiv_totalDegree_add_one_le {p : RotationPolynomial n}
    (i : RotationCoordinate n) (h : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  obtain ⟨s, hs, htotal⟩ := Finset.exists_mem_eq_sup _ (MvPolynomial.support_nonempty.mpr h)
    (fun s => s.sum fun _ e => e)
  change (MvPolynomial.pderiv i p).totalDegree = (s.sum fun _ e => e) at htotal
  have hNZ : coeff s (MvPolynomial.pderiv i p) ≠ 0 := mem_support_iff.mp hs
  rw [MvPolynomial.coeff_pderiv] at hNZ
  have hPS : s + Finsupp.single i 1 ∈ p.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hNZ)
  have hLe := MvPolynomial.le_totalDegree hPS
  rw [Finsupp.sum_add_index'] at hLe
  · simpa [htotal] using hLe
  · intro
    rfl
  · intros
    rfl

theorem rightVectorComponent_totalDegree (L : Matrix (Fin n) (Fin n) ℝ)
    (i : RotationCoordinate n) : (rightVectorComponent L i).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem polynomialDirection_totalDegree (L : Matrix (Fin n) (Fin n) ℝ)
    (p : RotationPolynomial n) : (polynomialDirection L p).totalDegree ≤ p.totalDegree := by
  rw [polynomialDirection_eq_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  by_cases h : MvPolynomial.pderiv i p = 0
  · simp [h]
  · have h1 := rightVectorComponent_totalDegree L i
    have h2 := pderiv_totalDegree_add_one_le i h
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

/-- Pullback of a Grassmannian polynomial along A ↦ A P Aᵀ. -/
def polynomialOrbit {l : ℕ} (P : SketchOrientation.OrthogonalProjector n l)
    (p : RotationPolynomial n) : RotationPolynomial n :=
  MvPolynomial.aeval (fun ij : RotationCoordinate n =>
    ∑ j, ∑ k, (X (ij.1, j) * C (P.val j k)) * X (ij.2, k)) p

theorem rotationEval_polynomialOrbit {l : ℕ} (P : SketchOrientation.OrthogonalProjector n l)
    (p : RotationPolynomial n) (A : Matrix (Fin n) (Fin n) ℝ) :
    rotationEval (polynomialOrbit P p) A = rotationEval p (A * P.val * Aᵀ) := by
  let f : RotationCoordinate n → RotationPolynomial n := fun ij =>
    ∑ j, ∑ k, (X (ij.1, j) * C (P.val j k)) * X (ij.2, k)
  let g : RotationCoordinate n → ℝ := fun ij => A ij.1 ij.2
  let h : RotationCoordinate n → ℝ := fun ij => (A * P.val * Aᵀ) ij.1 ij.2
  change ((MvPolynomial.aeval g).comp (MvPolynomial.aeval f)) p = MvPolynomial.aeval h p
  have hComp : (MvPolynomial.aeval g).comp (MvPolynomial.aeval f) = MvPolynomial.aeval h := by
    ext ij
    simp [f, g, h, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hComp]

end

end TypicalOrientations
