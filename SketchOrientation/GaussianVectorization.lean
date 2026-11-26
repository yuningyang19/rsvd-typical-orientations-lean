import SketchOrientation.SpectralCapGaussian
import SketchOrientation.GaussianInput
import SketchOrientation.RandomSignBlockLimit

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix Set

/-- Matrix coordinates of the standard Euclidean space of matrix units. -/
def matrixOfBlockEuclidean {k l : ℕ} (u : EuclideanSpace ℝ (Fin k × Fin l)) :
    Matrix (Fin k) (Fin l) ℝ :=
  Matrix.of fun i j => u (i, j)

theorem continuous_matrixOfBlockEuclidean {k l : ℕ} :
    Continuous (matrixOfBlockEuclidean (k := k) (l := l)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact PiLp.continuous_apply 2 _ (i, j)

private theorem gaussian_coordinate_product_uncurry (k l : ℕ) :
    (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin l => gaussianReal 0 1))).map
      (fun X (p : Fin k × Fin l) => X p.1 p.2) =
      Measure.pi (fun _ : Fin k × Fin l => gaussianReal 0 1) := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hMeas : Measurable (fun (X : Fin k → Fin l → ℝ) (p : Fin k × Fin l) =>
      X p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  rw [Measure.map_apply hMeas (MeasurableSet.pi Set.countable_univ (fun p _ => hs p))]
  have he : (fun (X : Fin k → Fin l → ℝ) (p : Fin k × Fin l) => X p.1 p.2) ⁻¹'
      Set.pi univ s = Set.pi univ (fun i => Set.pi univ (fun j => s (i, j))) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
  rw [he, Measure.pi_pi, Fintype.prod_prod_type]
  simp only [Measure.pi_pi]

/-- The i.i.d. Gaussian matrix is exactly the matrix of coordinates of a
standard Euclidean Gaussian. -/
theorem gaussianRowBlock_eq_map_stdGaussian (k l : ℕ) :
    (gaussianRowBlock k l : Measure (Matrix (Fin k) (Fin l) ℝ)) =
      (stdGaussian (EuclideanSpace ℝ (Fin k × Fin l))).map matrixOfBlockEuclidean := by
  have hRaw : Measurable (fun X : Fin k → Fin l → ℝ => Matrix.of (fun i j => X j i)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply i).comp (measurable_pi_apply j)
  have hFlat : Measurable (fun (X : Fin k → Fin l → ℝ) (p : Fin k × Fin l) => X p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hTo : Measurable (WithLp.toLp 2 : ((Fin k × Fin l) → ℝ) →
      EuclideanSpace ℝ (Fin k × Fin l)) := WithLp.measurable_toLp _ _
  have hMat := (continuous_matrixOfBlockEuclidean (k := k) (l := l)).measurable
  have hT : Measurable (Matrix.transpose : Matrix (Fin l) (Fin k) ℝ → Matrix (Fin k) (Fin l) ℝ) :=
    continuous_id.matrix_transpose.measurable
  change (gaussianMatrixLaw l k).map Matrix.transpose = _
  rw [gaussianMatrixLaw_eq_coordinate_product, Measure.map_map hT hRaw, ← map_pi_eq_stdGaussian,
    ← gaussian_coordinate_product_uncurry k l, Measure.map_map hTo hFlat,
    Measure.map_map hMat (hTo.comp hFlat)]
  rfl

/-- Mapping a finite uniform law applies the same map to every draw. -/
theorem finiteProbabilityLaw_map {A E F : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace E] [MeasurableSpace F] (X : A → E) {f : E → F} (hf : Measurable f) :
    (Edge.Walsh.finiteProbabilityLaw X).map hf.aemeasurable =
      Edge.Walsh.finiteProbabilityLaw (fun a => f (X a)) := by
  apply Subtype.ext
  change (Edge.Walsh.finiteLaw X).map f = Edge.Walsh.finiteLaw (fun a => f (X a))
  ext s hs
  rw [Measure.map_apply hf hs]
  simp only [Edge.Walsh.finiteLaw, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  rfl

end SketchOrientation
