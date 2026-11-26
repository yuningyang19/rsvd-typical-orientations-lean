import SketchOrientation.GaussianOrientationNorm
import SketchOrientation.DctSampleCovariance

namespace SketchOrientation

open MeasureTheory Matrix Filter Unitary
open scoped InnerProductSpace Topology

variable {n l : ℕ}

/-- The overlap of two sketch spaces is the squared Frobenius norm of
their cross-frame Gram matrix. -/
theorem projector_overlap_eq_squaredFrobenius (P Q : OrthogonalProjector n l)
    (U W : Matrix (Fin n) (Fin l) ℝ) (hP : U * Uᵀ = P.val)
    (hQ : W * Wᵀ = Q.val) :
    (P.val * Q.val).trace = squaredFrobenius (Uᵀ * W) := by
  rw [← hP, ← hQ]
  unfold squaredFrobenius
  rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, Matrix.mul_assoc,
    trace_mul_comm Wᵀ]
  simp only [Matrix.mul_assoc]

/-- The mean projector has trace equal to the fixed sketch width. -/
theorem trace_meanSketchProjector (ν : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure ν] : (meanSketchProjector ν).trace = l := by
  change (∑ i : Fin n, ∫ P : OrthogonalProjector n l, P.val i i ∂ν) = _
  rw [← integral_finsetSum _ (fun i _ => integrable_sketchProjector_entry ν i i)]
  have he (P : OrthogonalProjector n l) : (∑ i : Fin n, P.val i i) = (l : ℝ) := by
    change P.val.trace = _
    rw [← rangeProjector_of_projector P.val P.property.1 P.property.2.1,
      trace_rangeProjector, P.property.2.2]
  simp_rw [he]
  simp

/-- Two independently drawn sketch spaces have mean overlap
`tr((E P)^2)`, including discrete projector laws. -/
theorem mean_independentProjector_overlap (ν : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure ν] :
    (∫ z, (z.1.val * z.2.val).trace ∂ν.prod ν) =
      (meanSketchProjector ν * meanSketchProjector ν).trace := by
  change (∫ z : OrthogonalProjector n l × OrthogonalProjector n l,
    ∑ i : Fin n, ∑ j : Fin n, z.1.val i j * z.2.val j i ∂ν.prod ν) = _
  have hI (i j : Fin n) : Integrable (fun z : OrthogonalProjector n l × OrthogonalProjector n l =>
      z.1.val i j * z.2.val j i) (ν.prod ν) :=
    (integrable_sketchProjector_entry ν i j).mul_prod (integrable_sketchProjector_entry ν j i)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  change _ = ∑ i : Fin n, ∑ j : Fin n, (meanSketchProjector ν) i j * (meanSketchProjector ν) j i
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_prod_mul (fun P : OrthogonalProjector n l => P.val i j)
    (fun P : OrthogonalProjector n l => P.val j i)

private theorem meanSketchProjector_posSemidef (ν : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure ν] : (meanSketchProjector ν).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · exact (conjTranspose_eq_transpose_of_trivial _).trans (meanSketchProjector_transpose ν)
  · intro x
    have hr := meanSketchProjector_inner ν (WithLp.toLp 2 x)
    have h0 : 0 ≤ ∫ P, ‖(orientationRowSpace P).starProjection (WithLp.toLp 2 x)‖ ^ 2 ∂ν :=
      integral_nonneg fun _ => sq_nonneg _
    rw [← hr, EuclideanSpace.inner_eq_star_dotProduct] at h0
    simpa [dotProduct_comm] using h0

private theorem euclidean_opNorm_sq_le_frob (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖M.toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤ squaredFrobenius M := by
  let T := M.toEuclideanLin.toContinuousLinearMap
  have hnn := squaredFrobenius_nonneg M
  suffices h : ‖T‖ ≤ Real.sqrt (squaredFrobenius M) by
    calc
      ‖T‖ ^ 2 ≤ Real.sqrt (squaredFrobenius M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h _
      _ = _ := Real.sq_sqrt hnn
  apply T.opNorm_le_bound (Real.sqrt_nonneg _)
  intro u
  apply le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (by positivity)
  rw [mul_pow, Real.sq_sqrt hnn, PiLp.norm_sq_eq_of_L2 _ (T u), PiLp.norm_sq_eq_of_L2 _ u,
    Cosine.squaredFrobenius_eq_sum_entries, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simpa [T, Matrix.toLpLin_apply, Matrix.mulVec_apply, dotProduct, Real.norm_eq_abs, sq_abs] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) (fun j => u j)

/-- The squared diffuseness and width times diffuseness are the lower
and upper bounds for the independent mean overlap. -/
theorem mean_independentProjector_overlap_bounds (ν : Measure (OrthogonalProjector n l))
    [IsProbabilityMeasure ν] :
    let ρ := ‖(meanSketchProjector ν).toEuclideanLin.toContinuousLinearMap‖
    ρ ^ 2 ≤ (∫ z, (z.1.val * z.2.val).trace ∂ν.prod ν) ∧
      (∫ z, (z.1.val * z.2.val).trace ∂ν.prod ν) ≤ (l : ℝ) * ρ := by
  intro ρ
  let M := meanSketchProjector ν
  let T := M.toEuclideanLin.toContinuousLinearMap
  have hM := meanSketchProjector_posSemidef ν
  have hs := hM.isHermitian
  rw [mean_independentProjector_overlap ν]
  change ‖T‖ ^ 2 ≤ (M * M).trace ∧ (M * M).trace ≤ (l : ℝ) * ‖T‖
  constructor
  · simpa only [squaredFrobenius, M, meanSketchProjector_transpose] using euclidean_opNorm_sq_le_frob M
  · let ev := hs.eigenvalues
    have hEig (i : Fin n) : ev i ≤ ‖T‖ := by
      let u := hs.eigenvectorBasis i
      have he : T u = ev i • u := by
        apply WithLp.ofLp_injective 2
        exact hs.mulVec_eigenvectorBasis i
      have hu : ‖u‖ = 1 := hs.eigenvectorBasis.orthonormal.norm_eq_one i
      have hn : 0 ≤ ev i := hM.eigenvalues_nonneg i
      simpa only [he, norm_smul, Real.norm_of_nonneg hn, hu, mul_one] using
        T.le_opNorm u
    have htrace : ∑ i, ev i = (l : ℝ) :=
      hs.trace_eq_sum_eigenvalues.symm.trans (trace_meanSketchProjector ν)
    have htrace₂ : (M * M).trace = ∑ i, (ev i)^2 := by
      let U := hs.eigenvectorUnitary
      let C := conjStarAlgAut ℝ _ U
      have hd : M = C (diagonal ev) := hs.spectral_theorem
      calc
        (M * M).trace = (C (diagonal (fun i => ev i * ev i))).trace := by
          rw [← diagonal_mul_diagonal, map_mul, ← hd]
        _ = _ := by
          rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul, trace_diagonal]
          simp only [pow_two]
    rw [htrace₂, ← htrace, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (hEig i) (hM.eigenvalues_nonneg i)

/-- At fixed width, diffuseness is equivalent to vanishing mean overlap
of two independent draws. -/
theorem mean_independentProjector_overlap_tendsto_iff (n : ℕ → ℕ)
    (ν : ∀ i, Measure (OrthogonalProjector (n i) l)) [∀ i, IsProbabilityMeasure (ν i)] :
    Tendsto (fun i => ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖) atTop (𝓝 0) ↔
      Tendsto (fun i => ∫ z, (z.1.val * z.2.val).trace ∂(ν i).prod (ν i)) atTop (𝓝 0) := by
  let ρ (i : ℕ) := ‖(meanSketchProjector (ν i)).toEuclideanLin.toContinuousLinearMap‖
  let E (i : ℕ) := ∫ z, (z.1.val * z.2.val).trace ∂(ν i).prod (ν i)
  have hb (i : ℕ) : ρ i ^ 2 ≤ E i ∧ E i ≤ (l : ℝ) * ρ i :=
    mean_independentProjector_overlap_bounds (ν i)
  constructor
  · intro h
    change Tendsto ρ atTop (𝓝 0) at h
    exact squeeze_zero (fun i => (sq_nonneg (ρ i)).trans (hb i).1) (fun i => (hb i).2)
      (by simpa only [mul_zero] using h.const_mul (l : ℝ))
  · intro h
    change Tendsto E atTop (𝓝 0) at h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    apply squeeze_zero (g := fun i => Real.sqrt (E i)) (fun i => norm_nonneg _) _ ?_
    · intro i
      exact Real.le_sqrt_of_sq_le (hb i).1
    · simpa only [Function.comp_def, Real.sqrt_zero] using hs

end SketchOrientation
