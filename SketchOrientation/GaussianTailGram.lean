import SketchOrientation.GaussianVectorization
import SketchOrientation.GaussianOrthogonal
import Mathlib.Probability.ProductMeasure
import SketchOrientation.StandardGaussianMoments
import SketchOrientation.DctSampleCovariance

namespace SketchOrientation

open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal

noncomputable section

private abbrev scalarGaussian : Measure ℝ := gaussianReal 0 1

private theorem gaussianRows_flatten {I J : Type*} [Fintype I] [Fintype J] :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : J => scalarGaussian))).map
      (fun X (p : I × J) => X p.1 p.2) =
      Measure.pi (fun _ : I × J => scalarGaussian) := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hM : Measurable (fun (X : I → J → ℝ) (p : I × J) => X p.1 p.2) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  rw [Measure.map_apply hM (MeasurableSet.pi Set.countable_univ (fun p _ => hs p))]
  have he : (fun (X : I → J → ℝ) (p : I × J) => X p.1 p.2) ⁻¹'
      Set.pi univ s = Set.pi univ (fun i => Set.pi univ (fun j => s (i, j))) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
  rw [he, Measure.pi_pi, Fintype.prod_prod_type]
  simp only [Measure.pi_pi]

private theorem gaussianColumns_flatten (d k : ℕ) :
    (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => scalarGaussian))).map
      (fun X (p : Fin d × Fin k) => X p.2 p.1) =
      Measure.pi (fun _ : Fin d × Fin k => scalarGaussian) := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hM : Measurable (fun (X : Fin k → Fin d → ℝ) (p : Fin d × Fin k) => X p.2 p.1) :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)
  rw [Measure.map_apply hM (MeasurableSet.pi Set.countable_univ (fun p _ => hs p))]
  have he : (fun (X : Fin k → Fin d → ℝ) (p : Fin d × Fin k) => X p.2 p.1) ⁻¹'
      Set.pi univ s = Set.pi univ (fun j => Set.pi univ (fun i => s (i, j))) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    exact forall_comm
  rw [he, Measure.pi_pi, Fintype.prod_prod_type]
  simp only [Measure.pi_pi]
  exact Finset.prod_comm

/-- The primitive Gaussian matrix has independent rows with independent
standard real Gaussian entries in each row. -/
theorem gaussianMatrixLaw_eq_row_product (d k : ℕ) :
    gaussianMatrixLaw d k = Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin k => gaussianReal 0 1)) := by
  let f (Y : Fin d × Fin k → ℝ) : Matrix (Fin d) (Fin k) ℝ := Matrix.of (fun i j => Y (i,j))
  let col (X : Fin k → Fin d → ℝ) (p : Fin d × Fin k) := X p.2 p.1
  let row (X : Fin d → Fin k → ℝ) (p : Fin d × Fin k) := X p.1 p.2
  have hf : Measurable f := measurable_pi_iff.mpr fun i =>
    measurable_pi_iff.mpr fun j => measurable_pi_apply (i,j)
  have hc : Measurable col := measurable_pi_iff.mpr fun p =>
    (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)
  have hr : Measurable row := measurable_pi_iff.mpr fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  rw [gaussianMatrixLaw_eq_coordinate_product]
  change (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => scalarGaussian))).map
    (f ∘ col) = _
  rw [← Measure.map_map hf hc, show _ = _ from gaussianColumns_flatten d k,
    ← gaussianRows_flatten (I := Fin d) (J := Fin k), Measure.map_map hf hr]
  change Measure.map id _ = _
  exact @Measure.map_id (Matrix (Fin d) (Fin k) ℝ) _ _

private theorem gaussianRow_pair (a b : Fin k) (h : a ≠ b) :
    IndepFun (fun X : Fin k → ℝ => X a) (fun X : Fin k → ℝ => X b)
      (Measure.pi (fun _ : Fin k => scalarGaussian)) :=
  (iIndepFun_pi (μ := fun _ : Fin k => scalarGaussian)
    (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun h

private theorem gaussianRow_integral_coord (a : Fin k) (p : ℕ) :
    (∫ X : Fin k → ℝ, X a ^ p ∂Measure.pi (fun _ : Fin k => scalarGaussian)) =
    ∫ x, x ^ p ∂scalarGaussian := by
  exact integral_comp_eval (μ := fun _ : Fin k => scalarGaussian) (i := a)
    (show Measurable (fun x : ℝ => x ^ p) by fun_prop).aestronglyMeasurable

private theorem gaussianRow_integrable_coord (a : Fin k) (p : ℕ) :
    Integrable (fun X : Fin k → ℝ => X a ^ p) (Measure.pi (fun _ : Fin k => scalarGaussian)) :=
  (measurePreserving_eval (fun _ : Fin k => scalarGaussian) a).integrable_comp_of_integrable
    (standardGaussian_power_integrable p)

private theorem gaussianRow_product_memLp (a b : Fin k) :
    MemLp (fun X : Fin k → ℝ => X a * X b) 2 (Measure.pi (fun _ : Fin k => scalarGaussian)) := by
  apply (memLp_two_iff_integrable_sq
    (((measurable_pi_apply a).mul (measurable_pi_apply b)).aestronglyMeasurable)).2
  have h (c : Fin k) : MemLp (fun X : Fin k → ℝ => X c ^ 2) 2
      (Measure.pi (fun _ : Fin k => scalarGaussian)) := by
    apply (memLp_two_iff_integrable_sq
      ((measurable_pi_apply c).pow_const (2 : ℕ)).aestronglyMeasurable).2
    simpa only [← pow_mul] using gaussianRow_integrable_coord c 4
  simpa only [mul_pow, Pi.mul_def] using (h a).integrable_mul (h b)

private theorem gaussianRow_product_mean (a b : Fin k) :
    (∫ X : Fin k → ℝ, X a * X b ∂Measure.pi (fun _ : Fin k => scalarGaussian)) =
       if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    rw [if_pos rfl, ← show (fun X : Fin k → ℝ => X a ^ 2) = (fun X => X a * X a) from
      funext fun X => pow_two _, gaussianRow_integral_coord, standardGaussian_second_moment]
  · rw [if_neg h]
    change (∫ X : Fin k → ℝ, ((fun Y : Fin k → ℝ => Y a) * (fun Y : Fin k → ℝ => Y b)) X ∂
      Measure.pi (fun _ : Fin k => scalarGaussian)) = 0
    rw [(gaussianRow_pair a b h).integral_mul_eq_mul_integral
      (measurable_pi_apply a).aestronglyMeasurable (measurable_pi_apply b).aestronglyMeasurable]
    have hz (i : Fin k) :
        (∫ X : Fin k → ℝ, X i ∂Measure.pi (fun _ : Fin k => scalarGaussian)) = 0 := by
      simpa using (gaussianRow_integral_coord i 1).trans (by simp [scalarGaussian])
    rw [hz, zero_mul]

private theorem gaussianRow_product_variance (a b : Fin k) :
    Var[fun X : Fin k → ℝ => X a * X b; Measure.pi (fun _ : Fin k => scalarGaussian)] =
       if a = b then 2 else 1 := by
  classical
  rw [variance_eq_sub (gaussianRow_product_memLp a b), gaussianRow_product_mean]
  simp only [Pi.pow_apply]
  by_cases h : a = b
  · subst b
    have he : (fun X : Fin k → ℝ => (X a * X a)^2) = fun X => X a ^ 4 := by
      funext X
      ring
    rw [if_pos rfl, he, gaussianRow_integral_coord, standardGaussian_fourth_moment]
    norm_num
  · simp only [if_neg h, mul_pow]
    have hp : IndepFun (fun X : Fin k → ℝ => X a ^ 2) (fun X : Fin k → ℝ => X b ^ 2)
        (Measure.pi (fun _ : Fin k => scalarGaussian)) :=
      (gaussianRow_pair a b h).comp
        (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2) (by fun_prop) (by fun_prop)
    change (∫ X : Fin k → ℝ, ((fun Y : Fin k → ℝ => Y a ^ 2) * (fun Y : Fin k → ℝ => Y b ^ 2)) X ∂
      Measure.pi (fun _ : Fin k => scalarGaussian)) - 0 ^ 2 = 1
    rw [hp.integral_mul_eq_mul_integral
      ((measurable_pi_apply a).pow_const (2 : ℕ)).aestronglyMeasurable
      ((measurable_pi_apply b).pow_const (2 : ℕ)).aestronglyMeasurable,
      gaussianRow_integral_coord, gaussianRow_integral_coord, standardGaussian_second_moment]
    norm_num

/-- The unscaled Gaussian compression in the paper's tail Gram estimate. -/
def gaussianCompressedGram {d k : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (G : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ := Gᵀ * K * G

theorem gaussianCompressedGram_diagonal_apply {d k : ℕ} (w : Fin d → ℝ)
    (G : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k) :
    gaussianCompressedGram (diagonal w) G a b = ∑ i, w i * (G i a * G i b) := by
  unfold gaussianCompressedGram
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem gaussianDiag_moment_entry {d k : ℕ} (w : Fin d → ℝ) (a b : Fin k) :
    MemLp (fun G => gaussianCompressedGram (diagonal w) G a b) 2 (gaussianMatrixLaw d k) ∧
    (∫ G, gaussianCompressedGram (diagonal w) G a b ∂gaussianMatrixLaw d k) =
      (∑ i, w i) * (if a = b then 1 else 0) ∧
    Var[fun G => gaussianCompressedGram (diagonal w) G a b; gaussianMatrixLaw d k] =
      (∑ i, w i ^ 2) * (if a = b then 2 else 1) := by
  classical
  let μ := fun _ : Fin d => Measure.pi (fun _ : Fin k => scalarGaussian)
  let f (i : Fin d) (x : Fin k → ℝ) := w i * (x a * x b)
  have hLp (i : Fin d) : MemLp (f i) 2 (μ i) :=
    (gaussianRow_product_memLp a b).const_mul (w i)
  have hF (i : Fin d) : MemLp (fun G : Fin d → Fin k → ℝ => f i (G i)) 2 (Measure.pi μ) :=
    (hLp i).comp_measurePreserving (measurePreserving_eval μ i)
  have he (G : Fin d → Fin k → ℝ) :
      gaussianCompressedGram (diagonal w) (Matrix.of G) a b = ∑ i, f i (G i) :=
    gaussianCompressedGram_diagonal_apply w (Matrix.of G) a b
  rw [gaussianMatrixLaw_eq_row_product]
  change MemLp (fun G : Fin d → Fin k → ℝ => gaussianCompressedGram (diagonal w) (Matrix.of G) a b)
      2 (Measure.pi μ) ∧
    (∫ G : Fin d → Fin k → ℝ, gaussianCompressedGram (diagonal w) (Matrix.of G) a b ∂Measure.pi μ) =
      (∑ i, w i) * (if a = b then 1 else 0) ∧
    Var[fun G : Fin d → Fin k → ℝ => gaussianCompressedGram (diagonal w) (Matrix.of G) a b; Measure.pi μ] =
      (∑ i, w i ^ 2) * (if a = b then 2 else 1)
  simp only [he]
  refine ⟨memLp_finsetSum _ (fun i _ => hF i), ?_, ?_⟩
  · rw [integral_finsetSum _ (fun i _ => (hF i).integrable (by norm_num))]
    simp_rw [show ∀ i, (∫ G : Fin d → Fin k → ℝ, f i (G i) ∂Measure.pi μ) =
      ∫ x, f i x ∂μ i from fun i => integral_comp_eval (hLp i).aestronglyMeasurable]
    simp_rw [f, μ, integral_const_mul, gaussianRow_product_mean, Finset.sum_mul]
  · have heq : (fun G : Fin d → Fin k → ℝ => ∑ i, f i (G i)) =
        ∑ i, (fun G : Fin d → Fin k → ℝ => f i (G i)) := by
      funext G
      simp only [Finset.sum_apply]
    rw [heq, variance_sum_pi (μ := μ) (X := f) hLp]
    simp_rw [f, μ, variance_const_mul, gaussianRow_product_variance, Finset.sum_mul]

private theorem gaussianDiag_centered_moment_entry {d k : ℕ} (w : Fin d → ℝ) (a b : Fin k) :
    let X := fun G => (gaussianCompressedGram (diagonal w) G -
      (∑ i, w i) • (1 : Matrix (Fin k) (Fin k) ℝ)) a b ^ 2
    Integrable X (gaussianMatrixLaw d k) ∧
    (∫ G, X G ∂gaussianMatrixLaw d k) = (∑ i, w i ^ 2) * (if a = b then 2 else 1) := by
  classical
  obtain ⟨hLp, hMean, hVar⟩ := gaussianDiag_moment_entry w a b
  rw [variance_eq_integral hLp.aemeasurable, hMean] at hVar
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  exact ⟨(memLp_two_iff_integrable_sq
      (hLp.sub (memLp_const ((∑ i, w i) * (if a = b then 1 else 0)))).aestronglyMeasurable).1
      (hLp.sub (memLp_const _)), hVar⟩

/-- Exact trace and squared Frobenius moments for a Gaussian compression of
a diagonal matrix. These include the diagonal variance two and off-diagonal
variance one per unit squared eigenvalue. -/
theorem gaussianDiagGram_moments {d k : ℕ} (w : Fin d → ℝ) :
    Integrable (fun G => squaredFrobenius (gaussianCompressedGram (diagonal w) G -
        (∑ i, w i) • (1 : Matrix (Fin k) (Fin k) ℝ))) (gaussianMatrixLaw d k) ∧
    (∫ G, squaredFrobenius (gaussianCompressedGram (diagonal w) G -
        (∑ i, w i) • (1 : Matrix (Fin k) (Fin k) ℝ)) ∂gaussianMatrixLaw d k) =
      (k : ℝ) * ((k : ℝ) + 1) * (∑ i, w i ^ 2) ∧
    Integrable (fun G => (gaussianCompressedGram (diagonal w) G).trace) (gaussianMatrixLaw d k) ∧
    (∫ G, (gaussianCompressedGram (diagonal w) G).trace ∂gaussianMatrixLaw d k) = (k : ℝ) * ∑ i, w i := by
  classical
  let μ := gaussianMatrixLaw d k
  let f (G : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k) :=
    (gaussianCompressedGram (diagonal w) G - (∑ i, w i) • (1 : Matrix (Fin k) (Fin k) ℝ)) a b ^ 2
  have hf (a b : Fin k) : Integrable (fun G => f G a b) μ :=
    (gaussianDiag_centered_moment_entry w a b).1
  have hsum (a : Fin k) : Integrable (fun G => ∑ b, f G a b) μ :=
    integrable_finsetSum _ (fun b _ => hf a b)
  have ht (a : Fin k) : Integrable (fun G => gaussianCompressedGram (diagonal w) G a a) μ :=
    (gaussianDiag_moment_entry w a a).1.integrable (by norm_num)
  simp only [Cosine.squaredFrobenius_eq_sum_entries, Matrix.trace, Matrix.diag]
  change Integrable (fun G => ∑ a, ∑ b, f G a b) μ ∧
    (∫ G, ∑ a, ∑ b, f G a b ∂μ) = _ ∧
    Integrable (fun G => ∑ a, gaussianCompressedGram (diagonal w) G a a) μ ∧
    (∫ G, ∑ a, gaussianCompressedGram (diagonal w) G a a ∂μ) = _
  refine ⟨integrable_finsetSum _ (fun a _ => hsum a), ?_,
    integrable_finsetSum _ (fun a _ => ht a), ?_⟩
  · rw [integral_finsetSum _ (fun a _ => hsum a)]
    simp_rw [integral_finsetSum _ (fun b _ => hf _ b)]
    change (∑ a : Fin k, ∑ b : Fin k, ∫ G, f G a b ∂μ) = _
    simp_rw [show ∀ a b, (∫ G, f G a b ∂μ) =
      (∑ i, w i ^ 2) * (if a = b then 2 else 1) from
        fun a b => (gaussianDiag_centered_moment_entry w a b).2]
    have hrow (a : Fin k) : (∑ b : Fin k, (if a = b then (2 : ℝ) else 1)) = (k : ℝ) + 1 := by
      simp_rw [show ∀ b : Fin k, (if a = b then (2 : ℝ) else 1) =
        1 + (if b = a then 1 else 0) from fun b => by
          by_cases h : a = b
          · subst b
            norm_num
          · simp [h, Ne.symm h]]
      simp [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum, hrow]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · rw [integral_finsetSum _ (fun a _ => ht a)]
    simp_rw [show ∀ a : Fin k,
      (∫ G, gaussianCompressedGram (diagonal w) G a a ∂μ) = ∑ i, w i from
        fun a => by simpa using (gaussianDiag_moment_entry w a a).2.1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The Gaussian tail Gram identities for every real symmetric matrix. -/
theorem gaussianCompressedGram_moments {d k : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : Kᵀ = K) :
    Integrable (fun G => squaredFrobenius (gaussianCompressedGram K G -
        K.trace • (1 : Matrix (Fin k) (Fin k) ℝ))) (gaussianMatrixLaw d k) ∧
    (∫ G, squaredFrobenius (gaussianCompressedGram K G -
        K.trace • (1 : Matrix (Fin k) (Fin k) ℝ)) ∂gaussianMatrixLaw d k) =
      (k : ℝ) * ((k : ℝ) + 1) * squaredFrobenius K ∧
    Integrable (fun G => (gaussianCompressedGram K G).trace) (gaussianMatrixLaw d k) ∧
    (∫ G, (gaussianCompressedGram K G).trace ∂gaussianMatrixLaw d k) = (k : ℝ) * K.trace := by
  have hKh : K.IsHermitian := by
    change Kᴴ = K
    simpa only [conjTranspose_eq_transpose_of_trivial] using hK
  let U : Matrix (Fin d) (Fin d) ℝ := hKh.eigenvectorUnitary
  let w := hKh.eigenvalues
  have hu : Uᵀ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Matrix.UnitaryGroup.star_mul_self hKh.eigenvectorUnitary
  have hut : U * Uᵀ = 1 := mul_eq_one_comm.mp hu
  have hspec : K = U * diagonal w * Uᵀ := by
    simpa [U, w, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hKh.spectral_theorem
  have htrace : K.trace = ∑ i, w i := by
    rw [hspec, trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul, trace_diagonal]
  have hnorm : squaredFrobenius K = ∑ i, w i ^ 2 := by
    rw [hspec, squaredFrobenius_mul_orthogonal_right _ _ (by simpa only [transpose_transpose] using hu),
      squaredFrobenius_mul_orthogonal_left _ _ hu, Cosine.squaredFrobenius_eq_sum_entries]
    simp [Matrix.diagonal_apply]
  let F (G : Matrix (Fin d) (Fin k) ℝ) := Uᵀ * G
  let μ := gaussianMatrixLaw d k
  have hF : MeasurePreserving F μ μ :=
    ⟨(continuous_const.matrix_mul continuous_id).measurable,
      gaussianMatrixLaw_map_left_orthogonal Uᵀ (by simpa only [transpose_transpose] using hut)⟩
  have hC (G : Matrix (Fin d) (Fin k) ℝ) :
      gaussianCompressedGram K G = gaussianCompressedGram (diagonal w) (F G) := by
    simp only [gaussianCompressedGram, F, transpose_mul, transpose_transpose]
    rw [hspec]
    simp only [Matrix.mul_assoc]
  obtain ⟨hSq, hESq, hTr, hETr⟩ := gaussianDiagGram_moments (k := k) w
  have hInt {g : Matrix (Fin d) (Fin k) ℝ → ℝ} (hg : Integrable g μ) :
      (∫ G, g (F G) ∂μ) = ∫ G, g G ∂μ := by
    have hf := hg.aestronglyMeasurable
    rw [← hF.map_eq] at hf
    rw [← integral_map hF.measurable.aemeasurable hf, hF.map_eq]
  rw [htrace, hnorm]
  simp_rw [hC]
  exact ⟨hF.integrable_comp_of_integrable hSq, (hInt hSq).trans hESq,
    hF.integrable_comp_of_integrable hTr, (hInt hTr).trans hETr⟩

/-- Any fixed finite, injectively selected marginal of an infinite product
of identical laws is the corresponding finite product law. -/
theorem infiniteProduct_map_embedding {I X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} (q : Fin r ↪ I) :
    (Measure.infinitePi (fun _ : I => ν)).map (fun x i => x (q i)) =
      Measure.pi (fun _ : Fin r => ν) := by
  classical
  let s := Finset.univ.map q
  let f (i : Fin r) : s := ⟨q i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let e : Fin r ≃ s := Equiv.ofBijective f ⟨
    (fun _ _ hij => q.injective (congrArg Subtype.val hij)), fun x => by
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp x.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let F := MeasurableEquiv.piCongrLeft (fun _ : Fin r => X) e.symm
  have he : (fun (x : I → X) (i : Fin r) => x (q i)) = F ∘ s.restrict := by
    funext x i
    have h : F (s.restrict x) (e.symm (e i)) = s.restrict x (e i) :=
      MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : Fin r => X) (s.restrict x) (e i)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  rw [he, ← Measure.map_map F.measurable (Finset.measurable_restrict s),
    Measure.infinitePi_map_restrict]
  exact Measure.pi_map_piCongrLeft e.symm (fun _ : Fin r => ν)

/-- Selecting any prescribed distinct rows of a Gaussian matrix preserves
the primitive iid Gaussian block law. -/
theorem gaussianMatrixLaw_map_rows {d r k : ℕ} (q : Fin r ↪ Fin d) :
    (gaussianMatrixLaw d k).map (fun G => G.submatrix q id) = gaussianMatrixLaw r k := by
  rw [gaussianMatrixLaw_eq_row_product, gaussianMatrixLaw_eq_row_product]
  let ν := Measure.pi (fun _ : Fin k => gaussianReal 0 1)
  have h := infiniteProduct_map_embedding ν q
  rw [Measure.infinitePi_eq_pi] at h
  exact h

/-- The Gaussian block obtained from any fixed orthonormal frame is
the native iid Gaussian matrix of the corresponding dimensions. -/
theorem gaussianMatrixLaw_map_frame {d r k : ℕ} (hr : r ≤ d)
    (V : Matrix (Fin d) (Fin r) ℝ) (hV : Vᵀ * V = 1) :
    (gaussianMatrixLaw d k).map (fun G => Vᵀ * G) = gaussianMatrixLaw r k := by
  obtain ⟨U, hU, hV'⟩ := exists_orthogonal_extension hr V hV
  let q := Fin.castLEEmb hr
  let f (G : Matrix (Fin d) (Fin k) ℝ) := G.submatrix q id
  let g (G : Matrix (Fin d) (Fin k) ℝ) := Uᵀ * G
  have hf : Measurable f :=
    (continuous_id.matrix_submatrix q id).measurable
  have hg : Measurable g := (continuous_const.matrix_mul continuous_id).measurable
  have he : (fun G : Matrix (Fin d) (Fin k) ℝ => Vᵀ * G) = f ∘ g := by
    rw [← hV']
    funext G
    ext i j
    rfl
  rw [he, ← Measure.map_map hf hg,
    show (gaussianMatrixLaw d k).map g = _ from
      gaussianMatrixLaw_map_left_orthogonal Uᵀ (by
        simpa only [transpose_transpose] using mul_eq_one_comm.mp hU)]
  exact gaussianMatrixLaw_map_rows q

end

end SketchOrientation
