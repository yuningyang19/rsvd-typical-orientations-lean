import TypicalOrientations.RotationMarginal
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

namespace TypicalOrientations

open Matrix MeasureTheory ProbabilityTheory SketchOrientation Set Filter TopologicalSpace
open scoped Topology ENNReal

noncomputable section

variable {n l : ℕ}

private theorem projector_trace_eq_rank (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : Pᵀ = P) (hi : P * P = P) : P.trace = (P.rank : ℝ) := by
  simpa only [rangeProjector_of_projector P hs hi] using trace_rangeProjector P

private theorem projector_entry_abs_le_one (P : OrthogonalProjector n l) (i j : Fin n) :
    |P.val i j| ≤ 1 := by
  let u := EuclideanSpace.single j (1 : ℝ)
  have he : ((orientationRowSpace P).starProjection u) i = P.val i j := by
    rw [orientationRowSpace_starProjection]
    change (toLpLin 2 2 P.val u) i = _
    simp [u, Matrix.toLpLin_apply, EuclideanSpace.single]
  rw [← he, ← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le _ _).trans (((orientationRowSpace P).norm_starProjection_apply_le u).trans
    (le_of_eq (by simp [u, EuclideanSpace.single, PiLp.norm_single])))

theorem isCompact_orthogonalProjectors (n l : ℕ) :
    IsCompact {P : Matrix (Fin n) (Fin n) ℝ | Pᵀ = P ∧ P * P = P ∧ P.rank = l} := by
  let S := {P : Matrix (Fin n) (Fin n) ℝ | Pᵀ = P ∧ P * P = P ∧ P.rank = l}
  have hClosed : IsClosed S := by
    have hSet : S = {P : Matrix (Fin n) (Fin n) ℝ | Pᵀ = P ∧ P * P = P ∧ P.trace = (l : ℝ)} := by
      ext P
      change (_ ∧ _ ∧ P.rank = l) ↔ (_ ∧ _ ∧ P.trace = (l : ℝ))
      constructor
      · rintro ⟨hs, hi, hr⟩
        exact ⟨hs, hi, (projector_trace_eq_rank P hs hi).trans (by rw [hr])⟩
      · rintro ⟨hs, hi, ht⟩
        refine ⟨hs, hi, ?_⟩
        rw [projector_trace_eq_rank P hs hi] at ht
        exact_mod_cast ht
    rw [hSet]
    exact (isClosed_eq continuous_id.matrix_transpose continuous_id).inter
      ((isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id).inter
        (isClosed_eq (continuous_id.matrix_trace) continuous_const))
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Set.pi univ fun _ => Set.pi univ fun _ => Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hK.of_isClosed_subset hClosed ?_
  intro P hp i _ j _
  have h := projector_entry_abs_le_one (n := n) (l := l) ⟨P, hp⟩ i j
  exact abs_le.mp h

instance orthogonalProjectorCompactSpace : CompactSpace (OrthogonalProjector n l) :=
  isCompact_iff_compactSpace.mp (isCompact_orthogonalProjectors n l)

/-- Matrix-coordinate polynomials restricted to the rank-l Grassmannian. -/
abbrev ProjectorPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin n) ℝ

def evalProjectorPolynomial (p : ProjectorPolynomial n) (P : OrthogonalProjector n l) : ℝ :=
  p.eval (fun ij => P.val ij.1 ij.2)

private def projectorCoordinate (ij : Fin n × Fin n) : C(OrthogonalProjector n l, ℝ) :=
  ⟨fun P => P.val ij.1 ij.2, (continuous_id.matrix_elem _ _).comp continuous_subtype_val⟩

private def polynomialRestriction : ProjectorPolynomial n →ₐ[ℝ] C(OrthogonalProjector n l, ℝ) :=
  MvPolynomial.aeval projectorCoordinate

private theorem polynomialRestriction_eval (p : ProjectorPolynomial n) (P : OrthogonalProjector n l) :
    polynomialRestriction p P = evalProjectorPolynomial p P := by
  change ContinuousMap.evalAlgHom ℝ ℝ P (MvPolynomial.aeval projectorCoordinate p) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem continuous_evalProjectorPolynomial (p : ProjectorPolynomial n) :
    Continuous (evalProjectorPolynomial (l := l) p) := by
  convert (polynomialRestriction (l := l) p).continuous using 1
  funext x
  exact (polynomialRestriction_eval p x).symm

private theorem polynomialRestriction_separatesPoints :
    (polynomialRestriction (n := n) (l := l)).range.SeparatesPoints := by
  intro P Q hPQ
  have h : ∃ i j, P.val i j ≠ Q.val i j := by
    by_contra! h
    exact hPQ (Subtype.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := h
  refine ⟨_, ⟨projectorCoordinate (i, j), ?_, rfl⟩, hij⟩
  change ∃ p : ProjectorPolynomial n, polynomialRestriction p = projectorCoordinate (i, j)
  exact ⟨MvPolynomial.X (i, j), by simp [polynomialRestriction]⟩

theorem exists_projectorPolynomial_uniform_approx (f : OrthogonalProjector n l → ℝ)
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ProjectorPolynomial n, ∀ P, |evalProjectorPolynomial p P - f P| < ε := by
  obtain ⟨⟨g, hg⟩, h⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (polynomialRestriction (n := n) (l := l)).range polynomialRestriction_separatesPoints f hf ε hε
  obtain ⟨p, hp⟩ := hg
  refine ⟨p, fun P => ?_⟩
  have hp' : polynomialRestriction p = g := hp
  rw [← polynomialRestriction_eval, hp', ← Real.norm_eq_abs]
  exact h P


private def approximationError (m : ℕ) : ℝ := ((m : ℝ) + 1)⁻¹

private theorem approximationError_pos (m : ℕ) : 0 < approximationError m := by
  unfold approximationError
  positivity

private theorem approximationError_le_one (m : ℕ) : approximationError m ≤ 1 :=
  inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))

private theorem approximationError_tendsto :
    Tendsto approximationError atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0)
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

set_option maxHeartbeats 1800000 in
private theorem exists_bounded_continuous_ae_approx
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (f : OrthogonalProjector n l → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (h0 : ∀ P, 0 ≤ f P) (h1 : ∀ P, f P ≤ B) :
    ∃ g : ℕ → OrthogonalProjector n l → ℝ,
      (∀ m, Continuous (g m)) ∧
      (∀ m P, 0 ≤ g m P ∧ g m P ≤ B) ∧
      ∀ᵐ P ∂μ, Tendsto (fun m => g m P) atTop (𝓝 (f P)) := by
  have hInt : Integrable f μ := by
    refine Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun P => ?_)
    rw [Real.norm_of_nonneg (h0 P)]
    exact h1 P
  have hηpos (m : ℕ) : ENNReal.ofReal (approximationError m) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (approximationError_pos m)).ne'
  have : PseudoMetrizableSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin n → Fin n → ℝ))
  have : PseudoMetrizableSpace (OrthogonalProjector n l) :=
    PseudoMetrizableSpace.subtype _
  have : BorelSpace (OrthogonalProjector n l) := Subtype.borelSpace _
  have : μ.WeaklyRegular := Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure μ
  choose F hF hFI using fun m => hInt.exists_boundedContinuous_lintegral_sub_le (hηpos m)
  have hη : Tendsto (fun m => ENNReal.ofReal (approximationError m)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp approximationError_tendsto
  have hLp : Tendsto (fun m => eLpNorm (fun P => F m P - f P) 1 μ) atTop (𝓝 0) := by
    refine tendsto_const_nhds.squeeze hη (fun _ => zero_le) ?_
    intro m
    change eLpNorm (fun P => F m P - f P) 1 μ ≤ ENNReal.ofReal (approximationError m)
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine (le_of_eq (lintegral_congr fun P => ?_)).trans (hF m)
    rw [← enorm_neg, neg_sub]
  have hLPi : Tendsto (fun m => eLpNorm ((F m : OrthogonalProjector n l → ℝ) - f) 1 μ) atTop (𝓝 0) := hLp
  have hMeas := tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    (fun m => (hFI m).aestronglyMeasurable) hf.aestronglyMeasurable hLPi
  obtain ⟨a, _, ha⟩ := hMeas.exists_seq_tendsto_ae
  let clip : ℝ → ℝ := fun x => min B (max 0 x)
  have hc : Continuous clip := continuous_const.min (continuous_const.max continuous_id)
  let g (m : ℕ) (P : OrthogonalProjector n l) := clip (F (a m) P)
  refine ⟨g, fun m => hc.comp (F (a m)).continuous, ?_, ?_⟩
  · intro m P
    exact ⟨le_min hB (le_max_left _ _), min_le_left _ _⟩
  · filter_upwards [ha] with P hP
    have hV : clip (f P) = f P := by
      simp [clip, max_eq_right (h0 P), min_eq_right (h1 P)]
    rw [← hV]
    exact (hc.tendsto (f P)).comp hP

set_option maxHeartbeats 1200000 in
/-- A bounded nonnegative Borel function can be approximated almost
everywhere by a uniformly bounded sequence of strictly positive matrix polynomials. -/
theorem exists_positive_projectorPolynomial_ae_approx
    (μ : Measure (OrthogonalProjector n l)) [IsProbabilityMeasure μ]
    (f : OrthogonalProjector n l → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (h0 : ∀ P, 0 ≤ f P) (h1 : ∀ P, f P ≤ B) :
    ∃ p : ℕ → ProjectorPolynomial n,
      (∀ m (P : OrthogonalProjector n l), 0 < evalProjectorPolynomial (p m) P) ∧
      (∀ m (P : OrthogonalProjector n l), evalProjectorPolynomial (p m) P ≤ B + 3) ∧
      ∀ᵐ P ∂μ, Tendsto (fun m => evalProjectorPolynomial (p m) P) atTop (𝓝 (f P)) := by
  obtain ⟨g, hg, hb, hLim⟩ := exists_bounded_continuous_ae_approx μ f hf hB h0 h1
  choose q hq using fun m => exists_projectorPolynomial_uniform_approx (g m) (hg m)
    (approximationError_pos m)
  let p (m : ℕ) := q m + MvPolynomial.C (2 * approximationError m)
  have he (m : ℕ) (P : OrthogonalProjector n l) :
      evalProjectorPolynomial (p m) P = evalProjectorPolynomial (q m) P + 2 * approximationError m := by
    simp [p, evalProjectorPolynomial]
  have hBound (m : ℕ) (P : OrthogonalProjector n l) :
      approximationError m < evalProjectorPolynomial (p m) P - g m P ∧
      evalProjectorPolynomial (p m) P - g m P < 3 * approximationError m := by
    have h := abs_lt.mp (hq m P)
    rw [he]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · intro m P
    linarith [approximationError_pos m, (hb m P).1, (hBound m P).1]
  · intro m P
    linarith [approximationError_le_one m, (hb m P).2, (hBound m P).2]
  · filter_upwards [hLim] with P hP
    have hd : Tendsto (fun m => evalProjectorPolynomial (p m) P - g m P) atTop (𝓝 0) := by
      have hErr : Tendsto (fun m => 3 * approximationError m) atTop (𝓝 0) := by
        simpa only [mul_zero] using approximationError_tendsto.const_mul 3
      apply squeeze_zero _ _ hErr
      · intro m
        exact ((approximationError_pos m).trans (hBound m P).1).le
      · intro m
        exact (hBound m P).2.le
    have ht := hd.add hP
    rw [zero_add] at ht
    exact ht.congr (fun m => sub_add_cancel _ _)


/-- Equation (2.6) for a finite family of subspaces with individual ranks. -/
def RotationBrascampLiebAt (n m : ℕ) (rank : Fin m → ℕ) : Prop :=
  ∀ (P : (i : Fin m) → OrthogonalProjector n (rank i)) (c : Fin m → ℝ)
    (H : (i : Fin m) → OrthogonalProjector n (rank i) → ℝ),
    (∀ i, 0 < c i) →
    (∀ x : EuclideanSpace ℝ (Fin n), ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2) →
    (∀ i, Measurable (H i)) →
    (∀ i S, 0 ≤ H i S) →
    (∀ i, ∃ B, ∀ S, H i S ≤ B) →
    (∫ U, ∏ i, (H i (rotateProjector U (P i))) ^ (c i / 2) ∂specialOrientationLaw n) ≤
      ∏ i, (∫ U, H i (rotateProjector U (P i)) ∂specialOrientationLaw n) ^ (c i / 2)

/-- The mixed-rank form of the bounded Borel rotation-group inequality. -/
def RotationBrascampLiebMixedRanks : Prop :=
  ∀ (n m : ℕ) (rank : Fin m → ℕ),
    0 < n → (∀ i, rank i ≤ n) → RotationBrascampLiebAt n m rank

/-- The rotation-group inequality, restricted to strictly positive
matrix-coordinate polynomials on the indicated Grassmannians. -/
def RotationBrascampLiebPolynomialAt (n m : ℕ) (rank : Fin m → ℕ) : Prop :=
  ∀ (P : (i : Fin m) → OrthogonalProjector n (rank i)) (c : Fin m → ℝ)
    (p : Fin m → ProjectorPolynomial n),
    (∀ i, 0 < c i) →
    (∀ x : EuclideanSpace ℝ (Fin n), ∑ i, c i * ‖(P i).val.toEuclideanLin x‖ ^ 2 ≤ ‖x‖ ^ 2) →
    (∀ i (S : OrthogonalProjector n (rank i)), 0 < evalProjectorPolynomial (p i) S) →
    (∫ U, ∏ i, (evalProjectorPolynomial (p i) (rotateProjector U (P i))) ^ (c i / 2)
      ∂specialOrientationLaw n) ≤
      ∏ i, (∫ U, evalProjectorPolynomial (p i) (rotateProjector U (P i))
        ∂specialOrientationLaw n) ^ (c i / 2)

/-- The positive-polynomial inequality for a family of common rank. -/
def RotationBrascampLiebPolynomial : Prop :=
  ∀ (n l m : ℕ), 0 < n → l ≤ n → RotationBrascampLiebPolynomialAt n m (fun _ => l)

set_option maxHeartbeats 1500000 in
/-- Extend the positive-polynomial inequality to bounded nonnegative Borel
functions. Each factor is approximated in the Haar marginal at its own rank
and then pulled back by the corresponding rotation action. -/
theorem rotationBrascampLieb_of_polynomial_at {n m : ℕ} {rank : Fin m → ℕ}
    (hn : 0 < n) (hr : ∀ i, rank i ≤ n)
    (hPoly : RotationBrascampLiebPolynomialAt n m rank) : RotationBrascampLiebAt n m rank := by
  intro P c H hc hDir hH hH0 hHBound
  let η := specialOrientationLaw n
  let ν (i : Fin m) := haarSketchProjectorLaw (hr i)
  let R (i : Fin m) (U : Matrix (Fin n) (Fin n) ℝ) := rotateProjector U (P i)
  choose B hB using hHBound
  have hAppr (i : Fin m) :
      ∃ p : ℕ → ProjectorPolynomial n,
        (∀ (j : ℕ) (S : OrthogonalProjector n (rank i)), 0 < evalProjectorPolynomial (p j) S) ∧
        (∀ (j : ℕ) (S : OrthogonalProjector n (rank i)), evalProjectorPolynomial (p j) S ≤ max 0 (B i) + 3) ∧
        ∀ᵐ S ∂ν i, Tendsto (fun j => evalProjectorPolynomial (p j) S) atTop (𝓝 (H i S)) :=
    exists_positive_projectorPolynomial_ae_approx (ν i) (H i) (hH i) (le_max_left _ _) (hH0 i)
      (fun S => (hB i S).trans (le_max_right _ _))
  choose p hp hb hAE using hAppr
  let d (i : Fin m) := max 0 (B i) + 3
  let F (i : Fin m) (j : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) :=
    evalProjectorPolynomial (p i j) (R i U)
  let G (i : Fin m) (U : Matrix (Fin n) (Fin n) ℝ) := H i (R i U)
  have hR (i : Fin m) : Measurable (R i) := by
    have hPair : Measurable (fun U : Matrix (Fin n) (Fin n) ℝ => (U, P i)) :=
      measurable_id.prodMk measurable_const
    exact measurable_rotateProjector.comp hPair
  have hMap (i : Fin m) : MeasurePreserving (R i) η (ν i) := by
    have h := (rotateProjector_specialOrientation_identDistrib hn (hr i) (P i)).map_eq
    rw [Measure.map_id] at h
    exact ⟨hR i, h⟩
  have hLim (i : Fin m) :
      ∀ᵐ U ∂η, Tendsto (fun j => F i j U) atTop (𝓝 (G i U)) :=
    (hMap i).quasiMeasurePreserving.ae (hAE i)
  have hMeas (i : Fin m) (j : ℕ) : Measurable (F i j) :=
    (continuous_evalProjectorPolynomial (p i j)).measurable.comp (hR i)
  have hPos (i : Fin m) (j : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) : 0 < F i j U :=
    hp i j (R i U)
  have hBd (i : Fin m) (j : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) : F i j U ≤ d i :=
    hb i j (R i U)
  have hMarginal (i : Fin m) :
      Tendsto (fun j => ∫ U, F i j U ∂η) atTop (𝓝 (∫ U, G i U ∂η)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => d i)
      (fun j => (hMeas i j).aestronglyMeasurable) (integrable_const _) _ (hLim i)
    intro j
    exact ae_of_all _ (fun U => by rw [Real.norm_of_nonneg (hPos i j U).le]; exact hBd i j U)
  have hPow (i : Fin m) : Continuous (fun x : ℝ => x ^ (c i / 2)) :=
    Real.continuous_rpow_const (by linarith [hc i])
  have hPowNonneg (i : Fin m) : 0 ≤ c i / 2 := by linarith [hc i]
  have hJointLim :
      ∀ᵐ U ∂η, Tendsto (fun j => ∏ i, F i j U ^ (c i / 2)) atTop
        (𝓝 (∏ i, G i U ^ (c i / 2))) := by
    filter_upwards [ae_all_iff.mpr hLim] with U hU
    exact tendsto_finsetProd Finset.univ (fun i _ =>
      ((hPow i).tendsto (G i U)).comp (hU i))
  have hJoint :
      Tendsto (fun j => ∫ U, ∏ i, F i j U ^ (c i / 2) ∂η) atTop
        (𝓝 (∫ U, ∏ i, G i U ^ (c i / 2) ∂η)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ∏ i, d i ^ (c i / 2)) _ (integrable_const _) _ hJointLim
    · intro j
      exact (Finset.measurable_prod Finset.univ (fun i _ =>
        (hPow i).measurable.comp (hMeas i j))).aestronglyMeasurable
    · intro j
      refine ae_of_all _ (fun U => ?_)
      rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hPos i j U).le _)]
      exact Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hPos i j U).le _)
        (fun i _ => Real.rpow_le_rpow (hPos i j U).le (hBd i j U) (hPowNonneg i))
  have hMarginalProd :
      Tendsto (fun j => ∏ i, (∫ U, F i j U ∂η) ^ (c i / 2)) atTop
        (𝓝 (∏ i, (∫ U, G i U ∂η) ^ (c i / 2))) :=
    tendsto_finsetProd Finset.univ (fun i _ =>
      ((hPow i).tendsto (∫ U, G i U ∂η)).comp (hMarginal i))
  exact le_of_tendsto_of_tendsto' hJoint hMarginalProd
    (fun j => hPoly P c (fun i => p i j) hc hDir (fun i => hp i j))

/-- The polynomial-to-Borel extension for a family of common rank. -/
theorem rotationBrascampLieb_of_polynomial (hPoly : RotationBrascampLiebPolynomial) :
    RotationBrascampLieb := by
  intro n l m hn hl
  exact rotationBrascampLieb_of_polynomial_at hn (fun _ => hl) (hPoly n l m hn hl)

end

end TypicalOrientations
