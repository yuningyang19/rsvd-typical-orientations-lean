import SketchOrientation.GaussianPolarAlgebra
import SketchOrientation.GaussianOrthogonal

namespace SketchOrientation

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {n k : ℕ}

private theorem measurable_gramFrame :
    MeasurableSet {G : Matrix (Fin n) (Fin k) ℝ | Gᵀ * G = 1} := by
  have h : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => Gᵀ * G) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable
  exact h (measurableSet_singleton 1)

private theorem measurable_leftMatrixMul (Q : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun G : Matrix (Fin n) (Fin k) ℝ => Q * G) :=
  (continuous_const.matrix_mul continuous_id).measurable

private theorem measurable_rightMatrixMul (V : Matrix (Fin n) (Fin k) ℝ) :
    Measurable (fun Q : Matrix (Fin n) (Fin n) ℝ => Q * V) :=
  (continuous_id.matrix_mul continuous_const).measurable

private theorem measurable_polarFrameTranspose :
    Measurable (fun G : Matrix (Fin n) (Fin n) ℝ => (gaussianPolarFrame G)ᵀ) :=
  (show Continuous (fun G : Matrix (Fin n) (Fin n) ℝ => Gᵀ) from
    continuous_id.matrix_transpose).measurable.comp measurable_gaussianPolarFrame

/-- Construct the right-invariant orthogonal law by inverting the square
Gaussian polar factor. It lives on ambient matrices with full mass on the
orthogonal group. -/
noncomputable def gaussianRightOrthogonalLaw (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (gaussianMatrixLaw n n).map (fun G => (gaussianPolarFrame G)ᵀ)

instance (n : ℕ) : IsProbabilityMeasure (gaussianRightOrthogonalLaw n) :=
  Measure.isProbabilityMeasure_map measurable_polarFrameTranspose.aemeasurable

theorem ae_gaussianRightOrthogonal (n : ℕ) :
    ∀ᵐ Q ∂gaussianRightOrthogonalLaw n, Qᵀ * Q = 1 := by
  unfold gaussianRightOrthogonalLaw
  apply (ae_map_iff measurable_polarFrameTranspose.aemeasurable measurable_gramFrame).2
  filter_upwards [ae_gaussianMatrix_injective (d := n) (k := n) le_rfl] with G hG
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.mp (gaussianPolarFrame_transpose_mul_self G hG)

theorem gaussianRightOrthogonalLaw_map_right (R : Matrix (Fin n) (Fin n) ℝ) (hR : Rᵀ * R = 1) :
    (gaussianRightOrthogonalLaw n).map (fun Q => Q * R) = gaussianRightOrthogonalLaw n := by
  let f := fun G : Matrix (Fin n) (Fin n) ℝ => (gaussianPolarFrame G)ᵀ
  have hRt : Rᵀᵀ * Rᵀ = 1 := by
    rw [transpose_transpose]
    exact mul_eq_one_comm.mp hR
  have he : (fun Q : Matrix (Fin n) (Fin n) ℝ => Q * R) ∘ f =
      f ∘ fun G => Rᵀ * G := by
    funext G
    change (gaussianPolarFrame G)ᵀ * R = (gaussianPolarFrame (Rᵀ * G))ᵀ
    rw [gaussianPolarFrame_mul_orthogonal_left _ hRt, transpose_mul, transpose_transpose]
  unfold gaussianRightOrthogonalLaw
  change ((gaussianMatrixLaw n n).map f).map (fun Q => Q * R) = (gaussianMatrixLaw n n).map f
  rw [Measure.map_map (measurable_rightMatrixMul R) measurable_polarFrameTranspose, he,
    ← Measure.map_map measurable_polarFrameTranspose (measurable_leftMatrixMul Rᵀ),
    gaussianMatrixLaw_map_left_orthogonal _ hRt]

theorem exists_stiefel_frame (hkn : k ≤ n) :
    ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * V = 1 := by
  obtain ⟨G, hG⟩ := (ae_gaussianMatrix_injective (d := n) hkn).exists
  exact ⟨gaussianPolarFrame G, gaussianPolarFrame_transpose_mul_self G hG⟩

private noncomputable def haarFrameOrigin (hkn : k ≤ n) : Matrix (Fin n) (Fin k) ℝ :=
  (exists_stiefel_frame hkn).choose

private theorem haarFrameOrigin_orthonormal (hkn : k ≤ n) :
    (haarFrameOrigin hkn)ᵀ * haarFrameOrigin hkn = 1 :=
  (exists_stiefel_frame hkn).choose_spec

/-- Haar frame law obtained by taking the orbit of one orthonormal frame
by a right-invariant random orthogonal matrix. The orbit law is independent
of that frame. -/
noncomputable def gaussianHaarFrameLaw (hkn : k ≤ n) : Measure (Matrix (Fin n) (Fin k) ℝ) :=
  (gaussianRightOrthogonalLaw n).map (fun Q => Q * haarFrameOrigin hkn)

instance (hkn : k ≤ n) : IsProbabilityMeasure (gaussianHaarFrameLaw hkn) :=
  Measure.isProbabilityMeasure_map (measurable_rightMatrixMul _).aemeasurable

theorem gaussianHaarFrameLaw_eq_orbit (hkn : k ≤ n) (V : Matrix (Fin n) (Fin k) ℝ)
    (hV : Vᵀ * V = 1) :
    (gaussianRightOrthogonalLaw n).map (fun Q => Q * V) = gaussianHaarFrameLaw hkn := by
  obtain ⟨R, hR, hRV⟩ := exists_orthogonal_mul_frame_eq hkn (haarFrameOrigin_orthonormal hkn) hV
  rw [← hRV]
  unfold gaussianHaarFrameLaw
  have hh : (fun Q : Matrix (Fin n) (Fin n) ℝ => Q * (R * haarFrameOrigin hkn)) =
      (fun Q => Q * haarFrameOrigin hkn) ∘ fun Q => Q * R := by
    funext Q
    exact (Matrix.mul_assoc _ _ _).symm
  rw [hh, ← Measure.map_map (measurable_rightMatrixMul _) (measurable_rightMatrixMul R),
    gaussianRightOrthogonalLaw_map_right R hR]

private theorem measurable_matrixMul :
    Measurable (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin k) ℝ => p.1 * p.2) :=
  by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun a _ =>
      ((continuous_id.matrix_elem i a).measurable.comp measurable_fst).mul
        ((continuous_id.matrix_elem a j).measurable.comp measurable_snd)

set_option maxHeartbeats 800000 in
/-- A joint law invariant under left rotations of its frame alone factors
as Haar frame law times the other marginal. This argument averages over
the orthogonal group and applies to discrete as well as continuous laws of
the other coordinate. -/
theorem haarFrame_joint_eq_prod_of_invariant {B : Type*} [MeasurableSpace B]
    (hkn : k ≤ n) (J : Measure (Matrix (Fin n) (Fin k) ℝ × B)) [IsProbabilityMeasure J]
    (hFrame : ∀ᵐ p ∂J, p.1ᵀ * p.1 = (1 : Matrix (Fin k) (Fin k) ℝ))
    (hInv : ∀ R : Matrix (Fin n) (Fin n) ℝ, Rᵀ * R = 1 →
      J.map (fun p => (R * p.1, p.2)) = J) :
    J = (gaussianHaarFrameLaw hkn).prod (J.map Prod.snd) := by
  have : IsProbabilityMeasure (J.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  symm
  apply Measure.prod_eq
  intro s t hs ht
  let ν := gaussianRightOrthogonalLaw n
  let U := fun f : Matrix (Fin n) (Fin n) ℝ × (Matrix (Fin n) (Fin k) ℝ × B) =>
    (f.1 * f.2.1, f.2.2)
  let S := s ×ˢ t
  have hU : Measurable U :=
    (measurable_matrixMul.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hSet : MeasurableSet (U ⁻¹' S) := (hs.prod ht).preimage hU
  calc
    J S = ∫⁻ _q, J S ∂ν := by simp
    _ = ∫⁻ q, J ((fun p => (q, p)) ⁻¹' (U ⁻¹' S)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_gaussianRightOrthogonal n] with q hq
      have hm : Measurable (fun p : Matrix (Fin n) (Fin k) ℝ × B => (q * p.1, p.2)) :=
        ((measurable_leftMatrixMul q).comp measurable_fst).prodMk measurable_snd
      change J S = J ((fun p => (q * p.1, p.2)) ⁻¹' S)
      rw [← Measure.map_apply hm (hs.prod ht), hInv q hq]
    _ = (ν.prod J) (U ⁻¹' S) := (Measure.prod_apply hSet).symm
    _ = ∫⁻ p, ν ((fun q => (q, p)) ⁻¹' (U ⁻¹' S)) ∂J := Measure.prod_apply_symm hSet
    _ = ∫⁻ p, (Prod.snd ⁻¹' t).indicator (fun _ => gaussianHaarFrameLaw hkn s) p ∂J := by
      apply lintegral_congr_ae
      filter_upwards [hFrame] with p hp
      have hOrbit := gaussianHaarFrameLaw_eq_orbit hkn p.1 hp
      by_cases hpt : p.2 ∈ t
      · have he : (fun q => (q, p)) ⁻¹' (U ⁻¹' S) = (fun q => q * p.1) ⁻¹' s := by
          ext q
          simp [U, S, hpt]
        rw [he, ← Measure.map_apply (measurable_rightMatrixMul p.1) hs]
        change (gaussianRightOrthogonalLaw n).map (fun q => q * p.1) s = _
        rw [hOrbit, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' t from hpt)]
      · have he : (fun q => (q, p)) ⁻¹' (U ⁻¹' S) = ∅ := by
          ext q
          simp [U, S, hpt]
        rw [he, measure_empty, Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' t from hpt)]
    _ = gaussianHaarFrameLaw hkn s * (J.map Prod.snd) t := by
      rw [lintegral_indicator_const (ht.preimage measurable_snd), Measure.map_apply measurable_snd ht]


/-- The radial factor law of the iid Gaussian matrix polar decomposition. -/
noncomputable def gaussianRadialFactorLaw (n k : ℕ) : Measure (Matrix (Fin k) (Fin k) ℝ) :=
  (gaussianMatrixLaw n k).map gaussianPolarRadial

instance (n k : ℕ) : IsProbabilityMeasure (gaussianRadialFactorLaw n k) :=
  Measure.isProbabilityMeasure_map continuous_gaussianPolarRadial.measurable.aemeasurable

/-- The iid Gaussian polar factors jointly have Haar frame law times the
radial law. The polar maps are the standard positive-root construction. -/
theorem gaussianPolarLaw_eq_prod (hkn : k ≤ n) :
    (gaussianMatrixLaw n k).map (fun G => (gaussianPolarFrame G, gaussianPolarRadial G)) =
      (gaussianHaarFrameLaw hkn).prod (gaussianRadialFactorLaw n k) := by
  let F := fun G : Matrix (Fin n) (Fin k) ℝ => (gaussianPolarFrame G, gaussianPolarRadial G)
  let J := (gaussianMatrixLaw n k).map F
  have hF : Measurable F :=
    measurable_gaussianPolarFrame.prodMk continuous_gaussianPolarRadial.measurable
  have : IsProbabilityMeasure J := Measure.isProbabilityMeasure_map hF.aemeasurable
  have hFrame : ∀ᵐ p ∂J, p.1ᵀ * p.1 = (1 : Matrix (Fin k) (Fin k) ℝ) := by
    apply (ae_map_iff hF.aemeasurable (measurable_gramFrame.preimage measurable_fst)).2
    filter_upwards [ae_gaussianMatrix_injective hkn] with G hG
    exact gaussianPolarFrame_transpose_mul_self G hG
  have hInv (R : Matrix (Fin n) (Fin n) ℝ) (hR : Rᵀ * R = 1) :
      J.map (fun p => (R * p.1, p.2)) = J := by
    have hQ : Measurable (fun p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
          (R * p.1, p.2)) :=
      ((measurable_leftMatrixMul R).comp measurable_fst).prodMk measurable_snd
    have he :
        (fun p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ => (R * p.1, p.2)) ∘ F =
          F ∘ fun G => R * G := by
      funext G
      simp [F, gaussianPolarFrame_mul_orthogonal_left R hR, gaussianPolarRadial_mul_orthogonal_left R hR]
    unfold J
    rw [Measure.map_map hQ hF, he, ← Measure.map_map hF (measurable_leftMatrixMul R),
      gaussianMatrixLaw_map_left_orthogonal R hR]
  have h := haarFrame_joint_eq_prod_of_invariant hkn J hFrame hInv
  have hm : J.map Prod.snd = gaussianRadialFactorLaw n k := by
    unfold J gaussianRadialFactorLaw
    rw [Measure.map_map measurable_snd hF]
    rfl
  exact h.trans (congrArg ((gaussianHaarFrameLaw hkn).prod) hm)

theorem gaussianPolarFrameLaw_eq_haar (hkn : k ≤ n) :
    (gaussianMatrixLaw n k).map gaussianPolarFrame = gaussianHaarFrameLaw hkn := by
  have h := congrArg (Measure.map Prod.fst) (gaussianPolarLaw_eq_prod hkn)
  have hF : Measurable (fun G : Matrix (Fin n) (Fin k) ℝ =>
      (gaussianPolarFrame G, gaussianPolarRadial G)) :=
    measurable_gaussianPolarFrame.prodMk continuous_gaussianPolarRadial.measurable
  rw [Measure.map_map measurable_fst hF, Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-- The polar frame is independent of the positive Gram root. -/
theorem indepFun_gaussianPolarFrame_radial (hkn : k ≤ n) :
    IndepFun gaussianPolarFrame gaussianPolarRadial (gaussianMatrixLaw n k) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_gaussianPolarFrame.aemeasurable
    continuous_gaussianPolarRadial.measurable.aemeasurable,
    gaussianPolarFrameLaw_eq_haar hkn]
  exact gaussianPolarLaw_eq_prod hkn

/-- Haar frame law is left rotation invariant. -/
theorem gaussianHaarFrameLaw_map_left (hkn : k ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) :
    (gaussianHaarFrameLaw hkn).map (fun V => Q * V) = gaussianHaarFrameLaw hkn := by
  rw [← gaussianPolarFrameLaw_eq_haar hkn,
    Measure.map_map (measurable_leftMatrixMul Q) measurable_gaussianPolarFrame]
  have h : (fun V : Matrix (Fin n) (Fin k) ℝ => Q * V) ∘ gaussianPolarFrame =
      gaussianPolarFrame ∘ fun G => Q * G :=
    funext fun G => (gaussianPolarFrame_mul_orthogonal_left Q hQ G).symm
  rw [h, ← Measure.map_map measurable_gaussianPolarFrame (measurable_leftMatrixMul Q),
    gaussianMatrixLaw_map_left_orthogonal Q hQ]


/-- The Haar law gives full mass to the actual Stiefel frames. -/
theorem ae_gaussianHaarFrame_orthonormal (hkn : k ≤ n) :
    ∀ᵐ V ∂gaussianHaarFrameLaw hkn, Vᵀ * V = 1 := by
  rw [← gaussianPolarFrameLaw_eq_haar hkn]
  apply (ae_map_iff measurable_gaussianPolarFrame.aemeasurable measurable_gramFrame).2
  filter_upwards [ae_gaussianMatrix_injective hkn] with G hG
  exact gaussianPolarFrame_transpose_mul_self G hG

/-- The Haar frame law is the unique left-orthogonally invariant probability
law supported on the Stiefel frames. -/
theorem gaussianHaarFrameLaw_unique (hkn : k ≤ n) (μ : Measure (Matrix (Fin n) (Fin k) ℝ))
    [IsProbabilityMeasure μ] (hFrame : ∀ᵐ V ∂μ, Vᵀ * V = 1)
    (hInv : ∀ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 →
      μ.map (fun V => Q * V) = μ) :
    μ = gaussianHaarFrameLaw hkn := by
  let ν : Measure ℕ := Measure.dirac 0
  have : IsProbabilityMeasure ν := Measure.dirac.isProbabilityMeasure
  let J := μ.prod ν
  have : IsProbabilityMeasure J := by unfold J; infer_instance
  have hf : ∀ᵐ p ∂J, p.1ᵀ * p.1 = (1 : Matrix (Fin k) (Fin k) ℝ) :=
    (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hFrame
  have hi (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1) :
      J.map (fun p => (Q * p.1, p.2)) = J := by
    change (μ.prod ν).map (Prod.map (fun V => Q * V) id) = μ.prod ν
    rw [← Measure.map_prod_map _ _ (measurable_leftMatrixMul Q) measurable_id,
      Measure.map_id, hInv Q hQ]
  have h := congrArg (Measure.map Prod.fst) (haarFrame_joint_eq_prod_of_invariant hkn J hf hi)
  have hJ : IsProbabilityMeasure (J.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hJF : J.map Prod.fst = μ := (measurePreserving_fst (μ := μ) (ν := ν)).map_eq
  rw [hJF, Measure.map_fst_prod, hJ.measure_univ, one_smul] at h
  exact h

/-- Recombining the independent Haar and radial factors recovers the exact
iid Gaussian matrix law. -/
theorem gaussianPolarLaw_recombine (hkn : k ≤ n) :
    ((gaussianHaarFrameLaw hkn).prod (gaussianRadialFactorLaw n k)).map
      (fun p => p.1 * p.2) = gaussianMatrixLaw n k := by
  have hM : Measurable (fun p : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ => p.1 * p.2) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun a _ =>
      ((continuous_id.matrix_elem i a).measurable.comp measurable_fst).mul
        ((continuous_id.matrix_elem a j).measurable.comp measurable_snd)
  rw [← gaussianPolarLaw_eq_prod hkn, Measure.map_map hM
    (measurable_gaussianPolarFrame.prodMk continuous_gaussianPolarRadial.measurable)]
  trans (gaussianMatrixLaw n k).map id
  · apply Measure.map_congr
    filter_upwards [ae_gaussianMatrix_injective hkn] with G hG
    exact gaussianPolarFrame_mul_radial G hG
  · exact Measure.map_id

end SketchOrientation
