import SketchOrientation.GaussianChaosRows
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance

namespace SketchOrientation

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace ProbabilityTheory

private theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let a := ∫ x, f x ∂μ
  have h1 := hf.integrable (by norm_num)
  have h2 := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have h3 : Integrable (fun x => (2 * a) * f x) μ := h1.const_mul _
  have h4 : Integrable (fun x => f x ^ 2 - (2 * a) * f x) μ := h2.sub h3
  have hs (x : Ω) : (f x - a) ^ 2 = f x ^ 2 - (2 * a) * f x + a ^ 2 := by ring
  have h : 0 ≤ (∫ x, (f x - a) ^ 2 ∂μ) :=
    integral_nonneg (fun x => sq_nonneg (f x - a))
  simp_rw [hs] at h
  rw [integral_add h4 (integrable_const _), integral_sub h2 h3, integral_const_mul, integral_const] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * a * a + a ^ 2 at h
  nlinarith

private theorem inner_toLp {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, RCLike.inner_apply, conj_trivial, mul_comm]

private theorem sq_norm_toLp_eq {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f : E → ℝ} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp only [pow_two]

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

private theorem gaussianConditionalProjection_toLp_fixed (S : Submodule ℝ E) {f : E → ℝ}
    (hf : MemLp f 2 (stdGaussian E))
    (hm : Measurable[MeasurableSpace.comap S.orthogonalProjectionOnto inferInstance] f) :
    gaussianConditionalProjection S (hf.toLp f) = hf.toLp f := by
  have hS := S.orthogonalProjectionOnto.continuous.measurable.comap_le
  apply Lp.ext
  exact (hf.condExpL2_ae_eq_condExp hS).trans
    ((condExp_of_aestronglyMeasurable' hS hm.stronglyMeasurable.aestronglyMeasurable
      (hf.integrable (by norm_num))).trans hf.coeFn_toLp.symm)

private theorem gaussianConditionalProjection_adjoint (S : Submodule ℝ E)
    (u v : GaussianL2 E) :
    inner ℝ (gaussianConditionalProjection S u) v =
      inner ℝ u (gaussianConditionalProjection S v) :=
  inner_condExpL2_left_eq_right S.orthogonalProjectionOnto.continuous.measurable.comap_le

set_option maxHeartbeats 900000 in
private theorem projected_centered_average_second_moment
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (Y : Ω → E → ℝ) (hY : Measurable (Function.uncurry Y))
    (hObs : ∀ ω, Measurable[MeasurableSpace.comap (S ω).orthogonalProjectionOnto inferInstance] (Y ω))
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hLp : ∀ ω, MemLp (Y ω) 2 (stdGaussian E))
    (h0 : ∀ ω, (∫ z, Y ω z ∂stdGaussian E) = 0)
    (h2 : ∀ ω, (∫ z, (Y ω z) ^ 2 ∂stdGaussian E) = σ ^ 2) :
    Integrable (Function.uncurry Y) (μ.prod (stdGaussian E)) ∧
      (∫ z, (∫ ω, Y ω z ∂μ) ∂stdGaussian E) = 0 ∧
      (∫ z, (∫ ω, Y ω z ∂μ) ^ 2 ∂stdGaussian E) ≤ ρ * σ ^ 2 := by
  let γ := stdGaussian E
  let b := fun z => ∫ ω, Y ω z ∂μ
  have hYs : Integrable (fun w : Ω × E => (Y w.1 w.2) ^ 2) (μ.prod γ) := by
    apply (integrable_prod_iff (hY.pow_const (2 : ℕ)).aestronglyMeasurable).2
    refine ⟨ae_of_all _ fun ω => (memLp_two_iff_integrable_sq (hLp ω).aestronglyMeasurable).mp
      (hLp ω), ?_⟩
    have he (ω : Ω) : (∫ z, ‖(Y ω z) ^ 2‖ ∂γ) = σ ^ 2 := by
      simp only [Real.norm_of_nonneg (sq_nonneg _)]
      exact h2 ω
    change Integrable (fun ω => ∫ z, ‖(Y ω z) ^ 2‖ ∂γ) μ
    simp only [he]
    exact integrable_const _
  have hYLp : MemLp (Function.uncurry Y) 2 (μ.prod γ) :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).2 hYs
  have hbMeas : Measurable b := (hY.stronglyMeasurable.integral_prod_left).measurable
  have hb2 : MemLp b 2 γ := by
    apply (memLp_two_iff_integrable_sq hbMeas.aestronglyMeasurable).2
    refine hYs.integral_prod_right.mono' (hbMeas.pow_const _).aestronglyMeasurable ?_
    filter_upwards [(integrable_prod_iff' hYs.aestronglyMeasurable).mp hYs |>.1] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_integral_le_integral_sq μ ((memLp_two_iff_integrable_sq
      ((hY.comp measurable_prodMk_right).aestronglyMeasurable)).2 hz)
  let B := hb2.toLp b
  let y := fun ω => (hLp ω).toLp (Y ω)
  have hYInt := hYLp.integrable (by norm_num)
  have hbMean : (∫ z, b z ∂γ) = 0 := by
    unfold b
    rw [← integral_integral_swap hYInt]
    change (∫ ω, ∫ z, Y ω z ∂stdGaussian E ∂μ) = 0
    simp only [h0, integral_zero]
  have hb0 : (∫ z, B z ∂γ) = 0 := (integral_congr_ae hb2.coeFn_toLp).trans hbMean
  refine ⟨hYInt, hbMean, ?_⟩
  have hBnorm : ‖B‖ ^ 2 = ∫ z, (b z) ^ 2 ∂γ := sq_norm_toLp_eq hb2
  have hynorm (ω : Ω) : ‖y ω‖ = σ := by
    apply (sq_eq_sq₀ (norm_nonneg _) hσ).1
    rw [sq_norm_toLp_eq, h2]
  have hfix (ω : Ω) : gaussianConditionalProjection (S ω) (y ω) = y ω :=
    gaussianConditionalProjection_toLp_fixed _ (hLp ω) (hObs ω)
  let a := fun ω => ‖gaussianConditionalProjection (S ω) B‖
  obtain ⟨ham2, haBound⟩ := gaussianProjection_L2_contraction μ S hS ρ hρ B hb0
  have ham : Measurable a := by
    have ht : a = fun ω => Real.sqrt (a ω ^ 2) :=
      funext fun ω => (Real.sqrt_sq (norm_nonneg _)).symm
    rw [ht]
    exact ham2.sqrt
  have haLp : MemLp a 2 μ := by
    apply (memLp_two_iff_integrable_sq ham.aestronglyMeasurable).2
    refine (integrable_const (‖B‖ ^ 2)).mono' ham2.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gaussianConditionalProjection_le _ _) _
  have hpInt : Integrable (fun w : Ω × E => Y w.1 w.2 * b w.2) (μ.prod γ) :=
    hYLp.integrable_mul (hb2.comp_measurePreserving measurePreserving_snd)
  have hInner (ω : Ω) : inner ℝ (y ω) B = ∫ z, Y ω z * b z ∂γ :=
    inner_toLp (hLp ω) hb2
  have hInnerInt : Integrable (fun ω => inner ℝ (y ω) B) μ := by
    simp_rw [hInner]
    exact hpInt.integral_prod_left
  have hPair : (∫ ω, inner ℝ (y ω) B ∂μ) = ‖B‖ ^ 2 := by
    simp_rw [hInner]
    rw [integral_integral_swap hpInt, hBnorm]
    simp_rw [integral_mul_const]
    change (∫ z, b z * b z ∂γ) = ∫ z, (b z) ^ 2 ∂γ
    simp only [pow_two]
  have hSide (ω : Ω) : inner ℝ (y ω) B ≤ σ * a ω := by
    calc
      _ = inner ℝ (gaussianConditionalProjection (S ω) (y ω)) B :=
          congrArg (fun w => inner ℝ w B) (hfix ω).symm
      _ = inner ℝ (y ω) (gaussianConditionalProjection (S ω) B) :=
        gaussianConditionalProjection_adjoint _ _ _
      _ ≤ ‖y ω‖ * a ω := real_inner_le_norm _ _
      _ = _ := by rw [hynorm]
  have hFirst : ‖B‖ ^ 2 ≤ σ * ∫ ω, a ω ∂μ := by
    rw [← hPair, ← integral_const_mul]
    exact integral_mono hInnerInt ((haLp.integrable (by norm_num)).const_mul _) hSide
  have hSecond : (∫ ω, a ω ∂μ) ^ 2 ≤ ρ * ‖B‖ ^ 2 :=
    (sq_integral_le_integral_sq μ haLp).trans haBound
  rw [← hBnorm]
  by_cases hb : ‖B‖ = 0
  · simp [hb, mul_nonneg hρ0 (sq_nonneg _)]
  have hpos : 0 < ‖B‖ ^ 2 := sq_pos_of_ne_zero hb
  have hlast : (‖B‖ ^ 2) * (‖B‖ ^ 2) ≤ (ρ * σ ^ 2) * ‖B‖ ^ 2 := by
    have hh := (pow_le_pow_left₀ (sq_nonneg ‖B‖) hFirst (2 : ℕ))
    rw [mul_pow] at hh
    calc
      _ ≤ σ ^ 2 * (∫ ω, a ω ∂μ) ^ 2 := by simpa only [← pow_two] using hh
      _ ≤ σ ^ 2 * (ρ * ‖B‖ ^ 2) := mul_le_mul_of_nonneg_left hSecond (sq_nonneg _)
      _ = _ := by ring
  exact le_of_mul_le_mul_right hlast hpos


/-- The variance consequence of Lemma 3.2. The sketch observations use the
same Gaussian draw, and the conditional distributions over that draw agree.
The pointwise integral of the observations is the inner sketch average. -/
theorem gaussianProjection_variance_contraction
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → Submodule ℝ E)
    (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ u : E, (∫ ω, ‖(S ω).starProjection u‖ ^ 2 ∂μ) ≤ ρ * ‖u‖ ^ 2)
    (Y : Ω → E → ℝ) (hY : Measurable (Function.uncurry Y))
    (hObs : ∀ ω, Measurable[MeasurableSpace.comap (S ω).orthogonalProjectionOnto inferInstance] (Y ω))
    (Y₀ : E → ℝ) (hLp : MemLp Y₀ 2 (stdGaussian E))
    (hLaw : ∀ ω, IdentDistrib (Y ω) (Y₀) (stdGaussian E) (stdGaussian E)) :
    Var[fun z => ∫ ω, Y ω z ∂μ; stdGaussian E] ≤ ρ * Var[Y₀; stdGaussian E] := by
  let γ := stdGaussian E
  let m := ∫ z, Y₀ z ∂γ
  let σ := Real.sqrt (Var[Y₀; γ])
  let Yc := fun ω z => Y ω z - m
  let b := fun z => ∫ ω, Yc ω z ∂μ
  have hσ2 : σ ^ 2 = Var[Y₀; γ] := Real.sq_sqrt (variance_nonneg _ _)
  have hm (ω : Ω) : (∫ z, Y ω z ∂γ) = m := (hLaw ω).integral_eq
  have hI (ω : Ω) : MemLp (Y ω) 2 γ := (hLaw ω).symm.memLp_snd hLp
  have hcLp (ω : Ω) : MemLp (Yc ω) 2 γ := (hI ω).sub (memLp_const m)
  have hcY : Measurable (Function.uncurry Yc) := hY.sub_const m
  have hcObs (ω : Ω) :
      Measurable[MeasurableSpace.comap (S ω).orthogonalProjectionOnto inferInstance] (Yc ω) :=
    (hObs ω).sub_const m
  have hc0 (ω : Ω) : (∫ z, Yc ω z ∂γ) = 0 := by
    unfold Yc
    rw [integral_sub ((hI ω).integrable (by norm_num)) (integrable_const m), hm ω]
    simp
  have hc2 (ω : Ω) : (∫ z, (Yc ω z) ^ 2 ∂γ) = σ ^ 2 := by
    rw [hσ2, ← (hLaw ω).variance_eq, variance_eq_integral (hLaw ω).aemeasurable_fst, hm ω]
  obtain ⟨hcInt, hbMean, hbBound⟩ := projected_centered_average_second_moment μ S hS
    ρ hρ0 hρ Yc hcY hcObs σ (Real.sqrt_nonneg _) hcLp hc0 hc2
  let A := fun z => ∫ ω, Y ω z ∂μ
  have hAm : Measurable A := (hY.stronglyMeasurable.integral_prod_left).measurable
  have hShift : A =ᵐ[γ] (fun z => b z + m) := by
    filter_upwards [(integrable_prod_iff' hcInt.aestronglyMeasurable).mp hcInt |>.1] with z hz
    have hh (ω : Ω) : Y ω z = Yc ω z + m := by simp [Yc]
    change (∫ ω, Y ω z ∂μ) = b z + m
    simp only [hh]
    change Integrable (fun ω => Yc ω z) μ at hz
    rw [integral_add hz (integrable_const m)]
    simp [b]
  have hAvg : (∫ z, A z ∂γ) = m := by
    have hbInt : Integrable b γ := hcInt.integral_prod_right
    rw [integral_congr_ae hShift, integral_add hbInt (integrable_const m)]
    change (∫ z, ∫ ω, Yc ω z ∂μ ∂stdGaussian E) + _ = m
    simp [hbMean]
  change Var[A; γ] ≤ _
  rw [variance_eq_integral hAm.aemeasurable, hAvg, ← hσ2]
  refine (integral_congr_ae ?_).trans_le hbBound
  filter_upwards [hShift] with z hz
  change (A z - m) ^ 2 = (b z) ^ 2
  rw [hz, add_sub_cancel_right]


private theorem meanProjectedEnergy_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ E) (hS : ∀ u : E, Measurable (fun ω => (S ω).starProjection u)) :
    0 ≤ meanProjectedEnergy μ S := by
  by_cases h : Nonempty {z : E // ‖z‖ = 1}
  · obtain ⟨z⟩ := h
    exact (integral_nonneg (fun _ => sq_nonneg _)).trans (by
      simpa [z.property] using projectedEnergy_le_meanProjectedEnergy μ S hS (z : E))
  · unfold meanProjectedEnergy
    have he : (Set.range fun z : {z : E // ‖z‖ = 1} =>
        ∫ ω, ‖(S ω).starProjection z‖ ^ 2 ∂μ) = ∅ := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact False.elim (h ⟨z⟩)
      · simp
    rw [he, Real.sSup_empty]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The common-law variance bound of Lemma 3.2 for the entire Gaussian matrix,
with the same row-space coefficient as for one column. -/
theorem gaussianMatrixProjection_variance_contraction {n k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ u : EuclideanSpace ℝ (Fin n), Measurable (fun ω => (S ω).starProjection u))
    (Y : Ω → GaussianColumnHilbert n k → ℝ) (hY : Measurable (Function.uncurry Y))
    (hObs : ∀ ω, Measurable[MeasurableSpace.comap
      (columnwiseSubspace (S ω)).orthogonalProjectionOnto inferInstance] (Y ω))
    (Y₀ : GaussianColumnHilbert n k → ℝ)
    (hLp : MemLp Y₀ 2 (stdGaussian (GaussianColumnHilbert n k)))
    (hLaw : ∀ ω, IdentDistrib (Y ω) Y₀
      (stdGaussian (GaussianColumnHilbert n k)) (stdGaussian (GaussianColumnHilbert n k))) :
    Var[fun z => ∫ ω, Y ω z ∂μ; stdGaussian (GaussianColumnHilbert n k)] ≤
      meanProjectedEnergy μ S * Var[Y₀; stdGaussian (GaussianColumnHilbert n k)] := by
  apply gaussianProjection_variance_contraction μ (fun ω => columnwiseSubspace (S ω)) _
    (meanProjectedEnergy μ S) (meanProjectedEnergy_nonneg μ S hS)
    (projected_columns_le_meanProjectedEnergy μ S hS) Y hY hObs Y₀ hLp hLaw
  intro u
  simp_rw [columnwiseSubspace_starProjection]
  exact (WithLp.measurable_toLp _ _).comp (measurable_pi_iff.mpr fun j => hS (u j))

end SketchOrientation
