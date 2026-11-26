import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace SketchOrientation

open MeasureTheory Set

/-- If the joint image is a product, conditioning an integrable function on
the first image coordinate integrates the second coordinate in its own law. -/
theorem condExp_of_product_image {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure B)
    [IsProbabilityMeasure ν] (X : Ω → A) (H : Ω → B)
    (hX : Measurable X) (hH : Measurable H)
    (hProd : μ.map (fun ω => (X ω, H ω)) = (μ.map X).prod ν)
    (F : A × B → ℝ) (hF : Measurable F)
    (hInt : Integrable (fun ω => F (X ω, H ω)) μ) :
    μ[(fun ω => F (X ω, H ω)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => ∫ h, F (X ω, h) ∂ν := by
  let J := fun ω => (X ω, H ω)
  let M := fun a => ∫ h, F (a, h) ∂ν
  have hJ : Measurable J := hX.prodMk hH
  have hM : Measurable M := hF.stronglyMeasurable.integral_prod_right'.measurable
  have hM_obs : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (M ∘ X) :=
    (hM.comp (comap_measurable X)).stronglyMeasurable
  have hFJ : Integrable F ((μ.map X).prod ν) := by
    rw [← hProd, integrable_map_measure hF.aestronglyMeasurable hJ.aemeasurable]
    exact hInt
  have hMInt : Integrable M (μ.map X) := hFJ.integral_prod_left
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hInt
    (fun s _ _ => (hMInt.comp_measurable hX).integrableOn) ?_ hM_obs.aestronglyMeasurable
  intro s hs _
  change ∃ t, MeasurableSet t ∧ X ⁻¹' t = s at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have ht' : MeasurableSet (t ×ˢ (Set.univ : Set B)) := ht.prod MeasurableSet.univ
  have he : J ⁻¹' (t ×ˢ Set.univ) = X ⁻¹' t := by ext ω; simp [J]
  change (∫ ω in X ⁻¹' t, M (X ω) ∂μ) = ∫ ω in X ⁻¹' t, F (J ω) ∂μ
  calc
    _ = ∫ a in t, M a ∂μ.map X :=
      (setIntegral_map ht hM.aestronglyMeasurable hX.aemeasurable).symm
    _ = ∫ p in t ×ˢ Set.univ, F p ∂(μ.map X).prod ν := by
      rw [setIntegral_prod F hFJ.integrableOn]
      simp [M]
    _ = ∫ p in t ×ˢ Set.univ, F p ∂μ.map J := by rw [hProd]
    _ = _ := by rw [setIntegral_map ht' hF.aestronglyMeasurable hJ.aemeasurable, he]

/-- Averaging over an independent first coordinate commutes with conditioning
on a measurable function of the second coordinate. -/
theorem condExp_integral_prod_left {P G V : Type*} [MeasurableSpace P]
    [MeasurableSpace G] [MeasurableSpace V]
    (ν : Measure P) [IsProbabilityMeasure ν] (μ : Measure G) [IsProbabilityMeasure μ]
    (X : G → V) (hX : Measurable X)
    (f : P × G → ℝ) (g : P × V → ℝ) (hg : Measurable g)
    (hf : Integrable f (ν.prod μ))
    (h : (ν.prod μ)[f | MeasurableSpace.comap (Prod.map id X) inferInstance] =ᵐ[ν.prod μ]
      g ∘ Prod.map id X) :
    μ[(fun x => ∫ p, f (p, x) ∂ν) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (fun x => ∫ p, g (p, X x) ∂ν) := by
  let Y : P × G → P × V := Prod.map id X
  have hY : Measurable Y := measurable_id.prodMap hX
  have hgi : Integrable (g ∘ Y) (ν.prod μ) := integrable_condExp.congr h
  have hmg : Measurable (fun x => ∫ p, g (p, x) ∂ν) :=
    hg.stronglyMeasurable.integral_prod_left'.measurable
  have hmg' : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun x => ∫ p, g (p, X x) ∂ν) :=
    (hmg.comp (comap_measurable X)).stronglyMeasurable
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf.integral_prod_right
    (fun s _ _ => hgi.integral_prod_right.integrableOn) ?_ hmg'.aestronglyMeasurable
  intro s hs _
  have hS : MeasurableSet[MeasurableSpace.comap Y inferInstance] ((Set.univ : Set P) ×ˢ s) := by
    obtain ⟨t, ht, rfl⟩ := hs
    refine ⟨(Set.univ : Set P) ×ˢ t, MeasurableSet.univ.prod ht, ?_⟩
    ext x
    simp [Y]
  have hgOn : IntegrableOn (g ∘ Y) ((Set.univ : Set P) ×ˢ s) (ν.prod μ) := hgi.integrableOn
  have hfOn : IntegrableOn f ((Set.univ : Set P) ×ˢ s) (ν.prod μ) := hf.integrableOn
  have he : (ν.prod μ).restrict ((Set.univ : Set P) ×ˢ s) = ν.prod (μ.restrict s) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hset :
      (∫ z in (Set.univ : Set P) ×ˢ s, (g ∘ Y) z ∂ν.prod μ) =
        ∫ z in (Set.univ : Set P) ×ˢ s, f z ∂ν.prod μ := by
    rw [← setIntegral_condExp hY.comap_le hf hS]
    exact setIntegral_congr_ae (hY.comap_le _ hS) (h.symm.mono fun _ hz _ => hz)
  rw [IntegrableOn, he] at hgOn hfOn
  rw [he, integral_prod_symm _ hgOn, integral_prod_symm _ hfOn] at hset
  exact hset

end SketchOrientation
