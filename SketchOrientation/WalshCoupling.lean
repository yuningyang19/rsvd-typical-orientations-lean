import SketchOrientation.WalshSampling

/-!
# Walsh tables and independent signs
-/

open Function
open scoped BigOperators

noncomputable section
namespace SketchOrientation.Edge.Walsh

private def rowParity {m ell : ℕ} (c : Fin ell → Label m) :
    Label m →ₗ[ZMod 2] (Fin ell → ZMod 2) :=
  LinearMap.pi fun j => ∑ t, c j t • LinearMap.proj t

private theorem rowParity_apply {m ell : ℕ} (c : Fin ell → Label m) (r : Label m)
    (j : Fin ell) : rowParity c r j = parity r (c j) := by
  simp [rowParity, parity, LinearMap.sum_apply, mul_comm]

private theorem rowParity_surjective {m ell : ℕ} (c : Fin ell → Label m)
    (hc : LinearIndependent (ZMod 2) c) : Surjective (rowParity c) := by
  intro y
  let f := Fintype.linearCombination (ZMod 2) c
  have hf : Injective f := linearIndependent_iff_injective_fintypeLinearCombination.1 hc
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective hf
    (Fintype.linearCombination (ZMod 2) y)
  refine ⟨fun t => g (Pi.single t 1), ?_⟩
  ext j
  have h := DFunLike.congr_fun hg (Pi.single j 1)
  simp only [LinearMap.dualMap_apply, f,
    Fintype.linearCombination_apply_single, one_smul] at h
  rw [rowParity_apply, ← h, LinearMap.pi_apply_eq_sum_univ g (c j)]
  apply Finset.sum_congr rfl
  intro t _
  have hsingle : (Pi.single (M := fun _ : Fin m => ZMod 2) t 1) =
      (fun u => if t = u then 1 else 0) := by
    ext u
    simp [Pi.single_apply, eq_comm]
  change g (Pi.single t 1) * c j t = c j t * g (fun u => if t = u then 1 else 0)
  rw [hsingle, mul_comm]

private def rowsParity {m s ell : ℕ} (c : Fin ell → Label m) :
    (Fin s → Label m) →ₗ[ZMod 2] (Fin s → Fin ell → ZMod 2) :=
  LinearMap.pi fun i => (rowParity c).comp (LinearMap.proj i)

private def signEquiv : ZMod 2 ≃ Bool :=
  Equiv.ofBijective signBit (by decide)

private def tableEquiv {s ell : ℕ} (a : Fin s → ZMod 2) (b : Fin ell → ZMod 2) :
    (Fin s → Fin ell → ZMod 2) ≃ (Fin s → Fin ell → Bool) :=
  Equiv.piCongrRight fun i => Equiv.piCongrRight fun j =>
    (Equiv.addRight (a i)).trans ((Equiv.addRight (b j)).trans signEquiv)

/-- If the column labels are linearly independent, independently drawn uniform
rows produce a uniform table, including after any deterministic sign flips. -/
theorem uniformMean_signedTable_of_linearIndependent {m s ell : ℕ}
    (c : Fin ell → Label m) (hc : LinearIndependent (ZMod 2) c)
    (a : Fin s → ZMod 2) (b : Fin ell → ZMod 2) (f : (Fin s → Fin ell → Bool) → ℝ) :
    uniformMean (fun r => f (signedTable r c a b)) = uniformMean f := by
  have hq : Surjective (rowsParity (s := s) c) := by
    intro T
    choose r hr using fun i : Fin s => rowParity_surjective c hc (T i)
    exact ⟨r, funext hr⟩
  calc
    _ = uniformMean (fun r => f (tableEquiv a b (rowsParity c r))) := by
      congr 1
      ext r
      congr 1
      ext i j
      change signBit (parity (r i) (c j) + a i + b j) =
        signBit (rowParity c (r i) j + a i + b j)
      rw [rowParity_apply]
    _ = _ := (uniformMean_linear (rowsParity c) hq (fun T => f (tableEquiv a b T))).trans
      (uniformMean_equiv (tableEquiv a b) f)

private def relationMap {m ell : ℕ} (a : Fin ell → ZMod 2) :
    (Fin ell → Label m) →ₗ[ZMod 2] Label m :=
  ∑ j, a j • LinearMap.proj j

private theorem relationMap_apply {m ell : ℕ} (a : Fin ell → ZMod 2)
    (c : Fin ell → Label m) : relationMap a c = ∑ j, a j • c j := by
  simp [relationMap, LinearMap.sum_apply]

private theorem relationMap_surjective {m ell : ℕ} (a : Fin ell → ZMod 2)
    (ha : a ≠ 0) : Surjective (relationMap (m := m) a) := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  intro y
  refine ⟨Pi.single j ((a j)⁻¹ • y), ?_⟩
  rw [relationMap_apply, Finset.sum_eq_single j]
  · simp [smul_smul, hj]
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

/-- Union bound over the nonzero binary coefficient vectors. -/
theorem probability_dependent_columns_le {m ell : ℕ} :
    uniformProbability (fun c : Fin ell → Label m => ¬LinearIndependent (ZMod 2) c) ≤
      (2 : ℝ)^ell / (2 : ℝ)^m := by
  classical
  let A := {a : Fin ell → ZMod 2 // a ≠ 0}
  have hcover (c : Fin ell → Label m) (hc : ¬LinearIndependent (ZMod 2) c) :
      ∃ a : A, relationMap a.1 c = 0 := by
    rw [Fintype.linearIndependent_iff] at hc
    push Not at hc
    obtain ⟨a, ha, j, hj⟩ := hc
    exact ⟨⟨a, fun hz => hj (congrFun hz j)⟩, by rwa [relationMap_apply]⟩
  have hep (a : A) : uniformProbability (fun c => relationMap (m := m) a.1 c = 0) =
      1 / (2 : ℝ)^m := by
    change uniformMean (fun c => (fun x : Label m => indicator (x = 0)) (relationMap a.1 c)) = _
    rw [uniformMean_linear (relationMap a.1) (relationMap_surjective _ a.2)
      (fun x : Label m => indicator (x = 0))]
    change uniformProbability (fun x : Label m => x = 0) = _
    rw [uniformProbability_eq_card]
    simp
  calc
    _ ≤ uniformProbability (fun c : Fin ell → Label m => ∃ a : A, relationMap a.1 c = 0) :=
      uniformProbability_mono hcover
    _ ≤ ∑ a : A, uniformProbability (fun c : Fin ell → Label m => relationMap a.1 c = 0) :=
      uniformProbability_exists_le_sum _
    _ = (Fintype.card A : ℝ) / (2 : ℝ)^m := by
      simp_rw [hep]
      simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := Fintype.card_le_of_injective (Subtype.val : A → (Fin ell → ZMod 2))
        Subtype.val_injective
      have h' : Fintype.card A ≤ 2 ^ ell := by
        simpa only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ZMod.card] using h
      exact_mod_cast h'


/-- At fixed column labels, average the observable over the fair signs.
Only a non-independent column tuple can make the model with replacement
disagree with the independent sign table. -/
theorem abs_uniformMean_independentTable_sub {m s ell : ℕ}
    (f : (Fin s → Fin ell → Bool) → ℝ) (hf₀ : ∀ t, 0 ≤ f t) (hf₁ : ∀ t, f t ≤ 1) :
    |uniformMean (fun d : IndependentDraw m s ell => f (independentTable d)) -
      uniformMean f| ≤ (2 : ℝ)^ell / (2 : ℝ)^m := by
  classical
  let g (c : Fin ell → Label m) (a : Fin s → ZMod 2) (b : Fin ell → ZMod 2) :=
    uniformMean fun r => f (signedTable r c a b)
  have hg (c a b) : |g c a b - uniformMean f| ≤
      indicator (¬LinearIndependent (ZMod 2) c) := by
    by_cases hc : LinearIndependent (ZMod 2) c
    · simp [indicator, hc, g, uniformMean_signedTable_of_linearIndependent _ hc]
    · simp only [indicator, hc, not_false_eq_true, ↓reduceIte]
      apply abs_le.2
      have h₀ : 0 ≤ g c a b := uniformMean_nonneg fun _ => hf₀ _
      have h₁ : g c a b ≤ 1 := uniformMean_le_one fun _ => hf₁ _
      have h₂ : 0 ≤ uniformMean f := uniformMean_nonneg hf₀
      have h₃ : uniformMean f ≤ 1 := uniformMean_le_one hf₁
      constructor <;> linarith
  have avg (c : Fin ell → Label m) : |(uniformMean fun a => uniformMean (g c a)) -
      uniformMean f| ≤ indicator (¬LinearIndependent (ZMod 2) c) := by
    have hb (a : Fin s → ZMod 2) : |uniformMean (g c a) - uniformMean f| ≤
        indicator (¬LinearIndependent (ZMod 2) c) := by
      nth_rw 1 [← uniformMean_const (A := Fin ell → ZMod 2) (uniformMean f)]
      refine (abs_uniformMean_sub_le (fun b => hg c a b)).trans_eq ?_
      exact uniformMean_const _
    nth_rw 1 [← uniformMean_const (A := Fin s → ZMod 2) (uniformMean f)]
    refine (abs_uniformMean_sub_le hb).trans_eq ?_
    exact uniformMean_const _
  have hreorder : uniformMean (fun d : IndependentDraw m s ell => f (independentTable d)) =
      uniformMean (fun c => uniformMean (fun a => uniformMean (g c a))) := by
    simp only [IndependentDraw, independentTable, uniformMean_prod']
    rw [uniformMean_comm]
    apply congrArg uniformMean
    funext c
    rw [uniformMean_comm]
    apply congrArg uniformMean
    funext a
    exact uniformMean_comm _
  rw [hreorder]
  nth_rw 1 [← uniformMean_const (A := Fin ell → Label m) (uniformMean f)]
  exact (abs_uniformMean_sub_le avg).trans probability_dependent_columns_le

/-- Comparison with the independent uniform sign table for any observable in
the unit interval. The terms bound row collisions, column collisions, and
linear dependence of the columns respectively. -/
theorem abs_uniformMean_table_sub {m s ell : ℕ}
    [Nonempty (Fin s ↪ Label m)] [Nonempty (Fin ell ↪ Label m)]
    (f : (Fin s → Fin ell → Bool) → ℝ) (hf₀ : ∀ t, 0 ≤ f t) (hf₁ : ∀ t, f t ≤ 1) :
    |uniformMean (fun d : Draw m s ell => f (table d)) - uniformMean f| ≤
      ((s : ℝ)^2 + (ell : ℝ)^2 + (2 : ℝ)^ell) / (2 : ℝ)^m := by
  let g (r : Fin s → Label m) (c : Fin ell → Label m) :=
    uniformMean fun a => uniformMean fun b => f (signedTable r c a b)
  have hg₀ (r c) : 0 ≤ g r c := uniformMean_nonneg fun _ => uniformMean_nonneg fun _ => hf₀ _
  have hg₁ (r c) : g r c ≤ 1 := uniformMean_le_one fun _ => uniformMean_le_one fun _ => hf₁ _
  let μ := uniformMean fun c : Fin ell ↪ Label m => uniformMean fun r => g r c
  let ν := uniformMean (fun d : IndependentDraw m s ell => f (independentTable d))
  have h₁ : |uniformMean (fun d : Draw m s ell => f (table d)) - μ| ≤
      (s : ℝ)^2 / (2 : ℝ)^m := by
    simp only [Draw, table, uniformMean_prod']
    change |uniformMean (fun r : Fin s ↪ Label m => uniformMean fun c : Fin ell ↪ Label m =>
      g r c) - μ| ≤ _
    rw [uniformMean_comm]
    have h (c : Fin ell ↪ Label m) : |(uniformMean fun r : Fin s ↪ Label m => g r c) -
        (uniformMean fun r => g r c)| ≤ (s : ℝ)^2 / (2 : ℝ)^m :=
      (abs_uniformMean_embedding_sub (fun r => g r c) (fun r => hg₀ r c) (fun r => hg₁ r c)).trans
        (probability_collision_le m s)
    exact (abs_uniformMean_sub_le h).trans_eq (uniformMean_const _)
  have h₂ : |μ - ν| ≤ (ell : ℝ)^2 / (2 : ℝ)^m := by
    simp only [μ, ν, IndependentDraw, independentTable, uniformMean_prod']
    change |uniformMean (fun c : Fin ell ↪ Label m => uniformMean fun r => g r c) -
      uniformMean (fun r => uniformMean (g r))| ≤ _
    rw [uniformMean_comm (g : (Fin s → Label m) → (Fin ell → Label m) → ℝ)]
    exact (abs_uniformMean_embedding_sub _ (fun c => uniformMean_nonneg fun r => hg₀ r c)
      (fun c => uniformMean_le_one fun r => hg₁ r c)).trans (probability_collision_le m ell)
  calc
    _ ≤ |uniformMean (fun d : Draw m s ell => f (table d)) - μ| +
        (|μ - ν| + |ν - uniformMean f|) := by
      apply (abs_sub_le _ μ _).trans
      exact add_le_add_right (abs_sub_le _ ν _) _
    _ ≤ (s : ℝ)^2 / (2 : ℝ)^m +
        ((ell : ℝ)^2 / (2 : ℝ)^m + (2 : ℝ)^ell / (2 : ℝ)^m) :=
      add_le_add h₁ (add_le_add h₂ (abs_uniformMean_independentTable_sub f hf₀ hf₁))
    _ = _ := by ring

end SketchOrientation.Edge.Walsh
