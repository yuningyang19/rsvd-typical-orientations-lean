import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace SketchOrientation

/-- The cosine core in (edge:cosine-matrix), with spatial rows and frequency columns. -/
noncomputable def cosineCore (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun r ν =>
    (if ν.val = 0 then 1 else Real.sqrt 2) / Real.sqrt (n : ℝ) *
      Real.cos (Real.pi * ((2 * r.val + 1) * ν.val : ℕ) / (2 * (n : ℝ)))

private theorem cosine_phase_eq_zero_iff {n a : ℕ} (hn : 0 < n) :
    Real.cos (Real.pi * (a : ℝ) / (2 * (n : ℝ))) = 0 ↔ a ≡ n [MOD 2 * n] := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hk' : (a : ℝ) = (n : ℝ) + (2 * (n : ℝ)) * (k : ℝ) := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      have hcross := (div_eq_div_iff (mul_ne_zero two_ne_zero hnR) two_ne_zero).mp hk
      linear_combination hcross / 2
    have hkZ : (a : ℤ) = (n : ℤ) + (2 * (n : ℤ)) * k := by exact_mod_cast hk'
    apply Nat.modEq_iff_dvd.mpr
    exact ⟨-k, by push_cast; linarith⟩
  · intro h
    obtain ⟨k, hk⟩ := h.symm.dvd
    push_cast at hk
    have hkR : (a : ℝ) - n = (2 * (n : ℝ)) * (k : ℝ) := by exact_mod_cast hk
    refine ⟨k, ?_⟩
    rw [show (a : ℝ) = n + (2 * (n : ℝ)) * (k : ℝ) by linarith]
    field_simp [hnR]
    ring

/-- A cosine-core entry is zero exactly at the stated residue modulo `2 n`. -/
theorem cosineCore_eq_zero_iff {n : ℕ} (r ν : Fin n) :
    cosineCore n r ν = 0 ↔ (2 * r.val + 1) * ν.val ≡ n [MOD 2 * n] := by
  have hn : 0 < n := r.pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcoef : (if ν.val = 0 then 1 else Real.sqrt 2) / Real.sqrt (n : ℝ) ≠ 0 := by
    apply div_ne_zero _ (Real.sqrt_ne_zero'.mpr hnR)
    split <;> positivity
  unfold cosineCore
  rw [mul_eq_zero, or_iff_right hcoef, cosine_phase_eq_zero_iff hn]

/-- The transpose has the same zero criterion with the frequency index first. -/
theorem cosineCore_transpose_eq_zero_iff {n : ℕ} (ν r : Fin n) :
    Matrix.transpose (cosineCore n) ν r = 0 ↔ (2 * r.val + 1) * ν.val ≡ n [MOD 2 * n] :=
  cosineCore_eq_zero_iff r ν

/-- The constant-frequency column is nonzero in every dimension. -/
theorem cosineCore_constant {n : ℕ} (r ν : Fin n) (hν : ν.val = 0) :
    cosineCore n r ν = 1 / Real.sqrt (n : ℝ) := by
  simp [cosineCore, hν]

/-- The cosine core is zero-free in every dyadic dimension. -/
theorem cosineCore_dyadic_ne_zero (j : ℕ) (r ν : Fin (2 ^ j)) :
    cosineCore (2 ^ j) r ν ≠ 0 := by
  intro hzero
  have h := (cosineCore_eq_zero_iff r ν).mp hzero
  have hc : (2 * r.val + 1).Coprime 2 := by
    apply Nat.Coprime.symm
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    omega
  have hdvd : 2 ^ j ∣ (2 * r.val + 1) * ν.val := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact (h.of_mul_left 2).trans Nat.modulus_modEq_zero
  have hz : ν.val = 0 := Nat.eq_zero_of_dvd_of_lt ((hc.pow_right j).symm.dvd_of_dvd_mul_left hdvd) ν.isLt
  rw [cosineCore_constant r ν hz] at hzero
  have hn : 0 < ((2 ^ j : ℕ) : ℝ) := by positivity
  exact (div_ne_zero one_ne_zero (Real.sqrt_ne_zero'.mpr hn)) hzero

/-- The transposed cosine core is zero-free in every dyadic dimension. -/
theorem cosineCore_transpose_dyadic_ne_zero (j : ℕ) (ν r : Fin (2 ^ j)) :
    Matrix.transpose (cosineCore (2 ^ j)) ν r ≠ 0 :=
  cosineCore_dyadic_ne_zero j r ν

private theorem odd_mul_modEq_self {a m : ℕ} (ha : Odd a) : a * m ≡ m [MOD 2 * m] := by
  obtain ⟨k, rfl⟩ := ha.exists_bit1
  rw [show (2 * k + 1) * m = m + (2 * m) * k by ring]
  exact Nat.add_modEq_left_iff.mpr (dvd_mul_right _ _)

private theorem odd_of_dvd_odd {a b : ℕ} (hdvd : a ∣ b) (hb : Odd b) : Odd a := by
  apply Nat.coprime_two_left.mp
  exact hb.coprime_two_left.coprime_dvd_right hdvd

/-- In a spatial row, the zero frequencies form the residue class of `n / g`
modulo `2 * (n / g)`, where `g = gcd (2r + 1) (2n)`. -/
theorem cosineCore_spatial_zero_iff {n : ℕ} (r ν : Fin n) :
    let g := (2 * r.val + 1).gcd (2 * n)
    let m := n / g
    cosineCore n r ν = 0 ↔ ν.val ≡ m [MOD 2 * m] := by
  let a := 2 * r.val + 1
  let g := a.gcd (2 * n)
  let m := n / g
  let c := a / g
  change cosineCore n r ν = 0 ↔ ν.val ≡ m [MOD 2 * m]
  have ha : Odd a := odd_iff_exists_bit1.mpr ⟨r.val, rfl⟩
  have hga : g ∣ a := Nat.gcd_dvd_left _ _
  have hg2n : g ∣ 2 * n := Nat.gcd_dvd_right _ _
  have hgn : g ∣ n := (odd_of_dvd_odd hga ha).coprime_two_right.dvd_of_dvd_mul_left hg2n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _)
  have hgc : g * c = a := Nat.mul_div_cancel' hga
  have hgm : g * m = n := Nat.mul_div_cancel' hgn
  have hc : Odd c := odd_of_dvd_odd ⟨g, by rw [mul_comm, hgc]⟩ ha
  have h2m : (2 * n) / g = 2 * m := by
    apply Nat.div_eq_of_eq_mul_left hg
    calc
      2 * n = 2 * (g * m) := by rw [hgm]
      _ = (2 * m) * g := by ring
  have hcop : (2 * m).Coprime c := by
    have h := (Nat.coprime_div_gcd_div_gcd hg).symm
    change ((2 * n) / g).Coprime c at h
    rwa [h2m] at h
  rw [cosineCore_eq_zero_iff]
  change a * ν.val ≡ n [MOD 2 * n] ↔ _
  have hscale : g * (2 * m) = 2 * n := by rw [mul_left_comm, hgm]
  have hrew : g * (c * ν.val) = a * ν.val := by rw [← mul_assoc, hgc]
  have hcong : (a * ν.val ≡ n [MOD 2 * n]) ↔
      c * ν.val ≡ m [MOD 2 * m] := by
    calc
      _ ↔ g * (c * ν.val) ≡ g * m [MOD g * (2 * m)] := by rw [hrew, hgm, hscale]
      _ ↔ _ := Nat.ModEq.mul_left_cancel_iff' hg.ne'
  rw [hcong]
  have hcm := odd_mul_modEq_self (m := m) hc
  exact ⟨fun h => (h.trans hcm.symm).cancel_left_of_coprime hcop,
    fun h => (h.mul_left c).trans hcm⟩

private theorem odd_index_modEq_iff {r m : ℕ} (hm : Odd m) :
    2 * r + 1 ≡ m [MOD 2 * m] ↔ r ≡ m / 2 [MOD m] := by
  have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
  have heq : 2 * (m / 2) + 1 = m := by omega
  constructor
  · intro h
    have h' : 2 * r + 1 ≡ 2 * (m / 2) + 1 [MOD 2 * m] := by rwa [heq]
    exact (Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) h').mul_left_cancel' (by decide)
  · intro h
    simpa only [heq] using (h.mul_left' 2).add_right 1

/-- In a frequency row of the transpose with `d = gcd ν n`, zeros occur exactly
when `ν / d` and `n / d` are odd and `r ≡ (n / d) / 2 mod (n / d)`. -/
theorem cosineCore_frequency_zero_iff {n : ℕ} (ν r : Fin n) :
    let d := ν.val.gcd n
    let h := ν.val / d
    let m := n / d
    Matrix.transpose (cosineCore n) ν r = 0 ↔
      Odd h ∧ Odd m ∧ r.val ≡ m / 2 [MOD m] := by
  let d := ν.val.gcd n
  let h := ν.val / d
  let m := n / d
  change Matrix.transpose (cosineCore n) ν r = 0 ↔
    Odd h ∧ Odd m ∧ r.val ≡ m / 2 [MOD m]
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ r.pos
  have hdh : d * h = ν.val := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hdm : d * m = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hcop : m.Coprime h := (Nat.coprime_div_gcd_div_gcd hd).symm
  have hscale : d * (2 * m) = 2 * n := by rw [mul_left_comm, hdm]
  have hrew : d * (h * (2 * r.val + 1)) = (2 * r.val + 1) * ν.val := by
    rw [← mul_assoc, hdh, mul_comm]
  have hcong : ((2 * r.val + 1) * ν.val ≡ n [MOD 2 * n]) ↔
      h * (2 * r.val + 1) ≡ m [MOD 2 * m] := by
    calc
      _ ↔ d * (h * (2 * r.val + 1)) ≡ d * m [MOD d * (2 * m)] := by rw [hrew, hdm, hscale]
      _ ↔ _ := Nat.ModEq.mul_left_cancel_iff' hd.ne'
  rw [cosineCore_transpose_eq_zero_iff, hcong]
  constructor
  · intro hz
    have hparity : h % 2 = m % 2 := by
      have he := hz.of_mul_right m
      change (h * (2 * r.val + 1)) % 2 = m % 2 at he
      rw [Nat.mul_mod, show (2 * r.val + 1) % 2 = 1 by omega, mul_one,
        Nat.mod_mod] at he
      exact he
    have hh : Odd h := by
      by_contra hn
      have heh : 2 ∣ h := Nat.dvd_of_mod_eq_zero (Nat.not_odd_iff.mp hn)
      have hem : 2 ∣ m := Nat.dvd_of_mod_eq_zero (hparity ▸ Nat.not_odd_iff.mp hn)
      have htwo := Nat.dvd_gcd hem heh
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at htwo
      omega
    have hm : Odd m := Nat.odd_iff.mpr (hparity ▸ Nat.odd_iff.mp hh)
    have hcop' : (2 * m).Coprime h := hh.coprime_two_left.mul_left hcop
    have hcancel := (hz.trans (odd_mul_modEq_self hh).symm).cancel_left_of_coprime hcop'
    exact ⟨hh, hm, (odd_index_modEq_iff hm).mp hcancel⟩
  · rintro ⟨hh, hm, hr⟩
    exact (((odd_index_modEq_iff hm).mpr hr).mul_left h).trans (odd_mul_modEq_self hh)

end SketchOrientation
