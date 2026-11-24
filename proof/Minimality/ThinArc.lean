module

public import Mathlib

/-!
# Thin-solid arc and Chebyshev line-fit lemmas (L3 and L4)

* `exists_dir_small_dots`: L3 (arc lemma), finding a unit direction `(α, β)` whose dot products
  with at most `M` vectors of norm `≤ R` are all bounded by `(1 - 1 / (2 * (M + 1)^2)) * R`.
* `exists_line_fit`: L4 (Chebyshev line fit), Helly's theorem in `ℝ × ℝ` reducing a global
  `E`-strip fit to 3-point chord bounds.
-/

set_option autoImplicit false

namespace Minimality

open Finset

@[expose] public section

section ArcLemma

/-- Core of L3: two unit directions cannot both see one vector at more than `λ|c|` when
`2λ² > 1 + |ν|`. -/
private theorem two_dirs_bound (α β α' β' p q : ℝ) (h1 : α ^ 2 + β ^ 2 = 1)
    (h2 : α' ^ 2 + β' ^ 2 = 1) :
    (α * p + β * q) ^ 2 + (α' * p + β' * q) ^ 2 ≤
      (1 + |α * α' + β * β'|) * (p ^ 2 + q ^ 2) := by
  set A := α * p + β * q
  set A' := α * q - β * p
  set B := α' * p + β' * q
  set B' := α' * q - β' * p
  have hA : A ^ 2 + A' ^ 2 = p ^ 2 + q ^ 2 := by
    simp only [A, A']; linear_combination (p ^ 2 + q ^ 2) * h1
  have hB : B ^ 2 + B' ^ 2 = p ^ 2 + q ^ 2 := by
    simp only [B, B']; linear_combination (p ^ 2 + q ^ 2) * h2
  have key : A ^ 2 + B ^ 2 = (p ^ 2 + q ^ 2) + (α * α' + β * β') * (A * B - A' * B') := by
    simp only [A, A', B, B']
    linear_combination
      ((p ^ 2 + q ^ 2) / 2 - (α' * p + β' * q) ^ 2 + (α' ^ 2 + β' ^ 2) * (p ^ 2 + q ^ 2) / 2) * h1
      + ((p ^ 2 + q ^ 2) / 2 - (α * p + β * q) ^ 2 + (α ^ 2 + β ^ 2) * (p ^ 2 + q ^ 2) / 2) * h2
  have hQ1 : A * B - A' * B' ≤ p ^ 2 + q ^ 2 := by nlinarith [sq_nonneg (A - B), sq_nonneg (A' + B')]
  have hQ2 : -(A * B - A' * B') ≤ p ^ 2 + q ^ 2 := by
    nlinarith [sq_nonneg (A + B), sq_nonneg (A' - B')]
  rw [key]
  rcases le_total 0 (α * α' + β * β') with hν | hν
  · rw [abs_of_nonneg hν]; nlinarith [mul_le_mul_of_nonneg_left hQ1 hν]
  · rw [abs_of_nonpos hν]; nlinarith [mul_le_mul_of_nonneg_left hQ2 (neg_nonneg.2 hν)]

/-- Mathlib's bound gives the rational constant `1 - 2 / K^2`. -/
private theorem cos_pi_div_le (K : ℕ) (hK : 1 ≤ K) :
    Real.cos (Real.pi / K) ≤ 1 - 2 / (K : ℝ) ^ 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h := Real.cos_le_one_sub_mul_cos_sq (x := Real.pi / K) (by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self Real.pi_pos.le (by exact_mod_cast hK))
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc Real.cos (Real.pi / K) ≤ 1 - 2 / Real.pi ^ 2 * (Real.pi / K) ^ 2 := h
    _ = 1 - 2 / (K : ℝ) ^ 2 := by field_simp

private theorem abs_cos_mul_pi_div_le {d M : ℕ} (hd1 : 1 ≤ d) (hdM : d ≤ M) :
    |Real.cos ((d : ℝ) * Real.pi / (M + 1))| ≤ 1 - 2 / ((M : ℝ) + 1) ^ 2 := by
  set K : ℝ := (M : ℝ) + 1
  have hKpos : 0 < K := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdM' : (d : ℝ) ≤ M := by exact_mod_cast hdM
  set θ : ℝ := (d : ℝ) * Real.pi / K
  have hθ_lo : Real.pi / K ≤ θ := by
    simp only [θ]; exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hpi.le hd1') hKpos.le
  have hθ_hi : θ ≤ Real.pi := by
    simp only [θ]; rw [div_le_iff₀ hKpos]
    nlinarith [show (d : ℝ) ≤ K by linarith]
  have hcos_bound : Real.cos (Real.pi / K) ≤ 1 - 2 / K ^ 2 := by
    simpa [K] using cos_pi_div_le (M + 1) (by omega)
  rcases le_total 0 (Real.cos θ) with hpos | hneg
  · rw [abs_of_nonneg hpos]
    exact (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hθ_hi hθ_lo).trans hcos_bound
  · rw [abs_of_nonpos hneg, ← Real.cos_pi_sub]
    have hsub_lo : Real.pi / K ≤ Real.pi - θ := by
      simp only [θ]; rw [le_sub_iff_add_le]; field_simp
      nlinarith [show (d : ℝ) + 1 ≤ K by linarith]
    have hsub_hi : Real.pi - θ ≤ Real.pi := sub_le_self _ (by positivity)
    exact (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hsub_hi hsub_lo).trans hcos_bound

theorem exists_dir_small_dots {ι : Type*} (S : Finset ι) (p q : ι → ℝ) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : ∀ k ∈ S, p k ^ 2 + q k ^ 2 ≤ R ^ 2) (M : ℕ) (hM : S.card ≤ M) :
    ∃ α β : ℝ, α ^ 2 + β ^ 2 = 1 ∧
      ∀ k ∈ S, |α * p k + β * q k| ≤ (1 - 1 / (2 * ((M : ℝ) + 1) ^ 2)) * R := by
  set K : ℝ := (M : ℝ) + 1
  set lam : ℝ := 1 - 1 / (2 * K ^ 2)
  have hK1 : 1 ≤ K := by simp [K]
  have hlam0 : 0 ≤ lam := by
    have h1 : 1 / (2 * K ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  let α : ℕ → ℝ := fun j => Real.cos ((j : ℝ) * Real.pi / K)
  let β : ℕ → ℝ := fun j => Real.sin ((j : ℝ) * Real.pi / K)
  by_contra hnone
  push Not at hnone
  have hex : ∀ j : ℕ, ∃ k ∈ S, lam * R < |α j * p k + β j * q k| := by
    intro j
    exact hnone (α j) (β j) (Real.cos_sq_add_sin_sq _)
  choose f hf using hex
  have hcard : S.card < (Finset.range (M + 1)).card := by
    rw [Finset.card_range]; omega
  obtain ⟨j, hj, l, hl, hjl, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard fun j _ => (hf j).1
  wlog hjlt : j < l generalizing j l
  · exact this l hl j hj hjl.symm hfeq.symm (lt_of_le_of_ne (not_lt.1 hjlt) hjl.symm)
  set k := f j
  have hkS : k ∈ S := (hf j).1
  have hkj : lam * R < |α j * p k + β j * q k| := (hf j).2
  have hkl : lam * R < |α l * p k + β l * q k| := by simpa [k, ← hfeq] using (hf l).2
  have hsqj : (lam * R) ^ 2 < (α j * p k + β j * q k) ^ 2 := by
    nlinarith [sq_abs (α j * p k + β j * q k), abs_nonneg (α j * p k + β j * q k),
      mul_nonneg hlam0 hR0]
  have hsql : (lam * R) ^ 2 < (α l * p k + β l * q k) ^ 2 := by
    nlinarith [sq_abs (α l * p k + β l * q k), abs_nonneg (α l * p k + β l * q k),
      mul_nonneg hlam0 hR0]
  have h2dirs := two_dirs_bound (α j) (β j) (α l) (β l) (p k) (q k)
    (Real.cos_sq_add_sin_sq _) (Real.cos_sq_add_sin_sq _)
  have hdot : α j * α l + β j * β l = Real.cos (((l - j : ℕ) : ℝ) * Real.pi / K) := by
    have hsub : ((l : ℝ) * Real.pi / K) - ((j : ℝ) * Real.pi / K) =
        ((l - j : ℕ) : ℝ) * Real.pi / K := by
      rw [Nat.cast_sub hjlt.le]; ring
    rw [← hsub, Real.cos_sub]
    simp only [α, β]; ring
  have hcos : |α j * α l + β j * β l| ≤ 1 - 2 / K ^ 2 := by
    rw [hdot]
    have hlM : l ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    exact abs_cos_mul_pi_div_le (by omega) (by omega)
  have hpkq := hR k hkS
  have hupper : (α j * p k + β j * q k) ^ 2 + (α l * p k + β l * q k) ^ 2 ≤
      (2 - 2 / K ^ 2) * R ^ 2 := by
    calc (α j * p k + β j * q k) ^ 2 + (α l * p k + β l * q k) ^ 2
        ≤ (1 + |α j * α l + β j * β l|) * (p k ^ 2 + q k ^ 2) := h2dirs
      _ ≤ (1 + (1 - 2 / K ^ 2)) * R ^ 2 := by
          gcongr
          linarith [abs_nonneg (α j * α l + β j * β l)]
      _ = (2 - 2 / K ^ 2) * R ^ 2 := by ring
  have hlower : (2 - 2 / K ^ 2) * R ^ 2 ≤ 2 * (lam * R) ^ 2 := by
    have hlam_sq : 2 - 2 / K ^ 2 ≤ 2 * lam ^ 2 := by
      simp only [lam]
      have : 2 * (1 - 1 / (2 * K ^ 2)) ^ 2 - (2 - 2 / K ^ 2) = 1 / (2 * K ^ 4) := by
        field_simp; ring
      nlinarith [show (0 : ℝ) < 1 / (2 * K ^ 4) by positivity]
    nlinarith [sq_nonneg R]
  linarith

end ArcLemma

section LineFit

/-- The 3-point case (sorted, `z₁ < z₃`). -/
private theorem fit3_sorted (z₁ z₂ z₃ y₁ y₂ y₃ E : ℝ) (h13 : z₁ < z₃)
    (hc : |y₂ - ((z₃ - z₂) * y₁ + (z₂ - z₁) * y₃) / (z₃ - z₁)| ≤ 2 * E) :
    ∃ t β : ℝ, |y₁ - t * z₁ - β| ≤ E ∧ |y₂ - t * z₂ - β| ≤ E ∧ |y₃ - t * z₃ - β| ≤ E := by
  set c := y₂ - ((z₃ - z₂) * y₁ + (z₂ - z₁) * y₃) / (z₃ - z₁) with hcdef
  have hz : z₃ - z₁ ≠ 0 := by linarith
  refine ⟨(y₃ - y₁) / (z₃ - z₁), y₁ - (y₃ - y₁) / (z₃ - z₁) * z₁ + c / 2, ?_, ?_, ?_⟩
  · have : y₁ - (y₃ - y₁) / (z₃ - z₁) * z₁ - (y₁ - (y₃ - y₁) / (z₃ - z₁) * z₁ + c / 2) = -(c / 2) := by
      ring
    rw [this, abs_neg, abs_div]; norm_num; linarith [abs_nonneg c]
  · have : y₂ - (y₃ - y₁) / (z₃ - z₁) * z₂ - (y₁ - (y₃ - y₁) / (z₃ - z₁) * z₁ + c / 2) = c / 2 := by
      rw [hcdef]; field_simp; ring
    rw [this, abs_div]; norm_num; linarith [abs_nonneg c]
  · have : y₃ - (y₃ - y₁) / (z₃ - z₁) * z₃ - (y₁ - (y₃ - y₁) / (z₃ - z₁) * z₁ + c / 2) = -(c / 2) := by
      field_simp; ring
    rw [this, abs_neg, abs_div]; norm_num; linarith [abs_nonneg c]

private theorem fit3_equal_levels (y₁ y₂ y₃ E : ℝ)
    (h12 : |y₁ - y₂| ≤ 2 * E) (h13 : |y₁ - y₃| ≤ 2 * E) (h23 : |y₂ - y₃| ≤ 2 * E) :
    ∃ β : ℝ, |y₁ - β| ≤ E ∧ |y₂ - β| ≤ E ∧ |y₃ - β| ≤ E := by
  set M := max (max y₁ y₂) y₃
  set m := min (min y₁ y₂) y₃
  have hE0 : 0 ≤ E := by linarith [abs_nonneg (y₁ - y₂)]
  have hMm : M - m ≤ 2 * E := by
    simp only [M, m, sub_le_iff_le_add, max_le_iff]
    have hm1 : y₁ - 2 * E ≤ min (min y₁ y₂) y₃ :=
      le_min (le_min (by linarith) (by linarith [abs_sub_le_iff.1 h12])) (by linarith [abs_sub_le_iff.1 h13])
    have hm2 : y₂ - 2 * E ≤ min (min y₁ y₂) y₃ :=
      le_min (le_min (by linarith [abs_sub_le_iff.1 h12]) (by linarith)) (by linarith [abs_sub_le_iff.1 h23])
    have hm3 : y₃ - 2 * E ≤ min (min y₁ y₂) y₃ :=
      le_min (le_min (by linarith [abs_sub_le_iff.1 h13]) (by linarith [abs_sub_le_iff.1 h23])) (by linarith)
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨(M + m) / 2, ?_, ?_, ?_⟩
  · have hM : y₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    have hm : m ≤ y₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [abs_le]; constructor <;> linarith
  · have hM : y₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
    have hm : m ≤ y₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    rw [abs_le]; constructor <;> linarith
  · have hM : y₃ ≤ M := le_max_right _ _
    have hm : m ≤ y₃ := min_le_right _ _
    rw [abs_le]; constructor <;> linarith

private theorem fit3_ordered {ι : Type*} (s : Finset ι) (z y : ι → ℝ) (E : ℝ)
    (hchord : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, z i ≤ z j → z j ≤ z k → z i < z k →
      |y j - ((z k - z j) * y i + (z j - z i) * y k) / (z k - z i)| ≤ 2 * E)
    (heq : ∀ i ∈ s, ∀ j ∈ s, z i = z j → |y i - y j| ≤ 2 * E)
    {a b c : ι} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : z a ≤ z b) (hbc : z b ≤ z c) :
    ∃ t β : ℝ, |y a - t * z a - β| ≤ E ∧ |y b - t * z b - β| ≤ E ∧ |y c - t * z c - β| ≤ E := by
  by_cases hac : z a < z c
  · exact fit3_sorted (z a) (z b) (z c) (y a) (y b) (y c) E hac (hchord a ha b hb c hc hab hbc hac)
  · have hca : z a = z c := le_antisymm (hab.trans hbc) (not_lt.1 hac)
    have hab' : z a = z b := le_antisymm hab (hbc.trans hca.symm.le)
    have hbc' : z b = z c := hab'.symm.trans hca
    obtain ⟨β, h1, h2, h3⟩ := fit3_equal_levels (y a) (y b) (y c) E
      (heq a ha b hb hab') (heq a ha c hc hca) (heq b hb c hc hbc')
    exact ⟨0, β, by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem exists_line_fit {ι : Type*} (s : Finset ι) (z y : ι → ℝ) (E : ℝ)
    (hlev : ∃ i ∈ s, ∃ k ∈ s, z i < z k)
    (hchord : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, z i ≤ z j → z j ≤ z k → z i < z k →
      |y j - ((z k - z j) * y i + (z j - z i) * y k) / (z k - z i)| ≤ 2 * E) :
    ∃ t β : ℝ, ∀ i ∈ s, |y i - t * z i - β| ≤ E := by
  obtain ⟨i₀, hi₀, k₀, hk₀, hzk₀⟩ := hlev
  have hE : 0 ≤ E := by
    have h0 := hchord i₀ hi₀ i₀ hi₀ k₀ hk₀ le_rfl hzk₀.le hzk₀
    have hne : z k₀ - z i₀ ≠ 0 := by linarith
    have hid : y i₀ - ((z k₀ - z i₀) * y i₀ + (z i₀ - z i₀) * y k₀) / (z k₀ - z i₀) = 0 := by
      field_simp; ring
    rw [hid, abs_zero] at h0
    linarith
  have heq : ∀ i ∈ s, ∀ j ∈ s, z i = z j → |y i - y j| ≤ 2 * E := by
    intro i hi j hj hzij
    rcases lt_or_ge (z i) (z k₀) with hlt | hge
    · have h0 := hchord i hi j hj k₀ hk₀ hzij.le (hzij ▸ hlt.le) hlt
      have hid : y j - ((z k₀ - z j) * y i + (z j - z i) * y k₀) / (z k₀ - z i) = y j - y i := by
        rw [hzij]
        have hne : z k₀ - z j ≠ 0 := by linarith
        field_simp; ring
      rw [hid, abs_sub_comm] at h0
      exact h0
    · have hlt : z i₀ < z i := hzk₀.trans_le hge
      have h0 := hchord i₀ hi₀ j hj i hi (hzij ▸ hlt.le) hzij.symm.le hlt
      have hid : y j - ((z i - z j) * y i₀ + (z j - z i₀) * y i) / (z i - z i₀) = y j - y i := by
        rw [hzij]
        have hne : z j - z i₀ ≠ 0 := by linarith
        field_simp; ring
      rw [hid, abs_sub_comm] at h0
      exact h0
  have h3 : ∀ I ⊆ s, #I ≤ 3 → ∃ t β : ℝ, ∀ i ∈ I, |y i - t * z i - β| ≤ E := by
    intro I hIs hIcard
    classical
    have hI3 : I.card = 0 ∨ I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
    rcases hI3 with h0 | h1 | h2 | h3c
    · rw [Finset.card_eq_zero.1 h0]; exact ⟨0, 0, by simp⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
      exact ⟨0, y a, fun i hi => by
        rw [Finset.mem_singleton.1 hi]; simpa using hE⟩
    · obtain ⟨a, b, hab, hIeq⟩ := Finset.card_eq_two.1 h2
      subst hIeq
      have ha : a ∈ s := hIs (Finset.mem_insert_self _ _)
      have hb : b ∈ s := hIs (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rcases le_total (z a) (z b) with h | h
      · obtain ⟨t, β, hA, hB, _⟩ := fit3_ordered s z y E hchord heq ha hb hb h le_rfl
        exact ⟨t, β, fun i hi => by
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · exact hA
          · rw [Finset.mem_singleton.1 hi']; exact hB⟩
      · obtain ⟨t, β, hB, hA, _⟩ := fit3_ordered s z y E hchord heq hb ha ha h le_rfl
        exact ⟨t, β, fun i hi => by
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · exact hA
          · rw [Finset.mem_singleton.1 hi']; exact hB⟩
    · obtain ⟨a, b, c, hab, hac, hbc, hIeq⟩ := Finset.card_eq_three.1 h3c
      subst hIeq
      have ha : a ∈ s := hIs (by simp)
      have hb : b ∈ s := hIs (by simp)
      have hc : c ∈ s := hIs (by simp)
      have hsort : ∀ x₁ x₂ x₃ : ι, x₁ ∈ s → x₂ ∈ s → x₃ ∈ s →
          z x₁ ≤ z x₂ → z x₂ ≤ z x₃ →
          (∀ i ∈ ({a, b, c} : Finset ι), i = x₁ ∨ i = x₂ ∨ i = x₃) →
          ∃ t β : ℝ, ∀ i ∈ ({a, b, c} : Finset ι), |y i - t * z i - β| ≤ E := by
        intro x₁ x₂ x₃ hx₁ hx₂ hx₃ h12 h23 hmem
        obtain ⟨t, β, h1, h2, h3'⟩ := fit3_ordered s z y E hchord heq hx₁ hx₂ hx₃ h12 h23
        refine ⟨t, β, fun i hi => ?_⟩
        rcases hmem i hi with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact h3'
      rcases le_total (z a) (z b) with h1 | h1 <;> rcases le_total (z b) (z c) with h2 | h2 <;>
        rcases le_total (z a) (z c) with h3' | h3'
      · exact hsort a b c ha hb hc h1 h2 (by simp)
      · exact hsort a b c ha hb hc h1 h2 (by simp)
      · exact hsort a c b ha hc hb h3' h2 (by simp)
      · exact hsort c a b hc ha hb h3' h1 (by simp)
      · exact hsort b a c hb ha hc h1 h3' (by simp)
      · exact hsort b c a hb hc ha h2 h3' (by simp)
      · exact hsort b a c hb ha hc h1 h3' (by simp)
      · exact hsort c b a hc hb ha h2 h1 (by simp)
  let F : ι → Set (ℝ × ℝ) := fun i => {pt | |y i - pt.1 * z i - pt.2| ≤ E}
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  have hconv : ∀ i ∈ s, Convex ℝ (F i) := by
    intro i _ a ha b hb μ ν hμ hν hμν
    simp only [F, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at ha hb ⊢
    have : y i - (μ * a.1 + ν * b.1) * z i - (μ * a.2 + ν * b.2)
        = μ * (y i - a.1 * z i - a.2) + ν * (y i - b.1 * z i - b.2) := by
      linear_combination (-(y i)) * hμν
    rw [this]
    calc |μ * (y i - a.1 * z i - a.2) + ν * (y i - b.1 * z i - b.2)|
        ≤ μ * |y i - a.1 * z i - a.2| + ν * |y i - b.1 * z i - b.2| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hμ, abs_of_nonneg hν]
      _ ≤ μ * E + ν * E := by gcongr
      _ = E := by rw [← add_mul, hμν, one_mul]
  obtain ⟨pt, hpt⟩ := Convex.helly_theorem' (𝕜 := ℝ) hconv (by
    intro I hI hcard
    rw [hrank] at hcard
    obtain ⟨t, β, h⟩ := h3 I hI hcard
    exact ⟨(t, β), Set.mem_iInter₂.2 fun i hi => h i hi⟩)
  exact ⟨pt.1, pt.2, fun i hi => Set.mem_iInter₂.1 hpt i hi⟩

end LineFit

end

end Minimality
