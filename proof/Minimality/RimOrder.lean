module

public import Minimality.MonoCorner
public import Minimality.Type21SAT.Lex2

/-!
# RimOrder: general linear-order alternating-extrema criterion for `RobUni`

Formalizes `RobUniO` over any `LinearOrder α`, `robUniO_of_noAlt` (no alternating max-min-max-min
quadruple of weak extrema implies `RobUniO`), `robUni_iff_O`, `robUni_of_noAlt`, and
`robUniLex_iff_O` in `Minimality.GenRev`.
-/

@[expose] public section

set_option autoImplicit false
open Finset

namespace Minimality.GenRev

open Minimality Minimality.H21 Minimality.LexCell Minimality.Split

/-- RobUni over any linear order (RobUni = ℝ instance, RobUniLex = lex triples). -/
def RobUniO {α : Type*} [LinearOrder α] {k : ℕ} (z : ZMod k → α) : Prop :=
  ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
    ¬ (z (B + b) ≤ z B ∧ z (B + b) ≤ z (B + c) ∧ z (B + d) ≤ z B ∧ z (B + d) ≤ z (B + c))

private theorem zmod_add_sub_one {k : ℕ} (B : ZMod k) {m : ℕ} (hm : 0 < m) :
    B + (m : ZMod k) - 1 = B + ((m - 1 : ℕ) : ZMod k) := by
  have h1 : (m : ZMod k) = ((m - 1 : ℕ) : ZMod k) + 1 := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this]
    push_cast
    ring
  rw [h1]; ring

private theorem zmod_add_add_one {k : ℕ} (B : ZMod k) (m : ℕ) :
    B + (m : ZMod k) + 1 = B + ((m + 1 : ℕ) : ZMod k) := by
  push_cast; ring

private theorem arc_min_mem_Mn {α : Type*} [LinearOrder α] {k : ℕ} {z : ZMod k → α}
    (Mn : Finset (ZMod k))
    (hMn : ∀ v ∉ Mn, z (v - 1) < z v ∨ z (v + 1) < z v)
    (B : ZMod k) {l r b : ℕ} (hlb : l < b) (hbr : b < r)
    (hbl : z (B + b) ≤ z (B + l)) (hbr_le : z (B + b) ≤ z (B + r)) :
    ∃ m : ℕ, l < m ∧ m < r ∧ B + (m : ZMod k) ∈ Mn ∧
      z (B + m) ≤ z (B + l) ∧ z (B + m) ≤ z (B + r) := by
  have hne : (Finset.Ioo l r).Nonempty := ⟨b, Finset.mem_Ioo.2 ⟨hlb, hbr⟩⟩
  obtain ⟨m, hm, hm_min⟩ := Finset.exists_min_image (Finset.Ioo l r) (fun j => z (B + j)) hne
  obtain ⟨hlm, hmr⟩ := Finset.mem_Ioo.1 hm
  have hml : z (B + m) ≤ z (B + l) := le_trans (hm_min b (Finset.mem_Ioo.2 ⟨hlb, hbr⟩)) hbl
  have hmr_le : z (B + m) ≤ z (B + r) := le_trans (hm_min b (Finset.mem_Ioo.2 ⟨hlb, hbr⟩)) hbr_le
  have hpred : z (B + (m : ZMod k) - 1) ≥ z (B + m) := by
    rw [zmod_add_sub_one B (by omega)]
    by_cases h : m - 1 = l
    · rw [h]; exact hml
    · exact hm_min (m - 1) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩)
  have hsucc : z (B + (m : ZMod k) + 1) ≥ z (B + m) := by
    rw [zmod_add_add_one B m]
    by_cases h : m + 1 = r
    · rw [h]; exact hmr_le
    · exact hm_min (m + 1) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩)
  have hmMn : B + (m : ZMod k) ∈ Mn := by
    by_contra hnot
    rcases hMn _ hnot with h | h
    · exact absurd h (not_lt_of_ge hpred)
    · exact absurd h (not_lt_of_ge hsucc)
  exact ⟨m, hlm, hmr, hmMn, hml, hmr_le⟩

private theorem arc_max_mem_Mx {α : Type*} [LinearOrder α] {k : ℕ} {z : ZMod k → α}
    (Mx : Finset (ZMod k))
    (hMx : ∀ v ∉ Mx, z v < z (v - 1) ∨ z v < z (v + 1))
    (B : ZMod k) {l r c : ℕ} (hlc : l < c) (hcr : c < r)
    (hlc_le : z (B + l) ≤ z (B + c)) (hrc_le : z (B + r) ≤ z (B + c)) :
    ∃ M : ℕ, l < M ∧ M < r ∧ B + (M : ZMod k) ∈ Mx ∧
      z (B + l) ≤ z (B + M) ∧ z (B + r) ≤ z (B + M) := by
  have hne : (Finset.Ioo l r).Nonempty := ⟨c, Finset.mem_Ioo.2 ⟨hlc, hcr⟩⟩
  obtain ⟨M, hM, hM_max⟩ := Finset.exists_max_image (Finset.Ioo l r) (fun j => z (B + j)) hne
  obtain ⟨hlM, hMr⟩ := Finset.mem_Ioo.1 hM
  have hlM_le : z (B + l) ≤ z (B + M) := le_trans hlc_le (hM_max c (Finset.mem_Ioo.2 ⟨hlc, hcr⟩))
  have hrM_le : z (B + r) ≤ z (B + M) := le_trans hrc_le (hM_max c (Finset.mem_Ioo.2 ⟨hlc, hcr⟩))
  have hpred : z (B + (M : ZMod k) - 1) ≤ z (B + M) := by
    rw [zmod_add_sub_one B (by omega)]
    by_cases h : M - 1 = l
    · rw [h]; exact hlM_le
    · exact hM_max (M - 1) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩)
  have hsucc : z (B + (M : ZMod k) + 1) ≤ z (B + M) := by
    rw [zmod_add_add_one B M]
    by_cases h : M + 1 = r
    · rw [h]; exact hrM_le
    · exact hM_max (M + 1) (Finset.mem_Ioo.2 ⟨by omega, by omega⟩)
  have hMMx : B + (M : ZMod k) ∈ Mx := by
    by_contra hnot
    rcases hMx _ hnot with h | h
    · exact absurd h (not_lt_of_ge hpred)
    · exact absurd h (not_lt_of_ge hsucc)
  exact ⟨M, hlM, hMr, hMMx, hlM_le, hrM_le⟩

/-- One rim-order lemma: `Mn` contains every weak local minimum, `Mx` every weak local maximum; if
no cyclic quadruple alternates max, min, max, min, then RobUniO. -/
theorem robUniO_of_noAlt {α : Type*} [LinearOrder α] {k : ℕ} [NeZero k] {z : ZMod k → α}
    (Mn Mx : Finset (ZMod k))
    (hMn : ∀ v ∉ Mn, z (v - 1) < z v ∨ z (v + 1) < z v)
    (hMx : ∀ v ∉ Mx, z v < z (v - 1) ∨ z v < z (v + 1))
    (halt : ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
      ¬ (B ∈ Mx ∧ B + b ∈ Mn ∧ B + c ∈ Mx ∧ B + d ∈ Mn)) :
    RobUniO z := by
  intro B b c d hb hbc hcd hdk ⟨hbB, hbc_le, hdB, hdc_le⟩
  have hB0 : B + (0 : ℕ) = B := by simp
  have hBk : B + (k : ℕ) = B := by simp
  obtain ⟨m₁, hm₁_pos, hm₁_c, hm₁_Mn, hm₁_B, hm₁_c_le⟩ :=
    arc_min_mem_Mn Mn hMn B hb hbc (by simpa [hB0] using hbB) hbc_le
  obtain ⟨m₂, hc_m₂, hm₂_k, hm₂_Mn, hm₂_c_le, hm₂_B⟩ :=
    arc_min_mem_Mn Mn hMn B hcd hdk hdc_le (by simpa [hBk] using hdB)
  obtain ⟨M₁, hm₁_M₁, hM₁_m₂, hM₁_Mx, hm₁_M₁_le, hm₂_M₁_le⟩ :=
    arc_max_mem_Mx Mx hMx B hm₁_c hc_m₂ hm₁_c_le hm₂_c_le
  have hBkm₁ : B + ((k + m₁ : ℕ) : ZMod k) = B + (m₁ : ZMod k) := by
    push_cast; simp
  obtain ⟨M₂, hm₂_M₂, hM₂_km₁, hM₂_Mx, _, _⟩ :=
    arc_max_mem_Mx Mx hMx B hm₂_k (by omega : k < k + m₁)
      (by simpa [hBk] using hm₂_B) (by simpa [hBkm₁, hBk] using hm₁_B)
  have hhalt := halt (B + M₁) (m₂ - M₁) (M₂ - M₁) (k + m₁ - M₁)
    (by omega) (by omega) (by omega) (by omega)
  have hb' : B + (M₁ : ZMod k) + ((m₂ - M₁ : ℕ) : ZMod k) = B + (m₂ : ZMod k) := by
    have : M₁ + (m₂ - M₁) = m₂ := by omega
    rw [add_assoc, ← Nat.cast_add, this]
  have hc' : B + (M₁ : ZMod k) + ((M₂ - M₁ : ℕ) : ZMod k) = B + (M₂ : ZMod k) := by
    have : M₁ + (M₂ - M₁) = M₂ := by omega
    rw [add_assoc, ← Nat.cast_add, this]
  have hd' : B + (M₁ : ZMod k) + ((k + m₁ - M₁ : ℕ) : ZMod k) = B + (m₁ : ZMod k) := by
    have : M₁ + (k + m₁ - M₁) = k + m₁ := by omega
    rw [add_assoc, ← Nat.cast_add, this, hBkm₁]
  exact hhalt ⟨hM₁_Mx, hb' ▸ hm₂_Mn, hc' ▸ hM₂_Mx, hd' ▸ hm₁_Mn⟩

theorem robUni_iff_O {k : ℕ} (z : ZMod k → ℝ) : RobUni z ↔ RobUniO z := Iff.rfl

theorem robUni_of_noAlt {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (Mn Mx : Finset (ZMod k))
    (hMn : ∀ v ∉ Mn, z (v - 1) < z v ∨ z (v + 1) < z v)
    (hMx : ∀ v ∉ Mx, z v < z (v - 1) ∨ z v < z (v + 1))
    (halt : ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
      ¬ (B ∈ Mx ∧ B + b ∈ Mn ∧ B + c ∈ Mx ∧ B + d ∈ Mn)) :
    RobUni z :=
  (robUni_iff_O z).2 (robUniO_of_noAlt Mn Mx hMn hMx halt)

private theorem lexLt3_iff_toLex (p q : ℝ × ℝ × ℝ) :
    LexLt3 p q ↔ toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) := by
  simp only [LexLt3, LexPos3, Prod.Lex.lt_iff, ofLex_toLex]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h2', h3⟩⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
    · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
  · rintro (h | ⟨h1, h2 | ⟨h2', h3⟩⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
    · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

theorem robUniLex_iff_O {k : ℕ} (z : ZMod k → ℝ × ℝ × ℝ) :
    RobUniLex z ↔ RobUniO (fun i => toLex ((z i).1, toLex ((z i).2.1, (z i).2.2))) := by
  simp only [RobUniLex, RobUniO, lexLt3_iff_toLex]
  constructor
  · intro h B b c d hb hbc hcd hdk ⟨h1, h2, h3, h4⟩
    rcases h B b c d hb hbc hcd hdk with h' | h' | h' | h'
    · exact not_lt_of_ge h1 h'
    · exact not_lt_of_ge h2 h'
    · exact not_lt_of_ge h3 h'
    · exact not_lt_of_ge h4 h'
  · intro h B b c d hb hbc hcd hdk
    by_contra hnot
    push Not at hnot
    exact h B b c d hb hbc hcd hdk hnot

end Minimality.GenRev
