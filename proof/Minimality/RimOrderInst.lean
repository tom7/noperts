module

public import Minimality.RimCell
public import Minimality.LexCell
public import Minimality.GenRev24

@[expose] public section

/-!
# RimOrderInst: short `robUniO_of_noAlt` proof of `robUniLex_four_of_mixed`

Hydrogen Task EN / EW: `robUni_of_splitRows4` and `robUniLex_adjTie` were moved into
`Minimality/SplitRim4.lean` and `Minimality/AdjTie4.lean` respectively (`robUni_of_monoCorners` and
`robUni_of_edgeCone` stay in `MonoCorner.lean` / `EdgeLeaf.lean` because `RimOrder` imports
`MonoCorner`).  `robUniLex_four_of_mixed_viaNoAlt` remains here so `LexCell.lean` stays free of a
`RimOrder` import.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.RimOrderInst

open Minimality Minimality.H21 Minimality.GenRev Minimality.LexCell Minimality.RimCell

theorem robUniLex_four_of_mixed_viaNoAlt {z : ZMod 4 → ℝ × ℝ × ℝ}
    (hn : ∃ p ∈ diagPairs, LexLt3 (z p.1) (z p.2))
    (hp : ∃ q ∈ diagPairs, LexLt3 (z q.2) (z q.1)) :
    RobUniLex z := by
  classical
  rw [robUniLex_iff_O]
  let zz : ZMod 4 → ℝ ×ₗ ℝ ×ₗ ℝ := fun i => toLex ((z i).1, toLex ((z i).2.1, (z i).2.2))
  let Mn : Finset (ZMod 4) := univ.filter (fun v => ¬ (zz (v - 1) < zz v ∨ zz (v + 1) < zz v))
  let Mx : Finset (ZMod 4) := univ.filter (fun v => ¬ (zz v < zz (v - 1) ∨ zz v < zz (v + 1)))
  refine robUniO_of_noAlt Mn Mx ?_ ?_ ?_
  · intro v hv; by_contra hnot; exact hv (mem_filter.2 ⟨mem_univ v, hnot⟩)
  · intro v hv; by_contra hnot; exact hv (mem_filter.2 ⟨mem_univ v, hnot⟩)
  · intro B b c d hb hbc hcd hd ⟨hB, hBb, hBc, hBd⟩
    have hb1 : b = 1 := by omega
    have hc2 : c = 2 := by omega
    have hd3 : d = 3 := by omega
    subst hb1 hc2 hd3
    simp only [Mn, Mx, mem_filter, mem_univ, true_and, not_or, not_lt] at hB hBb hBc hBd
    have hB_cases : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by
      fin_cases B
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    obtain ⟨p, hpm, hpn⟩ := hn
    obtain ⟨q, hqm, hqp⟩ := hp
    simp only [diagPairs, mem_product, mem_insert, mem_singleton] at hpm hqm
    have h_toLex : ∀ {p q : ℝ × ℝ × ℝ}, LexLt3 p q →
        toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) := by
      intro p q h
      simp only [LexLt3, LexPos3, Prod.Lex.lt_iff, ofLex_toLex] at h ⊢
      rcases h with h1 | ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
      · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
    have hp' : zz p.1 < zz p.2 := h_toLex hpn
    have hq' : zz q.2 < zz q.1 := h_toLex hqp
    rcases hB_cases with rfl | rfl | rfl | rfl
    · have h10 : zz 1 ≤ zz 0 := hBb.1
      have h12 : zz 1 ≤ zz 2 := hBb.2
      have h32 : zz 3 ≤ zz 2 := hBd.1
      have h30 : zz 3 ≤ zz 0 := hBd.2
      rcases hpm with ⟨hp1 | hp1, hp2 | hp2⟩ <;> rw [hp1, hp2] at hp' <;> exact absurd hp' (not_lt_of_ge (by assumption))
    · have h21 : zz 2 ≤ zz 1 := hBb.1
      have h23 : zz 2 ≤ zz 3 := hBb.2
      have h03 : zz 0 ≤ zz 3 := hBd.1
      have h01 : zz 0 ≤ zz 1 := hBd.2
      rcases hqm with ⟨hq1 | hq1, hq2 | hq2⟩ <;> rw [hq1, hq2] at hq' <;> exact absurd hq' (not_lt_of_ge (by assumption))
    · have h32 : zz 3 ≤ zz 2 := hBb.1
      have h30 : zz 3 ≤ zz 0 := hBb.2
      have h10 : zz 1 ≤ zz 0 := hBd.1
      have h12 : zz 1 ≤ zz 2 := hBd.2
      rcases hpm with ⟨hp1 | hp1, hp2 | hp2⟩ <;> rw [hp1, hp2] at hp' <;> exact absurd hp' (not_lt_of_ge (by assumption))
    · have h03 : zz 0 ≤ zz 3 := hBb.1
      have h01 : zz 0 ≤ zz 1 := hBb.2
      have h21 : zz 2 ≤ zz 1 := hBd.1
      have h23 : zz 2 ≤ zz 3 := hBd.2
      rcases hqm with ⟨hq1 | hq1, hq2 | hq2⟩ <;> rw [hq1, hq2] at hq' <;> exact absurd hq' (not_lt_of_ge (by assumption))

end Minimality.RimOrderInst
