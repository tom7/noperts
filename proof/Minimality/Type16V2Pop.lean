module

public import Minimality.Type16V2Core
public import Minimality.Type16V2Uni4
public import Minimality.TwoRayDiag

@[expose] public section

/-!
# V2: the pop cell (diagonal variant) at a vertex view whose facet `P` is a quadrilateral

`P` has vertices `w`, `A` (opposite `w`, the far end), `m`, `m'` on opposite sides of the diagonal `w A` (an affine
function `G` with `G w = G A = 0`, `G m > 0 > G m'`).  Popping `m` (the tilt `σ_P = G(w + r)`) gives the 4-cycle
`(w, m, A, B)`; the cell needs its depths `⟪·, r⟫` to have exactly one peak (`peaks4`).
`pop_gen`: one of the two pops always works (`pop_choice`), so the cell holds whenever the depths of
`w, A, B, m₁, m₂` are pairwise distinct.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace V2
open TwoRay Type08Sp Type08Sp.C2

theorem zmod4_cases' (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide

set_option maxHeartbeats 3200000 in
theorem pop_aux (V : Finset ℝ³) (fP fQ f3Q G : ℝ³ → ℝ) (NP NQ N3Q NG : ℝ³)
    (hP : ∀ y z, fP y - fP z = ⟪NP, y - z⟫) (hQ : ∀ y z, fQ y - fQ z = ⟪NQ, y - z⟫)
    (h3Q : ∀ y z, f3Q y - f3Q z = ⟪N3Q, y - z⟫) (hG : ∀ y z, G y - G z = ⟪NG, y - z⟫)
    (w A B m m' r : ℝ³) (hwV : w ∈ V) (hAV : A ∈ V) (hBV : B ∈ V) (hmV : m ∈ V) (hm'V : m' ∈ V) (hr : r ≠ 0)
    (hPr : ⟪NP, r⟫ = 0) (hQr : ⟪NQ, r⟫ = 0)
    (hPw : fP w = 0) (hPA : fP A = 0) (hPB : fP B < 0) (hQw : fQ w = 0) (hQB : fQ B = 0) (hQA : fQ A < 0)
    (h3Qw : f3Q w = 0) (h3QB : f3Q B = 0)
    (hPm : fP m = 0) (hQm : fQ A < fQ m ∧ fQ m < 0) (hPm' : fP m' = 0) (hQm' : fQ A < fQ m' ∧ fQ m' < 0)
    (hGw : G w = 0) (hGA : G A = 0) (hGm : 0 < G m) (hGm' : G m' < 0)
    (hwA : ⟪w, r⟫ ≠ ⟪A, r⟫) (hwB : ⟪w, r⟫ ≠ ⟪B, r⟫) (hAB : ⟪A, r⟫ ≠ ⟪B, r⟫) (hwm : ⟪w, r⟫ ≠ ⟪m, r⟫)
    (hAm : ⟪A, r⟫ ≠ ⟪m, r⟫) (hBm : ⟪B, r⟫ ≠ ⟪m, r⟫)
    (hpk : peaks4 ⟪w, r⟫ ⟪m, r⟫ ⟪A, r⟫ ⟪B, r⟫ = 1)
    (hcls : ∀ y ∈ V, y ≠ w → y ≠ A → y ≠ B → y ≠ m → y ≠ m' →
      (fQ y < 0 ∧ fP y < 0 ∧ fQ y * fP B + fP y * fQ A < fQ A * fP B) ∨
      (fQ y = 0 ∧ fP B < fP y ∧ fP y < 0 ∧ f3Q y < 0)) :
    HasLexCellAt V r := by
  have hv : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) → ⟪N, r⟫ = 0 → f w = 0 → f (w + r) = 0 := by
    intro f N hf hNr hfw
    have := hf (w + r) w
    rw [add_sub_cancel_left, hNr] at this
    linarith
  have hPv := hv hP hPr hPw
  have hQv := hv hQ hQr hQw
  have hov : w ≠ w + r := by
    intro h; apply hr; have : w + r = w + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdet := frame16_det_ne hP hQ hPw hPv hPA hPB.ne hQw hQv hQB hQA.ne hov
  rw [add_sub_cancel_left] at hdet
  set p := A - w with hp
  set q := B - w with hq
  have hΔ : det3 p q r ≠ 0 := hdet
  have fc := fun y => frame_coords hP hQ hPw hPv hPA hPB.ne hQw hQv hQB hQA.ne hov y
  have key3 : ∀ (f : ℝ³ → ℝ) (N : ℝ³), (∀ y z, f y - f z = ⟪N, y - z⟫) → f w = 0 → ∀ y zz,
      y = w + (fQ y / fQ A) • (A - w) + (fP y / fP B) • (B - w) + zz • (w + r - w) →
      f y = fQ y / fQ A * f A + fP y / fP B * f B + zz * f (w + r) := by
    intro f N hf hfw y zz hzz
    have := affine_frame3 hf w A B (w + r) (fQ y / fQ A) (fP y / fP B) zz
    rw [← hzz, hfw] at this
    linarith
  -- coordinates of m and m'
  obtain ⟨z0, hz0e⟩ := fc m
  obtain ⟨z1, hz1e⟩ := fc m'
  set s0 := fQ m / fQ A with hs0def
  set s1 := fQ m' / fQ A with hs1def
  have hs0 : 0 < s0 := div_pos_of_neg_of_neg hQm.2 hQA
  have hs0' : s0 < 1 := by rw [hs0def, div_lt_one_of_neg hQA]; exact hQm.1
  have hs1 : 0 < s1 := div_pos_of_neg_of_neg hQm'.2 hQA
  have hs1' : s1 < 1 := by rw [hs1def, div_lt_one_of_neg hQA]; exact hQm'.1
  have hGz0 : G m = z0 * G (w + r) := by
    have := key3 G NG hG hGw m z0 hz0e
    rw [this, hGA]; simp [hPm]
  have hGz1 : G m' = z1 * G (w + r) := by
    have := key3 G NG hG hGw m' z1 hz1e
    rw [this, hGA]; simp [hPm']
  set c := G (w + r) with hc
  have hc0 : c ≠ 0 := by intro h0; rw [h0, mul_zero] at hGz0; linarith
  have hz0c : 0 < z0 * c := by rw [← hGz0]; exact hGm
  have hz1c : z1 * c < 0 := by rw [← hGz1]; exact hGm'
  -- frame points
  let Y : ZMod 4 → ℝ × ℝ × ℝ := fun i =>
    if i = 0 then (0, 0, 0) else if i = 1 then (s0, 0, z0) else if i = 2 then (1, 0, 0) else (0, 1, 0)
  have n10 : (1 : ZMod 4) ≠ 0 := by decide
  have n20 : (2 : ZMod 4) ≠ 0 := by decide
  have n21 : (2 : ZMod 4) ≠ 1 := by decide
  have n30 : (3 : ZMod 4) ≠ 0 := by decide
  have n31 : (3 : ZMod 4) ≠ 1 := by decide
  have n32 : (3 : ZMod 4) ≠ 2 := by decide
  have hY0 : Y 0 = (0, 0, 0) := by simp [Y]
  have hY1 : Y 1 = (s0, 0, z0) := by simp [Y, n10]
  have hY2 : Y 2 = (1, 0, 0) := by simp [Y, n20, n21]
  have hY3 : Y 3 = (0, 1, 0) := by simp [Y, n30, n31, n32]
  have hYm : Y (-1) = (0, 1, 0) := by
    have : (-1 : ZMod 4) = 3 := by decide
    rw [this]; exact hY3
  have e0 : fpoint p q r w (Y 0) = w := by simp [hY0, fpoint, fcomb]
  have e1 : fpoint p q r w (Y 1) = m := by
    rw [hY1]; conv_rhs => rw [hz0e]
    simp only [fpoint, fcomb, add_sub_cancel_left, hp, hq]; simp [hPm, hs0def]; abel
  have e2 : fpoint p q r w (Y 2) = A := by simp [hY2, fpoint, fcomb, hp]
  have e3 : fpoint p q r w (Y 3) = B := by simp [hY3, fpoint, fcomb, hq]
  have hmem : ∀ i, fpoint p q r w (Y i) ∈ V := by
    intro i
    rcases zmod4_cases' i with rfl | rfl | rfl | rfl
    · rw [e0]; exact hwV
    · rw [e1]; exact hmV
    · rw [e2]; exact hAV
    · rw [e3]; exact hBV
  have hdist : ∀ i j, ⟪fpoint p q r w (Y i), r⟫ = ⟪fpoint p q r w (Y j), r⟫ → i = j := by
    intro i j h
    rcases zmod4_cases' i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases' j with rfl | rfl | rfl | rfl <;>
      simp only [e0, e1, e2, e3] at h <;>
      first
        | rfl
        | exact absurd h hwA | exact absurd h.symm hwA | exact absurd h hwB | exact absurd h.symm hwB
        | exact absurd h hAB | exact absurd h.symm hAB | exact absurd h hwm | exact absurd h.symm hwm
        | exact absurd h hAm | exact absurd h.symm hAm | exact absurd h hBm | exact absurd h.symm hBm
  have hdep : LexUni (fun i => ⟪fpoint p q r w (Y i), r⟫) (fun _ => 0) := by
    refine lexUni4_of _ hdist ?_
    simp only [e0, e1, e2, e3]
    exact hpk
  set σP : ℝ := c with hσPdef
  set σQ : ℝ := if f3Q (w + r) = 0 then 1 else f3Q (w + r) with hσQdef
  have hσQ : σQ ≠ 0 := by
    rw [hσQdef]; split_ifs with h
    · exact one_ne_zero
    · exact h
  refine v1b_hasLexCellAt V p q r w hΔ (k := 4) (by norm_num) Y hY0 hY1 hY2 hYm hs0 hs0' hc0 hσQ hz0c hmem ?_ hdep ?_
  · intro i j hji hj t02 t10
    have hs := hs0; have hs' := hs0'
    rcases zmod4_cases' i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases' j with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hji
        | exact absurd (by decide) hj
        | exact absurd ⟨rfl, rfl⟩ t02
        | exact absurd ⟨rfl, rfl⟩ t10
        | (simp only [TwoRay.cross2, hY0, hY1, hY2, hY3, show (0 : ZMod 4) + 1 = 1 from rfl,
            show (1 : ZMod 4) + 1 = 2 from rfl, show (2 : ZMod 4) + 1 = 3 from rfl,
            show (3 : ZMod 4) + 1 = 0 from rfl, Prod.mk_sub_mk]
           nlinarith)
  · intro y hy hyx
    have hyw : y ≠ w := fun h => hyx 0 (by rw [e0]; exact h)
    have hym : y ≠ m := fun h => hyx 1 (by rw [e1]; exact h)
    have hyA : y ≠ A := fun h => hyx 2 (by rw [e2]; exact h)
    have hyB : y ≠ B := fun h => hyx 3 (by rw [e3]; exact h)
    by_cases hym' : y = m'
    · subst hym'
      refine ⟨(s1, 0, z1), ?_, Or.inr (Or.inl ⟨s1, z1, rfl, hs1, hs1', ?_⟩)⟩
      · conv_lhs => rw [hz1e]
        simp only [fpoint, fcomb, add_sub_cancel_left, hp, hq]; simp [hPm', hs1def]; abel
      · exact hz1c
    obtain ⟨zz, hzz⟩ := fc y
    refine ⟨(fQ y / fQ A, fP y / fP B, zz), ?_, ?_⟩
    · conv_lhs => rw [hzz]
      simp only [fpoint, fcomb, add_sub_cancel_left, hp, hq]
      abel
    rcases hcls y hy hyw hyA hyB hym hym' with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩
    · left
      have hs : 0 < fQ y / fQ A := div_pos_of_neg_of_neg c1 hQA
      have ht : 0 < fP y / fP B := div_pos_of_neg_of_neg c2 hPB
      have hst : fQ y / fQ A + fP y / fP B < 1 := by
        rw [div_add_div _ _ hQA.ne hPB.ne, div_lt_one (mul_pos_of_neg_of_neg hQA hPB)]
        nlinarith
      intro i
      rcases zmod4_cases' i with rfl | rfl | rfl | rfl
      · simp only [TwoRay.cross2, hY0, hY1, show (0 : ZMod 4) + 1 = 1 from rfl, Prod.mk_sub_mk]
        nlinarith
      · simp only [TwoRay.cross2, hY1, hY2, show (1 : ZMod 4) + 1 = 2 from rfl, Prod.mk_sub_mk]
        nlinarith
      · simp only [TwoRay.cross2, hY2, hY3, show (2 : ZMod 4) + 1 = 3 from rfl, Prod.mk_sub_mk]
        linarith
      · simp only [TwoRay.cross2, hY3, hY0, show (3 : ZMod 4) + 1 = 0 from rfl, Prod.mk_sub_mk]
        linarith
    · right; right
      refine ⟨fP y / fP B, zz, ?_, div_pos_of_neg_of_neg c3 hPB, ?_, ?_⟩
      · simp [c1]
      · rw [div_lt_one_of_neg hPB]; exact c2
      · have := key3 f3Q N3Q h3Q h3Qw y zz hzz
        have hz : f3Q y = zz * f3Q (w + r) := by rw [this]; simp [c1, h3QB]
        have hc : f3Q (w + r) ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hz; linarith
        rw [hσQdef, if_neg hc, ← hz]; exact c4

theorem depth_eq (w A B m r : ℝ³) (s z : ℝ) (hz : m = w + s • (A - w) + (0 : ℝ) • (B - w) + z • (w + r - w)) :
    ⟪m, r⟫ = ⟪w, r⟫ + s * (⟪A, r⟫ - ⟪w, r⟫) + z * ⟪r, r⟫ := by
  rw [hz]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, add_sub_cancel_left, zero_mul]
  ring

set_option maxHeartbeats 3200000 in
/-- **The pop cell** (`pop_gen`): quadrilateral `P` with `w`, far `A`, and `m₁`, `m₂` on opposite sides of the
diagonal `w A` (`g m₁ < 0 < g m₂`).  Depths of `w, A, B, m₁, m₂` pairwise distinct (a metric hypothesis). -/
theorem pop_gen (V : Finset ℝ³) (fP fQ f3Q g : ℝ³ → ℝ) (NP NQ N3Q Ng : ℝ³)
    (hP : ∀ y z, fP y - fP z = ⟪NP, y - z⟫) (hQ : ∀ y z, fQ y - fQ z = ⟪NQ, y - z⟫)
    (h3Q : ∀ y z, f3Q y - f3Q z = ⟪N3Q, y - z⟫) (hg : ∀ y z, g y - g z = ⟪Ng, y - z⟫)
    (w A B m1 m2 r : ℝ³) (hwV : w ∈ V) (hAV : A ∈ V) (hBV : B ∈ V) (hm1V : m1 ∈ V) (hm2V : m2 ∈ V) (hr : r ≠ 0)
    (hPr : ⟪NP, r⟫ = 0) (hQr : ⟪NQ, r⟫ = 0)
    (hPw : fP w = 0) (hPA : fP A = 0) (hPB : fP B < 0) (hQw : fQ w = 0) (hQB : fQ B = 0) (hQA : fQ A < 0)
    (h3Qw : f3Q w = 0) (h3QB : f3Q B = 0)
    (hPm1 : fP m1 = 0) (hQm1 : fQ A < fQ m1 ∧ fQ m1 < 0) (hPm2 : fP m2 = 0) (hQm2 : fQ A < fQ m2 ∧ fQ m2 < 0)
    (hgw : g w = 0) (hgA : g A = 0) (hgm1 : g m1 < 0) (hgm2 : 0 < g m2)
    (hwA : ⟪w, r⟫ ≠ ⟪A, r⟫) (hwB : ⟪w, r⟫ ≠ ⟪B, r⟫) (hAB : ⟪A, r⟫ ≠ ⟪B, r⟫)
    (hw1 : ⟪w, r⟫ ≠ ⟪m1, r⟫) (hA1 : ⟪A, r⟫ ≠ ⟪m1, r⟫) (hB1 : ⟪B, r⟫ ≠ ⟪m1, r⟫)
    (hw2 : ⟪w, r⟫ ≠ ⟪m2, r⟫) (hA2 : ⟪A, r⟫ ≠ ⟪m2, r⟫) (hB2 : ⟪B, r⟫ ≠ ⟪m2, r⟫)
    (hcls : ∀ y ∈ V, y ≠ w → y ≠ A → y ≠ B → y ≠ m1 → y ≠ m2 →
      (fQ y < 0 ∧ fP y < 0 ∧ fQ y * fP B + fP y * fQ A < fQ A * fP B) ∨
      (fQ y = 0 ∧ fP B < fP y ∧ fP y < 0 ∧ f3Q y < 0)) :
    HasLexCellAt V r := by
  have hv : ∀ {f : ℝ³ → ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) → ⟪N, r⟫ = 0 → f w = 0 → f (w + r) = 0 := by
    intro f N hf hNr hfw
    have := hf (w + r) w
    rw [add_sub_cancel_left, hNr] at this
    linarith
  have hPv := hv hP hPr hPw
  have hQv := hv hQ hQr hQw
  have hov : w ≠ w + r := by
    intro h; apply hr; have : w + r = w + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have fc := fun y => frame_coords hP hQ hPw hPv hPA hPB.ne hQw hQv hQB hQA.ne hov y
  obtain ⟨z1, hz1e⟩ := fc m1
  obtain ⟨z2, hz2e⟩ := fc m2
  rw [hPm1, zero_div] at hz1e
  rw [hPm2, zero_div] at hz2e
  have key : ∀ (f : ℝ³ → ℝ) (N : ℝ³), (∀ y z, f y - f z = ⟪N, y - z⟫) → f w = 0 → f A = 0 → ∀ (y : ℝ³) (zz s : ℝ),
      y = w + s • (A - w) + (0 : ℝ) • (B - w) + zz • (w + r - w) → f y = zz * f (w + r) := by
    intro f N hf hfw hfA y zz s hzz
    have := affine_frame3 hf w A B (w + r) s 0 zz
    rw [← hzz, hfw, hfA] at this
    linarith
  set s1 := fQ m1 / fQ A with hs1def
  set s2 := fQ m2 / fQ A with hs2def
  have hs1 : 0 < s1 := div_pos_of_neg_of_neg hQm1.2 hQA
  have hs1' : s1 < 1 := by rw [hs1def, div_lt_one_of_neg hQA]; exact hQm1.1
  have hs2 : 0 < s2 := div_pos_of_neg_of_neg hQm2.2 hQA
  have hs2' : s2 < 1 := by rw [hs2def, div_lt_one_of_neg hQA]; exact hQm2.1
  have hg1 : g m1 = z1 * g (w + r) := by
    have := key g Ng hg hgw hgA m1 z1 s1 hz1e; exact this
  have hg2 : g m2 = z2 * g (w + r) := by
    have := key g Ng hg hgw hgA m2 z2 s2 hz2e; exact this
  have d1 := depth_eq w A B m1 r s1 z1 hz1e
  have d2 := depth_eq w A B m2 r s2 z2 hz2e
  have hrr : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr
  set c := g (w + r) with hc
  have hneg : ∀ f : ℝ³ → ℝ, ∀ N : ℝ³, (∀ y z, f y - f z = ⟪N, y - z⟫) → ∀ y, (-f) y = -f y := fun _ _ _ _ => rfl
  have aux2 : peaks4 ⟪w, r⟫ ⟪m2, r⟫ ⟪A, r⟫ ⟪B, r⟫ = 1 → HasLexCellAt V r := fun hpk =>
    pop_aux V fP fQ f3Q g NP NQ N3Q Ng hP hQ h3Q hg w A B m2 m1 r hwV hAV hBV hm2V hm1V hr hPr hQr hPw hPA hPB
      hQw hQB hQA h3Qw h3QB hPm2 hQm2 hPm1 hQm1 hgw hgA hgm2 hgm1 hwA hwB hAB hw2 hA2 hB2 hpk
      (fun y hy a b c d e => hcls y hy a b c e d)
  have hgn : ∀ y z, (fun y => -g y) y - (fun y => -g y) z = ⟪-Ng, y - z⟫ := by
    intro y z; simp only [inner_neg_left]; linarith [hg y z]
  have aux1 : peaks4 ⟪w, r⟫ ⟪m1, r⟫ ⟪A, r⟫ ⟪B, r⟫ = 1 → HasLexCellAt V r := fun hpk =>
    pop_aux V fP fQ f3Q (fun y => -g y) NP NQ N3Q (-Ng) hP hQ h3Q hgn w A B m1 m2 r hwV hAV hBV hm1V hm2V hr hPr hQr
      hPw hPA hPB hQw hQB hQA h3Qw h3QB hPm1 hQm1 hPm2 hQm2 (by simp [hgw]) (by simp [hgA]) (by simp; exact hgm1)
      (by simp; exact hgm2) hwA hwB hAB hw1 hA1 hB1 hpk hcls
  have hc0 : c ≠ 0 := by intro h0; rw [h0, mul_zero] at hg2; linarith
  rcases lt_or_gt_of_ne hc0 with hcn | hcp
  · -- c < 0: z1 > 0 (m1 up), z2 < 0 (m2 down)
    have hz1 : 0 < z1 := by nlinarith
    have hz2 : z2 < 0 := by nlinarith
    have hu : (1 - s1) * ⟪w, r⟫ + s1 * ⟪A, r⟫ < ⟪m1, r⟫ := by rw [d1]; nlinarith [mul_pos hz1 hrr]
    have hd : ⟪m2, r⟫ < (1 - s2) * ⟪w, r⟫ + s2 * ⟪A, r⟫ := by rw [d2]; nlinarith [mul_neg_of_neg_of_pos hz2 hrr]
    rcases pop_choice _ _ ⟪B, r⟫ _ _ hwA hwB hAB hw1.symm hA1.symm hw2.symm hA2.symm
      (chord_above _ _ _ s1 hs1 hs1' hu) (chord_below _ _ _ s2 hs2 hs2' hd) with h | h
    · exact aux1 h
    · exact aux2 h
  · have hz2 : 0 < z2 := by nlinarith
    have hz1 : z1 < 0 := by nlinarith
    have hu : (1 - s2) * ⟪w, r⟫ + s2 * ⟪A, r⟫ < ⟪m2, r⟫ := by rw [d2]; nlinarith [mul_pos hz2 hrr]
    have hd : ⟪m1, r⟫ < (1 - s1) * ⟪w, r⟫ + s1 * ⟪A, r⟫ := by rw [d1]; nlinarith [mul_neg_of_neg_of_pos hz1 hrr]
    rcases pop_choice _ _ ⟪B, r⟫ _ _ hwA hwB hAB hw2.symm hA2.symm hw1.symm hA1.symm
      (chord_above _ _ _ s2 hs2 hs2' hu) (chord_below _ _ _ s1 hs1 hs1' hd) with h | h
    · exact aux2 h
    · exact aux1 h

end V2
end Minimality
