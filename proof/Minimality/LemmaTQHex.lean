module

public import Minimality.LemmaTQ2

@[expose] public section

/-!
# Lemma TQ in the hexagon cell (type 24, obtuse corner OB1)

HEXSPLIT24.md (2026-11-19), the half "not S" of the hexagon split.  The orthocentre view `c* = H 1`
of the corner 1 lies in the hexagon cell `046325` (front set `{4350, 235, 346}` = facets `{3, 6, 8}`).
With `y3 = (a3, b3, c3)` the corner coordinates of vertex 3, the condition list `S` is
`{b3 < 1, c3 < 1}`; outside `S` Q4 holds on the cell `0234` or on `0536`, hence `IsRupert`:
* `b3, c3 > 1`: Lemma TL (`ca_chart`) with points of `cl 0234` and `cl 0536` on `L_236`
  (`a2m_hex` and `a2_closed`);
* `b3 ≤ 1 < c3`: Lemma WT' = `wt_gen` with `T` on `L_236` (`τ := θ`, `γ := g_c (T)`) and `P` on
  `L_012` (`lemB_w`); the mirror `c3 ≤ 1 < b3` by the relabelling `(2 6)(4 5)`.
The chart lemmas `a2_closed`, `a2_open`, `lemB_w` of `Minimality.LemmaTQChart` take the weak region
`InW` (only `025`, `046`, `236` back at `t`), which the hexagon satisfies.

Special position `c3 = 1` (with `b3 ≤ 1`): `cl 0234 ∩ L_236 = {X}`, `X = 012 × 236 × 346`.  The cell
`0234` is open iff `w1 > 0` (`⟪N_346, x2 - x1⟫ > 0`): then WT' runs with `T = P = X`.  For `w1 ≤ 0`
the forms `-g_c`, `f236`, `f346` are positively dependent and `0234` is empty
(`not_op0234_of_c3_eq_one`), so this position is a hypothesis of the theorem (and its mirror
`b3 = 1`, `⟪N_235, x6 - x1⟫ > 0`).  In inner products (facets `0 = 012`, `1 = 016`):
`c3 > 1 ↔ ⟪N_012, x3 - x6⟫ < 0`, `b3 > 1 ↔ ⟪N_016, x3 - x2⟫ < 0`.

Main theorem: `lemmaTQHex` (and `lemmaTQHex_strict`: `b3 > 1` or `c3 > 1`, no special-position
conditions).  The bridge from the solid to the chart is `tq_bridge` of `Minimality.LemmaTQ`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.TQ
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.Cell0234
  Minimality.T24.FrontDiag

namespace Ch24
variable (S : Ch24)

/-- The hexagon cell `046325` (front `{4350, 235, 346}`), open. -/
def InHex (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < S.f4350 a b c ∧ 0 < S.f235 a b c ∧ 0 < S.f346 a b c ∧
    S.f025 a b c < 0 ∧ S.f046 a b c < 0 ∧ S.f236 a b c < 0

theorem InHex.toW {S : Ch24} {a b c : ℝ} (h : S.InHex a b c) : S.InW a b c := by
  obtain ⟨h0, h1, h2, -, -, -, h025, h046, h236⟩ := h
  exact ⟨h0, h1, h2, h025, h046, h236⟩

/-- **Lemma A2, mirror, weak region** (`c3 > 1`): the cell `0234` is open and `cl 0234` has a point
`T = (θ, 1 - θ - g, g)` on `L_236` with `0 < g ≤ γ`, `a3 g < c3 θ` (`T = 025 × 236` or `E36`).
Uses the empty cell `{235}`; no condition on `f346 (t)`. -/
theorem a2m_w {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No235)
    (hc3 : 1 < S.c3) :
    (∃ a b c, S.Op0234 a b c) ∧
      ∃ g, 0 < g ∧ g ≤ S.ga ∧ S.a3 * g < S.c3 * S.th ∧ S.Cl0234 S.th (1 - S.th - g) g := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hW hts
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  set u := S.th / S.a3
  have hθ0 := S.th_pos
  have hγ0 := S.ga_pos
  have hb : 0 < 1 - S.th - S.ga - S.thb := by linarith
  have hb' : 0 < 1 - S.th - S.ga := by linarith [S.thb_pos]
  by_cases hC : S.ga < u * (S.c3 - 1)
  · -- `T_b = 025 × 236`
    have h025 : S.f025 S.th (1 - S.th - S.ga) S.ga = 0 := by rw [S.f025_eq (by ring)]; ring
    have h236 : S.f236 S.th (1 - S.th - S.ga) S.ga = 0 := by rw [S.f236_eq (by ring)]; ring
    have h346 : S.f346 S.th (1 - S.th - S.ga) S.ga < 0 := by
      rw [S.f346_Tb]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith [S.hw1])
    have hcT : 0 < S.c3 * S.th - S.a3 * S.ga := by
      have e : S.c3 * S.th - S.a3 * S.ga = S.a3 * ((u * (S.c3 - 1) - S.ga) + u) := by
        rw [← hua]; ring
      rw [e]; exact mul_pos S.ha3 (by linarith)
    have h235 : 0 < S.f235 S.th (1 - S.th - S.ga) S.ga := by
      have h := S.e23 S.th (1 - S.th - S.ga) S.ga
      rw [h236, sub_zero] at h
      have : 0 < S.a3 * S.f235 S.th (1 - S.th - S.ga) S.ga := by
        rw [h]; exact mul_pos (by linarith [S.hs2]) hcT
      exact pos_of_mul_pos_right this S.ha3.le
    have h046 : S.f046 S.th (1 - S.th - S.ga) S.ga < 0 := by
      rw [S.f046_eq (by ring)]; exact mul_neg_of_pos_of_neg (by linarith [S.hq]) (by linarith)
    have h4350 : 0 ≤ S.f4350 S.th (1 - S.th - S.ga) S.ga := by
      by_contra h4
      push Not at h4
      obtain ⟨ht0, ht1, ht2, h025t, -, h236t⟩ := hW
      refine S.no235_pert hNo (x := t0 - S.th) (y := t1 - (1 - S.th - S.ga)) (z := t2 - S.ga)
        (Or.inl hθ0) (Or.inl (by linarith)) (Or.inl hγ0) (Or.inl h235) (Or.inl h4)
        (Or.inr ⟨h025.le, ?_⟩) (Or.inl h046) (Or.inr ⟨h236.le, ?_⟩) (Or.inl h346)
      · have : S.f025 (t0 - S.th) (t1 - (1 - S.th - S.ga)) (t2 - S.ga) =
            S.f025 t0 t1 t2 - S.f025 S.th (1 - S.th - S.ga) S.ga := by simp only [f025, L3]; ring
        rw [this, h025]; linarith
      · have : S.f236 (t0 - S.th) (t1 - (1 - S.th - S.ga)) (t2 - S.ga) =
            S.f236 t0 t1 t2 - S.f236 S.th (1 - S.th - S.ga) S.ga := by simp only [f236, L3]; ring
        rw [this, h236]; linarith
    refine ⟨?_, S.ga, hγ0, le_refl _, by linarith, hθ0.le, by linarith, hγ0.le, h025.ge, h4350,
      h235.le, h046.le, h236.le, h346.le⟩
    -- open: `T_b + ε (1, L - 1, -L)`
    have hm1 : 0 < 1 - S.m1 := by linarith [S.hm1]
    set L := (1 - S.m1) / (|S.m1 - S.m2| + 1) with hL
    have hL1 : L * (|S.m1 - S.m2| + 1) = 1 - S.m1 := by rw [hL]; field_simp
    have hL0 : 0 < L := div_pos hm1 (by positivity)
    have hm := neg_abs_le (S.m1 - S.m2)
    have e025 : 0 < S.f025 1 (L - 1) (-L) := by
      simp only [f025, L3]; nlinarith [mul_pos hL0 (show (0:ℝ) < 1 - S.p by linarith [S.hp])]
    have e4350 : 0 < S.f4350 1 (L - 1) (-L) := by
      simp only [f4350, L3]
      nlinarith [mul_nonneg hL0.le (show 0 ≤ |S.m1 - S.m2| + (S.m1 - S.m2) by linarith)]
    have e236 : S.f236 1 (L - 1) (-L) < 0 := by simp only [f236, L3]; linarith [S.hr]
    exact S.op0234_pert (x := 1) (y := L - 1) (z := -L) (Or.inl hθ0) (Or.inl (by linarith))
      (Or.inl hγ0) (Or.inr ⟨h025.ge, e025⟩) (Or.inr ⟨h4350, e4350⟩) (Or.inl h235) (Or.inl h046)
      (Or.inr ⟨h236.le, e236⟩) (Or.inl h346)
  · -- `E36 = u (y3 - e_c)`
    push Not at hC
    obtain ⟨hEs, hE236, hE346, hE4350, hE235, hE046⟩ := S.e36_facts
    have hE025 : 0 ≤ S.f025 S.th (u * S.b3) (u * (S.c3 - 1)) := by
      rw [S.f025_eq hEs]; exact mul_nonneg (by linarith [S.hp]) (by linarith)
    have hEb : 0 < u * S.b3 := mul_pos hu S.hb3
    have hEc : 0 < u * (S.c3 - 1) := mul_pos hu (by linarith)
    have hcl : S.Cl0234 S.th (u * S.b3) (u * (S.c3 - 1)) :=
      ⟨hθ0.le, hEb.le, hEc.le, hE025, hE4350.le, hE235.le, hE046.le, hE236.le, hE346.le⟩
    refine ⟨?_, u * (S.c3 - 1), hEc, hC, ?_, S.Cl0234_congr hcl rfl (by linarith) rfl⟩
    · -- open: `E36 + ε (1, K - 1, -K)`
      have hw1 : 0 < 1 - S.w1 := by linarith [S.hw1]
      set K := (|S.w0 - S.w1| + 1) / (1 - S.w1) with hK
      have hK1 : K * (1 - S.w1) = |S.w0 - S.w1| + 1 := by rw [hK]; field_simp
      have hK0 : 0 < K := div_pos (by positivity) hw1
      have hab := le_abs_self (S.w0 - S.w1)
      have d025 : 0 < S.f025 1 (K - 1) (-K) := by
        simp only [f025, L3]; nlinarith [mul_pos hK0 (show (0:ℝ) < 1 - S.p by linarith [S.hp])]
      have d346 : S.f346 1 (K - 1) (-K) < 0 := by simp only [f346, L3]; nlinarith
      have d236 : S.f236 1 (K - 1) (-K) < 0 := by simp only [f236, L3]; linarith [S.hr]
      exact S.op0234_pert (x := 1) (y := K - 1) (z := -K) (Or.inl hθ0) (Or.inl hEb) (Or.inl hEc)
        (Or.inr ⟨hE025, d025⟩) (Or.inl hE4350) (Or.inl hE235) (Or.inl hE046)
        (Or.inr ⟨hE236.le, d236⟩) (Or.inr ⟨hE346.le, d346⟩)
    · have e : S.a3 * (u * (S.c3 - 1)) = S.th * S.c3 - S.th := by rw [← hua]; ring
      linarith

/-- **Special position `c3 = 1`, `w1 > 0`**: `X = (θ, 1 - θ, 0) ∈ cl 0234` and `0234` is open
(at `X + ε (0, -1, δ)`). -/
theorem a2m_one {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1)
    (hc3 : S.c3 = 1) (hw1 : 0 < S.w1) :
    (∃ a b c, S.Op0234 a b c) ∧ S.Cl0234 S.th (1 - S.th - 0) 0 := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hW hts
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  set u := S.th / S.a3
  obtain ⟨hEs, hE236, hE346, hE4350, hE235, hE046⟩ := S.e36_facts
  have hz : u * (S.c3 - 1) = 0 := by rw [hc3]; ring
  have hE025 : 0 < S.f025 S.th (u * S.b3) (u * (S.c3 - 1)) := by
    rw [S.f025_eq hEs]; exact mul_pos (by linarith [S.hp]) (by linarith [S.ga_pos])
  have hEb : 0 < u * S.b3 := mul_pos hu S.hb3
  refine ⟨?_, S.Cl0234_congr ⟨S.th_pos.le, hEb.le, hz.ge, hE025.le, hE4350.le, hE235.le,
    hE046.le, hE236.le, hE346.le⟩ rfl (by linarith) hz⟩
  set δ := min 1 S.w1 / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min one_pos hw1)
  have hδ1 : δ < 1 := by
    have := min_le_left 1 S.w1; rw [hδ]; linarith [lt_min one_pos hw1]
  have hδw : δ < S.w1 := by
    have := min_le_right 1 S.w1; rw [hδ]; linarith [lt_min one_pos hw1]
  exact S.op0234_pert (x := 0) (y := -1) (z := δ) (Or.inl S.th_pos) (Or.inl hEb)
    (Or.inr ⟨hz.ge, hδ0⟩) (Or.inl hE025) (Or.inl hE4350) (Or.inl hE235) (Or.inl hE046)
    (Or.inr ⟨hE236.le, by simp only [f236, L3]; linarith⟩)
    (Or.inr ⟨hE346.le, by simp only [f346, L3]; linarith⟩)

/-- For `c3 = 1` and `w1 ≤ 0` the cell `0234` is empty: `(1 - w1) (-g_c) - w1 f236 + f346 = 0`
(the lines `L_012`, `L_236`, `L_346` meet at `X` with positively dependent forms).  This is why
the special position `c3 = 1` needs `w1 > 0` in `lemmaTQHex`. -/
theorem not_op0234_of_c3_eq_one (hc3 : S.c3 = 1) (hw1 : S.w1 ≤ 0) {a b c : ℝ} :
    ¬ S.Op0234 a b c := by
  rintro ⟨-, -, hc, -, -, -, -, h236, h346⟩
  have hw : S.w0 = S.r * S.w1 := by
    have h1 := S.i236
    have h2 := S.i346
    rw [hc3] at h1 h2
    have : S.a3 * (S.w0 - S.r * S.w1) = 0 := by linear_combination h2 - S.w1 * h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h S.ha3.ne'
    · linarith
  have e : (1 - S.w1) * (-c) - S.w1 * S.f236 a b c + S.f346 a b c = 0 := by
    simp only [f236, f346, L3]; rw [hw]; ring
  nlinarith [mul_pos (show (0:ℝ) < 1 - S.w1 by linarith) hc, mul_nonneg (neg_nonneg.2 hw1) (neg_nonneg.2 h236.le)]

/-- The `L_236` point of `cl 0234` for the class `c3 > 1` or the special position `c3 = 1`,
`w1 > 0`: `0234` open, `T = (θ, 1 - θ - g, g) ∈ cl 0234` with `0 ≤ g ≤ γ`, `a3 g < c3 θ`. -/
theorem a2m_hex {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No235)
    (hcl : 1 < S.c3 ∨ (S.c3 = 1 ∧ 0 < S.w1)) :
    (∃ a b c, S.Op0234 a b c) ∧
      ∃ g, 0 ≤ g ∧ g ≤ S.ga ∧ S.a3 * g < S.c3 * S.th ∧ S.Cl0234 S.th (1 - S.th - g) g := by
  rcases hcl with hc3 | ⟨hc3, hw1⟩
  · obtain ⟨hop, g, hg0, hg1, hg2, hg3⟩ := S.a2m_w hW hts hNo hc3
    exact ⟨hop, g, hg0.le, hg1, hg2, hg3⟩
  · obtain ⟨hop, hcl⟩ := S.a2m_one hW hts hc3 hw1
    refine ⟨hop, 0, le_refl _, S.ga_pos.le, ?_, hcl⟩
    rw [hc3, mul_zero, one_mul]; exact S.th_pos

end Ch24

/-- **Lemma TQ in the hexagon, chart form** (frame `04325`).  `t` is the orthocentre chart point, in
the hexagon `046325`; the 3-rim cells `{235}`, `{346}`, `{025}` are empty; `G t = h2 (1,1,1)`,
`G_ab, G_bc ≤ 0`, strict Cauchy-Schwarz for `x2 - x0`, `x6 - x0`.  Class `c3 > 1`, or the special
position `c3 = 1`, `b3 ≤ 1`, `w1 > 0`.  Conclusion as `tq_chart`: Q4 at one point of `cl 0234`
(`z0 < z2` or `z3 < z2`, `0234` open) or of `cl 0536` (`z0 < z6`, `0536` open). -/
theorem hex_chart (S : Ch24) {t0 t1 t2 : ℝ} (hH : S.InHex t0 t1 t2) (hts : t0 + t1 + t2 = 1)
    (hNo235 : S.No235) (hNo346 : S.No346) (hNo025 : S.No025)
    {G00 G01 G02 G11 G12 G22 h2 : ℝ} (hh2 : 0 < h2)
    (r0 : G00 * t0 + G01 * t1 + G02 * t2 = h2) (r1 : G01 * t0 + G11 * t1 + G12 * t2 = h2)
    (r2 : G02 * t0 + G12 * t1 + G22 * t2 = h2) (hab : G01 ≤ 0) (hbc : G12 ≤ 0)
    (hA : 0 < G00 - 2 * G01 + G11) (hB : 0 < G00 - 2 * G02 + G22)
    (hC : (G00 - G01 - G02 + G12) ^ 2 < (G00 - 2 * G01 + G11) * (G00 - 2 * G02 + G22))
    (hcl : 1 < S.c3 ∨ (S.c3 = 1 ∧ S.b3 ≤ 1 ∧ 0 < S.w1)) :
    ((∃ a b c, S.Op0234 a b c) ∧ ∃ g0 g1 g2, S.Cl0234 g0 g1 g2 ∧
        (G00 * g0 + G01 * g1 + G02 * g2 < G01 * g0 + G11 * g1 + G12 * g2 ∨
          S.a3 * (G00 * g0 + G01 * g1 + G02 * g2) + S.b3 * (G01 * g0 + G11 * g1 + G12 * g2) +
            S.c3 * (G02 * g0 + G12 * g1 + G22 * g2) < G01 * g0 + G11 * g1 + G12 * g2)) ∨
      ((∃ a b c, S.Op0536 a b c) ∧ ∃ g0 g1 g2, S.Cl0536 g0 g1 g2 ∧
        G00 * g0 + G01 * g1 + G02 * g2 < G02 * g0 + G12 * g1 + G22 * g2) := by
  have hW := hH.toW
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hW hts
  obtain ⟨ht0, ht1, ht2, -, h235t, -, -, -, h236t⟩ := hH
  have hc3 : 1 ≤ S.c3 := by rcases hcl with h | ⟨h, -⟩ <;> linarith
  obtain ⟨hop, g, hg0, hgγ, hgT, hTcl⟩ :=
    S.a2m_hex hW hts hNo235 (hcl.imp_right fun h => ⟨h.1, h.2.2⟩)
  rcases le_or_gt S.b3 1 with hb3 | hb3
  · -- class `b3 ≤ 1`: Lemma WT' (`T` on `L_236`, `P` on `L_012`)
    left
    refine ⟨hop, ?_⟩
    obtain ⟨x, hx0, hx1, hPcl⟩ := S.lemB_w hW hts hNo025 (Or.inr hc3)
    have hs2 : 0 < 1 - S.s2 := by linarith [S.hs2]
    have hal : 0 ≤ S.c3 * t0 - S.a3 * t2 := by
      have h := S.e23 t0 t1 t2
      have : 0 < S.a3 * (S.f235 t0 t1 t2 - S.f236 t0 t1 t2) := mul_pos S.ha3 (by linarith)
      rw [h] at this
      exact (pos_of_mul_pos_right this hs2.le).le
    rcases wt_gen G00 G01 G02 G11 G12 h2 t0 t1 t2 S.a3 S.b3 S.c3 S.th (S.a3 + S.b3 + S.c3 - 1) S.th g x
        hh2 r0 r1 ht1 ht2 hts hab hbc (by linarith) S.hc3 hb3 S.s3_pos S.th_s3.symm
        (by linarith [S.th_s3]) S.th_pos le_rfl hθ hg0 (by linarith) hx0 hx1.le hal
        (by linarith) with h | h
    · exact ⟨S.th, 1 - S.th - g, g, hTcl, Or.inl (by linarith)⟩
    · exact ⟨x, 1 - x, 0, hPcl, Or.inr (by linarith)⟩
  · -- class `b3 > 1`, `c3 > 1`: Lemma TL (both points on `L_236`)
    obtain ⟨y', z', hs', hP'⟩ := S.a2_closed hW hts hNo346 hb3.le
    have hop' := S.a2_open hW hts hNo346 hb3
    have hy' : y' ≤ S.thb := by
      have h := hP'.2.2.2.1
      rw [S.f046_eq hs'] at h
      by_contra hc; push Not at hc
      nlinarith [mul_pos (show 0 < 1 - S.q by linarith [S.hq]) (show 0 < y' - S.thb by linarith)]
    have hz' : S.ga ≤ z' := by
      have h := hP'.2.2.2.2.2.2.1
      rw [S.f025_eq hs'] at h
      by_contra hc; push Not at hc
      nlinarith [mul_pos (show 0 < 1 - S.p by linarith [S.hp]) (show 0 < S.ga - z' by linarith)]
    have hD : (g - t2) * (y' - t1) ≤ ((1 - S.th - g) - t1) * (z' - t2) := by
      have ey : (1 - S.th - g) - t1 = (t0 - S.th) + (t2 - g) := by linarith
      have ez : z' - t2 = (t0 - S.th) + (t1 - y') := by linarith
      rw [ey, ez]
      nlinarith [mul_pos (show 0 < t0 - S.th by linarith) (show 0 < t0 - S.th by linarith),
        mul_pos (show 0 < t0 - S.th by linarith) (show 0 < t1 - y' by linarith),
        mul_pos (show 0 < t2 - g by linarith) (show 0 < t0 - S.th by linarith)]
    rcases ca_chart G00 G01 G02 G11 G12 G22 h2 t0 t1 t2 S.th (1 - S.th - g) g S.th y' z' r0 r1 r2
        hA hB hC hts (by ring) hs' (by linarith) (by linarith) (by linarith) hD with h | h
    · exact Or.inl ⟨hop, S.th, 1 - S.th - g, g, hTcl, Or.inl h⟩
    · exact Or.inr ⟨hop', S.th, y', z', hP', h⟩

/-! ## The solid -/

section Bridge
variable {x : Fin 7 → ℝ³}

/-- **Lemma TQ in the hexagon, frame `04325`**: type-24 solid, corner 1 with independent edges,
`G_ab, G_bc ≤ 0`, orthocentre view `u` (`<x_e - x1, u> = 1`) in the hexagon cell `046325` (front
facets exactly `0345`, `235`, `346`), the 3-rim cells `{235}`, `{346}`, `{025}` empty, and
`c3 > 1` (`⟪N_012, x3 - x6⟫ < 0`) or the special position `c3 = 1`, `b3 ≤ 1`, `w1 > 0`
(`⟪N_016, x3 - x2⟫ ≥ 0`, `⟪N_346, x2 - x1⟫ > 0`).  Then `IsRupert`. -/
theorem lemmaTQHex_04325 (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6, 8} {0, 1, 2, 4, 5, 7} u)
    (hNo235 : ∀ w, ¬ CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w)
    (hNo346 : ∀ w, ¬ CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w)
    (hNo025 : ∀ w, ¬ CellAt F {2} {0, 1, 3, 4, 5, 6, 7, 8} w)
    (hcl : ⟪F.N 0, x 3 - x 6⟫ < 0 ∨
      (⟪F.N 0, x 3 - x 6⟫ = 0 ∧ 0 ≤ ⟪F.N 1, x 3 - x 2⟫ ∧ 0 < ⟪F.N 8, x 2 - x 1⟫)) :
    IsRupert (Finset.univ.image x) := by
  refine tq_bridge F hx hli hab hbc hu hR (by decide) (by decide) (by decide) hNo235 hNo346 hNo025 ?_
  intro S t0 t1 t2 h3 e8 hU hD hts No235 No346 No025 G00 G01 G02 G11 G12 G22 h2 hh2 r0 r1 r2
    hab' hbc' hA hB hC
  have hH : S.InHex t0 t1 t2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hD 5 (by decide); simp [chf] at this; linarith
    · have := hD 1 (by decide); simp [chf] at this; linarith
    · have := hD 0 (by decide); simp [chf] at this; linarith
    · simpa [chf] using hU 3 (by decide)
    · simpa [chf] using hU 6 (by decide)
    · simpa [chf] using hU 8 (by decide)
    · simpa [chf] using hD 2 (by decide)
    · simpa [chf] using hD 4 (by decide)
    · simpa [chf] using hD 7 (by decide)
  -- the class in chart terms
  have ec : ⟪F.N 0, x 3 - x 6⟫ = (S.c3 - 1) * F.f 0 (x 6) := by
    have e : x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) := by abel
    rw [e, inner_sub_right, h3, facet0_vw, F.inner_sub 0 6 1, F.zero 0 1 (by decide)]; ring
  have eb : ⟪F.N 1, x 3 - x 2⟫ = (S.b3 - 1) * F.f 1 (x 2) := by
    have e : x 3 - x 2 = (x 3 - x 1) - (x 2 - x 1) := by abel
    rw [e, inner_sub_right, h3, facet1_vw, F.inner_sub 1 2 1, F.zero 1 1 (by decide)]; ring
  have ew : ⟪F.N 8, x 2 - x 1⟫ = kap F 8 * S.w1 := by
    have := e8 0 1 0
    simp only [vw, zero_smul, one_smul, zero_add, add_zero, Ch24.f346, L3] at this
    rw [this]; ring
  have f6 := F.neg 0 6 (by decide)
  have f2 := F.neg 1 2 (by decide)
  have k8 := kap_pos F 8 (by decide)
  have hcl' : 1 < S.c3 ∨ (S.c3 = 1 ∧ S.b3 ≤ 1 ∧ 0 < S.w1) := by
    rw [ec, eb, ew] at hcl
    rcases hcl with h | ⟨h0, hb, hw⟩
    · left; by_contra hc; push Not at hc
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (show S.c3 - 1 ≤ 0 by linarith) f6.le]
    · right
      refine ⟨?_, ?_, pos_of_mul_pos_right hw k8.le⟩
      · rcases mul_eq_zero.1 h0 with h | h
        · linarith
        · exact absurd h f6.ne
      · by_contra hc; push Not at hc
        nlinarith [mul_neg_of_pos_of_neg (show 0 < S.b3 - 1 by linarith) f2]
  exact hex_chart S hH hts No235 No346 No025 hh2 r0 r1 r2 hab' hbc' hA hB hC hcl'

/-- **Lemma TQ in the hexagon, frame `04635`** (mirror under `(2 6)(4 5)`, `b ↔ c`): `G_ac, G_bc ≤ 0`,
the 3-rim cells `{346}`, `{235}`, `{046}` empty, and `b3 > 1` (`⟪N_016, x3 - x2⟫ < 0`) or the
special position `b3 = 1`, `c3 ≤ 1`, `⟪N_235, x6 - x1⟫ > 0`. -/
theorem lemmaTQHex_04635 (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6, 8} {0, 1, 2, 4, 5, 7} u)
    (hNo346 : ∀ w, ¬ CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w)
    (hNo235 : ∀ w, ¬ CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w)
    (hNo046 : ∀ w, ¬ CellAt F {4} {0, 1, 2, 3, 5, 6, 7, 8} w)
    (hcl : ⟪F.N 1, x 3 - x 2⟫ < 0 ∨
      (⟪F.N 1, x 3 - x 2⟫ = 0 ∧ 0 ≤ ⟪F.N 0, x 3 - x 6⟫ ∧ 0 < ⟪F.N 6, x 6 - x 1⟫)) :
    IsRupert (Finset.univ.image x) := by
  have himg : Finset.univ.image (x ∘ sg) = Finset.univ.image x := by
    rw [← Finset.image_image, show Finset.univ.image sg = Finset.univ from
      Finset.image_univ_of_surjective (Finite.surjective_of_injective sg_inj)]
  rw [← himg]
  have hv : ![(x ∘ sg) 0 - (x ∘ sg) 1, (x ∘ sg) 2 - (x ∘ sg) 1, (x ∘ sg) 6 - (x ∘ sg) 1] =
      ![x 0 - x 1, x 2 - x 1, x 6 - x 1] ∘ Equiv.swap 1 2 := by
    funext e; fin_cases e <;> rfl
  refine lemmaTQHex_04325 (relab F) (hx.comp sg_inj) (u := u) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hv]; exact hli.comp _ (Equiv.injective _)
  · exact hac
  · rw [real_inner_comm]; exact hbc
  · intro e; rw [hv]; exact hu _
  · exact cellAt_relab F hR (by decide) (by decide)
  · intro w h; exact hNo346 w (cellAt_unrelab F h (by decide) (by decide))
  · intro w h; exact hNo235 w (cellAt_unrelab F h (by decide) (by decide))
  · intro w h; exact hNo046 w (cellAt_unrelab F h (by decide) (by decide))
  · exact hcl

/-- **Lemma TQ in the hexagon** (type 24, obtuse corner 1, HEXSPLIT24 "not S"): orthocentre view `u`
in the hexagon cell `046325` (`CellAt F {3, 6, 8} {0, 1, 2, 4, 5, 7} u`), all three corner angles
obtuse, and NOT (`b3 < 1` and `c3 < 1`), i.e. not both `⟪N_016, x3 - x2⟫ > 0` and
`⟪N_012, x3 - x6⟫ > 0`.  The special positions `c3 = 1`, `b3 ≤ 1` and `b3 = 1`, `c3 ≤ 1` need
`⟪N_346, x2 - x1⟫ > 0` resp. `⟪N_235, x6 - x1⟫ > 0` (otherwise the cell `0234` resp. `0536` is
empty, `not_op0234_of_c3_eq_one`).  No empty-cell hypotheses (the 3-rim leaf, `LemmaTQ2`). -/
theorem lemmaTQHex (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6, 8} {0, 1, 2, 4, 5, 7} u)
    (hS : ¬ (0 < ⟪F.N 1, x 3 - x 2⟫ ∧ 0 < ⟪F.N 0, x 3 - x 6⟫))
    (hspc : ⟪F.N 0, x 3 - x 6⟫ = 0 → 0 ≤ ⟪F.N 1, x 3 - x 2⟫ → 0 < ⟪F.N 8, x 2 - x 1⟫)
    (hspb : ⟪F.N 1, x 3 - x 2⟫ = 0 → 0 ≤ ⟪F.N 0, x 3 - x 6⟫ → 0 < ⟪F.N 6, x 6 - x 1⟫) :
    IsRupert (Finset.univ.image x) := by
  by_cases h1 : ∃ w, CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w
  · obtain ⟨w, hw⟩ := h1
    exact isRupert_of_cell_single F (t := 6) (by decide) (by decide) hw
  by_cases h2 : ∃ w, CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w
  · obtain ⟨w, hw⟩ := h2
    exact isRupert_of_cell_single F (t := 8) (by decide) (by decide) hw
  by_cases h3 : ∃ w, CellAt F {2} {0, 1, 3, 4, 5, 6, 7, 8} w
  · obtain ⟨w, hw⟩ := h3
    exact isRupert_of_cell_single F (t := 2) (by decide) (by decide) hw
  by_cases h4 : ∃ w, CellAt F {4} {0, 1, 2, 3, 5, 6, 7, 8} w
  · obtain ⟨w, hw⟩ := h4
    exact isRupert_of_cell_single F (t := 4) (by decide) (by decide) hw
  push Not at h1 h2 h3 h4
  rcases lt_or_ge ⟪F.N 0, x 3 - x 6⟫ 0 with hC | hC
  · exact lemmaTQHex_04325 F hx hli hab hbc hu hR h1 h2 h3 (Or.inl hC)
  rcases lt_or_ge ⟪F.N 1, x 3 - x 2⟫ 0 with hB | hB
  · exact lemmaTQHex_04635 F hx hli hac hbc hu hR h2 h1 h4 (Or.inl hB)
  rcases hC.lt_or_eq with hC' | hC'
  · have hB0 : ⟪F.N 1, x 3 - x 2⟫ = 0 := by
      by_contra h; exact hS ⟨lt_of_le_of_ne hB (Ne.symm h), hC'⟩
    exact lemmaTQHex_04635 F hx hli hac hbc hu hR h2 h1 h4 (Or.inr ⟨hB0, hC, hspb hB0 hC⟩)
  · exact lemmaTQHex_04325 F hx hli hab hbc hu hR h1 h2 h3
      (Or.inr ⟨hC'.symm, hB, hspc hC'.symm hB⟩)

/-- `lemmaTQHex` outside the closed set `{b3 ≤ 1, c3 ≤ 1}`: `b3 > 1` or `c3 > 1`, no special
position conditions. -/
theorem lemmaTQHex_strict (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6, 8} {0, 1, 2, 4, 5, 7} u)
    (hcl : ⟪F.N 1, x 3 - x 2⟫ < 0 ∨ ⟪F.N 0, x 3 - x 6⟫ < 0) :
    IsRupert (Finset.univ.image x) := by
  refine lemmaTQHex F hx hli hab hac hbc hu hR ?_ ?_ ?_
  · rintro ⟨h1, h2⟩; rcases hcl with h | h <;> linarith
  · intro h0 hb; exfalso; rcases hcl with h | h <;> linarith
  · intro h0 hc; exfalso; rcases hcl with h | h <;> linarith

end Bridge

end Minimality.T24.TQ
