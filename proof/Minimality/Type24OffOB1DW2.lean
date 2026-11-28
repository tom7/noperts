module

public import Minimality.Type24OffOB1DW

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the other horizontal double-wall classes (job OSPEC21)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2i.  On the double wall a horizontal direction `m` sees the
top quad `0 4 3 5` and the bottom triangle `1 2 6` edge-on; the seven side facets are signed by `m` like the edges
of the two polygons, and the rim is the back chain of the quad, the front chain of the triangle and two side edges
(the junctions).  `Type24OffOB1DW.lean` (OSPEC20) proved the junction pair `46 | 52`.  Here: four more classes,
each `m` in an open cone of the top (two edges of the quad) and an open cone of the bottom (two edges of the
triangle); every facet sign and every chain shape is derived, the only letters are the two junction signs:

* `C0246` (`lexAny_of_c0246`): `m ∈ cone(x5 - x0, x3 - x4) ∩ cone(x2 - x1, x6 - x1)`, rim `2 0 4 6`,
  junctions `⟪x 2 - x 0, m⟫ > 0`, `⟪x 6 - x 4, m⟫ > 0`;
* `C0652` (`lexAny_of_c0652`, the mirror): `m ∈ cone(x4 - x0, x3 - x5) ∩ cone(x2 - x1, x6 - x1)`, rim `6 0 5 2`;
* `C0152` (`lexAny_of_c0152`): `m ∈ cone(x0 - x4, x5 - x3) ∩ cone(x2 - x6, x1 - x6)`, rim `2 5 3 4 0 1`
  (the top chain `5 3 4 0` is a V: `3`, `4` each below a neighbour, `dw_c0152_v3`, `dw_c0152_v4`);
* `C0146` (`lexAny_of_c0146`, the mirror): `m ∈ cone(x0 - x5, x4 - x3) ∩ cone(x6 - x2, x1 - x2)`,
  rim `6 4 3 5 0 1`.

Near the cone ray `e4` (resp. `e5`) two letters suffice (`dwC0652_of_e4`, `dwC0246_of_e5`).

Residue: `Q45ResSTP` (= `Q45ResSTO` minus `DwClsCut`), `Q45ResWP`, **`OpenSpecialP`** (implied by
`OpenSpecialO`); on the double wall the residue piece is exactly `¬ DwHorizOK ∧ ¬ DwCls`
(`not_dwHoriz_of_resP`).  [SAMPLED, exact, ospec21 dwcls: `DwHorizOK ∨ DwCls` holds on all 28544 DW points.]
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section HorizDW2
open Minimality.LexCell

theorem dw2_inner (F : S0xFac 9 s0x_S24 x) (u : Fin 9) (γ δ : ℝ) (a b c d : Fin 7) :
    ⟪F.N u, γ • (x a - x b) + δ • (x c - x d)⟫ =
      γ * (F.f u (x a) - F.f u (x b)) + δ * (F.f u (x c) - F.f u (x d)) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub u a b, F.inner_sub u c d]

/-- `c m = p (u - w) + q (v - w)` with `c, p, q > 0` and `m ≠ 0`: `w` is below `u` or `v` along `m`. -/
theorem dw2_below_of_comb {m u v w : ℝ³} {c p q : ℝ} (hm : m ≠ 0) (hc : 0 < c) (hp : 0 < p) (hq : 0 < q)
    (h : c • m = p • (u - w) + q • (v - w)) : ⟪w, m⟫ < ⟪u, m⟫ ∨ ⟪w, m⟫ < ⟪v, m⟫ := by
  have hE : 0 < ⟪m, m⟫ := real_inner_self_pos.mpr hm
  have e := congrArg (fun z => ⟪z, m⟫) h
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at e
  by_contra hc'
  push Not at hc'
  nlinarith [mul_le_mul_of_nonneg_left (sub_nonpos.2 hc'.1) hp.le,
    mul_le_mul_of_nonneg_left (sub_nonpos.2 hc'.2) hq.le, mul_pos hc hE]

theorem dw2_ne_of_inner {m : ℝ³} {N : ℝ³} (h : ⟪N, m⟫ ≠ 0) : m ≠ 0 := by
  rintro rfl; exact h (inner_zero_right _)

/-- `f346(x 5) > f346(x 0)` (affine relation on the top face; `s < 1`, `t > 0`). -/
theorem dw2_f8 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs1 : s < 1) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : F.f 8 (x 0) < F.f 8 (x 5) := by
  have e := dw_aff F hdec 8
  rw [F.zero 8 3 (by decide), F.zero 8 4 (by decide)] at e
  have h0 := F.neg 8 0 (by decide)
  by_contra hc; push Not at hc
  nlinarith [mul_pos (sub_pos.2 hs1) (neg_pos.2 h0), mul_nonneg ht0.le (sub_nonneg.2 hc)]

/-- `f235(x 4) > f235(x 0)` (mirror of `dw2_f8`; `t < 1`, `s > 0`). -/
theorem dw2_f6 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht1 : t < 1)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : F.f 6 (x 0) < F.f 6 (x 4) := by
  have e := dw_aff F hdec 6
  rw [F.zero 6 3 (by decide), F.zero 6 5 (by decide)] at e
  have h0 := F.neg 6 0 (by decide)
  by_contra hc; push Not at hc
  nlinarith [mul_pos (sub_pos.2 ht1) (neg_pos.2 h0), mul_nonneg hs0.le (sub_nonneg.2 hc)]

/-- `f025(x 3) = s f025(x 4)`. -/
theorem dw2_f2 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    F.f 2 (x 3) = s * F.f 2 (x 4) := by
  have e := dw_aff F hdec 2
  rw [F.zero 2 0 (by decide), F.zero 2 5 (by decide)] at e
  linarith

/-- `f046(x 3) = t f046(x 5)`. -/
theorem dw2_f4 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    F.f 4 (x 3) = t * F.f 4 (x 5) := by
  have e := dw_aff F hdec 4
  rw [F.zero 4 0 (by decide), F.zero 4 4 (by decide)] at e
  linarith

/-- A 4-cycle with `z1 < z0` and `z2 < z3` (level 1) is `RobUniLex`. -/
theorem robUniLex_four_dw (z : ZMod 4 → ℝ × ℝ × ℝ) (h10 : (z 1).1 < (z 0).1) (h23 : (z 2).1 < (z 3).1) :
    RobUniLex z :=
  robUniLex_four_of_mixed ⟨(2, 3), by decide, Or.inl (by simp only; linarith)⟩
    ⟨(0, 1), by decide, Or.inl (by simp only; linarith)⟩

/-! ### The four classes -/

/-- Class `02 | 46`: `m = γ (x5 - x0) + δ (x3 - x4) = a (x2 - x1) + b (x6 - x1)`, both junctions rising. -/
def DwC0246 (x : Fin 7 → ℝ³) : Prop :=
  ∃ γ δ a b : ℝ, 0 < γ ∧ 0 < δ ∧ 0 < a ∧ 0 < b ∧
    γ • (x 5 - x 0) + δ • (x 3 - x 4) = a • (x 2 - x 1) + b • (x 6 - x 1) ∧
    0 < ⟪x 2 - x 0, γ • (x 5 - x 0) + δ • (x 3 - x 4)⟫ ∧ 0 < ⟪x 6 - x 4, γ • (x 5 - x 0) + δ • (x 3 - x 4)⟫

/-- Class `06 | 52` (mirror): `m = γ (x4 - x0) + δ (x3 - x5) = a (x2 - x1) + b (x6 - x1)`. -/
def DwC0652 (x : Fin 7 → ℝ³) : Prop :=
  ∃ γ δ a b : ℝ, 0 < γ ∧ 0 < δ ∧ 0 < a ∧ 0 < b ∧
    γ • (x 4 - x 0) + δ • (x 3 - x 5) = a • (x 2 - x 1) + b • (x 6 - x 1) ∧
    0 < ⟪x 6 - x 0, γ • (x 4 - x 0) + δ • (x 3 - x 5)⟫ ∧ 0 < ⟪x 2 - x 5, γ • (x 4 - x 0) + δ • (x 3 - x 5)⟫

/-- Class `01 | 52`: `m = γ (x0 - x4) + δ (x5 - x3) = a (x2 - x6) + b (x1 - x6)`. -/
def DwC0152 (x : Fin 7 → ℝ³) : Prop :=
  ∃ γ δ a b : ℝ, 0 < γ ∧ 0 < δ ∧ 0 < a ∧ 0 < b ∧
    γ • (x 0 - x 4) + δ • (x 5 - x 3) = a • (x 2 - x 6) + b • (x 1 - x 6) ∧
    0 < ⟪x 1 - x 0, γ • (x 0 - x 4) + δ • (x 5 - x 3)⟫ ∧ 0 < ⟪x 2 - x 5, γ • (x 0 - x 4) + δ • (x 5 - x 3)⟫

/-- Class `01 | 46` (mirror of `C0152`): `m = γ (x0 - x5) + δ (x4 - x3) = a (x6 - x2) + b (x1 - x2)`. -/
def DwC0146 (x : Fin 7 → ℝ³) : Prop :=
  ∃ γ δ a b : ℝ, 0 < γ ∧ 0 < δ ∧ 0 < a ∧ 0 < b ∧
    γ • (x 0 - x 5) + δ • (x 4 - x 3) = a • (x 6 - x 2) + b • (x 1 - x 2) ∧
    0 < ⟪x 1 - x 0, γ • (x 0 - x 5) + δ • (x 4 - x 3)⟫ ∧ 0 < ⟪x 6 - x 4, γ • (x 0 - x 5) + δ • (x 4 - x 3)⟫

def rimC0246 : ZMod 4 → Fin 7 := ![2, 0, 4, 6]
def UC0246 : Finset (Fin 9) := {2, 3, 6, 7, 8}
def DnC0246 : Finset (Fin 9) := {0, 1, 4, 5}
theorem rimC0246_cyc : S0xCycUD s0x_S24 rimC0246 UC0246 DnC0246 := by decide
theorem rimC0246_inj : Function.Injective rimC0246 := by decide

def rimC0652 : ZMod 4 → Fin 7 := ![6, 0, 5, 2]
def UC0652 : Finset (Fin 9) := {3, 4, 6, 7, 8}
def DnC0652 : Finset (Fin 9) := {0, 1, 2, 5}
theorem rimC0652_cyc : S0xCycUD s0x_S24 rimC0652 UC0652 DnC0652 := by decide
theorem rimC0652_inj : Function.Injective rimC0652 := by decide

def rimC0152 : ZMod 6 → Fin 7 := ![2, 5, 3, 4, 0, 1]
def UC0152 : Finset (Fin 9) := {0, 2, 3}
def DnC0152 : Finset (Fin 9) := {1, 4, 5, 6, 7, 8}
theorem rimC0152_cyc : S0xCycUD s0x_S24 rimC0152 UC0152 DnC0152 := by decide
theorem rimC0152_inj : Function.Injective rimC0152 := by decide

def rimC0146 : ZMod 6 → Fin 7 := ![6, 4, 3, 5, 0, 1]
def UC0146 : Finset (Fin 9) := {1, 3, 4}
def DnC0146 : Finset (Fin 9) := {0, 2, 5, 6, 7, 8}
theorem rimC0146_cyc : S0xCycUD s0x_S24 rimC0146 UC0146 DnC0146 := by decide
theorem rimC0146_inj : Function.Injective rimC0146 := by decide

/-- **Class `02 | 46` gives a lex cell** (view `(m, N3, N3)`, rim `2 0 4 6`). -/
theorem lexAny_of_c0246 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (ht0 : 0 < t) (hs1 : s < 1) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : DwC0246 x) :
    Gen.LexAny F := by
  obtain ⟨γ, δ, a, b, hγ, hδ, ha, hb, hm, j1, j2⟩ := h
  set m := γ • (x 5 - x 0) + δ • (x 3 - x 4) with hmdef
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  have T (u : Fin 9) : ⟪F.N u, m⟫ = γ * (F.f u (x 5) - F.f u (x 0)) + δ * (F.f u (x 3) - F.f u (x 4)) :=
    dw2_inner F u γ δ 5 0 3 4
  have B (u : Fin 9) : ⟪F.N u, m⟫ = a * (F.f u (x 2) - F.f u (x 1)) + b * (F.f u (x 6) - F.f u (x 1)) := by
    rw [hm]; exact dw2_inner F u a b 2 1 6 1
  refine ⟨4, inferInstance, rimC0246, UC0246, DnC0246, m, F.N 3, F.N 3, le_refl _, rimC0246_inj,
    rimC0246_cyc, ?_, ?_, ?_⟩
  · intro u hu
    simp only [UC0246, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · left; rw [T, F.zero 2 5 (by decide), F.zero 2 0 (by decide), dw2_f2 F hdec]
      nlinarith [mul_pos hδ (mul_pos (sub_pos.2 hs1) (neg_pos.2 (F.neg 2 4 (by decide))))]
    · right; refine ⟨?_, Or.inl hN3⟩
      rw [T, F.zero 3 5 (by decide), F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 4 (by decide)]; ring
    · left; rw [T, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 6 0 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 6 4 (by decide)))]
    · left; rw [B, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
      nlinarith [mul_pos (add_pos ha hb) (neg_pos.2 (F.neg 7 1 (by decide)))]
    · left; rw [T, F.zero 8 3 (by decide), F.zero 8 4 (by decide)]
      nlinarith [mul_pos hγ (sub_pos.2 (dw2_f8 F hs1 ht0 hdec))]
  · intro u hu
    simp only [DnC0246, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · left; rw [B, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
      nlinarith [mul_pos hb (neg_pos.2 (F.neg 0 6 (by decide)))]
    · left; rw [B, F.zero 1 6 (by decide), F.zero 1 1 (by decide)]
      nlinarith [mul_pos ha (neg_pos.2 (F.neg 1 2 (by decide)))]
    · left; rw [T, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 4 5 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 4 3 (by decide)))]
    · right; refine ⟨?_, Or.inl (by linarith)⟩
      rw [B, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]; ring
  · rw [inner_sub_left] at j1 j2
    apply robUniLex_four_dw
    · show ⟪x 0, m⟫ < ⟪x 2, m⟫; linarith
    · show ⟪x 4, m⟫ < ⟪x 6, m⟫; linarith

/-- **Class `06 | 52` gives a lex cell** (view `(m, N3, N3)`, rim `6 0 5 2`). -/
theorem lexAny_of_c0652 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht1 : t < 1) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : DwC0652 x) :
    Gen.LexAny F := by
  obtain ⟨γ, δ, a, b, hγ, hδ, ha, hb, hm, j1, j2⟩ := h
  set m := γ • (x 4 - x 0) + δ • (x 3 - x 5) with hmdef
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  have T (u : Fin 9) : ⟪F.N u, m⟫ = γ * (F.f u (x 4) - F.f u (x 0)) + δ * (F.f u (x 3) - F.f u (x 5)) :=
    dw2_inner F u γ δ 4 0 3 5
  have B (u : Fin 9) : ⟪F.N u, m⟫ = a * (F.f u (x 2) - F.f u (x 1)) + b * (F.f u (x 6) - F.f u (x 1)) := by
    rw [hm]; exact dw2_inner F u a b 2 1 6 1
  refine ⟨4, inferInstance, rimC0652, UC0652, DnC0652, m, F.N 3, F.N 3, le_refl _, rimC0652_inj,
    rimC0652_cyc, ?_, ?_, ?_⟩
  · intro u hu
    simp only [UC0652, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · right; refine ⟨?_, Or.inl hN3⟩
      rw [T, F.zero 3 5 (by decide), F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 4 (by decide)]; ring
    · left; rw [T, F.zero 4 4 (by decide), F.zero 4 0 (by decide), dw2_f4 F hdec]
      nlinarith [mul_pos hδ (mul_pos (sub_pos.2 ht1) (neg_pos.2 (F.neg 4 5 (by decide))))]
    · left; rw [T, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]
      nlinarith [mul_pos hγ (sub_pos.2 (dw2_f6 F hs0 ht1 hdec))]
    · left; rw [B, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
      nlinarith [mul_pos (add_pos ha hb) (neg_pos.2 (F.neg 7 1 (by decide)))]
    · left; rw [T, F.zero 8 3 (by decide), F.zero 8 4 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 8 0 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 8 5 (by decide)))]
  · intro u hu
    simp only [DnC0652, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · left; rw [B, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
      nlinarith [mul_pos hb (neg_pos.2 (F.neg 0 6 (by decide)))]
    · left; rw [B, F.zero 1 6 (by decide), F.zero 1 1 (by decide)]
      nlinarith [mul_pos ha (neg_pos.2 (F.neg 1 2 (by decide)))]
    · left; rw [T, F.zero 2 0 (by decide), F.zero 2 5 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 2 4 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 2 3 (by decide)))]
    · right; refine ⟨?_, Or.inl (by linarith)⟩
      rw [B, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]; ring
  · rw [inner_sub_left] at j1 j2
    apply robUniLex_four_dw
    · show ⟪x 0, m⟫ < ⟪x 6, m⟫; linarith
    · show ⟪x 5, m⟫ < ⟪x 2, m⟫; linarith

theorem dw2_x3 {s t : ℝ} (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 0 + s • (x 4 - x 0) + t • (x 5 - x 0) := by
  rw [add_assoc, ← hdec]; abel

/-- **Class `01 | 52` gives a lex cell** (view `(m, N3, N3)`, rim `2 5 3 4 0 1`; the top chain `5 3 4 0` is a V
because `m` lies in the tangent cones of the quad at `3` and at `4`). -/
theorem lexAny_of_c0152 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (ht1 : t < 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : DwC0152 x) : Gen.LexAny F := by
  obtain ⟨γ, δ, a, b, hγ, hδ, ha, hb, hm, j1, j2⟩ := h
  set m := γ • (x 0 - x 4) + δ • (x 5 - x 3) with hmdef
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  have T (u : Fin 9) : ⟪F.N u, m⟫ = γ * (F.f u (x 0) - F.f u (x 4)) + δ * (F.f u (x 5) - F.f u (x 3)) :=
    dw2_inner F u γ δ 0 4 5 3
  have B (u : Fin 9) : ⟪F.N u, m⟫ = a * (F.f u (x 2) - F.f u (x 6)) + b * (F.f u (x 1) - F.f u (x 6)) := by
    rw [hm]; exact dw2_inner F u a b 2 6 1 6
  have n0 : 0 < ⟪F.N 0, m⟫ := by
    rw [B, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
    nlinarith [mul_pos (add_pos ha hb) (neg_pos.2 (F.neg 0 6 (by decide)))]
  have hm0 : m ≠ 0 := dw2_ne_of_inner n0.ne'
  have h3 := dw2_x3 hdec
  have v3 : ⟪x 3, m⟫ < ⟪x 4, m⟫ ∨ ⟪x 3, m⟫ < ⟪x 5, m⟫ := by
    refine dw2_below_of_comb hm0 (sub_pos.2 hst) (mul_pos hγ (sub_pos.2 ht1))
      (add_pos (mul_pos hγ ht0) (mul_pos hδ (sub_pos.2 hst))) ?_
    rw [hmdef, h3]; module
  have v4 : ⟪x 4, m⟫ < ⟪x 3, m⟫ ∨ ⟪x 4, m⟫ < ⟪x 0, m⟫ := by
    refine dw2_below_of_comb hm0 ht0 (mul_pos hδ (sub_pos.2 ht1))
      (add_pos (mul_pos hγ ht0) (mul_pos hδ (sub_pos.2 hst))) ?_
    rw [hmdef, h3]; module
  refine ⟨6, inferInstance, rimC0152, UC0152, DnC0152, m, F.N 3, F.N 3, by norm_num, rimC0152_inj,
    rimC0152_cyc, ?_, ?_, ?_⟩
  · intro u hu
    simp only [UC0152, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact Or.inl n0
    · left; rw [T, F.zero 2 0 (by decide), F.zero 2 5 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 2 4 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 2 3 (by decide)))]
    · right; refine ⟨?_, Or.inl hN3⟩
      rw [T, F.zero 3 5 (by decide), F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 4 (by decide)]; ring
  · intro u hu
    simp only [DnC0152, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · left; rw [B, F.zero 1 6 (by decide), F.zero 1 1 (by decide)]
      nlinarith [mul_pos ha (neg_pos.2 (F.neg 1 2 (by decide)))]
    · left; rw [T, F.zero 4 0 (by decide), F.zero 4 4 (by decide), dw2_f4 F hdec]
      nlinarith [mul_pos hδ (mul_pos (sub_pos.2 ht1) (neg_pos.2 (F.neg 4 5 (by decide))))]
    · right; refine ⟨?_, Or.inl (by linarith)⟩
      rw [B, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]; ring
    · left; rw [T, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]
      nlinarith [mul_pos hγ (sub_pos.2 (dw2_f6 F hs0 ht1 hdec))]
    · left; rw [B, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
      nlinarith [mul_pos hb (neg_pos.2 (F.neg 7 1 (by decide)))]
    · left; rw [T, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 8 0 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 8 5 (by decide)))]
  · rw [inner_sub_left] at j1 j2
    have L : ∀ p q : ℝ × ℝ × ℝ, p.1 < q.1 → LexLt3 p q := fun p q h => Or.inl (by linarith)
    apply robUniLex_six_dw
    · rcases v4 with h | h
      · exact Or.inl (L _ _ h)
      · exact Or.inr (L _ _ h)
    · exact Or.inr (L _ _ (show ⟪x 5, m⟫ < ⟪x 2, m⟫ by linarith))
    · exact Or.inl (L _ _ (show ⟪x 0, m⟫ < ⟪x 1, m⟫ by linarith))
    · rcases v3 with h | h
      · exact Or.inr (Or.inl (L _ _ h))
      · exact Or.inl (L _ _ h)

/-- **Class `01 | 46` gives a lex cell** (mirror of `lexAny_of_c0152`; rim `6 4 3 5 0 1`). -/
theorem lexAny_of_c0146 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : DwC0146 x) : Gen.LexAny F := by
  obtain ⟨γ, δ, a, b, hγ, hδ, ha, hb, hm, j1, j2⟩ := h
  set m := γ • (x 0 - x 5) + δ • (x 4 - x 3) with hmdef
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  have T (u : Fin 9) : ⟪F.N u, m⟫ = γ * (F.f u (x 0) - F.f u (x 5)) + δ * (F.f u (x 4) - F.f u (x 3)) :=
    dw2_inner F u γ δ 0 5 4 3
  have B (u : Fin 9) : ⟪F.N u, m⟫ = a * (F.f u (x 6) - F.f u (x 2)) + b * (F.f u (x 1) - F.f u (x 2)) := by
    rw [hm]; exact dw2_inner F u a b 6 2 1 2
  have n1 : 0 < ⟪F.N 1, m⟫ := by
    rw [B, F.zero 1 6 (by decide), F.zero 1 1 (by decide)]
    nlinarith [mul_pos (add_pos ha hb) (neg_pos.2 (F.neg 1 2 (by decide)))]
  have hm0 : m ≠ 0 := dw2_ne_of_inner n1.ne'
  have h3 := dw2_x3 hdec
  have v3 : ⟪x 3, m⟫ < ⟪x 5, m⟫ ∨ ⟪x 3, m⟫ < ⟪x 4, m⟫ := by
    refine dw2_below_of_comb hm0 (sub_pos.2 hst) (mul_pos hγ (sub_pos.2 hs1))
      (add_pos (mul_pos hγ hs0) (mul_pos hδ (sub_pos.2 hst))) ?_
    rw [hmdef, h3]; module
  have v5 : ⟪x 5, m⟫ < ⟪x 3, m⟫ ∨ ⟪x 5, m⟫ < ⟪x 0, m⟫ := by
    refine dw2_below_of_comb hm0 hs0 (mul_pos hδ (sub_pos.2 hs1))
      (add_pos (mul_pos hγ hs0) (mul_pos hδ (sub_pos.2 hst))) ?_
    rw [hmdef, h3]; module
  refine ⟨6, inferInstance, rimC0146, UC0146, DnC0146, m, F.N 3, F.N 3, by norm_num, rimC0146_inj,
    rimC0146_cyc, ?_, ?_, ?_⟩
  · intro u hu
    simp only [UC0146, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact Or.inl n1
    · right; refine ⟨?_, Or.inl hN3⟩
      rw [T, F.zero 3 5 (by decide), F.zero 3 0 (by decide), F.zero 3 3 (by decide), F.zero 3 4 (by decide)]; ring
    · left; rw [T, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 4 5 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 4 3 (by decide)))]
  · intro u hu
    simp only [DnC0146, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · left; rw [B, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
      nlinarith [mul_pos ha (neg_pos.2 (F.neg 0 6 (by decide)))]
    · left; rw [T, F.zero 2 0 (by decide), F.zero 2 5 (by decide), dw2_f2 F hdec]
      nlinarith [mul_pos hδ (mul_pos (sub_pos.2 hs1) (neg_pos.2 (F.neg 2 4 (by decide))))]
    · right; refine ⟨?_, Or.inl (by linarith)⟩
      rw [B, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]; ring
    · left; rw [T, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]
      nlinarith [mul_pos hγ (neg_pos.2 (F.neg 6 0 (by decide))), mul_pos hδ (neg_pos.2 (F.neg 6 4 (by decide)))]
    · left; rw [B, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
      nlinarith [mul_pos hb (neg_pos.2 (F.neg 7 1 (by decide)))]
    · left; rw [T, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]
      nlinarith [mul_pos hγ (sub_pos.2 (dw2_f8 F hs1 ht0 hdec))]
  · rw [inner_sub_left] at j1 j2
    have L : ∀ p q : ℝ × ℝ × ℝ, p.1 < q.1 → LexLt3 p q := fun p q h => Or.inl (by linarith)
    apply robUniLex_six_dw
    · rcases v5 with h | h
      · exact Or.inl (L _ _ h)
      · exact Or.inr (L _ _ h)
    · exact Or.inr (L _ _ (show ⟪x 4, m⟫ < ⟪x 6, m⟫ by linarith))
    · exact Or.inl (L _ _ (show ⟪x 0, m⟫ < ⟪x 1, m⟫ by linarith))
    · rcases v3 with h | h
      · exact Or.inr (Or.inl (L _ _ h))
      · exact Or.inl (L _ _ h)

/-! ### Two letters near a cone ray -/

theorem dw2_eventually {p : ℝ} (q : ℝ) (hp : 0 < p) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < p + ε * q := by
  have hc : Continuous (fun ε : ℝ => p + ε * q) := by fun_prop
  have h := hc.tendsto 0
  simp only [zero_mul, add_zero] at h
  exact (h.eventually (lt_mem_nhds hp)).filter_mono nhdsWithin_le_nhds

/-- On the double wall, `⟪x 3 - x 5, ·⟫`-perturbing `e4`: **`C0652` from two letters at `e4`**
(`⟪x 6 - x 0, e4⟫ > 0`, `⟪x 2 - x 5, e4⟫ > 0`; `m = e4 + ε (x 3 - x 5)`, `e4` inside the bottom cone). -/
theorem dwC0652_of_e4 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (j1 : 0 < ⟪x 6 - x 0, x 4 - x 0⟫) (j2 : 0 < ⟪x 2 - x 5, x 4 - x 0⟫) : DwC0652 x := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have ha3 : oblX0 x 3 = 1 := by rw [obl3_a F hdec, hw4, hw5]; ring
  obtain ⟨ε, ⟨e1, e2, e3, e4⟩, hε⟩ :=
    (((dw2_eventually (oblX2 x 3 - oblX2 x 5) hb4).and ((dw2_eventually (oblX6 x 3 - oblX6 x 5) hc4).and
      ((dw2_eventually ⟪x 6 - x 0, x 3 - x 5⟫ j1).and (dw2_eventually ⟪x 2 - x 5, x 3 - x 5⟫ j2)))).and
      self_mem_nhdsWithin).exists
  refine ⟨1, ε, _, _, one_pos, hε, e1, e2, ?_, ?_, ?_⟩
  · have r3 := T.rep 3
    have r4 := T.rep 4
    have r5 := T.rep 5
    rw [ha3] at r3
    rw [hw4] at r4
    rw [hw5] at r5
    rw [r3, r4, r5]; module
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; linarith
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; linarith

/-- Mirror: **`C0246` from two letters at `e5`** (`⟪x 2 - x 0, e5⟫ > 0`, `⟪x 6 - x 4, e5⟫ > 0`). -/
theorem dwC0246_of_e5 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (j1 : 0 < ⟪x 2 - x 0, x 5 - x 0⟫) (j2 : 0 < ⟪x 6 - x 4, x 5 - x 0⟫) : DwC0246 x := by
  have T := M4.type24OfFac F
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  have ha3 : oblX0 x 3 = 1 := by rw [obl3_a F hdec, hw4, hw5]; ring
  obtain ⟨ε, ⟨e1, e2, e3, e4⟩, hε⟩ :=
    (((dw2_eventually (oblX2 x 3 - oblX2 x 4) hb5).and ((dw2_eventually (oblX6 x 3 - oblX6 x 4) hc5).and
      ((dw2_eventually ⟪x 2 - x 0, x 3 - x 4⟫ j1).and (dw2_eventually ⟪x 6 - x 4, x 3 - x 4⟫ j2)))).and
      self_mem_nhdsWithin).exists
  refine ⟨1, ε, _, _, one_pos, hε, e1, e2, ?_, ?_, ?_⟩
  · have r3 := T.rep 3
    have r4 := T.rep 4
    have r5 := T.rep 5
    rw [ha3] at r3
    rw [hw4] at r4
    rw [hw5] at r5
    rw [r3, r4, r5]; module
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; linarith
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; linarith

/-! ### The residue after the four classes -/

/-- The four new horizontal double-wall classes. -/
def DwCls (x : Fin 7 → ℝ³) : Prop := DwC0246 x ∨ DwC0652 x ∨ DwC0152 x ∨ DwC0146 x

/-- **`DwCls` gives a lex cell on the double wall** (`0 < s, t < 1 < s + t`). -/
theorem lexAny_of_dwCls (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s < 1) (ht1 : t < 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : DwCls x) : Gen.LexAny F := by
  rcases h with h | h | h | h
  · exact lexAny_of_c0246 F hw4 hw5 ht0 hs1 hdec h
  · exact lexAny_of_c0652 F hw4 hw5 hs0 ht1 hdec h
  · exact lexAny_of_c0152 F hw4 hw5 hs0 ht0 ht1 hst hdec h
  · exact lexAny_of_c0146 F hw4 hw5 hs0 ht0 hs1 hst hdec h

/-- The cut of the four classes at `(s, t)`. -/
def DwClsCut (x : Fin 7 → ℝ³) (s t : ℝ) : Prop :=
  oblX0 x 4 = 1 ∧ oblX0 x 5 = 1 ∧ s < 1 ∧ t < 1 ∧ DwCls x

/-- `Q45ResSTO` where none of the four classes applies. -/
def Q45ResSTP (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTO F s t ∧ ¬ DwClsCut x s t

/-- The branch-tagged residue after OSPEC21. -/
def Q45ResWP (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTP F s t

theorem q45_resP_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : Q45ResSTO F s t) :
    Gen.LexAny F ∨ Q45ResSTP F s t := by
  by_cases hA : DwClsCut x s t
  · obtain ⟨h4, h5, hs1, ht1, hH⟩ := hA
    exact Or.inl (lexAny_of_dwCls F h4 h5 hs0 ht0 hs1 ht1 hst hdec hH)
  exact Or.inr ⟨h, hA⟩

/-- `Q45ResWP ⊆ Q45ResWO`. -/
theorem q45ResWO_of_P {F : S0xFac 9 s0x_S24 x} (h : Q45ResWP F) : Q45ResWO F := by
  obtain ⟨s, t, hs, ht, hst, hd, h, -⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h⟩

/-- On the double wall with the frame signs `b1`, `b2` a point of `Q45ResWP` fails `DwHorizOK` and `DwCls`. -/
theorem not_dwHoriz_of_resP {F : S0xFac 9 s0x_S24 x} (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) (h : Q45ResWP F) :
    ¬ DwHorizOK x ∧ ¬ DwCls x := by
  obtain ⟨s, t, hs, ht, -, hd, ⟨-, hO⟩, hc⟩ := h
  have hs1 := dw_s_lt_one F ht hd hw4 hw5 b1
  have ht1 := dw_t_lt_one F hs hd hw4 hw5 b2
  exact ⟨fun hH => hO ⟨hw4, hw5, hs1, ht1, hH⟩, fun hH => hc ⟨hw4, hw5, hs1, ht1, hH⟩⟩

/-- **The double-wall residue in letters at `e4`, `e5`** (from `dwC0652_of_e4`, `dwC0246_of_e5`). -/
theorem dw_letters_of_resP {F : S0xFac 9 s0x_S24 x} (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3) (h : Q45ResWP F) :
    (⟪x 6 - x 0, x 4 - x 0⟫ ≤ 0 ∨ ⟪x 2 - x 5, x 4 - x 0⟫ ≤ 0) ∧
      (⟪x 2 - x 0, x 5 - x 0⟫ ≤ 0 ∨ ⟪x 6 - x 4, x 5 - x 0⟫ ≤ 0) := by
  have hc := (not_dwHoriz_of_resP hw4 hw5 b1 b2 h).2
  obtain ⟨s, t, -, -, -, hd, -⟩ := h
  constructor
  · by_contra hn; push Not at hn
    exact hc (Or.inr (Or.inl (dwC0652_of_e4 F hw4 hw5 hd hn.1 hn.2)))
  · by_contra hn; push Not at hn
    exact hc (Or.inl (dwC0246_of_e5 F hw4 hw5 hd hn.1 hn.2))

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWP`. -/
theorem q45_resP (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWP F := by
  rcases q45_resO F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resP_local F hs0 ht hst hd h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after all six horizontal double-wall classes, Rupert form**: `OpenSpecialO`
with `Q45ResWP` in place of `Q45ResWO` (implied by it: `openSpecialP_of_openSpecialO`). -/
def OpenSpecialP : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWP F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialO → OpenSpecialP` (`Q45ResWP ⊆ Q45ResWO`). -/
theorem openSpecialP_of_openSpecialO (h : OpenSpecialO) : OpenSpecialP :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWO_of_P hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialP`. -/
theorem hole24_offOB1_P {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialP) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resP F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after all horizontal double-wall classes) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_P (h1 : OpenOB1) (h2 : OpenSpecialP) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_P hH hO h2

end HorizDW2

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialP` give `Stmt.Open24Rupert` (OSPEC21). -/
theorem open24Rupert_of_cellCoverEmpty_P {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialP) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_P (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain with `cells28` after OSPEC21: `CellCoverEmpty cells28` and `OSpec.OpenSpecialP` give
`Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmpty28_P (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialP) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_P hN hS

end Minimality.T24.Cell
