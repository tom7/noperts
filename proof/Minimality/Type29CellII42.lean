module

public import Minimality.Type29CellII41

@[expose] public section

/-!
# Type 29, `K1a ∩ G* ∩ Cell II`, Task L42 (`A42-REFEREE`)

* `L42-1` `fa_rows_of_R4R5`: pure order lemma over six reals (the F-A cone rows `FA3, FA21, FA23 ≥ 0`).
* `L42-2` identity blocks in the `G` entries (`v012_form` with the corrected sign, `R204_form`, `u20_entries`,
  `m34star`, `bq20_blocks`, `Q4neg_form`, `Q5pos_form`) and `cert_FA_CQ2_false` (`J = Q2`, rows
  `Q2, W21, M15, FA23, FA3, Q4neg`, routes F-alone / `(Q2-a)` / `E_{Q4neg}`).  `J = Q4` stays the open named
  hypothesis `FACQ4Hyp` (not proved).
* `L42-4` `cert_FB_Z3_false` (Q42.3): `Z_* = 0` positive syzygy.
`L42-3` is not formalized (its sign fact is refuted by A43).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.NF29

/-! ## L42-1: the F-A cone rows from the two failing rims `R4`, `R5` -/

/-- `Alt4 a b c d`: the 4-cycle `(a, b, c, d)` has a weak alternating pair of diagonals. -/
def Alt4 (a b c d : ℝ) : Prop :=
  (b ≤ a ∧ d ≤ a ∧ b ≤ c ∧ d ≤ c) ∨ (a ≤ b ∧ c ≤ b ∧ a ≤ d ∧ c ≤ d)

/-- `NotRU5 x0 … x4`: some weak alternating quadruple of the cyclic 5-sequence (omit one entry; 10 clauses). -/
def NotRU5 (x0 x1 x2 x3 x4 : ℝ) : Prop :=
  Alt4 x0 x1 x2 x3 ∨ Alt4 x1 x2 x3 x4 ∨ Alt4 x2 x3 x4 x0 ∨ Alt4 x3 x4 x0 x1 ∨ Alt4 x4 x0 x1 x2

/-- **L42-1** (`Q42.2`): on `(R4 ∩ R5) \ F-B` with `z4 = -a < 0 = z6 < b = z5`, the F-A rows hold. -/
theorem fa_rows_of_R4R5 (z1 z2 z3 a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h4 : NotRU5 (-a) z1 z2 z3 0) (h5 : NotRU5 b z1 z2 z3 0)
    (hn : ¬ (z2 ≤ z1 ∧ 0 ≤ z3)) : z3 ≤ 0 ∧ z1 ≤ z2 ∧ z3 ≤ z2 := by
  have hn' : z1 < z2 ∨ z3 < 0 := by
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    exact hn h
  simp only [NotRU5, Alt4] at h4 h5
  rcases hn' with hn' | hn' <;>
  rcases h4 with (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) <;>
  rcases h5 with (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) | (⟨_, _, _, _⟩ | ⟨_, _, _, _⟩) <;>
  refine ⟨?_, ?_, ?_⟩ <;> linarith


/-! ## L42-2: identity blocks in the `G` entries -/

section L42Blocks

/-- Shape (8 parameters) and the six `G` entries of the `(e3, e4, e5)` frame, including `G33`. -/
structure L42P extends L41P where
  G33 : ℝ

namespace L42P

variable (p : L42P)

abbrev P2 : ℝ := P2_sp p.a2 p.b2 p.h2 p.s p.t
abbrev D234 : ℝ := D234_sp p.a2 p.b2 p.h2 p.s p.t
abbrev P0 : ℝ := P0_sp p.a0 p.b0 p.h0 p.s p.t
abbrev D035 : ℝ := D035_sp p.a0 p.b0 p.h0 p.s p.t
abbrev C35 : ℝ := C35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2
abbrev B35 : ℝ := B35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2
abbrev G5 : ℝ := G5_sp p.a0 p.h0 p.a2 p.h2
abbrev del0 : ℝ := 1 - p.a0 - p.b0 - p.h0
abbrev del2 : ℝ := 1 - p.a2 - p.b2 - p.h2
abbrev KY : ℝ := KY_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t
abbrev KW : ℝ := KW_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t
/-- `|K_W| = -K_W` (`> 0` on Cell II). -/
abbrev KWa : ℝ := -p.KW
abbrev v4 : ℝ := v4_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t
abbrev v5 : ℝ := v5_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 p.s p.t

/-- `⟪e_3, G u⟫`, `⟪e_4, G u⟫`, `⟪e_5, G u⟫` for `u = u3 e3 + u4 e4 + u5 e5`. -/
abbrev ge3 (u3 u4 u5 : ℝ) : ℝ := p.G33 * u3 + p.g34 * u4 + p.g35 * u5
abbrev ge4 (u3 u4 u5 : ℝ) : ℝ := p.g34 * u3 + p.G44 * u4 + p.g45 * u5
abbrev ge5 (u3 u4 u5 : ℝ) : ℝ := p.g35 * u3 + p.g45 * u4 + p.G55 * u5
/-- `S ⟪x_i - x_j, G u⟫` for `S (x_i - x_j) = dq4 e4 + dq5 e5 + S dY e3`. -/
abbrev rowv (dq4 dq5 dY u3 u4 u5 : ℝ) : ℝ :=
  dq4 * p.ge4 u3 u4 u5 + dq5 * p.ge5 u3 u4 u5 + p.S * dY * p.ge3 u3 u4 u5

/-- `Q_2 = S z_2(v_Q)`, `Q_20 = S (z_2 - z_0)(v_Q)`, `W21' = S (z_2 - z_1)(v_14)`. -/
abbrev Q2 : ℝ := p.rowv p.P2 p.D234 p.h2 0 (-p.U4) (-p.U5)
abbrev Q20 : ℝ := p.rowv (p.P2 - p.D035) (p.D234 - p.P0) (p.h2 - p.h0) 0 (-p.U4) (-p.U5)
abbrev W21' : ℝ := p.rowv (p.P2 - p.s) (p.D234 - p.t) p.h2 0 (1 - p.t) p.t
/-- `M15 = S (z_1 - z_5)(u35)`, `u35 = (S C35, del2 D035, del0 D234)`. -/
abbrev M15 : ℝ := p.rowv p.s (1 - p.s) 0 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234)
/-- `FA23 = S (z_2 - z_3)(v012)`, `FA3 = S (-z_3)(v012)`. -/
abbrev FA23 : ℝ := p.rowv p.P2 p.D234 (p.h2 - 1) 0 p.v4 p.v5
abbrev FA3 : ℝ := -p.rowv 0 0 1 0 p.v4 p.v5
/-- `Q4_neg = S (-z_4)(v_Q)`, `Q5_pos = S z_5(v_Q)`. -/
abbrev Q4neg : ℝ := -p.rowv p.S 0 0 0 (-p.U4) (-p.U5)
abbrev Q5pos : ℝ := p.rowv 0 p.S 0 0 (-p.U4) (-p.U5)
/-- `R_{20,4} = C35 S (z_2 - z_0)(w34) + (h2 - h0)(z_3 - z_4)(u35)`, `w34 = (-1, 1, 0)`. -/
abbrev R204 : ℝ := p.C35 * p.rowv (p.P2 - p.D035) (p.D234 - p.P0) (p.h2 - p.h0) (-1) 1 0 +
  (p.h2 - p.h0) * (p.ge3 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234) -
    p.ge4 (p.S * p.C35) (p.del2 * p.D035) (p.del0 * p.D234))

end L42P

variable (p : L42P)

theorem l42_KY_form : p.KY = p.C35 * (p.P2 - p.D035) - (p.h2 - p.h0) * p.del2 * p.D035 := by
  simp only [L42P.KY, KY_sp, L_sp, L42P.C35, L42P.P2, L42P.D035, L42P.del2, C35_sp]; ring

/-- `Q4neg`, `Q5pos` in `G` entries (`Q4neg_form`, `Q5pos_form`). -/
theorem l42_Q4neg_form : p.Q4neg = p.S * (p.U4 * p.G44 + p.U5 * p.g45) := by
  simp only [L42P.Q4neg, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

theorem l42_Q5pos_form : p.Q5pos = -(p.S * (p.U4 * p.g45 + p.U5 * p.G55)) := by
  simp only [L42P.Q5pos, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

/-- The `W34_56` shape of `R204`: `R204 = K_Y (G44 - g34) + K_W (g45 - g35)` (`G33 = G55 = 0`). -/
theorem l42_R204_form : p.R204 = p.KY * (p.G44 - p.g34) + p.KW * (p.g45 - p.g35) := by
  rw [l42_KY_form p]
  simp only [L42P.R204, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L42P.KW, KW_sp, L42P.C35, L42P.P2, L42P.D035,
    L42P.D234, L42P.P0, L42P.del0, L42P.del2]
  ring

/-- `M15` entries. -/
theorem l42_M15_form : p.M15 = (p.s * p.del2 * p.D035) * p.G44 + ((1 - p.s) * p.del0 * p.D234) * p.G55 +
    (p.s * p.S * p.C35) * p.g34 + ((1 - p.s) * p.S * p.C35) * p.g35 +
    (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035) * p.g45 := by
  simp only [L42P.M15, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

/-- `U20 = |K_W| Q20 + S (h2 - h0) U5 R204` (`u20_entries`): `G33 = g35 = 0`. -/
abbrev L42P.U20 (p : L42P) : ℝ := p.KWa * p.Q20 + p.S * (p.h2 - p.h0) * p.U5 * p.R204

theorem l42_u20_entries : p.U20 =
    (-p.KWa * (p.P2 - p.D035) * p.U4 + p.S * (p.h2 - p.h0) * p.U5 * p.KY) * p.G44 +
    (-p.KWa * (p.D234 - p.P0) * p.U5) * p.G55 +
    (-(p.S * (p.h2 - p.h0) * (p.KWa * p.U4 + p.KY * p.U5))) * p.g34 +
    (-p.KWa * ((p.P2 - p.D035) * p.U5 + (p.D234 - p.P0) * p.U4 + p.S * (p.h2 - p.h0) * p.U5)) * p.g45 := by
  have hR := l42_R204_form p
  simp only [L42P.U20, L42P.Q20, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L42P.KWa]
  rw [hR]; ring

/-- `M15* = |K_W| M15 + (s-1) S C35 R204` (case `s ≥ 1`): `G33 = g35 = 0`, `g34` entry `m34*`. -/
abbrev L42P.M15s (p : L42P) : ℝ := p.KWa * p.M15 + (p.s - 1) * p.S * p.C35 * p.R204

/-- `m34* = S C35 (s |K_W| - (s-1) K_Y)`. -/
abbrev L42P.m34s (p : L42P) : ℝ := p.S * p.C35 * (p.s * p.KWa - (p.s - 1) * p.KY)

theorem l42_m34star_ge : p.M15s =
    (p.KWa * p.s * p.del2 * p.D035 + (p.s - 1) * p.S * p.C35 * p.KY) * p.G44 +
    (p.KWa * (1 - p.s) * p.del0 * p.D234) * p.G55 + p.m34s * p.g34 +
    (p.KWa * (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035) + (p.s - 1) * p.S * p.C35 * p.KW) * p.g45 := by
  have hM := l42_M15_form p
  have hR := l42_R204_form p
  simp only [L42P.M15s, L42P.m34s, L42P.KWa]
  rw [hM, hR]; ring

/-- `s < 1`: `M15* := M15`, `g34` entry `s S C35`. -/
theorem l42_m34star_lt : p.M15 =
    (p.s * p.del2 * p.D035) * p.G44 + ((1 - p.s) * p.del0 * p.D234) * p.G55 + (p.s * p.S * p.C35) * p.g34 +
    ((1 - p.s) * p.S * p.C35) * p.g35 + (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035) * p.g45 :=
  l42_M15_form p

/-- `U20* = m34* U20 + u34m M15*` (case `s ≥ 1`): `G33 = g34 = g35 = 0`. -/
abbrev L42P.u34m (p : L42P) : ℝ := p.S * (p.h2 - p.h0) * (p.KWa * p.U4 + p.KY * p.U5)

theorem l42_U20star_ge : p.m34s * p.U20 + p.u34m * p.M15s =
    (p.m34s * (-p.KWa * (p.P2 - p.D035) * p.U4 + p.S * (p.h2 - p.h0) * p.U5 * p.KY) +
      p.u34m * (p.KWa * p.s * p.del2 * p.D035 + (p.s - 1) * p.S * p.C35 * p.KY)) * p.G44 +
    (p.m34s * (-p.KWa * (p.D234 - p.P0) * p.U5) + p.u34m * (p.KWa * (1 - p.s) * p.del0 * p.D234)) * p.G55 +
    (p.m34s * (-p.KWa * ((p.P2 - p.D035) * p.U5 + (p.D234 - p.P0) * p.U4 + p.S * (p.h2 - p.h0) * p.U5)) +
      p.u34m * (p.KWa * (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035) +
        (p.s - 1) * p.S * p.C35 * p.KW)) * p.g45 := by
  have h1 := l42_u20_entries p
  have h2 := l42_m34star_ge p
  rw [h1, h2]
  simp only [L42P.u34m]; ring

/-- `s < 1`: `U20* = m34* U20 + u34m M15` with `m34* = s S C35`; `g35` entry `u34m (1-s) S C35 ≥ 0`-type. -/
theorem l42_U20star_lt : (p.s * p.S * p.C35) * p.U20 + p.u34m * p.M15 =
    ((p.s * p.S * p.C35) * (-p.KWa * (p.P2 - p.D035) * p.U4 + p.S * (p.h2 - p.h0) * p.U5 * p.KY) +
      p.u34m * (p.s * p.del2 * p.D035)) * p.G44 +
    ((p.s * p.S * p.C35) * (-p.KWa * (p.D234 - p.P0) * p.U5) + p.u34m * ((1 - p.s) * p.del0 * p.D234)) * p.G55 +
    (p.u34m * ((1 - p.s) * p.S * p.C35)) * p.g35 +
    ((p.s * p.S * p.C35) * (-p.KWa * ((p.P2 - p.D035) * p.U5 + (p.D234 - p.P0) * p.U4 +
        p.S * (p.h2 - p.h0) * p.U5)) +
      p.u34m * (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035)) * p.g45 := by
  have h1 := l42_u20_entries p
  have h2 := l42_M15_form p
  rw [h1, h2]
  simp only [L42P.u34m]; ring

/-- `B^(Q20) = (h2-h0) h2 G4 M15 + (h2-h0) C35 (-G5) W21' + h2 C35 Q20`: `G33 = g34 = g35 = 0` (`bq20_blocks`). -/
abbrev L42P.BQ20 (p : L42P) : ℝ := (p.h2 - p.h0) * p.h2 * p.G4 * p.M15 +
  (p.h2 - p.h0) * p.C35 * (-p.G5) * p.W21' + p.h2 * p.C35 * p.Q20

theorem l42_bq20_blocks : p.BQ20 =
    ((p.h2 - p.h0) * p.h2 * p.G4 * (p.s * p.del2 * p.D035) +
      (p.h2 - p.h0) * p.C35 * (-p.G5) * ((p.P2 - p.s) * (1 - p.t)) - p.h2 * p.C35 * ((p.P2 - p.D035) * p.U4)) * p.G44 +
    ((p.h2 - p.h0) * p.h2 * p.G4 * ((1 - p.s) * p.del0 * p.D234) +
      (p.h2 - p.h0) * p.C35 * (-p.G5) * ((p.D234 - p.t) * p.t) - p.h2 * p.C35 * ((p.D234 - p.P0) * p.U5)) * p.G55 +
    ((p.h2 - p.h0) * p.h2 * p.G4 * (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035) +
      (p.h2 - p.h0) * p.C35 * (-p.G5) * ((p.P2 - p.s) * p.t + (p.D234 - p.t) * (1 - p.t)) -
      p.h2 * p.C35 * ((p.P2 - p.D035) * p.U5 + (p.D234 - p.P0) * p.U4)) * p.g45 := by
  simp only [L42P.BQ20, L42P.M15, L42P.W21', L42P.Q20, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5, L41P.G4, L42P.G5,
    L41P.U4, L41P.U5, L42P.C35, L41P.S, L42P.P2, L42P.D234, L42P.D035, L42P.P0, L42P.del0, L42P.del2,
    U4_sp, U5_sp, D023_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp, S_sp, P2_sp, D234_sp, D035_sp, P0_sp]
  ring

end L42Blocks

/-! ## L42-2 (`J = Q2`): `cert_FA_CQ2_false` -/

section L42Q2

variable (p : L42P)

/-- `B_{M15}^{(Q2)} = h2 G4 M15 + C35 (-G5) W21' + C35 Q_2`. -/
abbrev L42P.BQ2 (p : L42P) : ℝ := p.h2 * p.G4 * p.M15 + p.C35 * (-p.G5) * p.W21' + p.C35 * p.Q2

abbrev L42P.mQ44 (p : L42P) : ℝ := p.h2 * p.G4 * (p.s * p.del2 * p.D035) +
  p.C35 * (-p.G5) * ((p.P2 - p.s) * (1 - p.t)) - p.C35 * (p.P2 * p.U4)
abbrev L42P.mQ55 (p : L42P) : ℝ := p.h2 * p.G4 * ((1 - p.s) * p.del0 * p.D234) +
  p.C35 * (-p.G5) * ((p.D234 - p.t) * p.t) - p.C35 * (p.D234 * p.U5)
abbrev L42P.mQ45 (p : L42P) : ℝ := p.h2 * p.G4 * (p.s * p.del0 * p.D234 + (1 - p.s) * p.del2 * p.D035) +
  p.C35 * (-p.G5) * ((p.P2 - p.s) * p.t + (p.D234 - p.t) * (1 - p.t)) - p.C35 * (p.P2 * p.U5 + p.D234 * p.U4)

/-- `B^{(Q2)}` has `G33 = g34 = g35 = 0`. -/
theorem l42_BQ2_form : p.BQ2 = p.mQ44 * p.G44 + p.mQ55 * p.G55 + p.mQ45 * p.g45 := by
  simp only [L42P.BQ2, L42P.mQ44, L42P.mQ55, L42P.mQ45, L42P.M15, L42P.W21', L42P.Q2, L42P.rowv, L42P.ge3,
    L42P.ge4, L42P.ge5, L41P.G4, L42P.G5, L41P.U4, L41P.U5, L42P.C35, L41P.S, L42P.P2, L42P.D234, L42P.D035,
    L42P.del0, L42P.del2, U4_sp, U5_sp, D023_sp, DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp, S_sp, P2_sp, D234_sp,
    D035_sp]
  ring

/-- `m_{Q2,55} = -C35 (-G5) t^2 - (s-1) G4 D234 B35`. -/
theorem l42_mQ55_form : p.mQ55 = -(p.C35 * (-p.G5) * p.t ^ 2) - (p.s - 1) * p.G4 * p.D234 * p.B35 := by
  simp only [L42P.mQ55, L41P.G4, L42P.G5, L41P.U5, L42P.C35, L42P.B35, L42P.D234, L42P.del0, U5_sp, D023_sp,
    DG4_sp, DG5_sp, D0_sp, G4_sp, G5_sp, B35_sp, C35_sp, D234_sp]
  ring

/-- `m_{Q2,55} < 0` on `s ≥ 1` (`C35 > 0`, `G5 < 0`, `t > 0`, `G4, D234, B35 > 0`). -/
theorem l42_mQ55_neg (hs : 1 ≤ p.s) (ht : 0 < p.t) (hC : 0 < p.C35) (hG5 : p.G5 < 0) (hG4 : 0 < p.G4)
    (hD : 0 < p.D234) (hB : 0 < p.B35) : p.mQ55 < 0 := by
  rw [l42_mQ55_form]
  have h1 : 0 < p.C35 * (-p.G5) * p.t ^ 2 := by
    have : 0 < -p.G5 := neg_pos.mpr hG5
    positivity
  have h2 : 0 ≤ (p.s - 1) * p.G4 * p.D234 * p.B35 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hG4.le) hD.le) hB.le
  linarith

/-- `P_FA^* = FA23 + (h2-1) FA3 = P2 v4 G44 + D234 v5 G55 + (P2 v5 + D234 v4) g45`. -/
theorem l42_PFA_form : p.FA23 + (p.h2 - 1) * p.FA3 =
    (p.P2 * p.v4) * p.G44 + (p.D234 * p.v5) * p.G55 + (p.P2 * p.v5 + p.D234 * p.v4) * p.g45 := by
  simp only [L42P.FA23, L42P.FA3, L42P.rowv, L42P.ge3, L42P.ge4, L42P.ge5]; ring

abbrev L42P.f44 (p : L42P) : ℝ := -p.mQ55 * (p.P2 * p.v4) + p.D234 * p.v5 * p.mQ44
abbrev L42P.f45 (p : L42P) : ℝ := -p.mQ55 * (p.P2 * p.v5 + p.D234 * p.v4) + p.D234 * p.v5 * p.mQ45

/-- `F^{(Q2)} = (-m55) P_FA^* + (D234 v5) B^{(Q2)} = f44 G44 + f45 g45` (`G55` cancelled). -/
theorem l42_F_form : (-p.mQ55) * (p.FA23 + (p.h2 - 1) * p.FA3) + p.D234 * p.v5 * p.BQ2 =
    p.f44 * p.G44 + p.f45 * p.g45 := by
  rw [l42_PFA_form, l42_BQ2_form]; ring

/-- Region facts of the `J = Q2` certificate. -/
structure L42Q2Facts (p : L42P) : Prop where
  hS : 0 < p.S
  hh2 : 1 < p.h2
  hU5 : 0 < p.U5
  hv5 : 0 < p.v5
  hD234 : 0 < p.D234
  hC35 : 0 < p.C35
  hG4 : 0 < p.G4
  hG5 : p.G5 ≤ 0
  hG44 : 0 < p.G44
  hG55 : 0 < p.G55
  hg45 : p.g45 ≤ 0

/-- The six valid rows of `C_{Q,1} ∪ C_{Q,3}` on `F-A`. -/
structure L42Q2Rows (p : L42P) : Prop where
  hQ2 : 0 ≤ p.Q2
  hW21 : 0 ≤ p.W21'
  hM15 : 0 ≤ p.M15
  hFA23 : 0 ≤ p.FA23
  hFA3 : 0 ≤ p.FA3
  hQ4neg : 0 ≤ p.Q4neg

theorem l42_BQ2_nonneg {p : L42P} (hf : L42Q2Facts p) (hr : L42Q2Rows p) : 0 ≤ p.BQ2 := by
  have h2 : 0 < p.h2 := by linarith [hf.hh2]
  have e1 : 0 ≤ p.h2 * p.G4 * p.M15 := mul_nonneg (mul_nonneg h2.le hf.hG4.le) hr.hM15
  have e2 : 0 ≤ p.C35 * (-p.G5) * p.W21' := mul_nonneg (mul_nonneg hf.hC35.le (by linarith [hf.hG5])) hr.hW21
  have e3 : 0 ≤ p.C35 * p.Q2 := mul_nonneg hf.hC35.le hr.hQ2
  simp only [L42P.BQ2]; linarith

theorem l42_F_nonneg {p : L42P} (hf : L42Q2Facts p) (hr : L42Q2Rows p) (hm : p.mQ55 < 0) :
    0 ≤ p.f44 * p.G44 + p.f45 * p.g45 := by
  rw [← l42_F_form]
  have hP : 0 ≤ p.FA23 + (p.h2 - 1) * p.FA3 :=
    add_nonneg hr.hFA23 (mul_nonneg (by linarith [hf.hh2]) hr.hFA3)
  have e1 := mul_nonneg (neg_nonneg.mpr hm.le) hP
  have e2 := mul_nonneg (mul_nonneg hf.hD234.le hf.hv5.le) (l42_BQ2_nonneg hf hr)
  linarith

/-- Route F-alone: `f45 ≥ 0`, `f44 < 0`. -/
theorem l42_Q2_routeF {p : L42P} (hf : L42Q2Facts p) (hr : L42Q2Rows p) (hm : p.mQ55 < 0)
    (h45 : 0 ≤ p.f45) (h44 : p.f44 < 0) : False := by
  have h := l42_F_nonneg hf hr hm
  have a : p.f44 * p.G44 < 0 := mul_neg_of_neg_of_pos h44 hf.hG44
  have b : p.f45 * p.g45 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h45 hf.hg45
  linarith

/-- Route `(Q2-a)`: `f45 < 0`, `U5 f44 - f45 U4 < 0`; `S U5 F + (-f45) Q4neg = S (U5 f44 - f45 U4) G44`. -/
theorem l42_Q2_routeQa {p : L42P} (hf : L42Q2Facts p) (hr : L42Q2Rows p) (hm : p.mQ55 < 0)
    (h45 : p.f45 < 0) (hc : p.U5 * p.f44 - p.f45 * p.U4 < 0) : False := by
  have h := l42_F_nonneg hf hr hm
  have e1 := mul_nonneg (mul_nonneg hf.hS.le hf.hU5.le) h
  have e2 := mul_nonneg (neg_nonneg.mpr h45.le) hr.hQ4neg
  rw [l42_Q4neg_form] at e2
  have e3 : p.S * (p.U5 * p.f44 - p.f45 * p.U4) * p.G44 < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hf.hS hc) hf.hG44
  have : p.S * p.U5 * (p.f44 * p.G44 + p.f45 * p.g45) + -p.f45 * (p.S * (p.U4 * p.G44 + p.U5 * p.g45)) =
      p.S * (p.U5 * p.f44 - p.f45 * p.U4) * p.G44 := by ring
  linarith

/-- Route `E_{Q4neg}`: `S U5 B^{(Q2)} + max(-m45, 0) Q4neg` (the `G55` entry `S U5 m55 < 0` is never flipped). -/
theorem l42_Q2_routeE {p : L42P} (hf : L42Q2Facts p) (hr : L42Q2Rows p) (hm : p.mQ55 < 0)
    (hc : (p.mQ45 ≤ 0 ∧ p.U5 * p.mQ44 - p.mQ45 * p.U4 ≤ 0) ∨ (0 ≤ p.mQ45 ∧ p.mQ44 ≤ 0)) : False := by
  have hB := l42_BQ2_nonneg hf hr
  rw [l42_BQ2_form] at hB
  have hSU := mul_pos hf.hS hf.hU5
  have hb : p.S * p.U5 * (p.mQ44 * p.G44 + p.mQ55 * p.G55 + p.mQ45 * p.g45) ≥ 0 := mul_nonneg hSU.le hB
  have hg : p.mQ55 * p.G55 < 0 := mul_neg_of_neg_of_pos hm hf.hG55
  rcases hc with ⟨h45, hq⟩ | ⟨h45, h44⟩
  · have e2 := mul_nonneg (neg_nonneg.mpr h45) hr.hQ4neg
    rw [l42_Q4neg_form] at e2
    have : p.S * p.U5 * (p.mQ44 * p.G44 + p.mQ55 * p.G55 + p.mQ45 * p.g45) + -p.mQ45 * (p.S * (p.U4 * p.G44 + p.U5 * p.g45)) =
        p.S * (p.U5 * p.mQ44 - p.mQ45 * p.U4) * p.G44 + p.S * p.U5 * (p.mQ55 * p.G55) := by ring
    have e3 : p.S * (p.U5 * p.mQ44 - p.mQ45 * p.U4) * p.G44 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hf.hS.le hq) hf.hG44.le
    have e4 : p.S * p.U5 * (p.mQ55 * p.G55) < 0 := mul_neg_of_pos_of_neg hSU hg
    linarith
  · have a : p.mQ44 * p.G44 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h44 hf.hG44.le
    have b : p.mQ45 * p.g45 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h45 hf.hg45
    have h0 : p.mQ44 * p.G44 + p.mQ55 * p.G55 + p.mQ45 * p.g45 < 0 := by linarith
    have := mul_neg_of_pos_of_neg hSU h0
    linarith

/-- The named sign case of the `J = Q2` certificate (all three are `G`-free sign conditions on the shape). -/
def Q2Case (p : L42P) : Prop :=
  (0 ≤ p.f45 ∧ p.f44 < 0) ∨ (p.f45 < 0 ∧ p.U5 * p.f44 - p.f45 * p.U4 < 0) ∨
    (p.mQ45 ≤ 0 ∧ p.U5 * p.mQ44 - p.mQ45 * p.U4 ≤ 0) ∨ (0 ≤ p.mQ45 ∧ p.mQ44 ≤ 0)

/-- **`cert_FA_CQ2_false`** (`J = Q2`, rows `Q2, W21', M15, FA23, FA3, Q4neg`): on `m_{Q2,55} < 0` and a named
sign case, the six rows cannot all be `≥ 0`.  (`m_{Q2,55} < 0` is `l42_mQ55_neg` on `s ≥ 1`.) -/
theorem cert_FA_CQ2_false {p : L42P} (hf : L42Q2Facts p) (hr : L42Q2Rows p) (hm : p.mQ55 < 0)
    (hc : Q2Case p) : False := by
  rcases hc with ⟨a, b⟩ | ⟨a, b⟩ | h | h
  · exact l42_Q2_routeF hf hr hm a b
  · exact l42_Q2_routeQa hf hr hm a b
  · exact l42_Q2_routeE hf hr hm (Or.inl h)
  · exact l42_Q2_routeE hf hr hm (Or.inr h)

/-- `S (z_2 - z_4)(v_Q)`, `S (z_5 - z_4)(v_Q)`, `S (z_5 - z_0)(v_Q)` (the extra rows of `C_{Q,4}`), `W23`, `FA21`. -/
abbrev L42P.Q24 (p : L42P) : ℝ := p.rowv (p.P2 - p.S) p.D234 p.h2 0 (-p.U4) (-p.U5)
abbrev L42P.Q54 (p : L42P) : ℝ := p.rowv (-p.S) p.S 0 0 (-p.U4) (-p.U5)
abbrev L42P.Q50 (p : L42P) : ℝ := p.rowv (-p.D035) (p.S - p.P0) (-p.h0) 0 (-p.U4) (-p.U5)
abbrev L42P.W23' (p : L42P) : ℝ := p.rowv p.P2 p.D234 (p.h2 - 1) 0 (1 - p.t) p.t
abbrev L42P.FA21 (p : L42P) : ℝ := p.rowv (p.P2 - p.s) (p.D234 - p.t) p.h2 0 p.v4 p.v5

/-- The valid rows of `C_{Q,4}` on `F-A` (`W34_56 = G45 - g35 ≥ 0` and `R204 ≥ 0` from `Q7 ∪ C_WI3`). -/
structure L42Q4Rows (p : L42P) : Prop where
  hQ24 : 0 ≤ p.Q24
  hQ20 : 0 ≤ p.Q20
  hQ54 : 0 ≤ p.Q54
  hQ50 : 0 ≤ p.Q50
  hW21 : 0 ≤ p.W21'
  hW23 : 0 ≤ p.W23'
  hM15 : 0 ≤ p.M15
  hR204 : 0 ≤ p.R204
  hW34 : 0 ≤ p.g45 - p.g35
  hFA23 : 0 ≤ p.FA23
  hFA3 : 0 ≤ p.FA3
  hFA21 : 0 ≤ p.FA21

/-- **Open named hypothesis** `FACQ4Hyp` (`J = Q4` on the F-A cone, region facts as `J = Q2`): the twelve rows of
`C_{Q,4}` cannot all be `≥ 0`.  NOT proved: A42's certificate leaves 76 (+15) of 11,441 shapes uncovered. -/
def FACQ4Hyp (p : L42P) : Prop := L42Q2Facts p → L42Q4Rows p → False

end L42Q2

/-! ## L42-4: `cert_FB_Z3_false` (Q42.3, `F-B`, `gam05 < 0`-free, `w5 ≤ 0`, `w4' ≥ 0`) -/

section L42Z3

variable (p : L41P)

abbrev L41P.kap6 : ℝ := p.qA4 * p.t * p.U4 - p.S * (1 - p.t) * (p.h2 - 1) * p.D0
/-- `H_+^{(04)} = (h2 - 1) B04 + h0 (h2 - h0) D0 H`. -/
abbrev L41P.Hp : ℝ := (p.h2 - 1) * p.B04 + p.h0 * (p.h2 - p.h0) * p.D0 * p.H
abbrev L41P.a4c : ℝ := p.h0 * (p.h2 - p.h0) * p.D0 * p.qA4 * (1 - p.t) * p.U4 - (p.h2 - 1) * p.P4 * p.U4 ^ 2 * p.w4p
abbrev L41P.a5c : ℝ := p.h0 * (p.h2 - p.h0) * p.D0 * p.kap6 - (p.h2 - 1) * p.P4 * p.U4 ^ 2 * p.w5p
abbrev L41P.cZ : ℝ := p.S ^ 3 * (p.h2 - 1) * (p.h2 - p.h0) * p.h0 * p.D0 ^ 2 * p.G4
abbrev L41P.z4s : ℝ := p.P4 * ((1 - p.w5) * p.w4p + p.w5p * p.w4)
abbrev L41P.z5s : ℝ := p.P4 * ((1 - p.w5) * p.w5p + p.w5p * p.w5)

/-- `H_+` as a nonnegative combination of rows (the `W21'` coefficient cancels). -/
theorem l42_Hp_rows : p.Hp = p.h2 * (p.h2 - 1) * p.P4 * p.Q04 + p.h0 * p.h2 * (p.h2 - p.h0) * p.D0 * p.W23 +
    p.h0 * (p.h2 - 1) * p.G4 * p.F12 := by
  simp only [L41P.Hp, L41P.B04, L41P.H]; ring

/-- `G55` scalar relation of `S U4^2 H`. -/
theorem l42_rel_G55 : p.S * p.U4 ^ 2 * (qA5_sp p.a2 p.b2 p.s p.t * p.t) =
    p.kap6 * (p.S * p.U5) - p.S ^ 3 * (p.h2 - 1) * p.D0 * p.G4 := by
  simp only [L41P.kap6, L41P.S, L41P.D0, L41P.U4, L41P.U5, L41P.qA4, U4_sp, U5_sp, D023_sp, DG4_sp,
    DG5_sp, D0_sp, G4_sp, G5_sp, qA4_sp, qA5_sp, S_sp]
  ring

/-- `g45` scalar relation of `S U4^2 H`. -/
theorem l42_rel_g45 : p.S * p.U4 ^ 2 * (p.qA4 * p.t + qA5_sp p.a2 p.b2 p.s p.t * (1 - p.t)) =
    p.qA4 * (1 - p.t) * p.U4 * (p.S * p.U5) + p.kap6 * (p.S * p.U4) := by
  simp only [L41P.kap6, L41P.S, L41P.D0, L41P.U4, L41P.U5, L41P.qA4, U4_sp, U5_sp, D023_sp, DG4_sp,
    DG5_sp, D0_sp, G4_sp, G5_sp, qA4_sp, qA5_sp, S_sp]
  ring

/-- `S U4^2 H = qA4 (1-t) U4 Q4neg + kap6' Q5neg - S^3 (h2-1) D0 G4 G55`. -/
theorem l42_SU4H : p.S * p.U4 ^ 2 * p.H =
    p.qA4 * (1 - p.t) * p.U4 * p.Q4n + p.kap6 * p.Q5n - p.S ^ 3 * (p.h2 - 1) * p.D0 * p.G4 * p.G55 := by
  rw [l41_H_eq, l41_Q4n_eq, l41_Q5n_eq]
  linear_combination p.G55 * l42_rel_G55 p + p.g45 * l42_rel_g45 p

/-- `S U4^2 H_+ = a4 Q4neg + a5 Q5neg - c G55`. -/
theorem l42_SU4Hp : p.S * p.U4 ^ 2 * p.Hp = p.a4c * p.Q4n + p.a5c * p.Q5n - p.cZ * p.G55 := by
  have h1 := l41_B04_zero p
  have h2 := l42_SU4H p
  simp only [L41P.Hp, L41P.a4c, L41P.a5c, L41P.cZ]
  linear_combination (p.h2 - 1) * p.U4 ^ 2 * h1 + p.h0 * (p.h2 - p.h0) * p.D0 * h2

/-- The positive syzygy `Z_* = 0`. -/
theorem l42_Zstar : (1 - p.w5) * (p.S * p.B04) + p.w5p * (p.S * p.B05) + p.z4s * p.Q4n + p.z5s * p.Q5n = 0 := by
  have h1 := l41_B04_zero p
  have h2 := l41_B05_zero p
  simp only [L41P.z4s, L41P.z5s]
  linear_combination (1 - p.w5) * h1 + p.w5p * h2

/-- Region facts of Q42.3: `L41Facts` without `del05 ≥ 0` (and without `gam05 < 0`), plus `w5 ≤ 0`,
`w4' ≥ 0`, `w5' > 0`. -/
structure L42Z3Facts (p : L41P) : Prop where
  hS : 0 < p.S
  hh0 : 0 < p.h0
  hh02 : p.h0 < p.h2
  hh2 : 1 < p.h2
  hD0 : 0 < p.D0
  hP4 : 0 < p.P4
  hG4 : 0 < p.G4
  hU4 : 0 < p.U4
  hw4 : 0 < p.w4
  hG55 : 0 < p.G55
  hchi : p.chi < 0
  hV : p.V < 0
  hw5 : p.w5 ≤ 0
  hw4p : 0 ≤ p.w4p
  hw5p : 0 < p.w5p

theorem l42_Q4n_nonneg {p : L41P} (hf : L42Z3Facts p) (hr : L41Rows p) : 0 ≤ p.Q4n := by
  have h := l41_CQ5 p
  have hc : 0 < -p.chi := neg_pos.mpr hf.hchi
  have hv : 0 < -p.V := neg_pos.mpr hf.hV
  have e1 : 0 ≤ p.S * (p.h2 - p.h0) * p.Q05 := mul_nonneg (mul_nonneg hf.hS.le (by linarith [hf.hh02])) hr.hQ05
  have e2 : 0 ≤ p.S * p.h0 * p.Q02 := mul_nonneg (mul_nonneg hf.hS.le hf.hh0.le) hr.hQ02
  have e3 : 0 ≤ ((-p.chi) + (-p.V)) * p.Q5n := mul_nonneg (by linarith) hr.hQ5n
  have h1 : 0 ≤ (-p.chi) * p.Q4n := by rw [← h]; linarith
  exact nonneg_of_mul_nonneg_right h1 hc

theorem l42_Q04_nonneg {p : L41P} (hf : L42Z3Facts p) (hr : L41Rows p) : 0 ≤ p.Q04 := by
  have h := l41_CQ5' p
  have hc : 0 < -p.chi := neg_pos.mpr hf.hchi
  have hv : 0 < -p.V := neg_pos.mpr hf.hV
  have e1 : 0 ≤ ((-p.chi) + p.S * (p.h2 - p.h0)) * p.Q05 :=
    mul_nonneg (by have := hf.hS; have := hf.hh02; nlinarith) hr.hQ05
  have e2 : 0 ≤ p.S * p.h0 * p.Q02 := mul_nonneg (mul_nonneg hf.hS.le hf.hh0.le) hr.hQ02
  have e3 : 0 ≤ (-p.V) * p.Q5n := mul_nonneg hv.le hr.hQ5n
  have h1 : 0 ≤ (-p.chi) * p.Q04 := by rw [← h]; linarith
  exact nonneg_of_mul_nonneg_right h1 hc

theorem l42_B05_nonneg {p : L41P} (hf : L42Z3Facts p) (hr : L41Rows p) : 0 ≤ p.B05 := by
  simp only [L41P.B05]
  have h2p : 0 < p.h2 := by linarith [hf.hh2]
  have e1 : 0 ≤ p.h2 * p.P4 * p.Q05 := mul_nonneg (by positivity [hf.hP4]) hr.hQ05
  have e2 : 0 ≤ p.h0 * (p.h2 - p.h0) * p.D0 * p.W21 :=
    mul_nonneg (mul_nonneg (mul_nonneg hf.hh0.le (by linarith [hf.hh02])) hf.hD0.le) hr.hW21
  have e3 : 0 ≤ p.h0 * p.G4 * p.F12 := mul_nonneg (mul_nonneg hf.hh0.le hf.hG4.le) hr.hF12
  linarith

theorem l42_B04_nonneg {p : L41P} (hf : L42Z3Facts p) (hr : L41Rows p) : 0 ≤ p.B04 := by
  simp only [L41P.B04]
  have h2p : 0 < p.h2 := by linarith [hf.hh2]
  have e1 : 0 ≤ p.h2 * p.P4 * p.Q04 := mul_nonneg (by positivity [hf.hP4]) (l42_Q04_nonneg hf hr)
  have e2 : 0 ≤ p.h0 * (p.h2 - p.h0) * p.D0 * p.W21 :=
    mul_nonneg (mul_nonneg (mul_nonneg hf.hh0.le (by linarith [hf.hh02])) hf.hD0.le) hr.hW21
  have e3 : 0 ≤ p.h0 * p.G4 * p.F12 := mul_nonneg (mul_nonneg hf.hh0.le hf.hG4.le) hr.hF12
  linarith

/-- **`cert_FB_Z3_false`** (Q42.3): `F-B × C_Q5^-`, `chi < 0`, `w5 ≤ 0`, `w4' ≥ 0`: the six rows cannot all be
`≥ 0` (no `del05`, no `gam05` hypothesis). -/
theorem cert_FB_Z3_false {p : L41P} (hf : L42Z3Facts p) (hr : L41Rows p) : False := by
  have hQ4 := l42_Q4n_nonneg hf hr
  have hQ5 := hr.hQ5n
  have hB4 := l42_B04_nonneg hf hr
  have hB5 := l42_B05_nonneg hf hr
  have hZ := l42_Zstar p
  have hP : 0 < p.P4 := hf.hP4
  have h1w : 0 < 1 - p.w5 := by linarith [hf.hw5]
  have hz4 : 0 < p.z4s := by
    simp only [L41P.z4s]
    have : 0 < (1 - p.w5) * p.w4p + p.w5p * p.w4 :=
      add_pos_of_nonneg_of_pos (mul_nonneg h1w.le hf.hw4p) (mul_pos hf.hw5p hf.hw4)
    exact mul_pos hP this
  have hz5 : 0 < p.z5s := by
    have : (1 - p.w5) * p.w5p + p.w5p * p.w5 = p.w5p := by ring
    simp only [L41P.z5s]; rw [this]; exact mul_pos hP hf.hw5p
  have s1 : 0 ≤ (1 - p.w5) * (p.S * p.B04) := mul_nonneg h1w.le (mul_nonneg hf.hS.le hB4)
  have s2 : 0 ≤ p.w5p * (p.S * p.B05) := mul_nonneg hf.hw5p.le (mul_nonneg hf.hS.le hB5)
  have t4 : 0 ≤ p.z4s * p.Q4n := mul_nonneg hz4.le hQ4
  have t5 : 0 ≤ p.z5s * p.Q5n := mul_nonneg hz5.le hQ5
  have e4 : p.z4s * p.Q4n = 0 := by linarith
  have e5 : p.z5s * p.Q5n = 0 := by linarith
  have q4 : p.Q4n = 0 := (mul_eq_zero.mp e4).resolve_left hz4.ne'
  have q5 : p.Q5n = 0 := (mul_eq_zero.mp e5).resolve_left hz5.ne'
  have hI := l42_SU4Hp p
  rw [q4, q5] at hI
  have hH : 0 ≤ p.Hp := by
    rw [l42_Hp_rows]
    have h2p : 0 < p.h2 := by linarith [hf.hh2]
    have a1 : 0 ≤ p.h2 * (p.h2 - 1) * p.P4 * p.Q04 :=
      mul_nonneg (mul_nonneg (mul_nonneg h2p.le (by linarith [hf.hh2])) hP.le) (l42_Q04_nonneg hf hr)
    have a2 : 0 ≤ p.h0 * p.h2 * (p.h2 - p.h0) * p.D0 * p.W23 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf.hh0.le h2p.le) (by linarith [hf.hh02])) hf.hD0.le) hr.hW23
    have a3 : 0 ≤ p.h0 * (p.h2 - 1) * p.G4 * p.F12 :=
      mul_nonneg (mul_nonneg (mul_nonneg hf.hh0.le (by linarith [hf.hh2])) hf.hG4.le) hr.hF12
    linarith
  have hcz : 0 < p.cZ := by
    have : 0 < p.h2 - 1 := by linarith [hf.hh2]
    have : 0 < p.h2 - p.h0 := by linarith [hf.hh02]
    simp only [L41P.cZ]
    have := hf.hS; have := hf.hh0; have := hf.hD0; have := hf.hG4
    positivity
  have hl : 0 ≤ p.S * p.U4 ^ 2 * p.Hp := mul_nonneg (mul_nonneg hf.hS.le (sq_nonneg _)) hH
  have hr2 : 0 < p.cZ * p.G55 := mul_pos hcz hf.hG55
  linarith

end L42Z3

/-! ### `v012_form` (corrected sign, A42-REFEREE F2) -/

section L42V012

variable {x : Fin 7 → ℝ³}

/-- **`v012_form`**: `v012 = S [h2 (x0 - x1) - h0 (x2 - x1)]` (the printed `h0 (x2 - x1) - h2 (x0 - x1)` is false). -/
theorem l42_v012_form (N : NF29 x) :
    l41_v012 N x = (S_sp N.s N.t * N.h2) • (x 0 - x 1) - N.h0 • (S_sp N.s N.t • (x 2 - x 1)) := by
  have h := l41_radon_v12 N
  linear_combination (norm := module) h

end L42V012

end Minimality.NF29
