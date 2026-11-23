module

public import Minimality.Type29CellII44

@[expose] public section

/-!
# Type 29, `K1a ∩ G* ∩ Cell II`, Task L45 (`A45-REFEREE`)

* `L45-1` `w14_true5rim_split`: pure order lemma, the split `A | B | C | D` of the TRUE 5-rim `(2,3,5,6,4)` at `v14 - ε d1`.
* `L45-2` `l45_m55_identity`, `neg_G5_pos`, `l45_m55_neg`.
* `L45-3` `front_pair_rows` (pure order) and `v46_front_pair`, `v46_rows_Ia` (view `u = (-U5, -D023, 0)`, SIGN-REPAIRED
  rows: `{0,4}` is in front of `{1,3}`, so a failing `(0,1,4,3)` gives `z1, z3 ≤ z0, z4`).
* `L45-4` `v46_rows_II` (corrected sign of the `u`-term).
* `L45-5` `u46_facets`: the nine facet values at `u`.
* `L45-6` only the named hypothesis `W34Rows` (no proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21 Minimality.H29

namespace Minimality.NF29

/-! ## L45-1 -/

theorem zmod5_all : ∀ B : ZMod 5, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by decide

/-- The TRUE 5-rim `(2,3,5,6,4)` depths `(z2, z3, z5, z6 = 0, z4)`. -/
def rim5 (z2 z3 z4 z5 : ℝ) : ZMod 5 → ℝ := ![z2, z3, z5, 0, z4]

/-- **L45-1**: the true 5-rim `(2,3,5,6,4)` at `v14 - ε d1` (`z6 = 0`) is robustly unimodal outside `A ∪ B ∪ C ∪ D`:
`z4 ≥ 0` (A), `z5 ≤ 0` (B), `z3 ≥ z4` (C), or `z4 ≤ 0 ≤ z5, z4 ≤ z2` (D). -/
theorem w14_true5rim_split {z2 z3 z4 z5 : ℝ}
    (h : ¬ RobUni (rim5 z2 z3 z4 z5)) :
    0 ≤ z4 ∨ z5 ≤ 0 ∨ z4 ≤ z3 ∨ (z4 ≤ 0 ∧ 0 ≤ z5 ∧ z4 ≤ z2) := by
  by_contra hc
  simp only [not_or, not_le, not_and] at hc
  obtain ⟨h4, h5, h3, hD⟩ := hc
  have h42 : z2 < z4 := hD h4.le h5.le
  simp only [RobUni, rim5, not_forall, not_not] at h
  obtain ⟨B, b, c, d, hb, hbc, hcd, hd, e1, e2, e3, e4⟩ := h
  have hb2 : b ≤ 2 := by omega
  have hc3 : c ≤ 3 := by omega
  interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals
    have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := zmod5_all B
    rcases hB with rfl | rfl | rfl | rfl | rfl <;> norm_num [Fin.isValue] at e1 e2 e3 e4 <;> linarith

/-! ## L45-2: `B_M15^(Q4)` and the sign of `m55` -/

section L45Q4

variable (p : L42P)

/-- `B_{M15}^{(Q4)} = h2 G4 M15 + C35 (-G5) W21' + C35 Q24`. -/
abbrev L42P.BM15Q4 : ℝ := p.h2 * p.G4 * p.M15 + p.C35 * (-p.G5) * p.W21' + p.C35 * p.Q24

/-- `m_{Q4,44}`. -/
abbrev L42P.m44 : ℝ := p.h2 * p.G4 * p.s * p.del2 * p.D035 + p.C35 * (-p.G5) * (p.P2 - p.s) * (1 - p.t) +
  p.C35 * (p.S - p.P2) * p.U4
/-- `m_{Q4,55}`. -/
abbrev L42P.m55 : ℝ := -p.h2 * p.G4 * (p.s - 1) * p.del0 * p.D234 + p.C35 * (-p.G5) * (p.D234 - p.t) * p.t -
  p.C35 * p.D234 * p.U5
/-- `m_{Q4,45}`. -/
abbrev L42P.m45 : ℝ := p.h2 * p.G4 * (p.s * p.del0 * p.D234 - (p.s - 1) * p.del2 * p.D035) +
  p.C35 * (-p.G5) * ((p.P2 - p.s) * p.t + (p.D234 - p.t) * (1 - p.t)) +
  p.C35 * ((p.S - p.P2) * p.U5 - p.D234 * p.U4)

/-- **L45-2 (B1)**: `B_{M15}^{(Q4)} = (0, m44, m55, 0, 0, m45)` in `(G33, G44, G55, g34, g35, g45)`:
the `G33`, `g34`, `g35` coefficients vanish identically. -/
theorem l45_BM15_form : p.BM15Q4 = p.m44 * p.G44 + p.m55 * p.G55 + p.m45 * p.g45 := by
  simp only [L42P.BM15Q4, L42P.m44, L42P.m55, L42P.m45, L42P.M15, L42P.W21', L42P.Q24, L42P.rowv, L42P.ge3,
    L42P.ge4, L42P.ge5, L41P.G4, L42P.G5, L41P.U4, L41P.U5, L41P.S, L42P.C35, L42P.P2, L42P.D234, L42P.D035,
    L42P.del0, L42P.del2, U4_sp, U5_sp, G4_sp, G5_sp, D023_sp, DG4_sp, DG5_sp, D0_sp, S_sp, D234_sp,
    D035_sp, P2_sp, C35_sp]
  ring

/-- **L45-2 (B2)**: `m55 = -C35 (-G5) t^2 - (s - 1) G4 D234 B35` (via `C35 - h2 del0 = -B35`). -/
theorem l45_m55_identity : p.m55 =
    -(p.C35 * (-p.G5) * p.t ^ 2) - (p.s - 1) * p.G4 * p.D234 * B35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 := by
  simp only [L42P.m55, L41P.G4, L42P.G5, L41P.U5, L42P.C35, L42P.D234, L42P.del0, U5_sp, G4_sp, G5_sp,
    D023_sp, DG4_sp, DG5_sp, D0_sp, D234_sp, C35_sp, B35_sp]
  ring

end L45Q4

/-- `-G5 = (-a2)(1 - h0) + (-a0)(h2 - 1) > 0` (`a0, a2 < 0 < 1 - h0`, `h2 > 1`). -/
theorem neg_G5_pos {a0 h0 a2 h2 : ℝ} (ha0 : a0 < 0) (ha2 : a2 < 0) (hh0 : h0 < 1) (hh2 : 1 < h2) :
    0 < -G5_sp a0 h0 a2 h2 := by
  have : -G5_sp a0 h0 a2 h2 = (-a2) * (1 - h0) + (-a0) * (h2 - 1) := by simp only [G5_sp]; ring
  rw [this]
  have h1 : 0 < (-a2) * (1 - h0) := mul_pos (by linarith) (by linarith)
  have h2' : 0 < (-a0) * (h2 - 1) := mul_pos (by linarith) (by linarith)
  linarith

/-- **L45-2**: `m55 < 0` for `s ≥ 1` (all factors are region facts). -/
theorem l45_m55_neg (p : L42P) (hs : 1 ≤ p.s) (ht : 0 < p.t) (hC : 0 < p.C35) (hG5 : 0 < -p.G5)
    (hG4 : 0 < p.G4) (hD : 0 < p.D234) (hB : 0 < B35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2) : p.m55 < 0 := by
  rw [l45_m55_identity]
  have h1 : 0 < p.C35 * (-p.G5) * p.t ^ 2 := by positivity
  have h2 : 0 ≤ (p.s - 1) * p.G4 * p.D234 * B35_sp p.a0 p.b0 p.h0 p.a2 p.b2 p.h2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hG4.le) hD.le) hB.le
  linarith

/-! ## L45-5: the nine facet values at `u = (-U5, -D023, 0)` -/

section L45U

variable {x : Fin 7 → ℝ³}

/-- `u_{23,46} = (-U5, -D023, 0) = D234 (x0 - x3) - P0 (x2 - x3)` (`= - N.u2346 x`). -/
noncomputable def uV46 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  N.D234 • (x 0 - x 3) - N.p0346 • (x 2 - x 3)

theorem uV46_eq_neg (N : NF29 x) : N.uV46 x = -(N.u2346 x) := by
  simp only [uV46, u2346]; rw [u2346_eq N]; module

local macro "uV46_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG4, f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

/-- `⟪N_f, uV46⟫ = D234 (f x0 - f x3) - P0 (f x2 - f x3)` for every facet. -/
theorem fdiff_uV46 (N : NF29 x) {S : Finset (Fin 7)} (F : Face16 x S) :
    F.f (x 3 + N.uV46 x) - F.f (x 3) = N.D234 * (F.f (x 0) - F.f (x 3)) - N.p0346 * (F.f (x 2) - F.f (x 3)) := by
  rw [F.hN (x 3 + N.uV46 x) (x 3), add_sub_cancel_left, uV46, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, ← F.hN (x 0) (x 3), ← F.hN (x 2) (x 3)]

theorem uV46_f012 (N : NF29 x) : N.f012.f (x 3 + N.uV46 x) - N.f012.f (x 3) =
    N.D ^ 2 * (N.D02 * (N.D234 - N.p0346)) := by
  rw [fdiff_uV46]
  dsimp only [D02, p0346, D234]
  uV46_fac_val N

theorem uV46_f015 (N : NF29 x) : N.f015.f (x 3 + N.uV46 x) - N.f015.f (x 3) =
    N.D ^ 2 * (N.p0346 * N.P4 + (-N.a0) * (N.D234 - N.p0346)) := by
  rw [fdiff_uV46]
  dsimp only [D02, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f023 (N : NF29 x) : N.f023.f (x 3 + N.uV46 x) - N.f023.f (x 3) = 0 := by
  rw [fdiff_uV46]
  dsimp only [D02, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f035 (N : NF29 x) : N.f035.f (x 3 + N.uV46 x) - N.f035.f (x 3) =
    N.D ^ 2 * (N.p0346 * N.DG5) := by
  rw [fdiff_uV46]
  dsimp only [DG5, D02, dG, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f124 (N : NF29 x) : N.f124.f (x 3 + N.uV46 x) - N.f124.f (x 3) =
    N.D ^ 2 * (-(N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023))) := by
  rw [fdiff_uV46]
  dsimp only [DG4, D023, D02, dG4, dG, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f234 (N : NF29 x) : N.f234.f (x 3 + N.uV46 x) - N.f234.f (x 3) =
    N.D ^ 2 * (-(N.DG4 * N.D234)) := by
  rw [fdiff_uV46]
  dsimp only [DG4, D02, dG4, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f346 (N : NF29 x) : N.f346.f (x 3 + N.uV46 x) - N.f346.f (x 3) = 0 := by
  rw [fdiff_uV46]
  dsimp only [D02, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f356 (N : NF29 x) : N.f356.f (x 3 + N.uV46 x) - N.f356.f (x 3) =
    N.D ^ 2 * ((N.s + N.t - 1) * N.D023) := by
  rw [fdiff_uV46]
  dsimp only [D023, D02, dG4, dG, p0346, D234, P4]
  uV46_fac_val N

theorem uV46_f1456 (N : NF29 x) : N.f1456.f (x 3 + N.uV46 x) - N.f1456.f (x 3) =
    N.D ^ 2 * (N.DG4 - N.D023) := by
  rw [fdiff_uV46]
  dsimp only [DG4, D023, D02, dG4, dG, p0346, D234, P4]
  uV46_fac_val N

/-- **L45-5** (`u46_facets`): the nine facet values at `u = (-U5, -D023, 0)` (common scale `D^2`):
`023 = 346 = 0`; `1456`, `356`, `035 > 0`; `234 < 0`; `012`, `124`, `015` are the three variable polynomials. -/
theorem u46_facets (N : NF29 x) :
    N.f012.f (x 3 + N.uV46 x) - N.f012.f (x 3) = N.D ^ 2 * (N.D02 * (N.D234 - N.p0346)) ∧
    N.f015.f (x 3 + N.uV46 x) - N.f015.f (x 3) =
      N.D ^ 2 * (N.p0346 * N.P4 + (-N.a0) * (N.D234 - N.p0346)) ∧
    N.f023.f (x 3 + N.uV46 x) - N.f023.f (x 3) = 0 ∧
    N.f035.f (x 3 + N.uV46 x) - N.f035.f (x 3) = N.D ^ 2 * (N.p0346 * N.DG5) ∧
    N.f124.f (x 3 + N.uV46 x) - N.f124.f (x 3) =
      N.D ^ 2 * (-(N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023))) ∧
    N.f234.f (x 3 + N.uV46 x) - N.f234.f (x 3) = N.D ^ 2 * (-(N.DG4 * N.D234)) ∧
    N.f346.f (x 3 + N.uV46 x) - N.f346.f (x 3) = 0 ∧
    N.f356.f (x 3 + N.uV46 x) - N.f356.f (x 3) = N.D ^ 2 * ((N.s + N.t - 1) * N.D023) ∧
    N.f1456.f (x 3 + N.uV46 x) - N.f1456.f (x 3) = N.D ^ 2 * (N.DG4 - N.D023) :=
  ⟨uV46_f012 N, uV46_f015 N, uV46_f023 N, uV46_f035 N, uV46_f124 N, uV46_f234 N, uV46_f346 N, uV46_f356 N,
    uV46_f1456 N⟩

/-- `-phi124 = h2 t DG4 + b2 U5 = P4 D234 + (-b2)(P0 - D234)` (`P4 = b0 h2 - b2 h0`, Carbon `P4`). -/
theorem phi124_id (N : NF29 x) :
    N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023) =
      N.P5 * N.D234 + (-N.b2) * (N.p0346 - N.D234) := by
  dsimp only [DG4, D023, D02, dG4, dG, p0346, D234, P5]; ring

/-- `D234 ≤ P0` and `D234 > 0` give `phi124 < 0` (`phi124 = -(h2 t DG4 + b2 U5)`). -/
theorem phi124_neg (N : NF29 x) (hD : 0 < N.D234) (hle : N.D234 ≤ N.p0346) :
    -(N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023)) < 0 := by
  rw [phi124_id]
  have h1 : 0 < N.P5 * N.D234 := mul_pos (by dsimp only [P5]; linarith [N.hF4]) hD
  have h2 : 0 ≤ (-N.b2) * (N.p0346 - N.D234) := mul_nonneg (by linarith [N.hb2]) (by linarith)
  linarith

/-- `D234 ≥ P0 > 0` gives `phi015 > 0` (`phi015 = P0 P4' + (-a0)(D234 - P0)`, `P4' = a2 h0 - a0 h2 > 0`). -/
theorem phi015_pos (N : NF29 x) (hP : 0 < N.p0346) (hge : N.p0346 ≤ N.D234) :
    0 < N.p0346 * N.P4 + (-N.a0) * (N.D234 - N.p0346) := by
  have h1 : 0 < N.p0346 * N.P4 := mul_pos hP (by dsimp only [P4]; linarith [N.hF5])
  have h2 : 0 ≤ (-N.a0) * (N.D234 - N.p0346) := mul_nonneg (by linarith [N.ha0]) (by linarith)
  linarith

/-- `uV46 ≠ 0` when `U5 = DG4 - D023 > 0` (the `1456` value is `D^2 U5`). -/
theorem uV46_ne_zero (N : NF29 x) (hU5 : 0 < N.DG4 - N.D023) : N.uV46 x ≠ 0 := by
  intro h0
  have h := uV46_f1456 N
  rw [h0, add_zero, sub_self] at h
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have := mul_pos hD2 hU5
  linarith

/-! ## L45-3, L45-4: front-pair identities and rows -/

/-- **L45-3 (`v46_front_pair`)**, vector identity in the `e`-frame:
`(t DG4) x0 + (D0 P0) x4 = (DG4 P0) x1 + (t h0 DG4 + b0 U5) x3 + b0 u`, `U5 = DG4 - D023`. -/
theorem v46_front_pair (N : NF29 x) :
    (N.t * N.DG4) • x 0 + (N.D02 * N.p0346) • x 4 =
      (N.DG4 * N.p0346) • x 1 + (N.t * N.h0 * N.DG4 + N.b0 * (N.DG4 - N.D023)) • x 3 +
        N.b0 • N.uV46 x := by
  dsimp only [uV46, DG4, D023, D02, dG4, dG, p0346, D234]
  nf29_vec N

/-- The weights of `v46_front_pair` have equal sums (`t (1 - h0) DG4 - G4 P0 - b0 U5 = 0`). -/
theorem v46_front_sum (N : NF29 x) :
    N.t * N.DG4 + N.D02 * N.p0346 =
      N.DG4 * N.p0346 + (N.t * N.h0 * N.DG4 + N.b0 * (N.DG4 - N.D023)) := by
  dsimp only [DG4, D023, D02, dG4, dG, p0346]; ring

/-- **L45-4 (`v46_front_pair_II`)**, with the corrected sign of the `u`-term:
`(t DG4) x2 + (D0 D234) x4 = (DG4 D234) x1 + (h2 t DG4 + b2 U5) x3 - (-b2) u`. -/
theorem v46_front_pair_II (N : NF29 x) :
    (N.t * N.DG4) • x 2 + (N.D02 * N.D234) • x 4 =
      (N.DG4 * N.D234) • x 1 + (N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023)) • x 3 -
        (-N.b2) • N.uV46 x := by
  dsimp only [uV46, DG4, D023, D02, dG4, dG, p0346, D234]
  nf29_vec N

theorem v46_front_sum_II (N : NF29 x) :
    N.t * N.DG4 + N.D02 * N.D234 =
      N.DG4 * N.D234 + (N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023)) := by
  dsimp only [DG4, D023, D02, dG4, dG, D234]; ring

/-- Pure order, chamber Ia: if `wa za + wb zb = wc zc + wd zd + W n` with positive weights of equal sums, `W n > 0`,
and the 4-cycle `(za, zc, zb, zd)` has a weak alternating pair, then `zc, zd ≤ za, zb`. -/
theorem front_pair_rows {za zb zc zd wa wb wc wd Wn : ℝ} (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc)
    (hwd : 0 ≤ wd) (hsum : wa + wb = wc + wd) (hWn : 0 < Wn)
    (hid : wa * za + wb * zb = wc * zc + wd * zd + Wn) (h : Alt4 za zc zb zd) :
    zc ≤ za ∧ zd ≤ za ∧ zc ≤ zb ∧ zd ≤ zb := by
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact h
  · exfalso
    rcases le_total zc zd with hcd | hcd
    · have e := congrArg (fun w => w * zc) hsum
      nlinarith [mul_nonneg hwa (sub_nonneg.2 h1), mul_nonneg hwb (sub_nonneg.2 h2),
        mul_nonneg hwd (sub_nonneg.2 hcd)]
    · have e := congrArg (fun w => w * zd) hsum
      nlinarith [mul_nonneg hwa (sub_nonneg.2 h3), mul_nonneg hwb (sub_nonneg.2 h4),
        mul_nonneg hwc (sub_nonneg.2 hcd)]

/-- Pure order, chamber II: `wa za + wb zb + W n = wc zc + wd zd`: the failing 4-cycle `(zc, za, zd, zb)` gives
`za, zb ≤ zc, zd`. -/
theorem front_pair_rows_II {za zb zc zd wa wb wc wd Wn : ℝ} (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc)
    (hwd : 0 ≤ wd) (hsum : wa + wb = wc + wd) (hWn : 0 < Wn)
    (hid : wa * za + wb * zb + Wn = wc * zc + wd * zd) (h : Alt4 zc za zd zb) :
    za ≤ zc ∧ zb ≤ zc ∧ za ≤ zd ∧ zb ≤ zd := by
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact h
  · exfalso
    rcases le_total za zb with hab | hab
    · have e := congrArg (fun w => w * za) hsum
      nlinarith [mul_nonneg hwc (sub_nonneg.2 h1), mul_nonneg hwd (sub_nonneg.2 h3),
        mul_nonneg hwb (sub_nonneg.2 hab)]
    · have e := congrArg (fun w => w * zb) hsum
      nlinarith [mul_nonneg hwc (sub_nonneg.2 h2), mul_nonneg hwd (sub_nonneg.2 h4),
        mul_nonneg hwa (sub_nonneg.2 hab)]

/-- **L45-3 (`v46_rows_Ia`)**, sign-repaired: at `u = (-U5, -D023, 0)` a failing 4-rim `(0, 1, 4, 3)` (`Alt4`) gives
`z1, z3 ≤ z0, z4` (`{0, 4}` is in front of `{1, 3}`).  The hypothesis `D234 ≤ P0 ∧ phi015 > 0` is only the rim
step and is not used. -/
theorem v46_rows_Ia (N : NF29 x) (hb0 : 0 < N.b0) (hP0 : 0 ≤ N.p0346)
    (hU5 : 0 < N.DG4 - N.D023)
    (h : Alt4 ⟪x 0, N.uV46 x⟫ ⟪x 1, N.uV46 x⟫ ⟪x 4, N.uV46 x⟫ ⟪x 3, N.uV46 x⟫) :
    ⟪x 1, N.uV46 x⟫ ≤ ⟪x 0, N.uV46 x⟫ ∧ ⟪x 3, N.uV46 x⟫ ≤ ⟪x 0, N.uV46 x⟫ ∧
      ⟪x 1, N.uV46 x⟫ ≤ ⟪x 4, N.uV46 x⟫ ∧ ⟪x 3, N.uV46 x⟫ ≤ ⟪x 4, N.uV46 x⟫ := by
  have hid := congrArg (fun v => ⟪v, N.uV46 x⟫) (v46_front_pair N)
  simp only [inner_add_left, real_inner_smul_left] at hid
  have hu : 0 < ⟪N.uV46 x, N.uV46 x⟫ := real_inner_self_pos.mpr (uV46_ne_zero N hU5)
  have hDG4 : 0 < N.DG4 := N.hDG4
  have hD0 : 0 < N.D02 := N.hDD
  have hw : 0 ≤ N.t * N.h0 * N.DG4 + N.b0 * (N.DG4 - N.D023) :=
    add_nonneg (mul_pos (mul_pos N.ht N.hh0) hDG4).le (mul_pos hb0 hU5).le
  have hr := front_pair_rows (za := ⟪x 0, N.uV46 x⟫) (zb := ⟪x 4, N.uV46 x⟫) (zc := ⟪x 1, N.uV46 x⟫)
    (zd := ⟪x 3, N.uV46 x⟫) (mul_pos N.ht hDG4).le (mul_nonneg hD0.le hP0) (mul_nonneg hDG4.le hP0) hw
    (v46_front_sum N) (mul_pos hb0 hu) (by linarith [hid]) h
  exact hr

/-- **L45-4 (`v46_rows_II`)**: at `u`, a failing 4-rim `(1, 2, 3, 4)` (`Alt4`) with `phi124 ≤ 0` (`-phi124 ≥ 0`) and
`b2 < 0` gives `z2, z4 ≤ z1, z3`. -/
theorem v46_rows_II (N : NF29 x) (hD234 : 0 ≤ N.D234)
    (hphi : 0 ≤ N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023)) (hU5 : 0 < N.DG4 - N.D023)
    (h : Alt4 ⟪x 1, N.uV46 x⟫ ⟪x 2, N.uV46 x⟫ ⟪x 3, N.uV46 x⟫ ⟪x 4, N.uV46 x⟫) :
    ⟪x 2, N.uV46 x⟫ ≤ ⟪x 1, N.uV46 x⟫ ∧ ⟪x 4, N.uV46 x⟫ ≤ ⟪x 1, N.uV46 x⟫ ∧
      ⟪x 2, N.uV46 x⟫ ≤ ⟪x 3, N.uV46 x⟫ ∧ ⟪x 4, N.uV46 x⟫ ≤ ⟪x 3, N.uV46 x⟫ := by
  have hid := congrArg (fun v => ⟪v, N.uV46 x⟫) (v46_front_pair_II N)
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at hid
  have hu : 0 < ⟪N.uV46 x, N.uV46 x⟫ := real_inner_self_pos.mpr (uV46_ne_zero N hU5)
  have hw : 0 < -N.b2 := by linarith [N.hb2]
  have hDG4 : 0 < N.DG4 := N.hDG4
  have hD0 : 0 < N.D02 := N.hDD
  have hr := front_pair_rows_II (za := ⟪x 2, N.uV46 x⟫) (zb := ⟪x 4, N.uV46 x⟫) (zc := ⟪x 1, N.uV46 x⟫)
    (zd := ⟪x 3, N.uV46 x⟫) (wa := N.t * N.DG4) (wb := N.D02 * N.D234) (wc := N.DG4 * N.D234)
    (wd := N.h2 * N.t * N.DG4 + N.b2 * (N.DG4 - N.D023)) (Wn := -N.b2 * ⟪N.uV46 x, N.uV46 x⟫)
    (mul_pos N.ht hDG4).le (mul_nonneg hD0.le hD234) (mul_nonneg hDG4.le hD234) hphi (v46_front_sum_II N) (mul_pos hw hu)
    (by linarith [hid]) h
  exact hr

end L45U

/-! ## L45-6: the `w34` rows (OPEN: hypothesis only) -/

/-- `Z20w = S (z2 - z0)(w34)`, `w34 = (-1, 1, 0)`. -/
abbrev L42P.Z20w (p : L42P) : ℝ := p.rowv (p.P2 - p.D035) (p.D234 - p.P0) (p.h2 - p.h0) (-1) 1 0

/-- **L45-6** (`W34Rows`, OPEN; NOT proved): on `W-I`, if all four rims at `w34` fail (`allRimsFail`, the weak
failure of `(0,2,3,6,5)`, `(0,2,3,4,6,5)`, `(0,2,4,3,6,5)`, `(0,2,4,6,5)`), then `z5(w34) ≥ 0` and
`S (z2 - z0)(w34) ≥ 0`.  Checked only by an exact arrangement census (A45-REFEREE F7), no proof; branches B, C and
the `R204 / M15*` rows depend on it.  A named hypothesis, to be passed where needed. -/
def W34Rows (p : L42P) (allRimsFail : Prop) : Prop :=
  allRimsFail → 0 ≤ p.W34_56 ∧ 0 ≤ p.Z20w

end Minimality.NF29
