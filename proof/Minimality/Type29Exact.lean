module

public import Minimality.Type29LeavesA16
public import Minimality.GenQuad

@[expose] public section

/-!
# Type 29: exact-region leaves in clause form (GEN29-REVIEW R2, R3)

Each leaf is a `LexAny29` leaf on the K1a dominant cell whose region is EXACT on its rim: the front diagonal of
every 4-subset (`FrontDet`, four `det3` signs, a shape fact) plus the not-`M_Q` clause of the other pairing
(`GenQuad.lexAny_of_clauses`, `GenQuad.clauses_five`):
1. `NF29.lexAny29_U023Qx` / `lexAny29_U023Qx8`: rim `![0, 2, 4, 6, 5]` at `u23Q`, `d1 = x 3 - x 6` (supersedes
   `lexAny29_U023Qp`; 268 + 8 shapes by the sign of chi(0256)); core `lexAny29_U023Qx_clauses`;
2. `NF29.lexAny29_W14x5` / `lexAny29_W14x5'`: rim `![1, 2, 3, 6, 5]` at `x 1 - x 4` for all `1 ≤ t` (supersedes
   `lexAny29_W14t1`; two sides of chi(1236));
3. `NF29.lexAny29_F012F1456`: line F012xF1456 at `bLine = h2 (x0 - x1) - h0 (x2 - x1)`, rim `![1, 2, 3, 6, 5]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21 Minimality.H29
open Minimality.GenQuad (FrontDet)

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-! ## U023Q'-exact -/
local macro "u023x_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG, dG4, D02, DG4, DG5, D023, E35, P4, P5, D234,
      f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def u023x_c : ZMod 5 → Fin 7 := ![0, 2, 4, 6, 5]
private def u023x_U : Finset (Fin 9) := {2, 3, 6, 7, 8}
private def u023x_Dn : Finset (Fin 9) := {0, 1, 4, 5}

private theorem u023x_c_inj : Function.Injective u023x_c := by decide
private theorem u023x_cyc : S0xCycUD s0x_S29 u023x_c u023x_U u023x_Dn := by decide

/-- Core: the facet part of `U023Q` with the ten rim clauses as hypotheses (`hA`/`hB` of `GenQuad.clauses_five`
at `p = ![x 0, x 2, x 4, x 6, x 5]`). -/
theorem lexAny29_U023Qx_clauses (N : NF29 x)
    (hdG : N.dG < 0) (hdG4 : 0 < N.dG4) (hh0 : N.h0 < 1) (hE35 : N.E35 < 0)
    (hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4) (hh2 : 1 ≤ N.h2)
    (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023)
    (hA0123 : GenQuad.LexClause (x 2) (x 6) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0123 : GenQuad.LexClause (x 0) (x 4) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hA0124 : GenQuad.LexClause (x 2) (x 5) (x 0) (x 4) (N.u23Q x) (x 3 - x 6) 0)
    (hB0124 : GenQuad.LexClause (x 0) (x 4) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0134 : GenQuad.LexClause (x 2) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0134 : GenQuad.LexClause (x 0) (x 6) (x 2) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA0234 : GenQuad.LexClause (x 4) (x 5) (x 0) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB0234 : GenQuad.LexClause (x 0) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0)
    (hA1234 : GenQuad.LexClause (x 4) (x 5) (x 2) (x 6) (N.u23Q x) (x 3 - x 6) 0)
    (hB1234 : GenQuad.LexClause (x 2) (x 6) (x 4) (x 5) (N.u23Q x) (x 3 - x 6) 0) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := u023x_c
  let U := u023x_U
  let Dn := u023x_Dn
  let b : ℝ³ := N.u23Q x
  let d1 : ℝ³ := x 3 - x 6
  have hc_inj : Function.Injective c := u023x_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := u023x_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := by
    intro t
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 6) := fun t => (F.hN t (x 3) (x 6)).symm
  have e3_023 : N.f023.f (x 3) - N.f023.f (x 6) = N.D023 * N.D ^ 2 := by u023x_fac_val N
  have e3_234 : N.f234.f (x 3) - N.f234.f (x 6) = N.D234 * N.D ^ 2 := by u023x_fac_val N
  have e3_1456 : N.f1456.f (x 3) - N.f1456.f (x 6) = -N.D ^ 2 := by u023x_fac_val N
  have hD023 : 0 < N.D023 := by have := N.d023; exact this
  have hD234 : 0 < N.D234 := by have := N.d234; exact this
  have hDG4 : 0 < N.DG4 := by have := N.hDG4; exact this
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    rw [hnb t, hnd t]
    fin_cases t
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · refine Or.inr ⟨?_, Or.inl ?_⟩
      · change N.f023.f (x 3 + N.u23Q x) - N.f023.f (x 3) = 0
        exact f023_u23Q N
      · change 0 < N.f023.f (x 3) - N.f023.f (x 6)
        rw [e3_023]; exact mul_pos hD023 hD2
    · refine Or.inl ?_
      change 0 < N.f035.f (x 3 + N.u23Q x) - N.f035.f (x 3)
      rw [f035_u23Q N]
      exact mul_pos (mul_pos_of_neg_of_neg (by linarith) hE35) hD2
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · rcases eq_or_lt_of_le hh2 with h | h
      · refine Or.inr ⟨?_, Or.inl ?_⟩
        · change N.f234.f (x 3 + N.u23Q x) - N.f234.f (x 3) = 0
          rw [f234_u23Q N, ← h]; ring
        · change 0 < N.f234.f (x 3) - N.f234.f (x 6)
          rw [e3_234]; exact mul_pos hD234 hD2
      · refine Or.inl ?_
        change 0 < N.f234.f (x 3 + N.u23Q x) - N.f234.f (x 3)
        rw [f234_u23Q N]
        have : 0 < (N.h2 - 1) * N.DG4 * N.D ^ 2 := mul_pos (mul_pos (sub_pos.mpr h) hDG4) hD2
        linarith
    · refine Or.inl ?_
      change 0 < N.f346.f (x 3 + N.u23Q x) - N.f346.f (x 3)
      rw [f346_u23Q N]; exact mul_pos h5 hD2
    · refine Or.inl ?_
      change 0 < N.f356.f (x 3 + N.u23Q x) - N.f356.f (x 3)
      rw [f356_u23Q N]; exact mul_pos h4 hD2
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, 0⟫) := by
    intro t ht_mem
    rw [hnb t, hnd t]
    fin_cases t
    · refine Or.inl ?_
      change 0 < -(N.f012.f (x 3 + N.u23Q x) - N.f012.f (x 3))
      rw [f012_u23Q N]
      have : 0 < ((-N.dG) * N.P5 + N.dG4 * N.P4) * N.D ^ 2 := mul_pos hK hD2
      linarith
    · refine Or.inl ?_
      change 0 < -(N.f015.f (x 3 + N.u23Q x) - N.f015.f (x 3))
      rw [f015_u23Q N]
      have : 0 < (-N.dG) * N.h0 * N.D ^ 2 := mul_pos (mul_pos (neg_pos.mpr hdG) N.hh0) hD2
      linarith
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · refine Or.inl ?_
      change 0 < -(N.f124.f (x 3 + N.u23Q x) - N.f124.f (x 3))
      rw [f124_u23Q N]
      have : 0 < N.dG4 * N.h2 * N.D ^ 2 := mul_pos (mul_pos hdG4 N.hh2) hD2
      linarith
    · refine Or.inr ⟨?_, Or.inl ?_⟩
      · change -(N.f1456.f (x 3 + N.u23Q x) - N.f1456.f (x 3)) = 0
        rw [f1456_u23Q N, neg_zero]
      · change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 6))
        rw [e3_1456, neg_neg]; exact hD2
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
  have hcl := GenQuad.clauses_five (p := fun i => x (c i)) (b := b) (d1 := d1) (d2 := 0)
    hA0123 hB0123 hA0124 hB0124 hA0134 hB0134 hA0234 hB0234 hA1234 hB1234
  exact ⟨5, inferInstance, c, U, Dn, b, d1, 0, by norm_num, hc_inj, hcyc, hU, hD,
    GenQuad.robUniLex_of_clauses (p := fun i => x (c i)) hcl⟩

/-- **U023Q'-exact**, 268 shapes (front table `26 25 25 06 26`): rim `(0 2 4 6 5)` at `b = u23Q`, `d1 = x 3 - x 6`;
five `FrontOf` facts, and the five not-M clauses of the other diagonals, `z i = ⟪x i - x 6, u23Q⟫`. -/
theorem lexAny29_U023Qx (N : NF29 x)
    (hdG : N.dG < 0) (hdG4 : 0 < N.dG4) (hh0 : N.h0 < 1) (hE35 : N.E35 < 0)
    (hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4) (hh2 : 1 ≤ N.h2)
    (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023)
    (f0246 : GenQuad.FrontOf (x 2) (x 6) (x 0) (x 4) (N.u23Q x))
    (f0245 : GenQuad.FrontOf (x 2) (x 5) (x 0) (x 4) (N.u23Q x))
    (f0265 : GenQuad.FrontOf (x 2) (x 5) (x 0) (x 6) (N.u23Q x))
    (f0465 : GenQuad.FrontOf (x 0) (x 6) (x 4) (x 5) (N.u23Q x))
    (f2465 : GenQuad.FrontOf (x 2) (x 6) (x 4) (x 5) (N.u23Q x))
    (m0246 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0))
    (m0245 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫ ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫))
    (m0265 : ¬ (0 ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ 0 ≤ ⟪x 5 - x 6, N.u23Q x⟫ ∧
                ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫))
    (m0465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0))
    (m2465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  have hb : N.u23Q x ≠ 0 := by
    intro h0
    have h := f012_u23Q N
    rw [h0, add_zero, sub_self] at h
    have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
    have : 0 < ((-N.dG) * N.P5 + N.dG4 * N.P4) * N.D ^ 2 := mul_pos hK hD2
    linarith
  refine lexAny29_U023Qx_clauses N hdG hdG4 hh0 hE35 hK hh2 h4 h5 ?A0123 ?B0123 ?A0124 ?B0124 ?A0134 ?B0134 ?A0234 ?B0234 ?A1234 ?B1234
  case A0123 => exact GenQuad.lexClause_of_frontOf hb f0246
  case B0123 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0246; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case A0124 => exact GenQuad.lexClause_of_frontOf hb f0245
  case B0124 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0245; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case A0134 => exact GenQuad.lexClause_of_frontOf hb f0265
  case B0134 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0265; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case A0234 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0465; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case B0234 => exact GenQuad.lexClause_of_frontOf hb f0465
  case A1234 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m2465; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case B1234 => exact GenQuad.lexClause_of_frontOf hb f2465

/-- Variant for the 8 shapes with `chi(0256)` flipped (front table `26 25 06 06 26`): only the `{0265}` front and
clause change. -/
theorem lexAny29_U023Qx8 (N : NF29 x)
    (hdG : N.dG < 0) (hdG4 : 0 < N.dG4) (hh0 : N.h0 < 1) (hE35 : N.E35 < 0)
    (hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4) (hh2 : 1 ≤ N.h2)
    (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023)
    (f0246 : GenQuad.FrontOf (x 2) (x 6) (x 0) (x 4) (N.u23Q x))
    (f0245 : GenQuad.FrontOf (x 2) (x 5) (x 0) (x 4) (N.u23Q x))
    (f0265 : GenQuad.FrontOf (x 0) (x 6) (x 2) (x 5) (N.u23Q x))
    (f0465 : GenQuad.FrontOf (x 0) (x 6) (x 4) (x 5) (N.u23Q x))
    (f2465 : GenQuad.FrontOf (x 2) (x 6) (x 4) (x 5) (N.u23Q x))
    (m0246 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0))
    (m0245 : ¬ (⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 0 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫ ∧
                ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 5 - x 6, N.u23Q x⟫))
    (m0265 : ¬ (⟪x 2 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 2 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0))
    (m0465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 0 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0))
    (m2465 : ¬ (⟪x 4 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 4 - x 6, N.u23Q x⟫ ≤ 0 ∧
                ⟪x 5 - x 6, N.u23Q x⟫ ≤ ⟪x 2 - x 6, N.u23Q x⟫ ∧ ⟪x 5 - x 6, N.u23Q x⟫ ≤ 0)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  have hb : N.u23Q x ≠ 0 := by
    intro h0
    have h := f012_u23Q N
    rw [h0, add_zero, sub_self] at h
    have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
    have : 0 < ((-N.dG) * N.P5 + N.dG4 * N.P4) * N.D ^ 2 := mul_pos hK hD2
    linarith
  refine lexAny29_U023Qx_clauses N hdG hdG4 hh0 hE35 hK hh2 h4 h5 ?A0123 ?B0123 ?A0124 ?B0124 ?A0134 ?B0134 ?A0234 ?B0234 ?A1234 ?B1234
  case A0123 => exact GenQuad.lexClause_of_frontOf hb f0246
  case B0123 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0246; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case A0124 => exact GenQuad.lexClause_of_frontOf hb f0245
  case B0124 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0245; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case A0134 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0265; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case B0134 => exact GenQuad.lexClause_of_frontOf hb f0265
  case A0234 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m0465; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case B0234 => exact GenQuad.lexClause_of_frontOf hb f0465
  case A1234 => exact GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩; apply m2465; simp only [inner_sub_left]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  case B1234 => exact GenQuad.lexClause_of_frontOf hb f2465

/-! ## W14-5 -/
local macro "w14x5_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG4, P5, f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def w14x5_c : ZMod 5 → Fin 7 := ![1, 2, 3, 6, 5]
private def w14x5_U : Finset (Fin 9) := {0, 1, 2, 3, 8}
private def w14x5_Dn : Finset (Fin 9) := {4, 5, 6, 7}

private theorem w14x5_c_inj : Function.Injective w14x5_c := by decide
private theorem w14x5_cyc : S0xCycUD s0x_S29 w14x5_c w14x5_U w14x5_Dn := by decide


/-- Shifting all four depths by `⟪w, b⟫` does not change `M` (here `q = w`, depth `0`). -/
private theorem w14x5_shiftM {p r s w b : ℝ³}
    (h : ¬ (⟪p - w, b⟫ ≤ ⟪r - w, b⟫ ∧ ⟪p - w, b⟫ ≤ ⟪s - w, b⟫ ∧
            (0 : ℝ) ≤ ⟪r - w, b⟫ ∧ (0 : ℝ) ≤ ⟪s - w, b⟫)) :
    ¬ (⟪p, b⟫ ≤ ⟪r, b⟫ ∧ ⟪p, b⟫ ≤ ⟪s, b⟫ ∧ ⟪w, b⟫ ≤ ⟪r, b⟫ ∧ ⟪w, b⟫ ≤ ⟪s, b⟫) := by
  rintro ⟨h1, h2, h3, h4⟩
  apply h
  simp only [inner_sub_left]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Shifting all four depths by `⟪w, b⟫` does not change `M`. -/
private theorem w14x5_shiftM4 {p q r s w b : ℝ³}
    (h : ¬ (⟪p - w, b⟫ ≤ ⟪r - w, b⟫ ∧ ⟪p - w, b⟫ ≤ ⟪s - w, b⟫ ∧
            ⟪q - w, b⟫ ≤ ⟪r - w, b⟫ ∧ ⟪q - w, b⟫ ≤ ⟪s - w, b⟫)) :
    ¬ (⟪p, b⟫ ≤ ⟪r, b⟫ ∧ ⟪p, b⟫ ≤ ⟪s, b⟫ ∧ ⟪q, b⟫ ≤ ⟪r, b⟫ ∧ ⟪q, b⟫ ≤ ⟪s, b⟫) := by
  rintro ⟨h1, h2, h3, h4⟩
  apply h
  simp only [inner_sub_left]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Core: facet signs at `b = x 1 - x 4`, the four fronts `25, 25, 35, 35`, the four not-`M` regions, and the
two clauses of the 4-subset `{1,2,3,6}` (rim positions `0123`). -/
private theorem w14x5_core (N : NF29 x)
    (ht : 1 ≤ N.t) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hF1235 : FrontDet (x 2) (x 5) (x 1) (x 3) (x 1 - x 4))
    (hF1265 : FrontDet (x 2) (x 5) (x 1) (x 6) (x 1 - x 4))
    (hF1365 : FrontDet (x 3) (x 5) (x 1) (x 6) (x 1 - x 4))
    (hF2365 : FrontDet (x 3) (x 5) (x 2) (x 6) (x 1 - x 4))
    (hM1235 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM1265 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM1365 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM2365 : ¬ (⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ ⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hA0123 : GenQuad.LexClause (x 2) (x 6) (x 1) (x 3) (x 1 - x 4) (x 3 - x 4) 0)
    (hB0123 : GenQuad.LexClause (x 1) (x 3) (x 2) (x 6) (x 1 - x 4) (x 3 - x 4) 0) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := w14x5_c
  let U := w14x5_U
  let Dn := w14x5_Dn
  let b : ℝ³ := x 1 - x 4
  let d1 : ℝ³ := x 3 - x 4
  have hc_inj : Function.Injective c := w14x5_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := w14x5_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 4) := (F.hN t (x 3) (x 4)).symm
    rw [hnb, hnd1]
    fin_cases t
    · refine Or.inl ?_
      have hv : N.f012.f (x 1) - N.f012.f (x 4) = N.P5 * N.D ^ 2 := by w14x5_fac_val N
      change 0 < N.f012.f (x 1) - N.f012.f (x 4)
      rw [hv]
      exact mul_pos (by dsimp [P5]; linarith [N.hF4]) hD2
    · refine Or.inl ?_
      have hv : N.f015.f (x 1) - N.f015.f (x 4) = N.h0 * N.D ^ 2 := by w14x5_fac_val N
      change 0 < N.f015.f (x 1) - N.f015.f (x 4)
      rw [hv]
      exact mul_pos N.hh0 hD2
    · refine Or.inl ?_
      have hv : N.f023.f (x 1) - N.f023.f (x 4) = N.dG4 * N.D ^ 2 := by w14x5_fac_val N
      change 0 < N.f023.f (x 1) - N.f023.f (x 4)
      rw [hv]
      exact mul_pos hdG4 hD2
    · refine Or.inl ?_
      have hv : N.f035.f (x 1) - N.f035.f (x 4) = (1 - N.b0 - N.h0) * N.D ^ 2 := by
        w14x5_fac_val N
      change 0 < N.f035.f (x 1) - N.f035.f (x 4)
      rw [hv]
      exact mul_pos hA hD2
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · have hv0 : N.f356.f (x 1) - N.f356.f (x 4) = (N.t - 1) * N.D ^ 2 := by w14x5_fac_val N
      have hd1v : N.f356.f (x 3) - N.f356.f (x 4) = (N.t - 1 + N.s) * N.D ^ 2 := by
        w14x5_fac_val N
      rcases eq_or_lt_of_le ht with h1 | h1
      · have hb0 : N.f356.f (x 1) - N.f356.f (x 4) = 0 := by
          rw [hv0, ← h1]; ring
        refine Or.inr ⟨hb0, Or.inl ?_⟩
        change 0 < N.f356.f (x 3) - N.f356.f (x 4)
        rw [hd1v, ← h1]
        exact mul_pos (by linarith [N.hs]) hD2
      · refine Or.inl ?_
        change 0 < N.f356.f (x 1) - N.f356.f (x 4)
        rw [hv0]
        exact mul_pos (by linarith) hD2
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, 0⟫) := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 4) := (F.hN t (x 3) (x 4)).symm
    rw [hnb, hnd1]
    fin_cases t
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · have hb0 : N.f124.f (x 1) - N.f124.f (x 4) = 0 := by w14x5_fac_val N
      have hd1v : N.f124.f (x 3) - N.f124.f (x 4) = N.b2 * N.D ^ 2 := by w14x5_fac_val N
      refine Or.inr ⟨by change -(N.f124.f (x 1) - N.f124.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f124.f (x 3) - N.f124.f (x 4))
      rw [hd1v]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · have hb0 : N.f1456.f (x 1) - N.f1456.f (x 4) = 0 := by w14x5_fac_val N
      have hd1v : N.f1456.f (x 3) - N.f1456.f (x 4) = -N.D ^ 2 := by w14x5_fac_val N
      refine Or.inr ⟨by change -(N.f1456.f (x 1) - N.f1456.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 4))
      rw [hd1v, neg_neg]
      exact hD2
    · refine Or.inl ?_
      have hv : N.f234.f (x 1) - N.f234.f (x 4) = N.b2 * N.D ^ 2 := by w14x5_fac_val N
      change 0 < -(N.f234.f (x 1) - N.f234.f (x 4))
      rw [hv]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · refine Or.inl ?_
      have hv : N.f346.f (x 1) - N.f346.f (x 4) = -N.t * N.D ^ 2 := by w14x5_fac_val N
      change 0 < -(N.f346.f (x 1) - N.f346.f (x 4))
      rw [hv, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.ht hD2
    · exact absurd ht_mem (by decide)
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
  have hnM : ∀ {p q r s : ℝ³}, ¬ (⟪p, b⟫ ≤ ⟪r, b⟫ ∧ ⟪p, b⟫ ≤ ⟪s, b⟫ ∧ ⟪q, b⟫ ≤ ⟪r, b⟫ ∧
      ⟪q, b⟫ ≤ ⟪s, b⟫) → GenQuad.LexClause p q r s b d1 0 := fun h => GenQuad.lexClause_of_notM h
  exact GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) hc_inj hcyc b d1 0 hU hD
    (GenQuad.clauses_five (p := fun i => x (c i)) hA0123 hB0123
      (GenQuad.lexClause_of_frontOf hb_ne hF1235.frontOf)
      (hnM (w14x5_shiftM4 hM1235))
      (GenQuad.lexClause_of_frontOf hb_ne hF1265.frontOf)
      (hnM (w14x5_shiftM hM1265))
      (GenQuad.lexClause_of_frontOf hb_ne hF1365.frontOf)
      (hnM (w14x5_shiftM hM1365))
      (GenQuad.lexClause_of_frontOf hb_ne hF2365.frontOf)
      (hnM (w14x5_shiftM hM2365)))

/-- **W14-5** (GEN29-REVIEW R2), `chi(1236)` side with front pair `13`: 5-rim `![1, 2, 3, 6, 5]` at
`b = x 1 - x 4` (line `F124 x F1456`, tilt `+-- / -++`), for all `1 ≤ t`. The five fronts are `13, 25, 25, 35, 35`;
the region is the five not-`M` clauses with depths `z i = ⟪x i - x 6, b⟫` (valleys `2 6`, `1 3`, `1 6`, `1 6`, `2 6`). -/
theorem lexAny29_W14x5 (N : NF29 x)
    (ht : 1 ≤ N.t) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hF1235 : FrontDet (x 2) (x 5) (x 1) (x 3) (x 1 - x 4))
    (hF1265 : FrontDet (x 2) (x 5) (x 1) (x 6) (x 1 - x 4))
    (hF1365 : FrontDet (x 3) (x 5) (x 1) (x 6) (x 1 - x 4))
    (hF2365 : FrontDet (x 3) (x 5) (x 2) (x 6) (x 1 - x 4))
    (hM1235 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM1265 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM1365 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM2365 : ¬ (⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ ⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hF1236 : FrontDet (x 1) (x 3) (x 2) (x 6) (x 1 - x 4))
    (hM1236 : ¬ (⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 1 - x 6, x 1 - x 4⟫ ∧ ⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 1 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  w14x5_core N ht hdG4 hA hF1235 hF1265 hF1365 hF2365 hM1235 hM1265 hM1365 hM2365
    (GenQuad.lexClause_of_notM (w14x5_shiftM hM1236))
    (GenQuad.lexClause_of_frontOf (sub_ne_zero.mpr (N.inj.ne (by decide))) hF1236.frontOf)

/-- **W14-5**, the other `chi(1236)` side: front pair `26`, clause region valleys `1 3`. -/
theorem lexAny29_W14x5' (N : NF29 x)
    (ht : 1 ≤ N.t) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hF1235 : FrontDet (x 2) (x 5) (x 1) (x 3) (x 1 - x 4))
    (hF1265 : FrontDet (x 2) (x 5) (x 1) (x 6) (x 1 - x 4))
    (hF1365 : FrontDet (x 3) (x 5) (x 1) (x 6) (x 1 - x 4))
    (hF2365 : FrontDet (x 3) (x 5) (x 2) (x 6) (x 1 - x 4))
    (hM1235 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM1265 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM1365 : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hM2365 : ¬ (⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ ⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫))
    (hF2613 : FrontDet (x 2) (x 6) (x 1) (x 3) (x 1 - x 4))
    (hM1236' : ¬ (⟪x 1 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 1 - x 6, x 1 - x 4⟫ ≤ (0 : ℝ) ∧
        ⟪x 3 - x 6, x 1 - x 4⟫ ≤ ⟪x 2 - x 6, x 1 - x 4⟫ ∧ ⟪x 3 - x 6, x 1 - x 4⟫ ≤ (0 : ℝ))) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  w14x5_core N ht hdG4 hA hF1235 hF1265 hF1365 hF2365 hM1235 hM1265 hM1365 hM2365
    (GenQuad.lexClause_of_frontOf (sub_ne_zero.mpr (N.inj.ne (by decide))) hF2613.frontOf)
    (GenQuad.lexClause_of_notM (by
      rintro ⟨h1, h2, h3, h4⟩
      apply hM1236'
      simp only [inner_sub_left] at *
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith))

/-! ## F012xF1456 -/
/-- The crossing view of facets `012` and `1456`: the direction of the line where the two facet planes
meet.  `h2 (x0 - x1) - h0 (x2 - x1)` lies in the plane of `0 1 2` (it is a combination of two edges of that facet)
and in the plane `1456` (both `x0` and `x2` have heights `-h0`, `-h2`). -/
noncomputable def bLine (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  N.h2 • (x 0 - x 1) - N.h0 • (x 2 - x 1)

/-- Values of the facets `035`, `234`, `346`, `356` at `bLine` (divided by `D²`). -/
noncomputable def v035 (N : NF29 x) : ℝ :=
  N.h0 * N.a2 * (1 - N.h0 - N.b0) - N.a0 * N.h2 * (1 - N.h0) + N.a0 * N.h0 * N.b2
noncomputable def v234 (N : NF29 x) : ℝ :=
  N.h0 * N.b2 * (1 - N.h2) - N.b0 * N.h2 * (1 - N.h2) + (N.b0 * N.a2 - N.a0 * N.b2) * N.h2
noncomputable def v346 (N : NF29 x) : ℝ :=
  N.h0 * N.b2 * (N.s - 1) - N.h0 * N.a2 * N.t + N.b0 * N.h2 * (1 - N.s) + N.a0 * N.h2 * N.t
noncomputable def v356 (N : NF29 x) : ℝ :=
  -N.h0 * N.b2 * N.s - N.h0 * N.a2 * (1 - N.t) + N.b0 * N.h2 * N.s + N.a0 * N.h2 * (1 - N.t)


local macro "f012_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [P4, P5, D02, v035, v234, v346, v356, f012, f015, f023, f035, f124, f1456, f234, f346, f356,
      Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def f012_c : ZMod 5 → Fin 7 := ![1, 2, 3, 6, 5]
private def f012_U : Finset (Fin 9) := {0, 1, 2, 3, 8}
private def f012_Dn : Finset (Fin 9) := {4, 5, 6, 7}

private theorem f012_c_inj : Function.Injective f012_c := by decide
private theorem f012_cyc : S0xCycUD s0x_S29 f012_c f012_U f012_Dn := by decide

theorem lexAny29_F012F1456 (N : NF29 x)
    (hh : N.h0 < N.h2) (h035 : 0 < N.v035) (h234 : N.v234 < 0) (h346 : N.v346 < 0) (h356 : 0 < N.v356)
    (hF0123 : (FrontDet (x 2) (x 6) (x 1) (x 3) (N.bLine x) ∧
        ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 6, N.bLine x⟫ ∧
           ⟪x 3, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 3, N.bLine x⟫ ≤ ⟪x 6, N.bLine x⟫)) ∨
      (FrontDet (x 1) (x 3) (x 2) (x 6) (N.bLine x) ∧
        ¬ (⟪x 2, N.bLine x⟫ ≤ ⟪x 1, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧
           ⟪x 6, N.bLine x⟫ ≤ ⟪x 1, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫)))
    (hF0124 : FrontDet (x 2) (x 5) (x 1) (x 3) (N.bLine x))
    (hM0124 : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 3, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 3, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0134 : FrontDet (x 2) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0134 : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 6, N.bLine x⟫ ≤ ⟪x 2, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF0234 : FrontDet (x 3) (x 5) (x 1) (x 6) (N.bLine x))
    (hM0234 : ¬ (⟪x 1, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 1, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫))
    (hF1234 : FrontDet (x 3) (x 5) (x 2) (x 6) (N.bLine x))
    (hM1234 : ¬ (⟪x 2, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 2, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫ ∧
                 ⟪x 6, N.bLine x⟫ ≤ ⟪x 3, N.bLine x⟫ ∧ ⟪x 6, N.bLine x⟫ ≤ ⟪x 5, N.bLine x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := f012_c
  let U := f012_U
  let Dn := f012_Dn
  let b : ℝ³ := N.bLine x
  let d1 : ℝ³ := x 1 - x 4
  let d2 : ℝ³ := x 3 - x 1
  have hc_inj : Function.Injective c := f012_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := f012_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hnb : ∀ t, ⟪F.N t, b⟫ = N.h2 * (F.f t (x 0) - F.f t (x 1)) - N.h0 * (F.f t (x 2) - F.f t (x 1)) := by
    intro t
    dsimp only [b, bLine]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, (F.hN t (x 0) (x 1)).symm,
      (F.hN t (x 2) (x 1)).symm]
  have hd1 : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 1) - F.f t (x 4) := fun t => (F.hN t (x 1) (x 4)).symm
  have hd2 : ∀ t, ⟪F.N t, d2⟫ = F.f t (x 3) - F.f t (x 1) := fun t => (F.hN t (x 3) (x 1)).symm
  have hP4 : 0 < N.P4 := by dsimp only [P4]; linarith [N.hF5]
  have hP5 : 0 < N.P5 := by dsimp only [P5]; linarith [N.hF4]
  have hD02 : 0 < N.D02 := by dsimp only [D02]; exact N.hDD
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫ := by
    intro t ht_mem
    rw [hnb t, hd1 t]
    fin_cases t
    · have hb0 : N.h2 * (N.f012.f (x 0) - N.f012.f (x 1)) - N.h0 * (N.f012.f (x 2) - N.f012.f (x 1)) = 0 := by
        f012_fac_val N
      have hd1v : N.f012.f (x 1) - N.f012.f (x 4) = N.P5 * N.D ^ 2 := by f012_fac_val N
      refine Or.inr ⟨hb0, Or.inl ?_⟩
      change 0 < N.f012.f (x 1) - N.f012.f (x 4)
      rw [hd1v]; exact mul_pos hP5 hD2
    · refine Or.inl ?_
      have hv : N.h2 * (N.f015.f (x 0) - N.f015.f (x 1)) - N.h0 * (N.f015.f (x 2) - N.f015.f (x 1)) =
          N.h0 * N.P4 * N.D ^ 2 := by f012_fac_val N
      change 0 < N.h2 * (N.f015.f (x 0) - N.f015.f (x 1)) - N.h0 * (N.f015.f (x 2) - N.f015.f (x 1))
      rw [hv]; exact mul_pos (mul_pos N.hh0 hP4) hD2
    · refine Or.inl ?_
      have hv : N.h2 * (N.f023.f (x 0) - N.f023.f (x 1)) - N.h0 * (N.f023.f (x 2) - N.f023.f (x 1)) =
          (N.h2 - N.h0) * N.D02 * N.D ^ 2 := by f012_fac_val N
      change 0 < N.h2 * (N.f023.f (x 0) - N.f023.f (x 1)) - N.h0 * (N.f023.f (x 2) - N.f023.f (x 1))
      rw [hv]; exact mul_pos (mul_pos (sub_pos.mpr hh) hD02) hD2
    · refine Or.inl ?_
      have hv : N.h2 * (N.f035.f (x 0) - N.f035.f (x 1)) - N.h0 * (N.f035.f (x 2) - N.f035.f (x 1)) =
          N.v035 * N.D ^ 2 := by f012_fac_val N
      change 0 < N.h2 * (N.f035.f (x 0) - N.f035.f (x 1)) - N.h0 * (N.f035.f (x 2) - N.f035.f (x 1))
      rw [hv]; exact mul_pos h035 hD2
    all_goals try exact absurd ht_mem (by decide)
    · refine Or.inl ?_
      have hv : N.h2 * (N.f356.f (x 0) - N.f356.f (x 1)) - N.h0 * (N.f356.f (x 2) - N.f356.f (x 1)) =
          N.v356 * N.D ^ 2 := by f012_fac_val N
      change 0 < N.h2 * (N.f356.f (x 0) - N.f356.f (x 1)) - N.h0 * (N.f356.f (x 2) - N.f356.f (x 1))
      rw [hv]; exact mul_pos h356 hD2
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫) := by
    intro t ht_mem
    rw [hnb t, hd1 t, hd2 t]
    fin_cases t
    all_goals try exact absurd ht_mem (by decide)
    · refine Or.inl ?_
      have hv : N.h2 * (N.f124.f (x 0) - N.f124.f (x 1)) - N.h0 * (N.f124.f (x 2) - N.f124.f (x 1)) =
          -(N.h2 * N.P5) * N.D ^ 2 := by f012_fac_val N
      change 0 < -(N.h2 * (N.f124.f (x 0) - N.f124.f (x 1)) - N.h0 * (N.f124.f (x 2) - N.f124.f (x 1)))
      rw [hv]
      have : 0 < N.h2 * N.P5 * N.D ^ 2 := mul_pos (mul_pos N.hh2 hP5) hD2
      linarith
    · have hb0 : N.h2 * (N.f1456.f (x 0) - N.f1456.f (x 1)) - N.h0 * (N.f1456.f (x 2) - N.f1456.f (x 1)) = 0 := by
        f012_fac_val N
      have hd1v : N.f1456.f (x 1) - N.f1456.f (x 4) = 0 := by f012_fac_val N
      have hd2v : N.f1456.f (x 3) - N.f1456.f (x 1) = -N.D ^ 2 := by f012_fac_val N
      have e0 : -(N.h2 * (N.f1456.f (x 0) - N.f1456.f (x 1)) - N.h0 * (N.f1456.f (x 2) - N.f1456.f (x 1))) = 0 := by
        rw [hb0, neg_zero]
      have e1 : -(N.f1456.f (x 1) - N.f1456.f (x 4)) = 0 := by rw [hd1v, neg_zero]
      refine Or.inr ⟨e0, Or.inr ⟨e1, ?_⟩⟩
      change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 1))
      rw [hd2v, neg_neg]; exact hD2
    · refine Or.inl ?_
      have hv : N.h2 * (N.f234.f (x 0) - N.f234.f (x 1)) - N.h0 * (N.f234.f (x 2) - N.f234.f (x 1)) =
          N.v234 * N.D ^ 2 := by f012_fac_val N
      change 0 < -(N.h2 * (N.f234.f (x 0) - N.f234.f (x 1)) - N.h0 * (N.f234.f (x 2) - N.f234.f (x 1)))
      rw [hv]
      have : N.v234 * N.D ^ 2 < 0 := mul_neg_of_neg_of_pos h234 hD2
      linarith
    · refine Or.inl ?_
      have hv : N.h2 * (N.f346.f (x 0) - N.f346.f (x 1)) - N.h0 * (N.f346.f (x 2) - N.f346.f (x 1)) =
          N.v346 * N.D ^ 2 := by f012_fac_val N
      change 0 < -(N.h2 * (N.f346.f (x 0) - N.f346.f (x 1)) - N.h0 * (N.f346.f (x 2) - N.f346.f (x 1)))
      rw [hv]
      have : N.v346 * N.D ^ 2 < 0 := mul_neg_of_neg_of_pos h346 hD2
      linarith
  have hb_ne : b ≠ 0 := by
    intro h0
    have hv : N.h2 * (N.f015.f (x 0) - N.f015.f (x 1)) - N.h0 * (N.f015.f (x 2) - N.f015.f (x 1)) =
        N.h0 * N.P4 * N.D ^ 2 := by f012_fac_val N
    have h1 := hnb 1
    have h2 : ⟪F.N 1, b⟫ = 0 := by rw [h0, inner_zero_right]
    have h3 : 0 < N.h0 * N.P4 * N.D ^ 2 := mul_pos (mul_pos N.hh0 hP4) hD2
    rw [h2] at h1
    change 0 = N.h2 * (N.f015.f (x 0) - N.f015.f (x 1)) - N.h0 * (N.f015.f (x 2) - N.f015.f (x 1)) at h1
    rw [hv] at h1
    linarith
  have cl : ∀ {p q r s : ℝ³}, FrontDet p q r s b → GenQuad.LexClause p q r s b d1 d2 := fun h =>
    GenQuad.lexClause_of_frontOf hb_ne (FrontDet.frontOf h)
  have cn : ∀ {p q r s : ℝ³}, ¬ (⟪p, b⟫ ≤ ⟪r, b⟫ ∧ ⟪p, b⟫ ≤ ⟪s, b⟫ ∧ ⟪q, b⟫ ≤ ⟪r, b⟫ ∧ ⟪q, b⟫ ≤ ⟪s, b⟫) →
      GenQuad.LexClause p q r s b d1 d2 := fun h => GenQuad.lexClause_of_notM h
  have h0123 : GenQuad.LexClause (x 2) (x 6) (x 1) (x 3) b d1 d2 ∧
      GenQuad.LexClause (x 1) (x 3) (x 2) (x 6) b d1 d2 := by
    rcases hF0123 with ⟨hf, hm⟩ | ⟨hf, hm⟩
    · exact ⟨cl hf, cn hm⟩
    · exact ⟨cn hm, cl hf⟩
  exact GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) hc_inj hcyc b d1 d2 hU hD
    (GenQuad.clauses_five (p := fun i => x (c i))
      h0123.1 h0123.2 (cl hF0124) (cn hM0124) (cl hF0134) (cn hM0134)
      (cl hF0234) (cn hM0234) (cl hF1234) (cn hM1234))

end Minimality.NF29
