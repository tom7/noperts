module

public import Minimality.Type29Exact
public import Minimality.Chi29

@[expose] public section

/-!
# Type 29: leaves for the 8 section-5 SAT shapes (Task CI, GEN29-REVIEW R3)

Four leaves via `GenQuad.lexAny_of_clauses`, `GenQuad.clauses_four` / `GenQuad.clauses_five`,
`NF29.FrontDet.frontOf`, and `GenQuad.lexClause_of_notM`:
1. `lexAny29_F015_124_pmp`: `F015xF124+-+` on 4-rim `![1, 2, 3, 5]` at `b = N.u015_124 x`.
2. `lexAny29_F015_035_ppp`: `F015xF035+++` on 4-rim `![1, 4, 3, 5]` at `b = x 0 - x 5`.
3. `lexAny29_F015_035_pmm`: `F015xF035+--` on 4-rim `![0, 1, 4, 3]` at `b = x 0 - x 5`.
4. `lexAny29_F015_124_5`: `F015xF124+-+` on 5-rim `![1, 2, 3, 6, 5]` at `b = N.u015_124 x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21 Minimality.H29 Minimality.GenQuad

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-! ### Crossing views and facet identities -/

/-- Crossing view of `F015` and `F124`: `(-a0*h2) • (x4 - x1) - (h0*b2) • (x5 - x1) + (h0*h2) • (x1 - x3)`. -/
noncomputable def u015_124 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  (-N.a0 * N.h2) • (x 4 - x 1) - (N.h0 * N.b2) • (x 5 - x 1) + (N.h0 * N.h2) • (x 1 - x 3)

local macro "u015_124_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [u015_124, f012, f015, f124, f1456, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

theorem f015_u015_124 (N : NF29 x) :
    N.f015.f (x 3 + N.u015_124 x) - N.f015.f (x 3) = 0 := by
  rw [N.f015.hN (x 3 + N.u015_124 x) (x 3), add_sub_cancel_left]
  dsimp only [u015_124]
  rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, ← N.f015.hN (x 4) (x 1), ← N.f015.hN (x 5) (x 1),
    ← N.f015.hN (x 1) (x 3)]
  u015_124_val N

theorem f124_u015_124 (N : NF29 x) :
    N.f124.f (x 3 + N.u015_124 x) - N.f124.f (x 3) = 0 := by
  rw [N.f124.hN (x 3 + N.u015_124 x) (x 3), add_sub_cancel_left]
  dsimp only [u015_124]
  rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, ← N.f124.hN (x 4) (x 1), ← N.f124.hN (x 5) (x 1),
    ← N.f124.hN (x 1) (x 3)]
  u015_124_val N

theorem f012_u015_124_eq (N : NF29 x) :
    N.f012.f (x 3 + N.u015_124 x) - N.f012.f (x 3) =
      -(N.h0 * N.a2 - N.h2 * N.a0) * (N.h2 * N.b0 - N.h0 * N.b2) * N.D ^ 2 := by
  rw [N.f012.hN (x 3 + N.u015_124 x) (x 3), add_sub_cancel_left]
  dsimp only [u015_124]
  rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, ← N.f012.hN (x 4) (x 1), ← N.f012.hN (x 5) (x 1),
    ← N.f012.hN (x 1) (x 3)]
  u015_124_val N

theorem f012_u015_124_neg (N : NF29 x) :
    N.f012.f (x 3 + N.u015_124 x) - N.f012.f (x 3) < 0 := by
  rw [f012_u015_124_eq]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos N.hF5) N.hF4)
    (sq_pos_of_ne_zero N.hD)

theorem f1456_u015_124_eq (N : NF29 x) :
    N.f1456.f (x 3 + N.u015_124 x) - N.f1456.f (x 3) = N.h0 * N.h2 * N.D ^ 2 := by
  rw [N.f1456.hN (x 3 + N.u015_124 x) (x 3), add_sub_cancel_left]
  dsimp only [u015_124]
  rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, ← N.f1456.hN (x 4) (x 1), ← N.f1456.hN (x 5) (x 1),
    ← N.f1456.hN (x 1) (x 3)]
  u015_124_val N

theorem f1456_u015_124_pos (N : NF29 x) :
    0 < N.f1456.f (x 3 + N.u015_124 x) - N.f1456.f (x 3) := by
  rw [f1456_u015_124_eq]
  exact mul_pos (mul_pos N.hh0 N.hh2) (sq_pos_of_ne_zero N.hD)

theorem f015_x05 (N : NF29 x) :
    N.f015.f (x 3 + (x 0 - x 5)) - N.f015.f (x 3) = 0 := by
  rw [N.f015.hN (x 3 + (x 0 - x 5)) (x 3), add_sub_cancel_left, ← N.f015.hN (x 0) (x 5),
    N.f015.zero 0 (by decide), N.f015.zero 5 (by decide), sub_zero]

theorem f035_x05 (N : NF29 x) :
    N.f035.f (x 3 + (x 0 - x 5)) - N.f035.f (x 3) = 0 := by
  rw [N.f035.hN (x 3 + (x 0 - x 5)) (x 3), add_sub_cancel_left, ← N.f035.hN (x 0) (x 5),
    N.f035.zero 0 (by decide), N.f035.zero 5 (by decide), sub_zero]

theorem f012_x05_pos (N : NF29 x) :
    0 < N.f012.f (x 3 + (x 0 - x 5)) - N.f012.f (x 3) := by
  rw [N.f012.hN (x 3 + (x 0 - x 5)) (x 3), add_sub_cancel_left, ← N.f012.hN (x 0) (x 5)]
  have hval : N.f012.f (x 0) - N.f012.f (x 5) = (N.h0 * N.a2 - N.h2 * N.a0) * N.D ^ 2 := by
    dsimp only [f012, Face16.ofPoly]
    nf29_simp N
    simp only [det3c, NF29.D]
    ring
  rw [hval]
  exact mul_pos N.hF5 (sq_pos_of_ne_zero N.hD)

theorem f023_x05_pos (N : NF29 x) :
    0 < N.f023.f (x 3 + (x 0 - x 5)) - N.f023.f (x 3) := by
  rw [N.f023.hN (x 3 + (x 0 - x 5)) (x 3), add_sub_cancel_left, ← N.f023.hN (x 0) (x 5)]
  have hval : N.f023.f (x 0) - N.f023.f (x 5) =
      -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) * N.D ^ 2 := by
    dsimp only [f023, Face16.ofPoly]
    nf29_simp N
    simp only [det3c, NF29.D]
    ring
  rw [hval]
  exact mul_pos (neg_pos.mpr N.hE35) (sq_pos_of_ne_zero N.hD)

theorem f1456_x05_neg (N : NF29 x) :
    N.f1456.f (x 3 + (x 0 - x 5)) - N.f1456.f (x 3) < 0 := by
  rw [N.f1456.hN (x 3 + (x 0 - x 5)) (x 3), add_sub_cancel_left, ← N.f1456.hN (x 0) (x 5)]
  have hval : N.f1456.f (x 0) - N.f1456.f (x 5) = -N.h0 * N.D ^ 2 := by
    dsimp only [f1456, Face16.ofPoly]
    nf29_simp N
    simp only [det3c, NF29.D]
    ring
  rw [hval]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos N.hh0) (sq_pos_of_ne_zero N.hD)

/-! ### 1. `F015xF124+-+` on 4-rim `![1, 2, 3, 5]` -/

private def c_1235 : ZMod 4 → Fin 7 := ![1, 2, 3, 5]
private def U_015_124_pmp : Finset (Fin 9) := {4, 5, 6, 7, 8}
private def Dn_015_124_pmp : Finset (Fin 9) := {0, 1, 2, 3}

private theorem c_1235_inj : Function.Injective c_1235 := by decide
private theorem cyc_015_124_pmp : S0xCycUD s0x_S29 c_1235 U_015_124_pmp Dn_015_124_pmp := by decide

theorem lexAny29_F015_124_pmp (N : NF29 x)
    (h023 : N.f023.f (x 3 + N.u015_124 x) - N.f023.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u015_124 x) - N.f035.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u015_124 x) - N.f234.f (x 3))
    (h346 : 0 < N.f346.f (x 3 + N.u015_124 x) - N.f346.f (x 3))
    (h356 : 0 < N.f356.f (x 3 + N.u015_124 x) - N.f356.f (x 3))
    (hF1235 : FrontDet (x 1) (x 3) (x 2) (x 5) (N.u015_124 x))
    (hM : ¬ (⟪x 2, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 2, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫ ∧
             ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := N.u015_124 x
  let d1 : ℝ³ := x 4 - x 0
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 4) - F.f t (x 0) := fun t => (F.hN t (x 4) (x 0)).symm
  have hb_ne : b ≠ 0 := by
    intro h0
    have : ⟪F.N 5, b⟫ = 0 := by rw [h0, inner_zero_right]
    rw [hnb 5] at this
    change N.f1456.f (x 3 + N.u015_124 x) - N.f1456.f (x 3) = 0 at this
    linarith [N.f1456_u015_124_pos]
  refine lexAny_of_clauses F (le_refl 4) c_1235_inj cyc_015_124_pmp b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inr ⟨N.f124_u015_124,
        Or.inl (by change 0 < N.f124.f (x 4) - N.f124.f (x 0)
                   rw [N.f124.zero 4 (by decide), zero_sub, neg_pos]
                   exact N.f124.neg 0 (by decide))⟩
    · exact Or.inl N.f1456_u015_124_pos
    · exact Or.inl h234
    · exact Or.inl h346
    · exact Or.inl h356
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr N.f012_u015_124_neg)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f015_u015_124,
        Or.inl (by change 0 < -(N.f015.f (x 4) - N.f015.f (x 0))
                   rw [N.f015.zero 0 (by decide), sub_zero, neg_pos]
                   exact N.f015.neg 4 (by decide))⟩
    · exact Or.inl (neg_pos.mpr h023)
    · exact Or.inl (neg_pos.mpr h035)
  · refine clauses_four (p := fun i => x (c_1235 i)) ?_ ?_
    · exact lexClause_of_notM hM
    · exact lexClause_of_frontOf hb_ne hF1235.frontOf

/-! ### 2a. `F015xF035+++` on 4-rim `![1, 4, 3, 5]` -/

private def c_1435 : ZMod 4 → Fin 7 := ![1, 4, 3, 5]
private def U_015_035_ppp : Finset (Fin 9) := {0, 1, 2, 3, 4, 6}
private def Dn_015_035_ppp : Finset (Fin 9) := {5, 7, 8}

private theorem c_1435_inj : Function.Injective c_1435 := by decide
private theorem cyc_015_035_ppp : S0xCycUD s0x_S29 c_1435 U_015_035_ppp Dn_015_035_ppp := by decide

theorem lexAny29_F015_035_ppp (N : NF29 x)
    (h124 : 0 < N.f124.f (x 3 + (x 0 - x 5)) - N.f124.f (x 3))
    (h234 : 0 < N.f234.f (x 3 + (x 0 - x 5)) - N.f234.f (x 3))
    (h346 : N.f346.f (x 3 + (x 0 - x 5)) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + (x 0 - x 5)) - N.f356.f (x 3) < 0)
    (hF1435 : FrontDet (x 1) (x 3) (x 4) (x 5) (x 0 - x 5))
    (hM : ¬ (⟪x 4, x 0 - x 5⟫ ≤ ⟪x 1, x 0 - x 5⟫ ∧ ⟪x 4, x 0 - x 5⟫ ≤ ⟪x 3, x 0 - x 5⟫ ∧
             ⟪x 5, x 0 - x 5⟫ ≤ ⟪x 1, x 0 - x 5⟫ ∧ ⟪x 5, x 0 - x 5⟫ ≤ ⟪x 3, x 0 - x 5⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := x 0 - x 5
  let d1 : ℝ³ := x 0 - x 4
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 0) - F.f t (x 4) := fun t => (F.hN t (x 0) (x 4)).symm
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
  refine lexAny_of_clauses F (le_refl 4) c_1435_inj cyc_015_035_ppp b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl N.f012_x05_pos
    · exact Or.inr ⟨N.f015_x05,
        Or.inl (by change 0 < N.f015.f (x 0) - N.f015.f (x 4)
                   rw [N.f015.zero 0 (by decide), zero_sub, neg_pos]
                   exact N.f015.neg 4 (by decide))⟩
    · exact Or.inl N.f023_x05_pos
    · exact Or.inr ⟨N.f035_x05,
        Or.inl (by change 0 < N.f035.f (x 0) - N.f035.f (x 4)
                   rw [N.f035.zero 0 (by decide), zero_sub, neg_pos]
                   exact N.f035.neg 4 (by decide))⟩
    · exact Or.inl h124
    · exact Or.inl h234
  · intro t ht
    rw [hnb t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr N.f1456_x05_neg)
    · exact Or.inl (neg_pos.mpr h346)
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_1435 i)) ?_ ?_
    · exact lexClause_of_notM hM
    · exact lexClause_of_frontOf hb_ne hF1435.frontOf

/-! ### 2b. `F015xF035+--` on 4-rim `![0, 1, 4, 3]` -/

private def c_0143 : ZMod 4 → Fin 7 := ![0, 1, 4, 3]
private def U_015_035_pmm : Finset (Fin 9) := {0, 2, 4, 6}
private def Dn_015_035_pmm : Finset (Fin 9) := {1, 3, 5, 7, 8}

private theorem c_0143_inj : Function.Injective c_0143 := by decide
private theorem cyc_015_035_pmm : S0xCycUD s0x_S29 c_0143 U_015_035_pmm Dn_015_035_pmm := by decide

theorem lexAny29_F015_035_pmm (N : NF29 x)
    (h124 : 0 < N.f124.f (x 3 + (x 0 - x 5)) - N.f124.f (x 3))
    (h234 : 0 < N.f234.f (x 3 + (x 0 - x 5)) - N.f234.f (x 3))
    (h346 : N.f346.f (x 3 + (x 0 - x 5)) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + (x 0 - x 5)) - N.f356.f (x 3) < 0)
    (hF0143 : FrontDet (x 1) (x 3) (x 0) (x 4) (x 0 - x 5))
    (hM : ¬ (⟪x 0, x 0 - x 5⟫ ≤ ⟪x 1, x 0 - x 5⟫ ∧ ⟪x 0, x 0 - x 5⟫ ≤ ⟪x 3, x 0 - x 5⟫ ∧
             ⟪x 4, x 0 - x 5⟫ ≤ ⟪x 1, x 0 - x 5⟫ ∧ ⟪x 4, x 0 - x 5⟫ ≤ ⟪x 3, x 0 - x 5⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := x 0 - x 5
  let d1 : ℝ³ := x 4 - x 0
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 4) - F.f t (x 0) := fun t => (F.hN t (x 4) (x 0)).symm
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
  refine lexAny_of_clauses F (le_refl 4) c_0143_inj cyc_015_035_pmm b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl N.f012_x05_pos
    · exact Or.inl N.f023_x05_pos
    · exact Or.inl h124
    · exact Or.inl h234
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f015_x05,
        Or.inl (by change 0 < -(N.f015.f (x 4) - N.f015.f (x 0))
                   rw [N.f015.zero 0 (by decide), sub_zero, neg_pos]
                   exact N.f015.neg 4 (by decide))⟩
    · exact Or.inr ⟨neg_eq_zero.mpr N.f035_x05,
        Or.inl (by change 0 < -(N.f035.f (x 4) - N.f035.f (x 0))
                   rw [N.f035.zero 0 (by decide), sub_zero, neg_pos]
                   exact N.f035.neg 4 (by decide))⟩
    · exact Or.inl (neg_pos.mpr N.f1456_x05_neg)
    · exact Or.inl (neg_pos.mpr h346)
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_0143 i)) ?_ ?_
    · exact lexClause_of_frontOf hb_ne hF0143.frontOf
    · exact lexClause_of_notM hM

/-! ### 3. `F015xF124+-+` on 5-rim `![1, 2, 3, 6, 5]` -/

private def c_12365 : ZMod 5 → Fin 7 := ![1, 2, 3, 6, 5]
private def U_015_124_5 : Finset (Fin 9) := {4, 5, 6, 7}
private def Dn_015_124_5 : Finset (Fin 9) := {0, 1, 2, 3, 8}

private theorem c_12365_inj : Function.Injective c_12365 := by decide
private theorem cyc_015_124_5 : S0xCycUD s0x_S29 c_12365 U_015_124_5 Dn_015_124_5 := by decide

theorem lexAny29_F015_124_5 (N : NF29 x)
    (h023 : N.f023.f (x 3 + N.u015_124 x) - N.f023.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u015_124 x) - N.f035.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u015_124 x) - N.f234.f (x 3))
    (h346 : 0 < N.f346.f (x 3 + N.u015_124 x) - N.f346.f (x 3))
    (h356 : N.f356.f (x 3 + N.u015_124 x) - N.f356.f (x 3) < 0)
    (h1236 :
      (FrontDet (x 1) (x 3) (x 2) (x 6) (N.u015_124 x) ∧
        ¬ (⟪x 2, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 2, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫ ∧
           ⟪x 6, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 6, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫)) ∨
      (FrontDet (x 2) (x 6) (x 1) (x 3) (N.u015_124 x) ∧
        ¬ (⟪x 1, N.u015_124 x⟫ ≤ ⟪x 2, N.u015_124 x⟫ ∧ ⟪x 1, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫ ∧
           ⟪x 3, N.u015_124 x⟫ ≤ ⟪x 2, N.u015_124 x⟫ ∧ ⟪x 3, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫)))
    (hF1235 : FrontDet (x 1) (x 3) (x 2) (x 5) (N.u015_124 x))
    (hM1235 : ¬ (⟪x 2, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 2, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫ ∧
                 ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫))
    (hF1265 : FrontDet (x 1) (x 6) (x 2) (x 5) (N.u015_124 x))
    (hM1265 : ¬ (⟪x 2, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 2, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫ ∧
                 ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫))
    (hF1365 : FrontDet (x 1) (x 6) (x 3) (x 5) (N.u015_124 x))
    (hM1365 : ¬ (⟪x 3, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 3, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫ ∧
                 ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 1, N.u015_124 x⟫ ∧ ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫))
    (h2365 :
      (FrontDet (x 2) (x 6) (x 3) (x 5) (N.u015_124 x) ∧
        ¬ (⟪x 3, N.u015_124 x⟫ ≤ ⟪x 2, N.u015_124 x⟫ ∧ ⟪x 3, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫ ∧
           ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 2, N.u015_124 x⟫ ∧ ⟪x 5, N.u015_124 x⟫ ≤ ⟪x 6, N.u015_124 x⟫)) ∨
      (FrontDet (x 3) (x 5) (x 2) (x 6) (N.u015_124 x) ∧
        ¬ (⟪x 2, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫ ∧ ⟪x 2, N.u015_124 x⟫ ≤ ⟪x 5, N.u015_124 x⟫ ∧
           ⟪x 6, N.u015_124 x⟫ ≤ ⟪x 3, N.u015_124 x⟫ ∧ ⟪x 6, N.u015_124 x⟫ ≤ ⟪x 5, N.u015_124 x⟫))) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := N.u015_124 x
  let d1 : ℝ³ := x 4 - x 0
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 4) - F.f t (x 0) := fun t => (F.hN t (x 4) (x 0)).symm
  have hb_ne : b ≠ 0 := by
    intro h0
    have : ⟪F.N 5, b⟫ = 0 := by rw [h0, inner_zero_right]
    rw [hnb 5] at this
    change N.f1456.f (x 3 + N.u015_124 x) - N.f1456.f (x 3) = 0 at this
    linarith [N.f1456_u015_124_pos]
  have hA1236 : LexClause (x 2) (x 6) (x 1) (x 3) b d1 0 := by
    rcases h1236 with ⟨_, hM⟩ | ⟨hF, _⟩
    · exact lexClause_of_notM hM
    · exact lexClause_of_frontOf hb_ne hF.frontOf
  have hB1236 : LexClause (x 1) (x 3) (x 2) (x 6) b d1 0 := by
    rcases h1236 with ⟨hF, _⟩ | ⟨_, hM⟩
    · exact lexClause_of_frontOf hb_ne hF.frontOf
    · exact lexClause_of_notM hM
  have hA2365 : LexClause (x 3) (x 5) (x 2) (x 6) b d1 0 := by
    rcases h2365 with ⟨_, hM⟩ | ⟨hF, _⟩
    · exact lexClause_of_notM hM
    · exact lexClause_of_frontOf hb_ne hF.frontOf
  have hB2365 : LexClause (x 2) (x 6) (x 3) (x 5) b d1 0 := by
    rcases h2365 with ⟨hF, _⟩ | ⟨_, hM⟩
    · exact lexClause_of_frontOf hb_ne hF.frontOf
    · exact lexClause_of_notM hM
  refine lexAny_of_clauses F (k := 5) (by norm_num) c_12365_inj cyc_015_124_5 b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inr ⟨N.f124_u015_124,
        Or.inl (by change 0 < N.f124.f (x 4) - N.f124.f (x 0)
                   rw [N.f124.zero 4 (by decide), zero_sub, neg_pos]
                   exact N.f124.neg 0 (by decide))⟩
    · exact Or.inl N.f1456_u015_124_pos
    · exact Or.inl h234
    · exact Or.inl h346
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr N.f012_u015_124_neg)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f015_u015_124,
        Or.inl (by change 0 < -(N.f015.f (x 4) - N.f015.f (x 0))
                   rw [N.f015.zero 0 (by decide), sub_zero, neg_pos]
                   exact N.f015.neg 4 (by decide))⟩
    · exact Or.inl (neg_pos.mpr h023)
    · exact Or.inl (neg_pos.mpr h035)
    · exact Or.inl (neg_pos.mpr h356)
  · exact clauses_five (p := fun i => x (c_12365 i))
      hA1236 hB1236
      (lexClause_of_notM hM1235) (lexClause_of_frontOf hb_ne hF1235.frontOf)
      (lexClause_of_notM hM1265) (lexClause_of_frontOf hb_ne hF1265.frontOf)
      (lexClause_of_notM hM1365) (lexClause_of_frontOf hb_ne hF1365.frontOf)
      hA2365 hB2365

end Minimality.NF29
