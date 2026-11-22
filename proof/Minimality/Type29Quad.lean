module

public import Minimality.Type29LeavesA16
public import Minimality.GenQuad

@[expose] public section

/-!
# Type 29: 4-rim leaves via `GenQuad` (`GEN29-REVIEW` R3)

Formalizes the five 4-rim leaves from `GEN29-REVIEW.md` §R3 in `Type29LeavesA16` style via
`GenQuad.lexAny_of_clauses`, `GenQuad.clauses_four`, `GenQuad.lexClause_of_frontOf`, and
`GenQuad.lexClause_of_notM`:
1. `lexAny29_F015_023_pmm`: `F015xF023+--` on 4-rim `![0, 1, 4, 2]`, front `1, 2`;
2. `lexAny29_F015_023_pmp`: `F015xF023+-+` on 4-rim `![0, 1, 4, 3]`, front `1, 3`;
3. `lexAny29_F035_234_ppp`: `F035xF234+++` on 4-rim `![1, 4, 3, 5]`, front `1, 3`;
4. `lexAny29_F023_346_pmm`: `F023xF346+--` on 4-rim `![1, 2, 3, 4]`, front `2, 4`;
5. `lexAny29_F124_1456_pmm`: `F124xF1456+--` on 4-rim `![0, 2, 1, 5]`, front `0, 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.GenQuad Minimality.LexCell Minimality.H21

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-! ### Crossing views and tie-facet vanishing lemmas -/

noncomputable def u015_023 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  (N.a0 * (1 - N.h2) + N.a2 * N.h0) • (x 0 - x 3) - N.a0 • (x 2 - x 3)

noncomputable def u023_346 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  N.D234 • (x 0 - x 3) - N.p0346 • (x 2 - x 3)

local macro "quad_fac_zero " N:term:max f:ident b:ident : tactic =>
  `(tactic| (
    rw [($f $N).hN (x 3 + $N.$b x) (x 3), add_sub_cancel_left]
    dsimp only [u015_023, u023_346, D234, p0346, del0, E35]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      ← ($f $N).hN (x 0) (x 3), ← ($f $N).hN (x 2) (x 3)]
    dsimp only [f015, f023, f035, f234, f346, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

theorem f015_u015_023 (N : NF29 x) :
    N.f015.f (x 3 + N.u015_023 x) - N.f015.f (x 3) = 0 := by
  quad_fac_zero N f015 u015_023

theorem f023_u015_023 (N : NF29 x) :
    N.f023.f (x 3 + N.u015_023 x) - N.f023.f (x 3) = 0 := by
  quad_fac_zero N f023 u015_023

theorem f035_u35_24 (N : NF29 x) :
    N.f035.f (x 3 + N.u35_24 x) - N.f035.f (x 3) = 0 := by
  rw [N.f035.hN (x 3 + N.u35_24 x) (x 3), add_sub_cancel_left]
  dsimp only [u35_24]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← N.f035.hN (x 2) (x 3), ← N.f035.hN (x 4) (x 3)]
  dsimp only [del0, E35, f035, Face16.ofPoly]
  nf29_simp N; simp only [det3c, NF29.D]; ring

theorem f234_u35_24 (N : NF29 x) :
    N.f234.f (x 3 + N.u35_24 x) - N.f234.f (x 3) = 0 := by
  rw [N.f234.hN (x 3 + N.u35_24 x) (x 3), add_sub_cancel_left]
  dsimp only [u35_24]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    ← N.f234.hN (x 2) (x 3), ← N.f234.hN (x 4) (x 3)]
  dsimp only [del0, E35, f234, Face16.ofPoly]
  nf29_simp N; simp only [det3c, NF29.D]; ring

theorem f023_u023_346 (N : NF29 x) :
    N.f023.f (x 3 + N.u023_346 x) - N.f023.f (x 3) = 0 := by
  quad_fac_zero N f023 u023_346

theorem f346_u023_346 (N : NF29 x) :
    N.f346.f (x 3 + N.u023_346 x) - N.f346.f (x 3) = 0 := by
  quad_fac_zero N f346 u023_346

theorem f124_w14 (N : NF29 x) :
    N.f124.f (x 3 + (x 1 - x 4)) - N.f124.f (x 3) = 0 := by
  rw [N.f124.hN (x 3 + (x 1 - x 4)) (x 3), add_sub_cancel_left,
    ← N.f124.hN (x 1) (x 4), N.f124.zero 1 (by decide), N.f124.zero 4 (by decide), sub_self]

theorem f1456_w14 (N : NF29 x) :
    N.f1456.f (x 3 + (x 1 - x 4)) - N.f1456.f (x 3) = 0 := by
  rw [N.f1456.hN (x 3 + (x 1 - x 4)) (x 3), add_sub_cancel_left,
    ← N.f1456.hN (x 1) (x 4), N.f1456.zero 1 (by decide), N.f1456.zero 4 (by decide), sub_self]

/-! ### 1a. `F015xF023+--` on rim `![0, 1, 4, 2]` -/

private def c_0142 : ZMod 4 → Fin 7 := ![0, 1, 4, 2]
private def U_015_023_pmm : Finset (Fin 9) := {0, 4}
private def Dn_015_023_pmm : Finset (Fin 9) := {1, 2, 3, 5, 6, 7, 8}

private theorem c_0142_inj : Function.Injective c_0142 := by decide
private theorem cyc_015_023_pmm : S0xCycUD s0x_S29 c_0142 U_015_023_pmm Dn_015_023_pmm := by decide

theorem lexAny29_F015_023_pmm (N : NF29 x)
    (h012 : 0 < N.f012.f (x 3 + N.u015_023 x) - N.f012.f (x 3))
    (h035 : N.f035.f (x 3 + N.u015_023 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u015_023 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u015_023 x) - N.f1456.f (x 3) < 0)
    (h234 : N.f234.f (x 3 + N.u015_023 x) - N.f234.f (x 3) < 0)
    (h346 : N.f346.f (x 3 + N.u015_023 x) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + N.u015_023 x) - N.f356.f (x 3) < 0)
    (hΔ : 0 < Split.det3 (x 1 - x 2) (x 0 - x 4) (N.u015_023 x))
    (hl0 : 0 ≤ Split.det3 (x 4 - x 2) (x 0 - x 4) (N.u015_023 x))
    (hl1 : Split.det3 (x 4 - x 2) (x 0 - x 4) (N.u015_023 x) ≤
      Split.det3 (x 1 - x 2) (x 0 - x 4) (N.u015_023 x))
    (hm0 : 0 ≤ -Split.det3 (x 1 - x 2) (x 4 - x 2) (N.u015_023 x))
    (hm1 : -Split.det3 (x 1 - x 2) (x 4 - x 2) (N.u015_023 x) ≤
      Split.det3 (x 1 - x 2) (x 0 - x 4) (N.u015_023 x))
    (he : Split.det3 (x 1 - x 2) (x 0 - x 4) (x 4 - x 2) < 0)
    (hM : ¬ (⟪x 0, N.u015_023 x⟫ ≤ ⟪x 1, N.u015_023 x⟫ ∧ ⟪x 0, N.u015_023 x⟫ ≤ ⟪x 2, N.u015_023 x⟫ ∧
             ⟪x 4, N.u015_023 x⟫ ≤ ⟪x 1, N.u015_023 x⟫ ∧ ⟪x 4, N.u015_023 x⟫ ≤ ⟪x 2, N.u015_023 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := N.u015_023 x
  let d1 : ℝ³ := x 4 - x 0
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 4) - F.f t (x 0) := fun t => (F.hN t (x 4) (x 0)).symm
  have hb_ne : b ≠ 0 := by
    intro h0
    have : ⟪F.N 0, b⟫ = 0 := by rw [h0, inner_zero_right]
    rw [hnb 0] at this
    change N.f012.f (x 3 + N.u015_023 x) - N.f012.f (x 3) = 0 at this
    linarith
  refine lexAny_of_clauses F (le_refl 4) c_0142_inj cyc_015_023_pmm b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl h012
    · exact Or.inl h124
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t
    · exact absurd ht (by decide)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f015_u015_023,
        Or.inl (by change 0 < -(N.f015.f (x 4) - N.f015.f (x 0))
                   rw [N.f015.zero 0 (by decide), sub_zero, neg_pos]
                   exact N.f015.neg 4 (by decide))⟩
    · exact Or.inr ⟨neg_eq_zero.mpr N.f023_u015_023,
        Or.inl (by change 0 < -(N.f023.f (x 4) - N.f023.f (x 0))
                   rw [N.f023.zero 0 (by decide), sub_zero, neg_pos]
                   exact N.f023.neg 4 (by decide))⟩
    · exact Or.inl (neg_pos.mpr h035)
    · exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h1456)
    · exact Or.inl (neg_pos.mpr h234)
    · exact Or.inl (neg_pos.mpr h346)
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_0142 i)) ?_ ?_
    · exact lexClause_of_frontOf hb_ne (frontOf_of_det hΔ hl0 hl1 hm0 hm1 he)
    · exact lexClause_of_notM hM

/-! ### 1b. `F015xF023+-+` on rim `![0, 1, 4, 3]` -/

private def c_0143 : ZMod 4 → Fin 7 := ![0, 1, 4, 3]
private def U_015_023_pmp : Finset (Fin 9) := {0, 2, 4, 6}
private def Dn_015_023_pmp : Finset (Fin 9) := {1, 3, 5, 7, 8}

private theorem c_0143_inj : Function.Injective c_0143 := by decide
private theorem cyc_015_023_pmp : S0xCycUD s0x_S29 c_0143 U_015_023_pmp Dn_015_023_pmp := by decide

theorem lexAny29_F015_023_pmp (N : NF29 x)
    (h012 : 0 < N.f012.f (x 3 + N.u015_023 x) - N.f012.f (x 3))
    (h035 : N.f035.f (x 3 + N.u015_023 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u015_023 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u015_023 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u015_023 x) - N.f234.f (x 3))
    (h346 : N.f346.f (x 3 + N.u015_023 x) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + N.u015_023 x) - N.f356.f (x 3) < 0)
    (hΔ : 0 < Split.det3 (x 1 - x 3) (x 0 - x 4) (N.u015_023 x))
    (hl0 : 0 ≤ Split.det3 (x 4 - x 3) (x 0 - x 4) (N.u015_023 x))
    (hl1 : Split.det3 (x 4 - x 3) (x 0 - x 4) (N.u015_023 x) ≤
      Split.det3 (x 1 - x 3) (x 0 - x 4) (N.u015_023 x))
    (hm0 : 0 ≤ -Split.det3 (x 1 - x 3) (x 4 - x 3) (N.u015_023 x))
    (hm1 : -Split.det3 (x 1 - x 3) (x 4 - x 3) (N.u015_023 x) ≤
      Split.det3 (x 1 - x 3) (x 0 - x 4) (N.u015_023 x))
    (he : Split.det3 (x 1 - x 3) (x 0 - x 4) (x 4 - x 3) < 0)
    (hM : ¬ (⟪x 0, N.u015_023 x⟫ ≤ ⟪x 1, N.u015_023 x⟫ ∧ ⟪x 0, N.u015_023 x⟫ ≤ ⟪x 3, N.u015_023 x⟫ ∧
             ⟪x 4, N.u015_023 x⟫ ≤ ⟪x 1, N.u015_023 x⟫ ∧ ⟪x 4, N.u015_023 x⟫ ≤ ⟪x 3, N.u015_023 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := N.u015_023 x
  let d1 : ℝ³ := x 2 - x 5
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 2) - F.f t (x 5) := fun t => (F.hN t (x 2) (x 5)).symm
  have hb_ne : b ≠ 0 := by
    intro h0
    have : ⟪F.N 0, b⟫ = 0 := by rw [h0, inner_zero_right]
    rw [hnb 0] at this
    change N.f012.f (x 3 + N.u015_023 x) - N.f012.f (x 3) = 0 at this
    linarith
  refine lexAny_of_clauses F (le_refl 4) c_0143_inj cyc_015_023_pmp b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t
    · exact Or.inl h012
    · exact absurd ht (by decide)
    · exact Or.inr ⟨N.f023_u015_023,
        Or.inl (by change 0 < N.f023.f (x 2) - N.f023.f (x 5)
                   rw [N.f023.zero 2 (by decide), zero_sub, neg_pos]
                   exact N.f023.neg 5 (by decide))⟩
    · exact absurd ht (by decide)
    · exact Or.inl h124
    · exact absurd ht (by decide)
    · exact Or.inl h234
    all_goals exact absurd ht (by decide)
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t
    · exact absurd ht (by decide)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f015_u015_023,
        Or.inl (by change 0 < -(N.f015.f (x 2) - N.f015.f (x 5))
                   rw [N.f015.zero 5 (by decide), sub_zero, neg_pos]
                   exact N.f015.neg 2 (by decide))⟩
    · exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h035)
    · exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h1456)
    · exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h346)
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_0143 i)) ?_ ?_
    · exact lexClause_of_frontOf hb_ne (frontOf_of_det hΔ hl0 hl1 hm0 hm1 he)
    · exact lexClause_of_notM hM

/-! ### 2. `F035xF234+++` on rim `![1, 4, 3, 5]` -/

private def c_1435 : ZMod 4 → Fin 7 := ![1, 4, 3, 5]
private def U_035_234_ppp : Finset (Fin 9) := {0, 1, 2, 3, 4, 6}
private def Dn_035_234_ppp : Finset (Fin 9) := {5, 7, 8}

private theorem c_1435_inj : Function.Injective c_1435 := by decide
private theorem cyc_035_234_ppp : S0xCycUD s0x_S29 c_1435 U_035_234_ppp Dn_035_234_ppp := by decide

theorem lexAny29_F035_234_ppp (N : NF29 x)
    (h012 : 0 < N.f012.f (x 3 + N.u35_24 x) - N.f012.f (x 3))
    (h015 : 0 < N.f015.f (x 3 + N.u35_24 x) - N.f015.f (x 3))
    (h023 : 0 < N.f023.f (x 3 + N.u35_24 x) - N.f023.f (x 3))
    (h124 : 0 < N.f124.f (x 3 + N.u35_24 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u35_24 x) - N.f1456.f (x 3) < 0)
    (h346 : N.f346.f (x 3 + N.u35_24 x) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + N.u35_24 x) - N.f356.f (x 3) < 0)
    (hΔ : Split.det3 (x 1 - x 3) (x 4 - x 5) (N.u35_24 x) < 0)
    (hl0 : Split.det3 (x 5 - x 3) (x 4 - x 5) (N.u35_24 x) ≤ 0)
    (hl1 : Split.det3 (x 1 - x 3) (x 4 - x 5) (N.u35_24 x) ≤
      Split.det3 (x 5 - x 3) (x 4 - x 5) (N.u35_24 x))
    (hm0 : -Split.det3 (x 1 - x 3) (x 5 - x 3) (N.u35_24 x) ≤ 0)
    (hm1 : Split.det3 (x 1 - x 3) (x 4 - x 5) (N.u35_24 x) ≤
      -Split.det3 (x 1 - x 3) (x 5 - x 3) (N.u35_24 x))
    (he : 0 < Split.det3 (x 1 - x 3) (x 4 - x 5) (x 5 - x 3))
    (hM : ¬ (⟪x 4, N.u35_24 x⟫ ≤ ⟪x 1, N.u35_24 x⟫ ∧ ⟪x 4, N.u35_24 x⟫ ≤ ⟪x 3, N.u35_24 x⟫ ∧
             ⟪x 5, N.u35_24 x⟫ ≤ ⟪x 1, N.u35_24 x⟫ ∧ ⟪x 5, N.u35_24 x⟫ ≤ ⟪x 3, N.u35_24 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := N.u35_24 x
  let d1 : ℝ³ := x 3 - x 1
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 1) := fun t => (F.hN t (x 3) (x 1)).symm
  have hb_ne : b ≠ 0 := by
    intro h0
    have : ⟪F.N 0, b⟫ = 0 := by rw [h0, inner_zero_right]
    rw [hnb 0] at this
    change N.f012.f (x 3 + N.u35_24 x) - N.f012.f (x 3) = 0 at this
    linarith
  refine lexAny_of_clauses F (le_refl 4) c_1435_inj cyc_035_234_ppp b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t
    · exact Or.inl h012
    · exact Or.inl h015
    · exact Or.inl h023
    · exact Or.inr ⟨N.f035_u35_24,
        Or.inl (by change 0 < N.f035.f (x 3) - N.f035.f (x 1)
                   rw [N.f035.zero 3 (by decide), zero_sub, neg_pos]
                   exact N.f035.neg 1 (by decide))⟩
    · exact Or.inl h124
    · exact absurd ht (by decide)
    · exact Or.inr ⟨N.f234_u35_24,
        Or.inl (by change 0 < N.f234.f (x 3) - N.f234.f (x 1)
                   rw [N.f234.zero 3 (by decide), zero_sub, neg_pos]
                   exact N.f234.neg 1 (by decide))⟩
    all_goals exact absurd ht (by decide)
  · intro t ht
    rw [hnb t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h1456)
    · exact Or.inl (neg_pos.mpr h346)
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_1435 i)) ?_ ?_
    · exact lexClause_of_notM hM
    · exact lexClause_of_frontOf hb_ne (frontOf_of_det_neg hΔ hl0 hl1 hm0 hm1 he)

/-! ### 3. `F023xF346+--` on rim `![1, 2, 3, 4]` -/

private def c_1234 : ZMod 4 → Fin 7 := ![1, 2, 3, 4]
private def U_023_346_pmm : Finset (Fin 9) := {4, 6}
private def Dn_023_346_pmm : Finset (Fin 9) := {0, 1, 2, 3, 5, 7, 8}

private theorem c_1234_inj : Function.Injective c_1234 := by decide
private theorem cyc_023_346_pmm : S0xCycUD s0x_S29 c_1234 U_023_346_pmm Dn_023_346_pmm := by decide

theorem lexAny29_F023_346_pmm (N : NF29 x)
    (h012 : N.f012.f (x 3 + N.u023_346 x) - N.f012.f (x 3) < 0)
    (h015 : N.f015.f (x 3 + N.u023_346 x) - N.f015.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u023_346 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u023_346 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u023_346 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u023_346 x) - N.f234.f (x 3))
    (h356 : N.f356.f (x 3 + N.u023_346 x) - N.f356.f (x 3) < 0)
    (hΔ : Split.det3 (x 2 - x 4) (x 1 - x 3) (N.u023_346 x) < 0)
    (hl0 : Split.det3 (x 3 - x 4) (x 1 - x 3) (N.u023_346 x) ≤ 0)
    (hl1 : Split.det3 (x 2 - x 4) (x 1 - x 3) (N.u023_346 x) ≤
      Split.det3 (x 3 - x 4) (x 1 - x 3) (N.u023_346 x))
    (hm0 : -Split.det3 (x 2 - x 4) (x 3 - x 4) (N.u023_346 x) ≤ 0)
    (hm1 : Split.det3 (x 2 - x 4) (x 1 - x 3) (N.u023_346 x) ≤
      -Split.det3 (x 2 - x 4) (x 3 - x 4) (N.u023_346 x))
    (he : 0 < Split.det3 (x 2 - x 4) (x 1 - x 3) (x 3 - x 4))
    (hM : ¬ (⟪x 1, N.u023_346 x⟫ ≤ ⟪x 2, N.u023_346 x⟫ ∧ ⟪x 1, N.u023_346 x⟫ ≤ ⟪x 4, N.u023_346 x⟫ ∧
             ⟪x 3, N.u023_346 x⟫ ≤ ⟪x 2, N.u023_346 x⟫ ∧ ⟪x 3, N.u023_346 x⟫ ≤ ⟪x 4, N.u023_346 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := N.u023_346 x
  let d1 : ℝ³ := x 1 - x 3
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 1) - F.f t (x 3) := fun t => (F.hN t (x 1) (x 3)).symm
  have hb_ne : b ≠ 0 := by
    intro h0
    have : ⟪F.N 4, b⟫ = 0 := by rw [h0, inner_zero_right]
    rw [hnb 4] at this
    change N.f124.f (x 3 + N.u023_346 x) - N.f124.f (x 3) = 0 at this
    linarith
  refine lexAny_of_clauses F (le_refl 4) c_1234_inj cyc_023_346_pmm b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t]
    fin_cases t <;> try exact absurd ht (by decide)
    · exact Or.inl h124
    · exact Or.inl h234
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t
    · exact Or.inl (neg_pos.mpr h012)
    · exact Or.inl (neg_pos.mpr h015)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f023_u023_346,
        Or.inl (by change 0 < -(N.f023.f (x 1) - N.f023.f (x 3))
                   rw [N.f023.zero 3 (by decide), sub_zero, neg_pos]
                   exact N.f023.neg 1 (by decide))⟩
    · exact Or.inl (neg_pos.mpr h035)
    · exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h1456)
    · exact absurd ht (by decide)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f346_u023_346,
        Or.inl (by change 0 < -(N.f346.f (x 1) - N.f346.f (x 3))
                   rw [N.f346.zero 3 (by decide), sub_zero, neg_pos]
                   exact N.f346.neg 1 (by decide))⟩
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_1234 i)) ?_ ?_
    · exact lexClause_of_frontOf hb_ne (frontOf_of_det_neg hΔ hl0 hl1 hm0 hm1 he)
    · exact lexClause_of_notM hM

/-! ### 4. `F124xF1456+--` on rim `![0, 2, 1, 5]` -/

private def c_0215 : ZMod 4 → Fin 7 := ![0, 2, 1, 5]
private def U_124_1456_pmm : Finset (Fin 9) := {0, 1}
private def Dn_124_1456_pmm : Finset (Fin 9) := {2, 3, 4, 5, 6, 7, 8}

private theorem c_0215_inj : Function.Injective c_0215 := by decide
private theorem cyc_124_1456_pmm : S0xCycUD s0x_S29 c_0215 U_124_1456_pmm Dn_124_1456_pmm := by decide

theorem lexAny29_F124_1456_pmm (N : NF29 x)
    (h012 : 0 < N.f012.f (x 3 + (x 1 - x 4)) - N.f012.f (x 3))
    (h015 : 0 < N.f015.f (x 3 + (x 1 - x 4)) - N.f015.f (x 3))
    (h023 : N.f023.f (x 3 + (x 1 - x 4)) - N.f023.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + (x 1 - x 4)) - N.f035.f (x 3) < 0)
    (h234 : N.f234.f (x 3 + (x 1 - x 4)) - N.f234.f (x 3) < 0)
    (h346 : N.f346.f (x 3 + (x 1 - x 4)) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + (x 1 - x 4)) - N.f356.f (x 3) < 0)
    (hΔ : 0 < Split.det3 (x 0 - x 1) (x 2 - x 5) (x 1 - x 4))
    (hl0 : 0 ≤ Split.det3 (x 5 - x 1) (x 2 - x 5) (x 1 - x 4))
    (hl1 : Split.det3 (x 5 - x 1) (x 2 - x 5) (x 1 - x 4) ≤
      Split.det3 (x 0 - x 1) (x 2 - x 5) (x 1 - x 4))
    (hm0 : 0 ≤ -Split.det3 (x 0 - x 1) (x 5 - x 1) (x 1 - x 4))
    (hm1 : -Split.det3 (x 0 - x 1) (x 5 - x 1) (x 1 - x 4) ≤
      Split.det3 (x 0 - x 1) (x 2 - x 5) (x 1 - x 4))
    (he : Split.det3 (x 0 - x 1) (x 2 - x 5) (x 5 - x 1) < 0)
    (hM : ¬ (⟪x 2, x 1 - x 4⟫ ≤ ⟪x 0, x 1 - x 4⟫ ∧ ⟪x 2, x 1 - x 4⟫ ≤ ⟪x 1, x 1 - x 4⟫ ∧
             ⟪x 5, x 1 - x 4⟫ ≤ ⟪x 0, x 1 - x 4⟫ ∧ ⟪x 5, x 1 - x 4⟫ ≤ ⟪x 1, x 1 - x 4⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let b : ℝ³ := x 1 - x 4
  let d1 : ℝ³ := x 3 - x 1
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 1) := fun t => (F.hN t (x 3) (x 1)).symm
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
  refine lexAny_of_clauses F (le_refl 4) c_0215_inj cyc_124_1456_pmm b d1 0 ?_ ?_ ?_
  · intro t ht
    rw [hnb t]
    fin_cases t
    · exact Or.inl h012
    · exact Or.inl h015
    all_goals exact absurd ht (by decide)
  · intro t ht
    rw [hnb t, hnd t]
    fin_cases t
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact Or.inl (neg_pos.mpr h023)
    · exact Or.inl (neg_pos.mpr h035)
    · exact Or.inr ⟨neg_eq_zero.mpr N.f124_w14,
        Or.inl (by change 0 < -(N.f124.f (x 3) - N.f124.f (x 1))
                   rw [N.f124.zero 1 (by decide), sub_zero, neg_pos]
                   exact N.f124.neg 3 (by decide))⟩
    · exact Or.inr ⟨neg_eq_zero.mpr N.f1456_w14,
        Or.inl (by change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 1))
                   rw [N.f1456.zero 1 (by decide), sub_zero, neg_pos]
                   exact N.f1456.neg 3 (by decide))⟩
    · exact Or.inl (neg_pos.mpr h234)
    · exact Or.inl (neg_pos.mpr h346)
    · exact Or.inl (neg_pos.mpr h356)
  · refine clauses_four (p := fun i => x (c_0215 i)) ?_ ?_
    · exact lexClause_of_notM hM
    · exact lexClause_of_frontOf hb_ne (frontOf_of_det hΔ hl0 hl1 hm0 hm1 he)

end Minimality.NF29
