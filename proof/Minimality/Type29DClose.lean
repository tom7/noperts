module

public import Minimality.Type29Exact
public import Minimality.Type29T1Pair
public import Minimality.Type29Quad

@[expose] public section

/-!
# Type 29, `t = 1` pair D (`W14 x F124xF346`)

Formalizes the pair-D closing lemma from `PAIRS29.md` at `t = 1`:
1. `u124_346`: the `F124xF346` view direction `(b2 + h2) • (x 4 - x 6) - h2 • (x 3 - x 6)`;
2. `d1_row_neg`: under `0 < b2 + h2` and `g34 ≤ 0`, `⟪x 6 - x 4, u124_346⟫ < 0`;
3. `d3_identity`: the uniform 3-row identity at `t = 1` linking `W14` (`z3 - z2`, `z3`) and
   `F124xF346` (`z5`);
4. `lexAny29_F124xF346_clauses`: clause-form `F124xF346` leaf on rim `![3, 4, 6, 5]`;
5. `t1_D_closed`: closes `¬ LexAny29` on the `t = 1` pair-D region.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21
open Minimality.GenQuad (FrontDet)

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-- The `F124xF346` view direction at `t = 1`. -/
noncomputable def u124_346 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  (N.b2 + N.h2) • (x 4 - x 6) - N.h2 • (x 3 - x 6)

/-- At `t = 1`, `0 < b2 + h2` and `g34 ≤ 0` give `⟪x 6 - x 4, u124_346⟫ < 0` (so `z6 < z4`). -/
theorem d1_row_neg (N : NF29 x) (hb2h2 : 0 < N.b2 + N.h2)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ ≤ 0) :
    ⟪x 6 - x 4, N.u124_346 x⟫ < 0 := by
  have h46 : 0 < ⟪x 4 - x 6, x 4 - x 6⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have heq : ⟪x 6 - x 4, N.u124_346 x⟫ =
      -(N.b2 + N.h2) * ⟪x 4 - x 6, x 4 - x 6⟫ + N.h2 * ⟪x 3 - x 6, x 4 - x 6⟫ := by
    have h64 : x 6 - x 4 = -(x 4 - x 6) := by abel
    rw [h64, u124_346, inner_neg_left, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm (x 4 - x 6) (x 3 - x 6)]
    ring
  rw [heq]
  have hh2 : 0 < N.h2 := N.hh2
  nlinarith

/-- The 3-row pair-D identity at `t = 1`. -/
theorem d3_identity (N : NF29 x) (ht : N.t = 1) :
    N.s * (N.b2 + N.h2) * ⟪x 3 - x 2, x 1 - x 4⟫ +
      (-N.b2 * N.s) * ⟪x 3 - x 6, x 1 - x 4⟫ +
      (1 - N.b2 - N.h2) * ⟪x 5 - x 6, N.u124_346 x⟫ =
      -(N.s * (N.b2 + N.h2) * (-N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1)) *
        ⟪x 1 - x 4, x 1 - x 4⟫ := by
  dsimp only [u124_346]
  nf29_simp N
  rw [ht]
  simp only [nfV, inner_add_left, inner_add_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm N.E₂ N.E₁, real_inner_comm N.E₃ N.E₁, real_inner_comm N.E₃ N.E₂]
  ring

local macro "u124_fac_val " N:term:max f:ident : tactic =>
  `(tactic| (
    rw [($f $N).hN (x 3 + u124_346 $N x) (x 3), add_sub_cancel_left]
    dsimp only [u124_346]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      ← ($f $N).hN (x 4) (x 6), ← ($f $N).hN (x 3) (x 6)]
    dsimp only [f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]))

private def c_D : ZMod 4 → Fin 7 := ![1, 4, 6, 5]
private def U_D : Finset (Fin 9) := {0, 2, 3, 5}
private def Dn_D : Finset (Fin 9) := {1, 4, 6, 7, 8}

private theorem c_D_inj : Function.Injective c_D := by decide
private theorem cyc_D : S0xCycUD s0x_S29 c_D U_D Dn_D := by decide

/-- Clause-form `F124xF346` leaf on the 4-rim `![1, 4, 6, 5]` at `u124_346`, with `d1 = x 5 - x 4`. -/
theorem lexAny29_F124xF346_clauses (N : NF29 x) (ht : N.t = 1)
    (hb2h2 : 0 < N.b2 + N.h2) (hpos : 0 < -N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1)
    (h012 : 0 < N.f012.f (x 3 + N.u124_346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u124_346 x) - N.f015.f (x 3) < 0)
    (h023 : 0 < N.f023.f (x 3 + N.u124_346 x) - N.f023.f (x 3))
    (h035 : 0 < N.f035.f (x 3 + N.u124_346 x) - N.f035.f (x 3))
    (hA0123 : GenQuad.LexClause (x 4) (x 5) (x 1) (x 6) (N.u124_346 x) (x 5 - x 4) 0)
    (hB0123 : GenQuad.LexClause (x 1) (x 6) (x 4) (x 5) (N.u124_346 x) (x 5 - x 4) 0) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  have hnb : ∀ t : Fin 9, ⟪F.N t, N.u124_346 x⟫ = F.f t (x 3 + N.u124_346 x) - F.f t (x 3) := by
    intro t; rw [F.hN t (x 3 + N.u124_346 x) (x 3), add_sub_cancel_left]
  have hnd : ∀ t : Fin 9, ⟪F.N t, x 5 - x 4⟫ = F.f t (x 5) - F.f t (x 4) :=
    fun t => (F.hN t (x 5) (x 4)).symm
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  refine GenQuad.lexAny_of_clauses F (le_refl 4) c_D_inj cyc_D (N.u124_346 x) (x 5 - x 4) 0
    ?_ ?_ (GenQuad.clauses_four (p := fun i => x (c_D i)) hA0123 hB0123)
  · intro t ht_mem
    rw [hnb t]
    fin_cases t <;> try exact absurd ht_mem (by decide)
    · exact Or.inl h012
    · exact Or.inl h023
    · exact Or.inl h035
    · refine Or.inl ?_
      change 0 < N.f1456.f (x 3 + N.u124_346 x) - N.f1456.f (x 3)
      have hv : N.f1456.f (x 3 + N.u124_346 x) - N.f1456.f (x 3) = N.h2 * N.D ^ 2 := by
        u124_fac_val N f1456; rw [ht]; ring
      rw [hv]
      exact mul_pos N.hh2 hD2
  · intro t ht_mem
    rw [hnb t, hnd t]
    fin_cases t <;> try exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr h015)
    · have hb0 : N.f124.f (x 3 + N.u124_346 x) - N.f124.f (x 3) = 0 := by
        u124_fac_val N f124; rw [ht]; ring
      have hd1 : N.f124.f (x 5) - N.f124.f (x 4) = -N.h2 * N.D ^ 2 := by
        dsimp only [f124, Face16.ofPoly]
        nf29_simp N; simp only [det3c, NF29.D]; ring
      refine Or.inr ⟨neg_eq_zero.mpr hb0, Or.inl ?_⟩
      change 0 < -(N.f124.f (x 5) - N.f124.f (x 4))
      rw [hd1, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.hh2 hD2
    · refine Or.inl ?_
      change 0 < -(N.f234.f (x 3 + N.u124_346 x) - N.f234.f (x 3))
      have hv : N.f234.f (x 3 + N.u124_346 x) - N.f234.f (x 3) =
          N.b2 * (-N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1) * N.D ^ 2 := by
        u124_fac_val N f234; rw [ht]; ring
      rw [hv]
      have hprod : 0 < (-N.b2) * (-N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1) * N.D ^ 2 :=
        mul_pos (mul_pos (neg_pos.mpr N.hb2) hpos) hD2
      linarith
    · have hb0 : N.f346.f (x 3 + N.u124_346 x) - N.f346.f (x 3) = 0 := by
        u124_fac_val N f346; rw [ht]; ring
      have hd1 : N.f346.f (x 5) - N.f346.f (x 4) = -N.s * N.D ^ 2 := by
        dsimp only [f346, Face16.ofPoly]
        nf29_simp N; rw [ht]; simp only [det3c, NF29.D]; ring
      refine Or.inr ⟨neg_eq_zero.mpr hb0, Or.inl ?_⟩
      change 0 < -(N.f346.f (x 5) - N.f346.f (x 4))
      rw [hd1, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.hs hD2
    · refine Or.inl ?_
      change 0 < -(N.f356.f (x 3 + N.u124_346 x) - N.f356.f (x 3))
      have hv : N.f356.f (x 3 + N.u124_346 x) - N.f356.f (x 3) = -((N.b2 + N.h2) * N.s) * N.D ^ 2 := by
        u124_fac_val N f356; rw [ht]; ring
      rw [hv, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos (mul_pos hb2h2 N.hs) hD2

/-- **Pair-D closing theorem at `t = 1`** (`W14 x F124xF346`): under the `t = 1` pair-D shape
inequalities, the `W14` and `F124xF346` non-`M` clauses, and `g34 ≤ 0`, `LexAny29` cannot fail. -/
theorem t1_D_closed (N : NF29 x) (ht : N.t = 1) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hb2h2 : 0 < N.b2 + N.h2) (hb2h2_lt : N.b2 + N.h2 < 1)
    (hpos : 0 < -N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1)
    (hg34 : ⟪x 3 - x 6, x 4 - x 6⟫ ≤ 0)
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
    (hF1236 : FrontDet (x 1) (x 3) (x 2) (x 6) (x 1 - x 4))
    (h012 : 0 < N.f012.f (x 3 + N.u124_346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u124_346 x) - N.f015.f (x 3) < 0)
    (h023 : 0 < N.f023.f (x 3 + N.u124_346 x) - N.f023.f (x 3))
    (h035 : 0 < N.f035.f (x 3 + N.u124_346 x) - N.f035.f (x 3))
    (hnf : ¬ Minimality.H29.LexAny29 (s0x_fac29 N.facets)) : False := by
  have hd1 := d1_row_neg N hb2h2 hg34
  have hz4_pos : 0 < ⟪x 4 - x 6, N.u124_346 x⟫ := by
    have h64 : x 6 - x 4 = -(x 4 - x 6) := by abel
    rw [h64, inner_neg_left] at hd1
    linarith
  have hw32_36 : 0 ≤ ⟪x 3 - x 2, x 1 - x 4⟫ ∧ 0 ≤ ⟪x 3 - x 6, x 1 - x 4⟫ := by
    by_cases h2365 : ⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧
        ⟪x 2 - x 6, x 1 - x 4⟫ ≤ ⟪x 5 - x 6, x 1 - x 4⟫ ∧
        (0 : ℝ) ≤ ⟪x 3 - x 6, x 1 - x 4⟫ ∧ (0 : ℝ) ≤ ⟪x 5 - x 6, x 1 - x 4⟫
    · rw [show x 3 - x 2 = (x 3 - x 6) - (x 2 - x 6) by abel, inner_sub_left]
      exact ⟨by linarith [h2365.1], h2365.2.2.1⟩
    · by_contra hnot
      apply hnf
      refine lexAny29_W14x5 N (by linarith) hdG4 hA hF1235 hF1265 hF1365 hF2365
        hM1235 hM1265 hM1365 h2365 hF1236 ?_
      rintro ⟨-, h23, -, h03⟩
      apply hnot
      rw [show x 3 - x 2 = (x 3 - x 6) - (x 2 - x 6) by abel, inner_sub_left]
      exact ⟨by linarith, h03⟩
  have hz5_nonneg : 0 ≤ ⟪x 5 - x 6, N.u124_346 x⟫ := by
    by_contra hneg
    push Not at hneg
    apply hnf
    have hA0123 : GenQuad.LexClause (x 4) (x 5) (x 1) (x 6) (N.u124_346 x) (x 5 - x 4) 0 :=
      GenQuad.lexClause_of_notM (by
        rintro ⟨-, h2, -, -⟩
        rw [inner_sub_left] at hz4_pos
        linarith)
    have hB0123 : GenQuad.LexClause (x 1) (x 6) (x 4) (x 5) (N.u124_346 x) (x 5 - x 4) 0 :=
      GenQuad.lexClause_of_notM (by
        rintro ⟨-, -, -, h4⟩
        rw [inner_sub_left] at hneg
        linarith)
    exact lexAny29_F124xF346_clauses N ht hb2h2 hpos h012 h015 h023 h035 hA0123 hB0123
  have hid := d3_identity N ht
  have h14 : 0 < ⟪x 1 - x 4, x 1 - x 4⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have hs := N.hs
  have hb2 := N.hb2
  have t1 : 0 ≤ N.s * (N.b2 + N.h2) * ⟪x 3 - x 2, x 1 - x 4⟫ :=
    mul_nonneg (mul_nonneg hs.le hb2h2.le) hw32_36.1
  have t2 : 0 ≤ (-N.b2 * N.s) * ⟪x 3 - x 6, x 1 - x 4⟫ :=
    mul_nonneg (mul_nonneg (neg_nonneg.mpr hb2.le) hs.le) hw32_36.2
  have t3 : 0 ≤ (1 - N.b2 - N.h2) * ⟪x 5 - x 6, N.u124_346 x⟫ :=
    mul_nonneg (by linarith) hz5_nonneg
  have hrhs : 0 < N.s * (N.b2 + N.h2) * (-N.a2 + N.b2 * N.s - N.b2 - N.h2 + 1) *
      ⟪x 1 - x 4, x 1 - x 4⟫ :=
    mul_pos (mul_pos (mul_pos hs hb2h2) hpos) h14
  linarith

end Minimality.NF29
