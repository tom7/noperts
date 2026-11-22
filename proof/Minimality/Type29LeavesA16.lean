module

public import Minimality.Type29Leaves

@[expose] public section

/-!
# Type 29: region leaves from `A16-REFEREE`

Formalizes the refereed A16 leaves (nopert229 out/bottleneck/p29/sat/k1c/A16-REFEREE.md, section 7) on the K1a
dominant cell, each a `LexAny29` leaf conditional on a linear region in the depths:
1. `NF29.lexAny29_U023Qp`: 5-rim `![0, 2, 4, 6, 5]` at `b = u23Q`, `d1 = x 3 - x 6`, for `1 ≤ h2`, in the two
   regimes `0 > z4 > z5` / `0 > z5 > z4` with their valley conditions;
2. `NF29.lexAny29_U3524`: 4-rim `![0, 1, 4, 3]` at `b = u35_24` (front pair `front3524`), outside `M_{35,24}`;
3. `NF29.u2346_eq`, `NF29.lexAny29_U2346`: the referee's U2346' (4-rim `![0, 1, 4, 3]` at `u2346`, front pair as a
   hypothesis), outside `M_{23,46}`;
4. `NF29.lexAny29_W14t1`: 5-rim `![1, 2, 3, 6, 5]` at `b = x 1 - x 4` for `t = 1`, under `z2 < z1`, `z3 < 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.LexCell Minimality.H21

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

/-! ## U023Qp -/
/-- 5-rim, 6 at index 3 the unique peak; both regimes. -/
theorem rob5_u023 (z e f : ZMod 5 → ℝ)
    (h : (z 2 < z 3 ∧ z 4 < z 2 ∧ z 1 < z 2 ∧ z 0 < z 2 ∧ (z 0 < z 1 ∨ z 0 < z 4)) ∨
         (z 4 < z 3 ∧ z 2 < z 4 ∧ z 0 < z 4 ∧ z 1 < z 4 ∧ (z 1 < z 0 ∨ z 1 < z 2))) :
    RobUniLex (fun i => (z i, e i, f i)) := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl]
  all_goals
    rcases h with ⟨h1, h2, h3, h4, h5 | h5⟩ | ⟨h1, h2, h3, h4, h5 | h5⟩ <;>
    first
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

/-- `D234` (positive by `d234`). -/
noncomputable def D234 (N : NF29 x) : ℝ := N.b2 * N.s + (1 - N.h2 - N.a2) * N.t - N.b2

local macro "u023_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG, dG4, D02, DG4, DG5, D023, E35, P4, P5, D234,
      f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def u023_c : ZMod 5 → Fin 7 := ![0, 2, 4, 6, 5]
private def u023_U : Finset (Fin 9) := {2, 3, 6, 7, 8}
private def u023_Dn : Finset (Fin 9) := {0, 1, 4, 5}

private theorem u023_c_inj : Function.Injective u023_c := by decide
private theorem u023_cyc : S0xCycUD s0x_S29 u023_c u023_U u023_Dn := by decide

theorem lexAny29_U023Qp (N : NF29 x)
    (hdG : N.dG < 0) (hdG4 : 0 < N.dG4) (hh0 : N.h0 < 1) (hE35 : N.E35 < 0)
    (hK : 0 < (-N.dG) * N.P5 + N.dG4 * N.P4) (hh2 : 1 ≤ N.h2)
    (h4 : 0 < N.D023 - N.DG5) (h5 : 0 < N.DG4 - N.D023)
    (hreg : (⟪x 4 - x 6, N.u23Q x⟫ < 0 ∧ ⟪x 5 - x 6, N.u23Q x⟫ < ⟪x 4 - x 6, N.u23Q x⟫ ∧
              ⟪x 2 - x 6, N.u23Q x⟫ < ⟪x 4 - x 6, N.u23Q x⟫ ∧
              ⟪x 0 - x 6, N.u23Q x⟫ < ⟪x 4 - x 6, N.u23Q x⟫ ∧
              (⟪x 0 - x 6, N.u23Q x⟫ < ⟪x 2 - x 6, N.u23Q x⟫ ∨
               ⟪x 0 - x 6, N.u23Q x⟫ < ⟪x 5 - x 6, N.u23Q x⟫)) ∨
            (⟪x 5 - x 6, N.u23Q x⟫ < 0 ∧ ⟪x 4 - x 6, N.u23Q x⟫ < ⟪x 5 - x 6, N.u23Q x⟫ ∧
              ⟪x 0 - x 6, N.u23Q x⟫ < ⟪x 5 - x 6, N.u23Q x⟫ ∧
              ⟪x 2 - x 6, N.u23Q x⟫ < ⟪x 5 - x 6, N.u23Q x⟫ ∧
              (⟪x 2 - x 6, N.u23Q x⟫ < ⟪x 0 - x 6, N.u23Q x⟫ ∨
               ⟪x 2 - x 6, N.u23Q x⟫ < ⟪x 4 - x 6, N.u23Q x⟫))) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := u023_c
  let U := u023_U
  let Dn := u023_Dn
  let b : ℝ³ := N.u23Q x
  let d1 : ℝ³ := x 3 - x 6
  have hc_inj : Function.Injective c := u023_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := u023_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := by
    intro t
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 6) := fun t => (F.hN t (x 3) (x 6)).symm
  have e3_023 : N.f023.f (x 3) - N.f023.f (x 6) = N.D023 * N.D ^ 2 := by u023_fac_val N
  have e3_234 : N.f234.f (x 3) - N.f234.f (x 6) = N.D234 * N.D ^ 2 := by u023_fac_val N
  have e3_1456 : N.f1456.f (x 3) - N.f1456.f (x 6) = -N.D ^ 2 := by u023_fac_val N
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
  have hRob : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), 0⟫)) := by
    have hreg' := hreg
    simp only [inner_sub_left] at hreg'
    refine rob5_u023 (fun i => ⟪x (c i), b⟫) (fun i => ⟪x (c i), d1⟫) (fun i => ⟪x (c i), 0⟫) ?_
    simp only [c, u023_c, Matrix.cons_val]
    show (_ < _ ∧ _) ∨ _
    rcases hreg' with ⟨r1, r2, r3, r4, r5 | r5⟩ | ⟨r1, r2, r3, r4, r5 | r5⟩
    · left; refine ⟨?_, ?_, ?_, ?_, Or.inl ?_⟩ <;> linarith
    · left; refine ⟨?_, ?_, ?_, ?_, Or.inr ?_⟩ <;> linarith
    · right; refine ⟨?_, ?_, ?_, ?_, Or.inl ?_⟩ <;> linarith
    · right; refine ⟨?_, ?_, ?_, ?_, Or.inr ?_⟩ <;> linarith
  exact ⟨5, inferInstance, c, U, Dn, b, d1, 0, by norm_num, hc_inj, hcyc, hU, hD, hRob⟩

/-! ## U3524 -/
local macro "u35_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [u35_24, del0, E35, DG4, D02, dG4, f012, f015, f023, f035, f124, f1456, f234,
      f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def u35_c : ZMod 4 → Fin 7 := ![0, 1, 4, 3]
private def u35_U : Finset (Fin 9) := {0, 2, 4, 6}
private def u35_Dn : Finset (Fin 9) := {1, 3, 5, 7, 8}

private theorem u35_c_inj : Function.Injective u35_c := by decide
private theorem u35_cyc : S0xCycUD s0x_S29 u35_c u35_U u35_Dn := by decide

theorem lexAny29_U3524 (N : NF29 x)
    (hb0 : 0 < N.b0) (h : N.del2 * (1 - N.h0) < N.DG4)
    (h012 : 0 < N.f012.f (x 3 + N.u35_24 x) - N.f012.f (x 3))
    (h124 : 0 < N.f124.f (x 3 + N.u35_24 x) - N.f124.f (x 3))
    (h015 : N.f015.f (x 3 + N.u35_24 x) - N.f015.f (x 3) < 0)
    (h023 : 0 < N.f023.f (x 3 + N.u35_24 x) - N.f023.f (x 3))
    (h346 : N.f346.f (x 3 + N.u35_24 x) - N.f346.f (x 3) < 0)
    (h356 : N.f356.f (x 3 + N.u35_24 x) - N.f356.f (x 3) < 0)
    (hM : ¬ (⟪x 0, N.u35_24 x⟫ ≤ ⟪x 1, N.u35_24 x⟫ ∧ ⟪x 4, N.u35_24 x⟫ ≤ ⟪x 1, N.u35_24 x⟫ ∧
             ⟪x 0, N.u35_24 x⟫ ≤ ⟪x 3, N.u35_24 x⟫ ∧ ⟪x 4, N.u35_24 x⟫ ≤ ⟪x 3, N.u35_24 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := u35_c
  let U := u35_U
  let Dn := u35_Dn
  let b : ℝ³ := N.u35_24 x
  let d1 : ℝ³ := (2 * (-N.a0)) • (x 4 - x 3) + N.del0 • (x 3 - x 1)
  have hc_inj : Function.Injective c := u35_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := u35_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hdel0 : 0 < N.del0 := by dsimp only [del0]; linarith [N.t345_0]
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := by
    intro t
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hbv : ∀ t, ⟪F.N t, b⟫ = N.del0 * (F.f t (x 2) - F.f t (x 3)) +
      N.E35 * (F.f t (x 4) - F.f t (x 3)) := by
    intro t
    dsimp only [b, u35_24]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN t (x 2) (x 3), ← F.hN t (x 4) (x 3)]
  have hnd : ∀ t, ⟪F.N t, d1⟫ = (2 * (-N.a0)) * (F.f t (x 4) - F.f t (x 3)) +
      N.del0 * (F.f t (x 3) - F.f t (x 1)) := by
    intro t
    dsimp only [d1]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← F.hN t (x 4) (x 3), ← F.hN t (x 3) (x 1)]
  have h1456 : N.f1456.f (x 3 + N.u35_24 x) - N.f1456.f (x 3) < 0 := by
    rw [fhat_1456_u35]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr h)) hD2
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    fin_cases t
    · exact Or.inl ((hnb 0).symm ▸ h012)
    · exact absurd ht_mem (by decide)
    · exact Or.inl ((hnb 2).symm ▸ h023)
    · exact absurd ht_mem (by decide)
    · exact Or.inl ((hnb 4).symm ▸ h124)
    · exact absurd ht_mem (by decide)
    · have hb0' : ⟪F.N 6, b⟫ = 0 := by
        rw [hbv 6]
        change N.del0 * (N.f234.f (x 2) - N.f234.f (x 3)) +
          N.E35 * (N.f234.f (x 4) - N.f234.f (x 3)) = 0
        u35_fac_val N
      have hd1v : (2 * (-N.a0)) * (N.f234.f (x 4) - N.f234.f (x 3)) +
          N.del0 * (N.f234.f (x 3) - N.f234.f (x 1)) = N.del0 * (-N.b2) * N.D ^ 2 := by
        u35_fac_val N
      refine Or.inr ⟨hb0', Or.inl ?_⟩
      show 0 < ⟪F.N 6, d1⟫
      rw [hnd 6]
      change 0 < (2 * (-N.a0)) * (N.f234.f (x 4) - N.f234.f (x 3)) +
          N.del0 * (N.f234.f (x 3) - N.f234.f (x 1))
      rw [hd1v]
      exact mul_pos (mul_pos hdel0 (neg_pos.mpr N.hb2)) hD2
    all_goals exact absurd ht_mem (by decide)
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, 0⟫) := by
    intro t ht_mem
    fin_cases t
    · exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr ((hnb 1) ▸ h015))
    · exact absurd ht_mem (by decide)
    · have hb0' : ⟪F.N 3, b⟫ = 0 := by
        rw [hbv 3]
        change N.del0 * (N.f035.f (x 2) - N.f035.f (x 3)) +
          N.E35 * (N.f035.f (x 4) - N.f035.f (x 3)) = 0
        u35_fac_val N
      have hd1v : (2 * (-N.a0)) * (N.f035.f (x 4) - N.f035.f (x 3)) +
          N.del0 * (N.f035.f (x 3) - N.f035.f (x 1)) = N.a0 * N.del0 * N.D ^ 2 := by
        u35_fac_val N
      refine Or.inr ⟨?_, Or.inl ?_⟩
      · show -⟪F.N 3, b⟫ = 0
        rw [hb0', neg_zero]
      · show 0 < -⟪F.N 3, d1⟫
        rw [hnd 3]
        change 0 < -((2 * (-N.a0)) * (N.f035.f (x 4) - N.f035.f (x 3)) +
          N.del0 * (N.f035.f (x 3) - N.f035.f (x 1)))
        rw [hd1v]
        have : N.a0 * N.del0 * N.D ^ 2 < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos N.ha0 hdel0) hD2
        linarith
    · exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr ((hnb 5) ▸ h1456))
    · exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr ((hnb 7) ▸ h346))
    · exact Or.inl (neg_pos.mpr ((hnb 8) ▸ h356))
  have hRob : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), 0⟫)) := by
    obtain ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he0, hvec⟩ := front3524 N hb0 h
    have hb_ne : b ≠ 0 := by
      intro h0
      have : ⟪F.N 0, b⟫ = 0 := by rw [h0, inner_zero_right]
      rw [hnb 0] at this
      change N.f012.f (x 3 + N.u35_24 x) - N.f012.f (x 3) = 0 at this
      linarith
    have hb_sq : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb_ne
    have hz_id :
        lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ =
          mu * ⟪x 0, b⟫ + (1 - mu) * ⟪x 4, b⟫ + eta * ⟪b, b⟫ := by
      have h := congrArg (fun v => ⟪v, b⟫) hvec
      simp only [inner_add_left, inner_smul_left, conj_trivial] at h
      exact h
    have hex_pos : ∃ p ∈ Minimality.RimCell.diagPairs,
        LexLt3 (⟪x (c p.1), b⟫, ⟪x (c p.1), d1⟫, ⟪x (c p.1), 0⟫)
               (⟪x (c p.2), b⟫, ⟪x (c p.2), d1⟫, ⟪x (c p.2), 0⟫) := by
      by_contra hnone
      simp only [Minimality.RimCell.diagPairs, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and] at hnone
      have hle : ∀ i ∈ ({0, 2} : Finset (ZMod 4)), ∀ j ∈ ({1, 3} : Finset (ZMod 4)),
          ⟪x (c j), b⟫ ≤ ⟪x (c i), b⟫ := by
        intro i hi j hj
        by_contra hgt
        push Not at hgt
        exact hnone (i, j) ⟨by simpa using hi, by simpa using hj⟩ (Or.inl (sub_pos.mpr hgt))
      have h10 : ⟪x 1, b⟫ ≤ ⟪x 0, b⟫ := hle 0 (by simp) 1 (by simp)
      have h14 : ⟪x 1, b⟫ ≤ ⟪x 4, b⟫ := hle 2 (by simp) 1 (by simp)
      have h30 : ⟪x 3, b⟫ ≤ ⟪x 0, b⟫ := hle 0 (by simp) 3 (by simp)
      have h34 : ⟪x 3, b⟫ ≤ ⟪x 4, b⟫ := hle 2 (by simp) 3 (by simp)
      have hA : lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ ≤ mu * ⟪x 0, b⟫ + (1 - mu) * ⟪x 4, b⟫ := by
        have e1 : lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ ≤ mu * ⟪x 0, b⟫ + (1 - mu) * ⟪x 4, b⟫ := by
          nlinarith [mul_nonneg hl0.le (sub_nonneg.mpr h10), mul_nonneg hl0.le (sub_nonneg.mpr h14),
            mul_nonneg (sub_nonneg.mpr hl1.le) (sub_nonneg.mpr h30),
            mul_nonneg (sub_nonneg.mpr hl1.le) (sub_nonneg.mpr h34),
            mul_nonneg hm0.le (sub_nonneg.mpr h10), mul_nonneg (sub_nonneg.mpr hm1.le) (sub_nonneg.mpr h14),
            mul_nonneg hm0.le (sub_nonneg.mpr h30), mul_nonneg (sub_nonneg.mpr hm1.le) (sub_nonneg.mpr h34)]
        exact e1
      linarith [mul_pos he0 hb_sq]
    have hex_neg : ∃ q ∈ Minimality.RimCell.diagPairs,
        LexLt3 (⟪x (c q.2), b⟫, ⟪x (c q.2), d1⟫, ⟪x (c q.2), 0⟫)
               (⟪x (c q.1), b⟫, ⟪x (c q.1), d1⟫, ⟪x (c q.1), 0⟫) := by
      by_contra hnone
      simp only [Minimality.RimCell.diagPairs, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and] at hnone
      have hle : ∀ i ∈ ({0, 2} : Finset (ZMod 4)), ∀ j ∈ ({1, 3} : Finset (ZMod 4)),
          ⟪x (c i), b⟫ ≤ ⟪x (c j), b⟫ := by
        intro i hi j hj
        by_contra hgt
        push Not at hgt
        exact hnone (i, j) ⟨by simpa using hi, by simpa using hj⟩ (Or.inl (sub_pos.mpr hgt))
      exact hM ⟨hle 0 (by simp) 1 (by simp), hle 2 (by simp) 1 (by simp),
                hle 0 (by simp) 3 (by simp), hle 2 (by simp) 3 (by simp)⟩
    exact robUniLex_four_of_mixed hex_pos hex_neg
  exact ⟨4, inferInstance, c, U, Dn, b, d1, 0, le_rfl, hc_inj, hcyc, hU, hD, hRob⟩

/-! ## U2346 -/
noncomputable def p0346 (N : NF29 x) : ℝ := N.b0 * (N.s - 1) + (1 - N.a0 - N.h0) * N.t

noncomputable def u2346 (N : NF29 x) (x : Fin 7 → ℝ³) : ℝ³ :=
  (N.DG4 - N.D023) • (x 3 - x 6) + N.D023 • (x 4 - x 6)

theorem u2346_eq (N : NF29 x) :
    (N.DG4 - N.D023) • (x 3 - x 6) + N.D023 • (x 4 - x 6) =
      N.p0346 • (x 2 - x 3) - N.D234 • (x 0 - x 3) := by
  dsimp only [DG4, D02, dG4, D023, dG, p0346, D234]
  nf29_vec N


local macro "u2346_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG4, f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def u2346_c : ZMod 4 → Fin 7 := ![0, 1, 4, 3]
private def u2346_U : Finset (Fin 9) := {0, 2, 4, 6}
private def u2346_Dn : Finset (Fin 9) := {1, 3, 5, 7, 8}

private theorem u2346_c_inj : Function.Injective u2346_c := by decide
private theorem u2346_cyc : S0xCycUD s0x_S29 u2346_c u2346_U u2346_Dn := by decide

theorem lexAny29_U2346 (N : NF29 x) (hdG4 : 0 < N.dG4)
    (h012 : 0 < N.f012.f (x 3 + N.u2346 x) - N.f012.f (x 3))
    (h015 : N.f015.f (x 3 + N.u2346 x) - N.f015.f (x 3) < 0)
    (h035 : N.f035.f (x 3 + N.u2346 x) - N.f035.f (x 3) < 0)
    (h124 : 0 < N.f124.f (x 3 + N.u2346 x) - N.f124.f (x 3))
    (h1456 : N.f1456.f (x 3 + N.u2346 x) - N.f1456.f (x 3) < 0)
    (h234 : 0 < N.f234.f (x 3 + N.u2346 x) - N.f234.f (x 3))
    (h356 : N.f356.f (x 3 + N.u2346 x) - N.f356.f (x 3) < 0)
    (lam mu eta : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hmu0 : 0 < mu) (hmu1 : mu < 1)
    (heta : 0 < eta)
    (hfront : lam • x 1 + (1 - lam) • x 3 = mu • x 0 + (1 - mu) • x 4 + eta • N.u2346 x)
    (hM : ¬ (⟪x 0, N.u2346 x⟫ ≤ ⟪x 1, N.u2346 x⟫ ∧ ⟪x 4, N.u2346 x⟫ ≤ ⟪x 1, N.u2346 x⟫ ∧
             ⟪x 0, N.u2346 x⟫ ≤ ⟪x 3, N.u2346 x⟫ ∧ ⟪x 4, N.u2346 x⟫ ≤ ⟪x 3, N.u2346 x⟫)) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := u2346_c
  let U := u2346_U
  let Dn := u2346_Dn
  let b : ℝ³ := N.u2346 x
  let d1 : ℝ³ := x 1 - x 4
  have hc_inj : Function.Injective c := u2346_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := u2346_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hb_eq : b = N.p0346 • (x 2 - x 3) - N.D234 • (x 0 - x 3) := u2346_eq N
  have hz023 : N.f023.f (x 3 + b) - N.f023.f (x 3) = 0 := by
    have h2 : N.f023.f (x 2) - N.f023.f (x 3) = 0 := by u2346_fac_val N
    have h0 : N.f023.f (x 0) - N.f023.f (x 3) = 0 := by u2346_fac_val N
    rw [N.f023.hN (x 3 + b) (x 3), add_sub_cancel_left, hb_eq, inner_sub_right,
      real_inner_smul_right, real_inner_smul_right, ← N.f023.hN (x 2) (x 3),
      ← N.f023.hN (x 0) (x 3), h2, h0]
    simp
  have hz346 : N.f346.f (x 3 + b) - N.f346.f (x 3) = 0 := by
    have h4 : N.f346.f (x 4) - N.f346.f (x 6) = 0 := by u2346_fac_val N
    have h3 : N.f346.f (x 3) - N.f346.f (x 6) = 0 := by u2346_fac_val N
    rw [N.f346.hN (x 3 + b) (x 3), add_sub_cancel_left]
    dsimp only [b, u2346]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ← N.f346.hN (x 3) (x 6), ← N.f346.hN (x 4) (x 6), h3, h4]
    simp
  have hd023 : N.f023.f (x 1) - N.f023.f (x 4) = N.dG4 * N.D ^ 2 := by u2346_fac_val N
  have hd346 : N.f346.f (x 1) - N.f346.f (x 4) = -N.t * N.D ^ 2 := by u2346_fac_val N
  have hnb : ∀ t, ⟪F.N t, b⟫ = F.f t (x 3 + b) - F.f t (x 3) := fun t => by
    rw [F.hN t (x 3 + b) (x 3), add_sub_cancel_left]
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    rw [hnb t]
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    rw [hnd1]
    fin_cases t
    · exact Or.inl h012
    · exact absurd ht_mem (by decide)
    · refine Or.inr ⟨hz023, Or.inl ?_⟩
      change 0 < N.f023.f (x 1) - N.f023.f (x 4)
      rw [hd023]; exact mul_pos hdG4 hD2
    · exact absurd ht_mem (by decide)
    · exact Or.inl h124
    · exact absurd ht_mem (by decide)
    · exact Or.inl h234
    all_goals exact absurd ht_mem (by decide)
  have hD : ∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, 0⟫) := by
    intro t ht_mem
    rw [hnb t]
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    rw [hnd1]
    fin_cases t
    · exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr h015)
    · exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr h035)
    · exact absurd ht_mem (by decide)
    · exact Or.inl (neg_pos.mpr h1456)
    · exact absurd ht_mem (by decide)
    · refine Or.inr ⟨by change -(N.f346.f (x 3 + b) - N.f346.f (x 3)) = 0; rw [hz346, neg_zero],
        Or.inl ?_⟩
      change 0 < -(N.f346.f (x 1) - N.f346.f (x 4))
      rw [hd346, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.ht hD2
    · exact Or.inl (neg_pos.mpr h356)
  have hRob : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), 0⟫)) := by
    have hb_ne : b ≠ 0 := by
      intro h0
      have h5 : ⟪F.N 5, b⟫ < 0 := by rw [hnb 5]; exact h1456
      rw [h0, inner_zero_right] at h5
      exact lt_irrefl _ h5
    have hb_sq : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb_ne
    have hz_id :
        lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ =
          mu * ⟪x 0, b⟫ + (1 - mu) * ⟪x 4, b⟫ + eta * ⟪b, b⟫ := by
      have h := congrArg (fun v => ⟪v, b⟫) hfront
      simp only [inner_add_left, inner_smul_left, conj_trivial] at h
      exact h
    have hex_pos : ∃ p ∈ Minimality.RimCell.diagPairs,
        LexLt3 (⟪x (c p.1), b⟫, ⟪x (c p.1), d1⟫, ⟪x (c p.1), 0⟫)
               (⟪x (c p.2), b⟫, ⟪x (c p.2), d1⟫, ⟪x (c p.2), 0⟫) := by
      by_contra hnone
      simp only [Minimality.RimCell.diagPairs, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and] at hnone
      have hle : ∀ i ∈ ({0, 2} : Finset (ZMod 4)), ∀ j ∈ ({1, 3} : Finset (ZMod 4)),
          ⟪x (c j), b⟫ ≤ ⟪x (c i), b⟫ := by
        intro i hi j hj
        by_contra hgt
        push Not at hgt
        exact hnone (i, j) ⟨by simpa using hi, by simpa using hj⟩ (Or.inl (sub_pos.mpr hgt))
      have h01 : ⟪x 1, b⟫ ≤ ⟪x 0, b⟫ := hle 0 (by simp) 1 (by simp)
      have h03 : ⟪x 3, b⟫ ≤ ⟪x 0, b⟫ := hle 0 (by simp) 3 (by simp)
      have h41 : ⟪x 1, b⟫ ≤ ⟪x 4, b⟫ := hle 2 (by simp) 1 (by simp)
      have h43 : ⟪x 3, b⟫ ≤ ⟪x 4, b⟫ := hle 2 (by simp) 3 (by simp)
      have hL : lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ ≤
          mu * ⟪x 0, b⟫ + (1 - mu) * ⟪x 4, b⟫ := by
        have e1 : lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ ≤ ⟪x 0, b⟫ := by nlinarith
        have e2 : lam * ⟪x 1, b⟫ + (1 - lam) * ⟪x 3, b⟫ ≤ ⟪x 4, b⟫ := by nlinarith
        nlinarith
      linarith [mul_pos heta hb_sq]
    have hex_neg : ∃ q ∈ Minimality.RimCell.diagPairs,
        LexLt3 (⟪x (c q.2), b⟫, ⟪x (c q.2), d1⟫, ⟪x (c q.2), 0⟫)
               (⟪x (c q.1), b⟫, ⟪x (c q.1), d1⟫, ⟪x (c q.1), 0⟫) := by
      by_contra hnone
      simp only [Minimality.RimCell.diagPairs, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, not_exists, not_and] at hnone
      have hle : ∀ i ∈ ({0, 2} : Finset (ZMod 4)), ∀ j ∈ ({1, 3} : Finset (ZMod 4)),
          ⟪x (c i), b⟫ ≤ ⟪x (c j), b⟫ := by
        intro i hi j hj
        by_contra hgt
        push Not at hgt
        exact hnone (i, j) ⟨by simpa using hi, by simpa using hj⟩ (Or.inl (sub_pos.mpr hgt))
      exact hM ⟨hle 0 (by simp) 1 (by simp), hle 2 (by simp) 1 (by simp),
                hle 0 (by simp) 3 (by simp), hle 2 (by simp) 3 (by simp)⟩
    exact robUniLex_four_of_mixed hex_pos hex_neg
  exact ⟨4, inferInstance, c, U, Dn, b, d1, 0, le_rfl, hc_inj, hcyc, hU, hD, hRob⟩

/-! ## W14t1 -/
local macro "w14t1_fac_val " N:term:max : tactic =>
  `(tactic| (
    dsimp only [dG4, P5, f012, f015, f023, f035, f124, f1456, f234, f346, f356, Face16.ofPoly]
    nf29_simp $N
    simp only [det3c, NF29.D]
    ring))

private def w14t1_c : ZMod 5 → Fin 7 := ![1, 2, 3, 6, 5]
private def w14t1_U : Finset (Fin 9) := {0, 1, 2, 3, 8}
private def w14t1_Dn : Finset (Fin 9) := {4, 5, 6, 7}

private theorem w14t1_c_inj : Function.Injective w14t1_c := by decide
private theorem w14t1_cyc : S0xCycUD s0x_S29 w14t1_c w14t1_U w14t1_Dn := by decide

/-- Five reals around the cycle `1 2 3 6 5`: `z2 < z1`, `z3 < z6 < z5` give `RobUniLex`
already at the first level. -/
private theorem w14t1_rob (z d1 : ZMod 5 → ℝ)
    (h01 : z 1 < z 0) (h23 : z 2 < z 3) (h34 : z 3 < z 4) :
    RobUniLex (fun i => (z i, d1 i, (0 : ℝ))) := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl] <;>
  first
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

theorem lexAny29_W14t1 (N : NF29 x)
    (ht : N.t = 1) (hdG4 : 0 < N.dG4) (hA : 0 < 1 - N.b0 - N.h0)
    (hz21 : ⟪x 2 - x 6, x 1 - x 4⟫ < ⟪x 1 - x 6, x 1 - x 4⟫)
    (hz3 : ⟪x 3 - x 6, x 1 - x 4⟫ < 0) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) := by
  let F := s0x_fac29 N.facets
  let c := w14t1_c
  let U := w14t1_U
  let Dn := w14t1_Dn
  let b : ℝ³ := x 1 - x 4
  let d1 : ℝ³ := x 3 - x 4
  have hc_inj : Function.Injective c := w14t1_c_inj
  have hcyc : S0xCycUD s0x_S29 c U Dn := w14t1_cyc
  have hD2 : 0 < N.D ^ 2 := sq_pos_of_ne_zero N.hD
  have hU : ∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, 0⟫ := by
    intro t ht_mem
    have hnb : ⟪F.N t, b⟫ = F.f t (x 1) - F.f t (x 4) := (F.hN t (x 1) (x 4)).symm
    have hnd1 : ⟪F.N t, d1⟫ = F.f t (x 3) - F.f t (x 4) := (F.hN t (x 3) (x 4)).symm
    rw [hnb, hnd1]
    fin_cases t
    · refine Or.inl ?_
      have hv : N.f012.f (x 1) - N.f012.f (x 4) = N.P5 * N.D ^ 2 := by w14t1_fac_val N
      change 0 < N.f012.f (x 1) - N.f012.f (x 4)
      rw [hv]
      exact mul_pos (by dsimp [P5]; linarith [N.hF4]) hD2
    · refine Or.inl ?_
      have hv : N.f015.f (x 1) - N.f015.f (x 4) = N.h0 * N.D ^ 2 := by w14t1_fac_val N
      change 0 < N.f015.f (x 1) - N.f015.f (x 4)
      rw [hv]
      exact mul_pos N.hh0 hD2
    · refine Or.inl ?_
      have hv : N.f023.f (x 1) - N.f023.f (x 4) = N.dG4 * N.D ^ 2 := by w14t1_fac_val N
      change 0 < N.f023.f (x 1) - N.f023.f (x 4)
      rw [hv]
      exact mul_pos hdG4 hD2
    · refine Or.inl ?_
      have hv : N.f035.f (x 1) - N.f035.f (x 4) = (1 - N.b0 - N.h0) * N.D ^ 2 := by
        w14t1_fac_val N
      change 0 < N.f035.f (x 1) - N.f035.f (x 4)
      rw [hv]
      exact mul_pos hA hD2
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · exact absurd ht_mem (by decide)
    · have hb0 : N.f356.f (x 1) - N.f356.f (x 4) = 0 := by
        have hv : N.f356.f (x 1) - N.f356.f (x 4) = (N.t - 1) * N.D ^ 2 := by w14t1_fac_val N
        rw [hv, ht]; ring
      have hd1v : N.f356.f (x 3) - N.f356.f (x 4) = (N.t - 1 + N.s) * N.D ^ 2 := by
        w14t1_fac_val N
      refine Or.inr ⟨hb0, Or.inl ?_⟩
      change 0 < N.f356.f (x 3) - N.f356.f (x 4)
      rw [hd1v, ht]
      exact mul_pos (by linarith [N.hs]) hD2
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
    · have hb0 : N.f124.f (x 1) - N.f124.f (x 4) = 0 := by w14t1_fac_val N
      have hd1v : N.f124.f (x 3) - N.f124.f (x 4) = N.b2 * N.D ^ 2 := by w14t1_fac_val N
      refine Or.inr ⟨by change -(N.f124.f (x 1) - N.f124.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f124.f (x 3) - N.f124.f (x 4))
      rw [hd1v]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · have hb0 : N.f1456.f (x 1) - N.f1456.f (x 4) = 0 := by w14t1_fac_val N
      have hd1v : N.f1456.f (x 3) - N.f1456.f (x 4) = -N.D ^ 2 := by w14t1_fac_val N
      refine Or.inr ⟨by change -(N.f1456.f (x 1) - N.f1456.f (x 4)) = 0; rw [hb0, neg_zero], Or.inl ?_⟩
      change 0 < -(N.f1456.f (x 3) - N.f1456.f (x 4))
      rw [hd1v, neg_neg]
      exact hD2
    · refine Or.inl ?_
      have hv : N.f234.f (x 1) - N.f234.f (x 4) = N.b2 * N.D ^ 2 := by w14t1_fac_val N
      change 0 < -(N.f234.f (x 1) - N.f234.f (x 4))
      rw [hv]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos N.hb2 hD2)
    · refine Or.inl ?_
      have hv : N.f346.f (x 1) - N.f346.f (x 4) = -N.t * N.D ^ 2 := by w14t1_fac_val N
      change 0 < -(N.f346.f (x 1) - N.f346.f (x 4))
      rw [hv, neg_mul_eq_neg_mul, neg_neg]
      exact mul_pos N.ht hD2
    · exact absurd ht_mem (by decide)
  have hvec : x 5 - x 6 = N.s • b := by
    dsimp only [b]
    nf29_simp N
    rw [ht]
    ext i
    simp only [nfV, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hb_ne : b ≠ 0 := sub_ne_zero.mpr (N.inj.ne (by decide))
  have hb_sq : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb_ne
  have hz5 : 0 < ⟪x 5 - x 6, b⟫ := by
    rw [hvec, inner_smul_left]
    simpa using mul_pos N.hs hb_sq
  have hRob : RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), 0⟫)) := by
    have h := w14t1_rob (fun i => ⟪x (c i), b⟫) (fun i => ⟪x (c i), d1⟫)
      (by
        have := hz21
        simp only [inner_sub_left] at this
        change ⟪x 2, b⟫ < ⟪x 1, b⟫
        linarith)
      (by
        have := hz3
        simp only [inner_sub_left] at this
        change ⟪x 3, b⟫ < ⟪x 6, b⟫
        linarith)
      (by
        have := hz5
        simp only [inner_sub_left] at this
        change ⟪x 6, b⟫ < ⟪x 5, b⟫
        linarith)
    simpa only [inner_zero_right] using h
  exact ⟨5, inferInstance, c, U, Dn, b, d1, 0, by norm_num, hc_inj, hcyc, hU, hD, hRob⟩

end Minimality.NF29
