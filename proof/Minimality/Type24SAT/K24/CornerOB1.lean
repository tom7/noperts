module

public import Minimality.Type24SAT.Tie.KDec
public import Minimality.Type29SAT.Mir

@[expose] public section

/-!
# Type 24, off the obtuse corner `OB1`: the class clause for `¬OB1` and the mirror

`OB1` says that all three face angles at vertex `1` (faces `012`, `016`, `126`) are non-acute.  Its negation says that one
of them is acute, which is the clause `clauseOB1` of the SAT cores (edges `01 = 0`, `12 = 6`, `16 = 10`, the views
`x0 - x1`, `x1 - x2`, `x1 - x6`; an acute angle at `1` between `a` and `b` is `⟪x1 - xa, x1 - xb⟫ > 0`, the literal `tp`, or
`⟪x_a - x1, x_1 - x_b⟫ < 0`, the literal `tq`).  `¬OB1` is invariant under the mirror.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

variable {x : Fin 7 → ℝ³}

/-- **The obtuse corner `OB1`**: all three face angles at vertex `1` are non-acute. -/
def OB1 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0

open V W in
/-- The OB1 clause: some face angle at vertex `1` is acute (`0 = d01`, `6 = d12`, `10 = d16`). -/
def clauseOB1 : List LitW :=
  [(true, base (tq 0 6)), (true, base (tq 0 10)), (true, base (tp 6 10))]

/-- The OB1 clause holds when one face angle at vertex `1` is acute. -/
theorem clauseOB1_true (F : S0xFac 9 s0x_S24 x) (hO : ¬ OB1 x) : HoldsW (rhoW (geoF F)) clauseOB1 := by
  have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  have v0 : (geoF F).vv 0 = x 0 - x 1 := by simp [H24.SAT.Geo.vv, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e0, e1]
  have v6 : (geoF F).vv 6 = x 1 - x 2 := by simp [H24.SAT.Geo.vv, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e1, e2]
  have v10 : (geoF F).vv 10 = x 1 - x 6 := by simp [H24.SAT.Geo.vv, H24.SAT.Geo.dv, H24.SAT.EA, H24.SAT.EB, H24.SAT.edges, e1, e6]
  unfold OB1 at hO
  simp only [not_and_or, not_le] at hO
  have n6 : x 1 - x 2 = -(x 2 - x 1) := by abel
  have n10 : x 1 - x 6 = -(x 6 - x 1) := by abel
  rcases hO with h | h | h
  · have h' : ⟪x 0 - x 1, x 1 - x 2⟫ < 0 := by rw [n6, inner_neg_right]; linarith
    exact ⟨_, List.mem_cons_self .., by simp [evalW, rhoW_base, H24.SAT.rho, v0, v6, h']⟩
  · have h' : ⟪x 0 - x 1, x 1 - x 6⟫ < 0 := by rw [n10, inner_neg_right]; linarith
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
      simp [evalW, rhoW_base, H24.SAT.rho, v0, v10, h']⟩
  · have h' : 0 < ⟪x 1 - x 2, x 1 - x 6⟫ := by rw [n6, n10, inner_neg_left, inner_neg_right]; linarith
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by
      simp [evalW, rhoW_base, H24.SAT.rho, v6, v10, h']⟩

/-- `¬OB1` is invariant under the mirror. -/
theorem ob1_mir (hO : ¬ OB1 x) : ¬ OB1 (fun i => mir (x i)) := by
  intro h
  apply hO
  obtain ⟨z1, z2, z3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [← mir_sub, mir_inner] at z1 z2 z3 <;> assumption

end Minimality.H24K.SAT
