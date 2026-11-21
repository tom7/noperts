module

public import Minimality.Type24SAT.Tie.TDec

@[expose] public section

/-!
# L24T, T7: the top theorem for a tie-file core (copy of Type29SAT.Top.case_of_unsat over `W`)

`CoreUnsat rows` is the existing statement about the numbered clauses (it only mentions the packed rows).  If it holds, and
every row passes `rowW` (names `chunks : List (List W)`, class literals `U`), then every type 24 shape of the chirality
`Bq 0 1 2 6 < 0` whose real data satisfy the class literals is Rupert.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

open Minimality.T24.SAT (s0x_S24)

namespace Minimality.H24T.SAT
open Minimality.H24.SAT Minimality.H29.SAT

variable {x : Fin 7 → ℝ³}

/-- A clause that holds under `rhoW g` gives the numbered-clause condition for the assignment `i -> rhoW g` of the name. -/
theorem code_of_holdsW (chunks : List (List W)) (g : Geo) (n : Nat)
    (h : HoldsW (rhoW g) ((decRow n).2.2.map (litOfCW chunks))) :
    ∃ c ∈ (decRow n).2.2, ((c % 2 == 0) == evalW (rhoW g) (nmOfW chunks (c / 2))) = true := by
  obtain ⟨l, hl, hev⟩ := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  refine ⟨c, hc, ?_⟩
  have : evalW (rhoW g) (litOfCW chunks c) = ((c % 2 == 0) == evalW (rhoW g) (nmOfW chunks (c / 2))) := by
    unfold litOfCW
    by_cases hc2 : (c % 2 == 0) = true
    · simp [hc2]
    · have : (c % 2 == 0) = false := by simpa using hc2
      simp [this, evalW_neg]
  rw [this] at hev
  exact hev


end Minimality.H24T.SAT
