module

public import Minimality.Type29TSAT.TDec

@[expose] public section

/-!
# L29T, T7: the top theorem for a tie-file core (copy of Type29SAT.Top.case_of_unsat over `W`)

`CoreUnsat rows` is the existing statement about the numbered clauses (it only mentions the packed rows).  If it holds, and
every row passes `rowW` (names `chunks : List (List W)`, class literals `U`), then every type 29 shape of the chirality
`0 < [0123]` whose real data satisfy the class literals is Rupert.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29T.SAT
open Minimality.H29.SAT

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

/-- **Top theorem for a tie-file core.**  If the numbered clauses are unsatisfiable and every row passes its check, every
type 29 shape of the chirality `0 < [0123]` that satisfies the class literals `U` is Rupert. -/
theorem caseW_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U : List LitW)
    (hA : CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowW U chunks n = true)
    (F : S0xFac 9 s0x_S29 x) (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n (rowWc_holds U F (inj_of_fac F) hNR hG hU (hall ch hch n hn))

end Minimality.H29T.SAT
