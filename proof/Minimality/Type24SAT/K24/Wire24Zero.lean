module

public import Minimality.Type24SAT.K24.Wire24
public import Minimality.Type24SAT.K24.FinalZpmmm
public import Minimality.Type24SAT.K24.FinalZpmpp
public import Minimality.Type24SAT.K24.FinalZpppm
public import Minimality.Type24SAT.K24.FinalZpmpm
public import Minimality.Type24SAT.K24.FinalZpppp
public import Minimality.Type24SAT.K24.FinalPzmpp
public import Minimality.Type24SAT.K24.FinalPzpppNotP
public import Minimality.Type24SAT.K24.FinalPzpppPq
public import Minimality.Type24SAT.K24.FinalPpzpp
public import Minimality.Type24SAT.K24.FinalPpzpm
public import Minimality.Type24SAT.K24.FinalPmzpp
public import Minimality.Type24SAT.K24.FinalMpzpp
public import Minimality.Type24SAT.K24.FinalMpzpm
public import Minimality.Type24SAT.K24.FinalPpmzm
public import Minimality.Type24SAT.K24.FinalMpmzmNotP
public import Minimality.Type24SAT.K24.FinalMpmzmPq
public import Minimality.Type24SAT.K24.FinalPpmpzNotP
public import Minimality.Type24SAT.K24.FinalPpmpzPq
public import Minimality.Type24SAT.K24.FinalPpppzNotP
public import Minimality.Type24SAT.K24.FinalPpppzPq
public import Minimality.Type24SAT.K24.FinalMpmpzNotP
public import Minimality.Type24SAT.K24.FinalMpmpzPq
public import Minimality.Type24SAT.K24.FinalZpzpp
public import Minimality.Type24SAT.K24.FinalZpzpm
public import Minimality.Type24SAT.K24.FinalZpmzm
public import Minimality.Type24SAT.K24.FinalZpmpzNotP
public import Minimality.Type24SAT.K24.FinalZpmpzPq
public import Minimality.Type24SAT.K24.FinalZpppzNotP
public import Minimality.Type24SAT.K24.FinalZpppzPq
public import Minimality.Type24SAT.K24.FinalPzzpp
public import Minimality.Type24SAT.K24.FinalPpzpzNotP
public import Minimality.Type24SAT.K24.FinalPpzpzPq
public import Minimality.Type24SAT.K24.FinalMpzpzNotP
public import Minimality.Type24SAT.K24.FinalMpzpzPq
public import Minimality.Type24SAT.K24.FinalZpzpzNotP
public import Minimality.Type24SAT.K24.FinalZpzpzPq

@[expose] public section

/-!
# Type 24: the zero-bracket sub-classes off the obtuse corner, wired

`rupert_or_zres24` applies the sub-class theorems `Minimality.T24.isRupert_offOB1_<cls>[_notP|_Pq]` (via the zero
split `zero_split` of `Wire24`) and the parallel-pair stratum `Minimality.T24.Par.isRupert_par`.  What is left is `ZRes24`:
the open class `mpppz` (not wired).  The three-zero class `Cls3` closes by `isRupert_offOB1_zpzpz_notP` / `_Pq` (its
parallelogram split, as the two-zero classes).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24
open Minimality Minimality.H21 Minimality.T24.SAT

/-- `D` (facet `0345`) is a parallelogram. -/
def ParD (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  det3 (x 0 - x 4) (x 3 - x 5) (F.N 3) = 0 ∧ det3 (x 0 - x 5) (x 3 - x 4) (F.N 3) = 0

/-- Combine the `D` not a parallelogram case (`hnot`), the parallelogram without a parallel facet pair (`hpq`) and the
parallel-pair stratum (`Par.isRupert_par`). -/
theorem par_combine {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {R : Prop}
    (hnot : ¬ ParD x F → IsRupert (univ.image x) ∨ R)
    (hpq : ParD x F → ¬ (⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0) →
      ¬ (⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0) → IsRupert (univ.image x)) :
    IsRupert (univ.image x) ∨ R := by
  by_cases hD : ParD x F
  · left
    by_cases hEG : ⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0
    · exact Par.isRupert_par F hD (Or.inl hEG.1)
    by_cases hCI : ⟪F.N 2, x 3 - x 6⟫ = 0 ∧ ⟪F.N 2, x 4 - x 6⟫ = 0
    · exact Par.isRupert_par F hD (Or.inr hCI.1)
    exact hpq hD hEG hCI
  · exact hnot hD

/-- What the zero-bracket wiring leaves: the open class `mpppz` (not wired: its `Pq` case closes in the SAT runs, its
`notP` case is open). -/
def ZRes24 (x : Fin 7 → ℝ³) : Prop :=
  clsz24 x (some false) (some true) (some true) (some true) none

/-- **The zero-bracket classes off `OB1`**: if some class bracket vanishes (and not `OB1`), the points are Rupert
or `ZRes24` holds (the open class `mpppz`). -/
theorem rupert_or_zres24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hO : ¬ H24K.SAT.OB1 x)
    (h : b1234 x = 0 ∨ b1245 x = 0 ∨ b1356 x = 0 ∨ b1456 x = 0 ∨ b2456 x = 0) :
    IsRupert (univ.image x) ∨ ZRes24 x := by
  rcases zero_split F h with h18 | h8 | h3
  · rcases h18 with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
    · -- zpmmm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpmmm F (by first | exact Or.inl ⟨hc, a1, a2, a3, a4⟩ | exact Or.inr ⟨hc, a1, a2, a3, a4⟩) hO a0)
    · -- zpmpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpmpp F (by first | exact Or.inl ⟨hc, a1, a2, a3, a4⟩ | exact Or.inr ⟨hc, a1, a2, a3, a4⟩) hO a0)
    · -- zpppm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpppm F (by first | exact Or.inl ⟨hc, a1, a2, a3, a4⟩ | exact Or.inr ⟨hc, a1, a2, a3, a4⟩) hO a0)
    · -- zpmpm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpmpm F (by first | exact Or.inl ⟨hc, a1, a2, a3, a4⟩ | exact Or.inr ⟨hc, a1, a2, a3, a4⟩) hO a0)
    · -- zpppp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpppp F (by first | exact Or.inl ⟨hc, a1, a2, a3, a4⟩ | exact Or.inr ⟨hc, a1, a2, a3, a4⟩) hO a0)
    · -- pzmpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_pzmpp F (by first | exact Or.inl ⟨hc, a0, a2, a3, a4⟩ | exact Or.inr ⟨hc, a0, a2, a3, a4⟩) hO a1)
    · -- pzppp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_pzppp_notP F (by first | exact Or.inl ⟨hc, a0, a2, a3, a4⟩ | exact Or.inr ⟨hc, a0, a2, a3, a4⟩) hO a1 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_pzppp_Pq F (by first | exact Or.inl ⟨hc, a0, a2, a3, a4⟩ | exact Or.inr ⟨hc, a0, a2, a3, a4⟩) hO a1 hD hEG hCI)
    · -- ppzpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_ppzpp F (by first | exact Or.inl ⟨hc, a0, a1, a3, a4⟩ | exact Or.inr ⟨hc, a0, a1, a3, a4⟩) hO a2)
    · -- ppzpm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_ppzpm F (by first | exact Or.inl ⟨hc, a0, a1, a3, a4⟩ | exact Or.inr ⟨hc, a0, a1, a3, a4⟩) hO a2)
    · -- pmzpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_pmzpp F (by first | exact Or.inl ⟨hc, a0, a1, a3, a4⟩ | exact Or.inr ⟨hc, a0, a1, a3, a4⟩) hO a2)
    · -- mpzpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_mpzpp F (by first | exact Or.inl ⟨hc, a0, a1, a3, a4⟩ | exact Or.inr ⟨hc, a0, a1, a3, a4⟩) hO a2)
    · -- mpzpm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_mpzpm F (by first | exact Or.inl ⟨hc, a0, a1, a3, a4⟩ | exact Or.inr ⟨hc, a0, a1, a3, a4⟩) hO a2)
    · -- ppmzm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_ppmzm F (by first | exact Or.inl ⟨hc, a0, a1, a2, a4⟩ | exact Or.inr ⟨hc, a0, a1, a2, a4⟩) hO a3)
    · -- mpmzm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_mpmzm_notP F (by first | exact Or.inl ⟨hc, a0, a1, a2, a4⟩ | exact Or.inr ⟨hc, a0, a1, a2, a4⟩) hO a3 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_mpmzm_Pq F (by first | exact Or.inl ⟨hc, a0, a1, a2, a4⟩ | exact Or.inr ⟨hc, a0, a1, a2, a4⟩) hO a3 hD hEG hCI)
    · -- ppmpz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_ppmpz_notP F (by first | exact Or.inl ⟨hc, a0, a1, a2, a3⟩ | exact Or.inr ⟨hc, a0, a1, a2, a3⟩) hO a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_ppmpz_Pq F (by first | exact Or.inl ⟨hc, a0, a1, a2, a3⟩ | exact Or.inr ⟨hc, a0, a1, a2, a3⟩) hO a4 hD hEG hCI)
    · -- ppppz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_ppppz_notP F (by first | exact Or.inl ⟨hc, a0, a1, a2, a3⟩ | exact Or.inr ⟨hc, a0, a1, a2, a3⟩) hO a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_ppppz_Pq F (by first | exact Or.inl ⟨hc, a0, a1, a2, a3⟩ | exact Or.inr ⟨hc, a0, a1, a2, a3⟩) hO a4 hD hEG hCI)
    · -- mpmpz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_mpmpz_notP F (by first | exact Or.inl ⟨hc, a0, a1, a2, a3⟩ | exact Or.inr ⟨hc, a0, a1, a2, a3⟩) hO a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_mpmpz_Pq F (by first | exact Or.inl ⟨hc, a0, a1, a2, a3⟩ | exact Or.inr ⟨hc, a0, a1, a2, a3⟩) hO a4 hD hEG hCI)
    · -- mpppz
      exact Or.inr hcase
  · rcases h8 with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
    · -- zpzpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpzpp F (by first | exact Or.inl ⟨hc, a1, a3, a4⟩ | exact Or.inr ⟨hc, a1, a3, a4⟩) hO a0 a2)
    · -- zpzpm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpzpm F (by first | exact Or.inl ⟨hc, a1, a3, a4⟩ | exact Or.inr ⟨hc, a1, a3, a4⟩) hO a0 a2)
    · -- zpmzm
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_zpmzm F (by first | exact Or.inl ⟨hc, a1, a2, a4⟩ | exact Or.inr ⟨hc, a1, a2, a4⟩) hO a0 a3)
    · -- zpmpz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_zpmpz_notP F (by first | exact Or.inl ⟨hc, a1, a2, a3⟩ | exact Or.inr ⟨hc, a1, a2, a3⟩) hO a0 a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_zpmpz_Pq F (by first | exact Or.inl ⟨hc, a1, a2, a3⟩ | exact Or.inr ⟨hc, a1, a2, a3⟩) hO a0 a4 hD hEG hCI)
    · -- zpppz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_zpppz_notP F (by first | exact Or.inl ⟨hc, a1, a2, a3⟩ | exact Or.inr ⟨hc, a1, a2, a3⟩) hO a0 a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_zpppz_Pq F (by first | exact Or.inl ⟨hc, a1, a2, a3⟩ | exact Or.inr ⟨hc, a1, a2, a3⟩) hO a0 a4 hD hEG hCI)
    · -- pzzpp
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact Or.inl (Minimality.T24.isRupert_offOB1_pzzpp F (by first | exact Or.inl ⟨hc, a0, a3, a4⟩ | exact Or.inr ⟨hc, a0, a3, a4⟩) hO a1 a2)
    · -- ppzpz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_ppzpz_notP F (by first | exact Or.inl ⟨hc, a0, a1, a3⟩ | exact Or.inr ⟨hc, a0, a1, a3⟩) hO a2 a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_ppzpz_Pq F (by first | exact Or.inl ⟨hc, a0, a1, a3⟩ | exact Or.inr ⟨hc, a0, a1, a3⟩) hO a2 a4 hD hEG hCI)
    · -- mpzpz
      rcases hcase with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
      exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_mpzpz_notP F (by first | exact Or.inl ⟨hc, a0, a1, a3⟩ | exact Or.inr ⟨hc, a0, a1, a3⟩) hO a2 a4 hD))
        (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_mpzpz_Pq F (by first | exact Or.inl ⟨hc, a0, a1, a3⟩ | exact Or.inr ⟨hc, a0, a1, a3⟩) hO a2 a4 hD hEG hCI)
  · -- zpzpz (the three-zero class Cls3)
    rcases h3 with ⟨hc, a0, a1, a2, a3, a4⟩ | ⟨hc, a0, a1, a2, a3, a4⟩ <;>
    exact par_combine F (fun hD => Or.inl (Minimality.T24.isRupert_offOB1_zpzpz_notP F (by first | exact Or.inl ⟨hc, a1, a3⟩ | exact Or.inr ⟨hc, a1, a3⟩) hO a0 a2 a4 hD))
      (fun hD hEG hCI => Minimality.T24.isRupert_offOB1_zpzpz_Pq F (by first | exact Or.inl ⟨hc, a1, a3⟩ | exact Or.inr ⟨hc, a1, a3⟩) hO a0 a2 a4 hD hEG hCI)

end Minimality.T24
