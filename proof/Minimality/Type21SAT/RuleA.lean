module

public import Minimality.Type21SAT.Rule2
public import Minimality.Type21SAT.RowA

@[expose] public section

/-!
# L3, part 18: rule rows of core A, soundness and the kernel check
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

/-- **A rule row that passes the check is true of the real data, if the shape is not Rupert.** -/
theorem ruleOK_sound {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) {p : List Nat} {cl : List Lit}
    (h : ruleOK p cl = true) : Holds (rho (geoF F)) cl := by
  by_contra hn
  apply hNR
  unfold ruleOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨he, hpp, hmask⟩, hsig⟩, hcyc⟩, halt⟩, hcov⟩ := h
  refine rule_core F hx hG _ _ _ _ _ he hmask hsig hcyc halt ?_
  intro l hl
  rw [coversF_eq] at hcov
  have := List.all_eq_true.mp hcov l hl
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  rcases this with h0 | h0
  · subst h0
    have e : rho (geoF F) V.tru = true := rho_proper _
    simp [lfalse, evalL, e]
  · rw [← Bool.not_eq_true]; exact fun he' => hn ⟨l, h0, he'⟩

/-- A packed row is not a rule row, or its rule check passes. -/
def ruleD (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 17 || ruleOK r.2.1 (r.2.2.map litOfA)

/-- Chunk 0 of core A: rule rows pass. -/
theorem rchunk0 : (rowsA0.all ruleD) = true := by decide +kernel

/-- Chunk 1 of core A: rule rows pass. -/
theorem rchunk1 : (rowsA1.all ruleD) = true := by decide +kernel

/-- Chunk 2 of core A: rule rows pass. -/
theorem rchunk2 : (rowsA2.all ruleD) = true := by decide +kernel

/-- Chunk 3 of core A: rule rows pass. -/
theorem rchunk3 : (rowsA3.all ruleD) = true := by decide +kernel

/-- Chunk 4 of core A: rule rows pass. -/
theorem rchunk4 : (rowsA4.all ruleD) = true := by decide +kernel

/-- Chunk 5 of core A: rule rows pass. -/
theorem rchunk5 : (rowsA5.all ruleD) = true := by decide +kernel

/-- Chunk 6 of core A: rule rows pass. -/
theorem rchunk6 : (rowsA6.all ruleD) = true := by decide +kernel

/-- Chunk 7 of core A: rule rows pass. -/
theorem rchunk7 : (rowsA7.all ruleD) = true := by decide +kernel

/-- Chunk 8 of core A: rule rows pass. -/
theorem rchunk8 : (rowsA8.all ruleD) = true := by decide +kernel

/-- Chunk 9 of core A: rule rows pass. -/
theorem rchunk9 : (rowsA9.all ruleD) = true := by decide +kernel

/-- Chunk 10 of core A: rule rows pass. -/
theorem rchunk10 : (rowsA10.all ruleD) = true := by decide +kernel

/-- Chunk 11 of core A: rule rows pass. -/
theorem rchunk11 : (rowsA11.all ruleD) = true := by decide +kernel

/-- Chunk 12 of core A: rule rows pass. -/
theorem rchunk12 : (rowsA12.all ruleD) = true := by decide +kernel

/-- Chunk 13 of core A: rule rows pass. -/
theorem rchunk13 : (rowsA13.all ruleD) = true := by decide +kernel


end Minimality.H21.SAT
