module

public import Minimality.Type16SAT.Rule2
public import Minimality.Type16SAT.Dec

@[expose] public section

/-!
# Type 16: rule rows, soundness and the row checker
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- **A rule row that passes the check is true of the real data, if the shape is not Rupert.** -/
theorem ruleOK_sound {x : Fin 7 → ℝ³} (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
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
def ruleD (chunks : List (List V)) (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 17 || ruleOK r.2.1 (r.2.2.map (litOfC chunks))

end Minimality.H16.SAT
