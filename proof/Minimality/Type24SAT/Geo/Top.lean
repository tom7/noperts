module

public import Minimality.Type24SAT.Geo.KRel
public import Minimality.Type24SAT.Geo.Dec

@[expose] public section

/-!
# type 24: the top theorem for a core (generic over the data)

The facts about the real data of a type 24 shape (`GeoOK (geoF F)`), the statement `CoreUnsat rows` over the
numbered clauses, and `case_of_unsat`: if all rows pass the kernel checks and the numbered clauses are
unsatisfiable, the shape is Rupert.  The unit rows (family 26) are the class literals `U`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21
open Minimality.T24.SAT (s0x_S24)

open Minimality.H29.SAT

namespace Minimality.H24.SAT

variable {x : Fin 7 → ℝ³}

/-- Points of a facet list are points of the shape, and the facet is one of nine. -/
theorem inF_lt (t i : Nat) (h : inF t i = true) : t < 9 ∧ i < 7 := by
  have ht : t < 9 := by
    by_contra hc
    have e : FSl.getD t [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [FSl]; omega)]; rfl
    have h' : (FSl.getD t []).contains i = true := h
    rw [e] at h'; simp at h'
  refine ⟨ht, ?_⟩
  have key : ∀ t < 9, ∀ i ∈ FSl.getD t [], i < 7 := by decide
  exact key t ht i (by simpa [inF] using h)

/-- **`FacOK` of the real data of a type 24 shape.** -/
theorem facOK_geoF (F : S0xFac 9 s0x_S24 x) : FacOK (geoF F) := by
  have key : ∀ (t i j : Nat) (ht : t < 9) (hi : i < 7) (hj : j < 7),
      ⟪(geoF F).N t, (geoF F).x i - (geoF F).x j⟫ = F.f ⟨t, ht⟩ (x ⟨i, hi⟩) - F.f ⟨t, ht⟩ (x ⟨j, hj⟩) := by
    intro t i j ht hi hj
    have a1 := geoF_x F ⟨i, hi⟩
    have a2 := geoF_x F ⟨j, hj⟩
    have a3 := geoF_N F ⟨t, ht⟩
    simp only at a1 a2 a3
    rw [a1, a2, a3, ← F.hN]
  refine ⟨fun t i j hi hj => ?_, fun t i j hj hi hnj => ?_⟩
  · obtain ⟨ht, hi7⟩ := inF_lt t i hi
    obtain ⟨-, hj7⟩ := inF_lt t j hj
    rw [key t i j ht hi7 hj7, F.zero ⟨t, ht⟩ ⟨i, hi7⟩ ((mem_S24 ⟨t, ht⟩ ⟨i, hi7⟩).mpr hi),
      F.zero ⟨t, ht⟩ ⟨j, hj7⟩ ((mem_S24 ⟨t, ht⟩ ⟨j, hj7⟩).mpr hj), sub_self]
  · obtain ⟨ht, hi7⟩ := inF_lt t i hi
    rw [key t i j ht hi7 hj, F.zero ⟨t, ht⟩ ⟨i, hi7⟩ ((mem_S24 ⟨t, ht⟩ ⟨i, hi7⟩).mpr hi)]
    have hn : (⟨j, hj⟩ : Fin 7) ∉ s0x_S24 ⟨t, ht⟩ := fun h => by
      have := (mem_S24 ⟨t, ht⟩ ⟨j, hj⟩).mp h
      simp_all
    have := F.neg ⟨t, ht⟩ ⟨j, hj⟩ hn
    linarith

/-- The points of a type 24 shape are distinct (each pair is separated by a facet). -/
theorem inj_of_fac (F : S0xFac 9 s0x_S24 x) : Function.Injective x := by
  have key : ∀ i j : Fin 7, i ≠ j → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide +kernel
  intro i j hij
  by_contra hne
  obtain ⟨t, hi, hj⟩ := key i j hne
  have h1 := F.zero t i hi
  have h2 := F.neg t j hj
  rw [hij] at h1
  linarith

/-- **The facts the rows need** about the real data of a type 24 shape of the chirality `Bq 0 1 2 6 < 0`. -/
theorem geoOK_of (F : S0xFac 9 s0x_S24 x) (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0) :
    GeoOK (geoF F) := by
  have hF := facOK_geoF F
  refine ⟨hF, oriOK_of_chir hF ?_, ?_⟩
  · show det3 (((geoF F).x 1) - (geoF F).x 0) ((geoF F).x 2 - (geoF F).x 0) ((geoF F).x 6 - (geoF F).x 0) < 0
    have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
    have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
    have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
    have e3 : (geoF F).x 6 = x 6 := geoF_x F 6
    rw [e0, e1, e2, e3]
    exact hchir
  · intro e he
    rw [vv_lt _ he]
    have hab := EAB_lt e he
    have hne : EA e ≠ EB e := by
      have : ∀ e < 21, EA e ≠ EB e := by decide +kernel
      exact this e he
    have a1 := geoF_x F ⟨EA e, hab.1⟩
    have a2 := geoF_x F ⟨EB e, hab.2⟩
    simp only at a1 a2
    simp only [Geo.dv]
    rw [a1, a2]
    intro h0
    exact hne (congrArg Fin.val (inj_of_fac F (sub_eq_zero.mp h0)))

/-! ### The row checkers, the statement and the theorem -/




/-- **The core is unsatisfiable**, as a statement about the numbered clauses (literal code `2 i + (1 if negative)`). -/
def CoreUnsat (rows : List (List Nat)) : Prop :=
  ∀ ρ : Nat → Bool, ¬ ∀ ch ∈ rows, ∀ n ∈ ch, ∃ c ∈ (decRow n).2.2, ((c % 2 == 0) == ρ (c / 2)) = true




end Minimality.H24.SAT

