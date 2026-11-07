module

public import Minimality.Type21SAT.WitA
public import Minimality.Type21SAT.RuleA

@[expose] public section

/-!
# L3, part 21: the top theorem for core A

The case clause (family 30), the facts about the real data of a type 21 shape (`GeoOK (geoF F)`), the statement
`CoreUnsatA` over the numbered clauses, and `caseA_of_unsat`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

variable {x : Fin 7 → ℝ³}

/-! ### The case clause -/

/-- The four literals of the case clause: the atoms `fv 3 2 3` and `fv 3 2 5` are not both zero. -/
def caseLits : List Lit :=
  [(true, V.fv 3 2 3), (true, V.ng (V.fv 3 2 3)), (true, V.fv 3 2 5), (true, V.ng (V.fv 3 2 5))]

/-- A packed row is not the case row, or it contains the four case literals. -/
def caseD (n : Nat) : Bool :=
  let r := decRow n
  r.1 != 30 || coversF (r.2.2.map litOfA) caseLits

/-- All case rows of core A are the case clause. -/
theorem caseAll : (rowsA.all fun ch => ch.all caseD) = true := by decide +kernel

/-- **The case clause is true** when the facet `D` is not parallel to `H`, in the form
`not (<N_D, x2 - x3> = 0 and <N_D, x2 - x5> = 0)`. -/
theorem case_holds (F : S0xFac 8 S21 x)
    (hDH : ¬ (⟪F.N 3, x 2 - x 3⟫ = 0 ∧ ⟪F.N 3, x 2 - x 5⟫ = 0)) {cl : List Lit}
    (h : coversF cl caseLits = true) : Holds (rho (geoF F)) cl := by
  have eN3 : (geoF F).N 3 = F.N 3 := geoF_N F 3
  have ex2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have ex3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have ex5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have a1 : (geoF F).atom (V.fv 3 2 3) = ⟪F.N 3, x 2 - x 3⟫ := by
    simp only [Geo.atom]
    rw [eN3, ex2, ex3]
  have a2 : (geoF F).atom (V.fv 3 2 5) = ⟪F.N 3, x 2 - x 5⟫ := by
    simp only [Geo.atom]
    rw [eN3, ex2, ex5]
  rw [coversF_eq] at h
  have mem : ∀ l ∈ caseLits, l ∈ cl := fun l hl => by
    have := List.all_eq_true.mp h l hl
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
    rcases this with h0 | h0
    · subst h0; simp [caseLits, lfalse] at hl
    · exact h0
  have hp : ∀ v : V, isAtom v = true → rho (geoF F) v = decide (0 < (geoF F).atom v) := fun v hv => rho_atom _ hv
  have hq : ∀ v : V, rho (geoF F) (V.ng v) = decide ((geoF F).atom v < 0) := fun v => rfl
  by_cases h1 : ⟪F.N 3, x 2 - x 3⟫ = 0
  · have h2 : ⟪F.N 3, x 2 - x 5⟫ ≠ 0 := fun h2 => hDH ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h2 with h3 | h3
    · refine ⟨_, mem (true, V.ng (V.fv 3 2 5)) (by simp [caseLits]), ?_⟩
      simp [evalL, hq, a2, h3]
    · refine ⟨_, mem (true, V.fv 3 2 5) (by simp [caseLits]), ?_⟩
      simp [evalL, hp (V.fv 3 2 5) rfl, a2, h3]
  · rcases lt_or_gt_of_ne h1 with h3 | h3
    · refine ⟨_, mem (true, V.ng (V.fv 3 2 3)) (by simp [caseLits]), ?_⟩
      simp [evalL, hq, a1, h3]
    · refine ⟨_, mem (true, V.fv 3 2 3) (by simp [caseLits]), ?_⟩
      simp [evalL, hp (V.fv 3 2 3) rfl, a1, h3]

/-! ### The real data of a type 21 shape -/

/-- Points of a facet list are points of the shape, and the facet is one of eight. -/
theorem inF_lt (t i : Nat) (h : inF t i = true) : t < 8 ∧ i < 7 := by
  have ht : t < 8 := by
    by_contra hc
    have e : FSl.getD t [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [FSl]; omega)]; rfl
    have h' : (FSl.getD t []).contains i = true := h
    rw [e] at h'; simp at h'
  refine ⟨ht, ?_⟩
  have key : ∀ t < 8, ∀ i ∈ FSl.getD t [], i < 7 := by decide
  exact key t ht i (by simpa [inF] using h)

/-- **`FacOK` of the real data of a type 21 shape.** -/
theorem facOK_geoF (F : S0xFac 8 S21 x) : FacOK (geoF F) := by
  have key : ∀ (t i j : Nat) (ht : t < 8) (hi : i < 7) (hj : j < 7),
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
    rw [key t i j ht hi7 hj7, F.zero ⟨t, ht⟩ ⟨i, hi7⟩ ((mem_S21 ⟨t, ht⟩ ⟨i, hi7⟩).mpr hi),
      F.zero ⟨t, ht⟩ ⟨j, hj7⟩ ((mem_S21 ⟨t, ht⟩ ⟨j, hj7⟩).mpr hj), sub_self]
  · obtain ⟨ht, hi7⟩ := inF_lt t i hi
    rw [key t i j ht hi7 hj, F.zero ⟨t, ht⟩ ⟨i, hi7⟩ ((mem_S21 ⟨t, ht⟩ ⟨i, hi7⟩).mpr hi)]
    have hn : (⟨j, hj⟩ : Fin 7) ∉ S21 ⟨t, ht⟩ := fun h => by
      have := (mem_S21 ⟨t, ht⟩ ⟨j, hj⟩).mp h
      simp_all
    have := F.neg ⟨t, ht⟩ ⟨j, hj⟩ hn
    linarith

/-- The points of a type 21 shape are distinct (each pair is separated by a facet). -/
theorem inj_of_fac (F : S0xFac 8 S21 x) : Function.Injective x := by
  have key : ∀ i j : Fin 7, i ≠ j → ∃ t : Fin 8, i ∈ S21 t ∧ j ∉ S21 t := by decide +kernel
  intro i j hij
  by_contra hne
  obtain ⟨t, hi, hj⟩ := key i j hne
  have h1 := F.zero t i hi
  have h2 := F.neg t j hj
  rw [hij] at h1
  linarith

/-- **The facts the rows need** about the real data of a type 21 shape of the chirality of `S0`. -/
theorem geoOK_of (F : S0xFac 8 S21 x) (hchir : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2)) :
    GeoOK (geoF F) := by
  have hF := facOK_geoF F
  refine ⟨hF, oriOK_of_chir hF ?_, ?_⟩
  · show 0 < det3 (((geoF F).x 0) - (geoF F).x 2) ((geoF F).x 3 - (geoF F).x 2) ((geoF F).x 6 - (geoF F).x 2)
    have e0 : (geoF F).x 0 = x 0 := geoF_x F 0
    have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
    have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
    have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
    rw [e0, e2, e3, e6]
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

/-! ### The statement and the theorem -/

/-- **The core A is unsatisfiable**, as a statement about the numbered clauses (literal code `2 i + (1 if negative)`). -/
def CoreUnsatA : Prop :=
  ∀ ρ : Nat → Bool, ¬ ∀ ch ∈ rowsA, ∀ n ∈ ch, ∃ c ∈ (decRow n).2.2, ((c % 2 == 0) == ρ (c / 2)) = true

/-- Every row of core A is checked by the four kernel checks. -/
theorem rowsA_ok : ∀ ch ∈ rowsA, ∀ n ∈ ch, rowD n = true ∧ ruleD n = true := by
  intro ch hch n hn
  simp only [rowsA, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨List.all_eq_true.mp chunk0 n hn, List.all_eq_true.mp rchunk0 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk1 n hn, List.all_eq_true.mp rchunk1 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk2 n hn, List.all_eq_true.mp rchunk2 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk3 n hn, List.all_eq_true.mp rchunk3 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk4 n hn, List.all_eq_true.mp rchunk4 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk5 n hn, List.all_eq_true.mp rchunk5 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk6 n hn, List.all_eq_true.mp rchunk6 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk7 n hn, List.all_eq_true.mp rchunk7 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk8 n hn, List.all_eq_true.mp rchunk8 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk9 n hn, List.all_eq_true.mp rchunk9 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk10 n hn, List.all_eq_true.mp rchunk10 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk11 n hn, List.all_eq_true.mp rchunk11 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk12 n hn, List.all_eq_true.mp rchunk12 n hn⟩
  · exact ⟨List.all_eq_true.mp chunk13 n hn, List.all_eq_true.mp rchunk13 n hn⟩

/-- **Every row of core A is true of the real data** of a non-Rupert type 21 shape (of the chirality of `S0`,
off `D ∥ H`). -/
theorem rowsA_holds (F : S0xFac 8 S21 x) (hG : GeoOK (geoF F)) (hNR : ¬ IsRupert (univ.image x))
    (hDH : ¬ (⟪F.N 3, x 2 - x 3⟫ = 0 ∧ ⟪F.N 3, x 2 - x 5⟫ = 0)) :
    ∀ ch ∈ rowsA, ∀ n ∈ ch, Holds (rho (geoF F)) ((decRow n).2.2.map litOfA) := by
  intro ch hch n hn
  obtain ⟨h1, h2⟩ := rowsA_ok ch hch n hn
  have h3 := List.all_eq_true.mp (List.all_eq_true.mp wchunkAll ch hch) n hn
  have h4 := List.all_eq_true.mp (List.all_eq_true.mp caseAll ch hch) n hn
  unfold rowD at h1
  unfold ruleD at h2
  unfold witD at h3
  unfold caseD at h4
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1 h2 h3 h4
  rcases h1 with ((h | h) | h) | h
  · rcases h2 with h' | h'
    · exact absurd h h'
    · exact ruleOK_sound F (inj_of_fac F) hNR hG h'
  · rcases h3 with h' | h'
    · exact absurd h h'
    · exact witOK_sound F hG h'
  · rcases h4 with h' | h'
    · exact absurd h h'
    · exact case_holds F hDH h'
  · exact rowOK3_sound hG h

/-- A clause that holds under `rho` gives the numbered-clause condition for the assignment `i -> rho (name i)`. -/
theorem code_of_holds (g : Geo) (n : Nat) (h : Holds (rho g) ((decRow n).2.2.map litOfA)) :
    ∃ c ∈ (decRow n).2.2, ((c % 2 == 0) == evalL (rho g) (nmA (c / 2))) = true := by
  obtain ⟨l, hl, hev⟩ := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  refine ⟨c, hc, ?_⟩
  have : evalL (rho g) (litOfA c) = ((c % 2 == 0) == evalL (rho g) (nmA (c / 2))) := by
    unfold litOfA
    by_cases hc2 : (c % 2 == 0) = true
    · simp [hc2]
    · have : (c % 2 == 0) = false := by simpa using hc2
      simp [this, evalL_neg]
  rw [this] at hev
  exact hev

/-- **Top theorem for core A.**  If the numbered clauses of core A are unsatisfiable, every type 21 shape of the chirality
of `S0` with `D` not parallel to `H` (`not (<N_D, x2 - x3> = 0 and <N_D, x2 - x5> = 0)`) is Rupert. -/
theorem caseA_of_unsat (hA : CoreUnsatA) (F : S0xFac 8 S21 x)
    (hchir : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2))
    (hDH : ¬ (⟪F.N 3, x 2 - x 3⟫ = 0 ∧ ⟪F.N 3, x 2 - x 5⟫ = 0)) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalL (rho (geoF F)) (nmA i)) ?_
  intro ch hch n hn
  exact code_of_holds _ n (rowsA_holds F hG hNR hDH ch hch n hn)

end Minimality.H21.SAT

