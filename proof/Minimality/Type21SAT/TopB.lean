module

public import Minimality.Type21SAT.SpecB
public import Minimality.Type21SAT.TopT

@[expose] public section

/-!
# L3, part 28: the top theorem for core B (`D ∥ H`)
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

variable {x : Fin 7 → ℝ³}

/-- The four units are true when `D ∥ H`: the atoms `<N_D, x2 - x3>`, `<N_D, x2 - x5>` vanish. -/
theorem units_hold (F : S0xFac 8 S21 x) (hpar : ∃ r : ℝ, F.N 3 = r • F.N 7) :
    ∀ s ∈ unitsB, Holds (rho (geoF F)) s := by
  obtain ⟨r, hr⟩ := hpar
  have eN3 : (geoF F).N 3 = F.N 3 := geoF_N F 3
  have ex2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have ex3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have ex5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have z : ∀ j : Fin 7, j ∈ S21 7 → ⟪F.N 3, x 2 - x j⟫ = 0 := fun j hj => by
    rw [hr, inner_smul_left, F.inner_sub, F.zero 7 2 (by decide +kernel), F.zero 7 j hj]; simp
  have a1 : (geoF F).atom (V.fv 3 2 3) = 0 := by
    simp only [Geo.atom]; rw [eN3, ex2, ex3]; exact z 3 (by decide +kernel)
  have a2 : (geoF F).atom (V.fv 3 2 5) = 0 := by
    simp only [Geo.atom]; rw [eN3, ex2, ex5]; exact z 5 (by decide +kernel)
  have p1 : rho (geoF F) (V.fv 3 2 3) = false := by simp [rho, a1]
  have p2 : rho (geoF F) (V.fv 3 2 5) = false := by simp [rho, a2]
  have q1 : rho (geoF F) (V.ng (V.fv 3 2 3)) = false := by simp [rho, a1]
  have q2 : rho (geoF F) (V.ng (V.fv 3 2 5)) = false := by simp [rho, a2]
  intro s hs
  simp only [unitsB, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨(false, V.fv 3 2 3), by simp, by simp [evalL, p1]⟩
  · exact ⟨(false, V.ng (V.fv 3 2 3)), by simp, by simp [evalL, q1]⟩
  · exact ⟨(false, V.fv 3 2 5), by simp, by simp [evalL, p2]⟩
  · exact ⟨(false, V.ng (V.fv 3 2 5)), by simp, by simp [evalL, q2]⟩

/-- **The core B is unsatisfiable**, as a statement about the numbered clauses. -/
def CoreUnsatB : Prop :=
  ∀ ρ : Nat → Bool, ¬ ∀ ch ∈ rowsB, ∀ n ∈ ch, ∃ c ∈ (decRow n).2.2, ((c % 2 == 0) == ρ (c / 2)) = true

/-- Every row of core B passes the kernel checks. -/
theorem rowsB_ok : ∀ ch ∈ rowsB, ∀ n ∈ ch, rowDB n = true := by
  intro ch hch n hn
  simp only [rowsB, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp bchunk0 n hn
  · exact List.all_eq_true.mp bchunk1 n hn
  · exact List.all_eq_true.mp bchunk2 n hn
  · exact List.all_eq_true.mp bchunk3 n hn
  · exact List.all_eq_true.mp bchunk4 n hn
  · exact List.all_eq_true.mp bchunk5 n hn
  · exact List.all_eq_true.mp bchunk6 n hn

/-- **Every row of core B is true of the real data** of a non-Rupert type 21 shape with `D ∥ H`. -/
theorem rowsB_holds (F : S0xFac 8 S21 x) (hG : GeoOK (geoF F)) (hNR : ¬ IsRupert (univ.image x))
    (hpar : ∃ r : ℝ, F.N 3 = r • F.N 7) :
    ∀ ch ∈ rowsB, ∀ n ∈ ch, Holds (rho (geoF F)) ((decRow n).2.2.map litOfB) := by
  intro ch hch n hn
  have h1 := rowsB_ok ch hch n hn
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp bspecialAll ch hch) n hn
  unfold rowDB at h1
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨h2r, h2w⟩, h2l⟩, h2u⟩ := h2
  unfold ruleDB at h2r
  unfold witDB at h2w
  unfold lexDB at h2l
  unfold unitDB at h2u
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1 h2r h2w h2l h2u
  rcases h1 with ((((h | h) | h) | h) | h) | h
  · rcases h2r with h' | h'
    · exact absurd h h'
    · exact ruleOK_sound F (inj_of_fac F) hNR hG h'
  · rcases h2w with h' | h'
    · exact absurd h h'
    · exact witOK_sound F hG h'
  · rcases h2l with h' | h'
    · exact absurd h h'
    · exact lexOK_sound F (inj_of_fac F) hNR hG hpar h'
  · rcases h2u with h' | h'
    · exact absurd h h'
    · exact anyCov_holds (rho_proper _) h' (units_hold F hpar)
  · exact rowOK3_sound hG h
  · exact lexDefOK_sound _ hG h

/-- A clause that holds under `rho` gives the numbered-clause condition for the assignment `i -> rho (name i)`. -/
theorem code_of_holdsB (g : Geo) (n : Nat) (h : Holds (rho g) ((decRow n).2.2.map litOfB)) :
    ∃ c ∈ (decRow n).2.2, ((c % 2 == 0) == evalL (rho g) (nmB (c / 2))) = true := by
  obtain ⟨l, hl, hev⟩ := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
  refine ⟨c, hc, ?_⟩
  have : evalL (rho g) (litOfB c) = ((c % 2 == 0) == evalL (rho g) (nmB (c / 2))) := by
    unfold litOfB
    by_cases hc2 : (c % 2 == 0) = true
    · simp [hc2]
    · have : (c % 2 == 0) = false := by simpa using hc2
      simp [this, evalL_neg]
  rw [this] at hev
  exact hev

/-- **Top theorem for core B.**  If the numbered clauses of core B are unsatisfiable, every type 21 shape of the
chirality of `S0` with `D ∥ H` (`N_D` a multiple of `N_H`) is Rupert. -/
theorem caseB_of_unsat (hB : CoreUnsatB) (F : S0xFac 8 S21 x)
    (hchir : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2))
    (hpar : ∃ r : ℝ, F.N 3 = r • F.N 7) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hB (fun i => evalL (rho (geoF F)) (nmB i)) ?_
  intro ch hch n hn
  exact code_of_holdsB _ n (rowsB_holds F hG hNR hpar ch hch n hn)

/-- Core B for `Facets21`. -/
theorem caseB_of_unsat_T (hB : CoreUnsatB) (T : Facets21 x)
    (hchir : 0 < det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2))
    (hpar : ∃ r : ℝ, T.f046.N = r • T.f235.N) : IsRupert (univ.image x) :=
  caseB_of_unsat hB (toS0xFac T) hchir hpar

end Minimality.H21.SAT

