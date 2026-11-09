module

public import Minimality.Type21SAT.LexRule

@[expose] public section

/-!
# L3, part 26: soundness of the lex rule rows
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

/-- **The core of the lex rule soundness**: all literals of the lex rule clause false (with `D ∥ H`) gives a Rupert shape. -/
theorem lex_core {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (hx : Function.Injective x) (hG : GeoOK (geoF F))
    (hpar : ∃ r : ℝ, F.N 3 = r • F.N 7)
    (e pp mask d ep zi : Nat) (cyc : List Nat) (he : e < 36) (hd : d < 21) (hmask : mask < 255)
    (hpp : pp.testBit 3 ≠ pp.testBit 7)
    (hzi : zi = 999 ∨ ((zi = 0 ∨ zi = 1 ∨ zi = 2 ∨ zi = 4 ∨ zi = 5 ∨ zi = 6) ∧ mask.testBit zi = true))
    (hdin : dinDH d = true) (hcyc : cycChk pp (patCyc.getD pp []) = true)
    (hlen : 3 < (patCyc.getD pp []).length) (halt : altChk (patCyc.getD pp []) cyc = true)
    (hno : ∀ l ∈ lexLits e pp mask d ep zi cyc, evalL (rho (geoF F)) l = false) :
    IsRupert (univ.image x) := by
  set L := patCyc.getD pp [] with hL
  haveI : NeZero L.length := ⟨by omega⟩
  obtain ⟨hk3, hinj, hcycOK⟩ := cycFacts (k := L.length) rfl hcyc
  set u := (geoF F).vv e with hu
  set δ := (geoF F).dv d with hδ
  have hdA := (EAB_lt d hd).1
  have hdB := (EAB_lt d hd).2
  have S : ∀ t : Fin 8, Sg3 (rho (geoF F)) (Fe e t.val) ⟪F.N t, u⟫ := fun t => by
    have := Fe_sound hG he t.isLt
    rwa [geoF_N] at this
  have FS : ∀ t : Fin 8, Sg3 (rho (geoF F)) (fup3 t.val (EA d) (EB d)) ⟪F.N t, δ⟫ := fun t => by
    have := fup3_sound hG.hF t.val (EA d) (EB d) hdA hdB
    rwa [geoF_N] at this
  have neg_false : ∀ l : Lit, evalL (rho (geoF F)) l.neg = false → evalL (rho (geoF F)) l = true := by
    intro l h; rw [evalL_neg] at h; simpa using h
  -- state
  have mem1 : ∀ t : Fin 8, mask.testBit t.val = false → pp.testBit t.val = true →
      (Fe e t.val).1.neg ∈ lexLits e pp mask d ep zi cyc := fun t h1 h2 => by
    simp only [lexLits, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1, h2]⟩)
  have mem2 : ∀ t : Fin 8, mask.testBit t.val = false → pp.testBit t.val = false →
      (Fe e t.val).2.neg ∈ lexLits e pp mask d ep zi cyc := fun t h1 h2 => by
    simp only [lexLits, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1, h2]⟩)
  have mem3 : ∀ t : Fin 8, mask.testBit t.val = true →
      (Fe e t.val).1 ∈ lexLits e pp mask d ep zi cyc ∧ (Fe e t.val).2 ∈ lexLits e pp mask d ep zi cyc :=
    fun t h1 => by
      simp only [lexLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact ⟨Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1]⟩), Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1]⟩)⟩
  have hoff : ∀ t : Fin 8, mask.testBit t.val = false →
      (bits pp t = true → 0 < ⟪F.N t, u⟫) ∧ (bits pp t = false → ⟪F.N t, u⟫ < 0) := by
    intro t ht
    constructor
    · intro hp
      exact (S t).1.mp (neg_false _ (hno _ (mem1 t ht hp)))
    · intro hp
      exact (S t).2.mp (neg_false _ (hno _ (mem2 t ht hp)))
  have hon : ∀ t : Fin 8, mask.testBit t.val = true → ⟪F.N t, u⟫ = 0 := by
    intro t ht
    obtain ⟨m1, m2⟩ := mem3 t ht
    have a1 := hno _ m1
    have a2 := hno _ m2
    have n1 : ¬ 0 < ⟪F.N t, u⟫ := fun h' => by simp [(S t).1.mpr h'] at a1
    have n2 : ¬ ⟪F.N t, u⟫ < 0 := fun h' => by simp [(S t).2.mpr h'] at a2
    exact le_antisymm (not_lt.mp n1) (not_lt.mp n2)
  -- the other edge-on facets: the sign of d
  have hzero : ∀ t : Fin 8, mask.testBit t.val = true → t.val ≠ 3 → t.val ≠ 7 → t.val = zi →
      ⟪F.N t, δ⟫ = 0 := by
    intro t ht h3' h7' hz
    have m1 : (fup3 t.val (EA d) (EB d)).1 ∈ lexLits e pp mask d ep zi cyc := by
      simp only [lexLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr ⟨t.val, t.isLt, by simp [ht, h3', h7', ← hz]⟩)
    have m2 : (fup3 t.val (EA d) (EB d)).2 ∈ lexLits e pp mask d ep zi cyc := by
      simp only [lexLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr ⟨t.val, t.isLt, by simp [ht, h3', h7', ← hz]⟩)
    have a1 := hno _ m1
    have a2 := hno _ m2
    have n1 : ¬ 0 < ⟪F.N t, δ⟫ := fun h' => by simp [(FS t).1.mpr h'] at a1
    have n2 : ¬ ⟪F.N t, δ⟫ < 0 := fun h' => by simp [(FS t).2.mpr h'] at a2
    exact le_antisymm (not_lt.mp n1) (not_lt.mp n2)
  have hstr : ∀ t : Fin 8, mask.testBit t.val = true → t.val ≠ 3 → t.val ≠ 7 → t.val ≠ zi →
      (bits pp t = true → 0 < epR ep * ⟪F.N t, δ⟫) ∧ (bits pp t = false → epR ep * ⟪F.N t, δ⟫ < 0) := by
    intro t ht h3' h7' hz
    have hmem : ∀ l : Lit, (l = (if pp.testBit t.val == decide (ep = 1) then (fup3 t.val (EA d) (EB d)).1
        else (fup3 t.val (EA d) (EB d)).2).neg) → l ∈ lexLits e pp mask d ep zi cyc := by
      intro l hl
      subst hl
      simp only [lexLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr ⟨t.val, t.isLt, by simp [ht, h3', h7', hz]⟩)
    have a1 := neg_false _ (hno _ (hmem _ rfl))
    by_cases hep : ep = 1
    · cases hb : pp.testBit t.val
      · simp only [hep, decide_true, hb, Bool.false_eq_true, beq_iff_eq, ite_false] at a1
        have := (FS t).2.mp a1
        simp [bits, hb, epR, hep, this]
      · simp only [hep, decide_true, hb, beq_self_eq_true, ite_true] at a1
        have := (FS t).1.mp a1
        simp [bits, hb, epR, hep, this]
    · cases hb : pp.testBit t.val
      · simp only [hep, decide_false, hb, beq_self_eq_true, ite_true] at a1
        have := (FS t).1.mp a1
        simp [bits, hb, epR, hep, this]
      · simp only [hep, decide_false, hb, Bool.true_eq_false, beq_iff_eq, ite_false] at a1
        have := (FS t).2.mp a1
        simp [bits, hb, epR, hep, this]
  -- D and H are zero at d
  obtain ⟨q, hq, h7q⟩ := dh_neg F hpar
  obtain ⟨r, hr⟩ := hpar
  have hz37 : ⟪F.N 3, δ⟫ = 0 ∧ ⟪F.N 7, δ⟫ = 0 := by
    have hδ' : δ = x ⟨EA d, hdA⟩ - x ⟨EB d, hdB⟩ := by
      simp only [hδ, Geo.dv]
      rw [show (geoF F).x (EA d) = x ⟨EA d, hdA⟩ from geoF_x F ⟨EA d, hdA⟩,
        show (geoF F).x (EB d) = x ⟨EB d, hdB⟩ from geoF_x F ⟨EB d, hdB⟩]
    have zt : ∀ t : Fin 8, (inF t.val (EA d) = true ∧ inF t.val (EB d) = true) → ⟪F.N t, δ⟫ = 0 := by
      intro t ⟨ha, hb⟩
      rw [hδ', F.inner_sub, F.zero t _ ((mem_S21 t ⟨EA d, hdA⟩).mpr ha),
        F.zero t _ ((mem_S21 t ⟨EB d, hdB⟩).mpr hb), sub_self]
    have hcase : (inF 3 (EA d) = true ∧ inF 3 (EB d) = true) ∨ (inF 7 (EA d) = true ∧ inF 7 (EB d) = true) := by
      simpa [dinDH] using hdin
    have e7 : ⟪F.N 7, δ⟫ = q * ⟪F.N 3, δ⟫ := by rw [h7q, inner_smul_left]; simp
    have e3 : ⟪F.N 3, δ⟫ = r * ⟪F.N 7, δ⟫ := by rw [hr, inner_smul_left]; simp
    rcases hcase with hc | hc
    · have := zt 3 hc
      exact ⟨this, by rw [e7, this]; ring⟩
    · have := zt 7 hc
      exact ⟨by rw [e3, this]; ring, this⟩
  -- the tilt w
  have hzi' : zi = 999 ∨ zi = 0 ∨ zi = 1 ∨ zi = 2 ∨ zi = 4 ∨ zi = 5 ∨ zi = 6 := by
    rcases hzi with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨w, hw3, hw7, hwz⟩ := exists_w F hq h7q (bits pp 3) (bits pp 7) (bits pp ⟨zi % 8, Nat.mod_lt _ (by omega)⟩)
    hpp zi hzi'
  -- the facings
  have hfac : ∀ t : Fin 8, (bits pp t = true → LP3 ⟪F.N t, u⟫ ⟪F.N t, epR ep • δ⟫ ⟪F.N t, w⟫) ∧
      (bits pp t = false → LP3 (-⟪F.N t, u⟫) (-⟪F.N t, epR ep • δ⟫) (-⟪F.N t, w⟫)) := by
    intro t
    have hsc : ⟪F.N t, epR ep • δ⟫ = epR ep * ⟪F.N t, δ⟫ := real_inner_smul_right _ _ _
    by_cases hm : mask.testBit t.val = true
    · have h0 := hon t hm
      by_cases ht3 : t.val = 3
      · have : t = 3 := Fin.ext ht3
        subst this
        exact lp3_c h0 (by rw [hsc, hz37.1]; ring) hw3
      by_cases ht7 : t.val = 7
      · have : t = 7 := Fin.ext ht7
        subst this
        exact lp3_c h0 (by rw [hsc, hz37.2]; ring) hw7
      by_cases hz : t.val = zi
      · refine lp3_c h0 (by rw [hsc, hzero t hm ht3 ht7 hz]; ring) ?_
        have := hwz t hz
        have hb : bits pp ⟨zi % 8, Nat.mod_lt _ (by omega)⟩ = bits pp t := by
          congr 1; exact Fin.ext (by simp only; rw [← hz]; exact Nat.mod_eq_of_lt t.isLt)
        rw [hb] at this
        exact this
      · exact lp3_b h0 (by rw [hsc]; exact hstr t hm ht3 ht7 hz)
    · have hm' : mask.testBit t.val = false := by simpa using hm
      exact lp3_a (hoff t hm')
  -- u is not zero
  obtain ⟨t0, ht0⟩ := mask_miss mask hmask
  have hune : u ≠ 0 := by
    intro h0
    have := hoff t0 ht0
    cases hp : bits pp t0 <;> simp [hp, h0] at this
  -- the lex failure
  have hm : ((true, V.faill e d ep cyc) : Lit) ∈ lexLits e pp mask d ep zi cyc := by
    simp [lexLits]
  have hrf : rho (geoF F) (V.faill e d ep cyc) = false := by simpa [evalL] using hno _ hm
  have hA : AltCover2 (cOf (k := L.length) L) cyc := by
    refine altFacts rfl ?_ halt
    unfold cycChk at hcyc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcyc
    exact fun v hv => hcyc.1.1.2 v hv
  have hU := robUniL_of_alt (geoF F) (geoF_x F) (u := u) (δ := δ) hu.symm ((vv_lt _ hd).trans hδ.symm) hA hrf
  exact s0x_lex2_rupert F hx hinj hk3 hcycOK hune hfac hU

/-- **A lex rule row that passes the check is true of the real data**, if the shape is not Rupert and `D ∥ H`. -/
theorem lexOK_sound {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hpar : ∃ r : ℝ, F.N 3 = r • F.N 7)
    {p : List Nat} {cl : List Lit} (h : lexOK p cl = true) : Holds (rho (geoF F)) cl := by
  by_contra hn
  apply hNR
  unfold lexOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨he, hpp, hmask, hd, h3, h7, hpd, hzi, hlen⟩, hdin⟩, hcyc⟩, halt⟩, hcov⟩ := h
  refine lex_core F hx hG hpar (prm p 0) (prm p 1) (prm p 5) (prm p 2) (if prm p 3 = 1 then 1 else 0) (prm p 4)
    (failLOf cl (prm p 0) (prm p 2) (if prm p 3 = 1 then 1 else 0)) he hd hmask hpd hzi hdin hcyc hlen halt ?_
  intro l hl
  rw [coversF_eq] at hcov
  have := List.all_eq_true.mp hcov l hl
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  rcases this with h0 | h0
  · subst h0
    have e : rho (geoF F) V.tru = true := rho_proper _
    simp [lfalse, evalL, e]
  · rw [← Bool.not_eq_true]; exact fun he' => hn ⟨l, h0, he'⟩

end Minimality.H21.SAT
