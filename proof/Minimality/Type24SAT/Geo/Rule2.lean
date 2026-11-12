module

public import Minimality.Type24SAT.Geo.Rule

@[expose] public section

/-!
# L3, part 17: soundness of the rule rows
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21
open Minimality.T24.SAT (s0x_S24)

open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-- **The list check gives `AltCover2` of the cycle map.** -/
theorem altFacts {k : ℕ} [NeZero k] {L cyc : List Nat} (hk : L.length = k) (h7 : ∀ v ∈ L, v < 7)
    (h : altChk L cyc = true) : AltCover2 (cOf (k := k) L) cyc := by
  intro B b hb e he d hd h0 h1 h2
  unfold altChk at h
  simp only [List.all_eq_true, List.mem_range, hk] at h
  have := h B.val (ZMod.val_lt B) b hb e he d hd
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
  rcases this with hn | hy
  · exact absurd ⟨h0, h1, h2⟩ hn
  · obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp hy
    refine ⟨t, ht, ?_⟩
    rw [← mtB_iff] at *
    have v1 : (B + (e : ZMod k)).val = (B.val + e) % k := val_add_nat B e
    have v2 : (B + (b : ZMod k)).val = (B.val + b) % k := val_add_nat B b
    have v3 : (B + (d : ZMod k)).val = (B.val + d) % k := val_add_nat B d
    rw [cOf_val h7, cOf_val h7, cOf_val h7, cOf_val h7, v1, v2, v3]
    exact hm

/-- If a matching alternation has four weak inequalities, `fail` is true. -/
theorem rho_fail_of (g : Geo) {e : Nat} {cyc : List Nat} {t : Nat × Nat × Nat × Nat}
    (ht : t ∈ alts cyc) {p1 p2 q1 q2 : Nat} (hm : Mt t p1 p2 q1 q2)
    (h11 : 0 ≤ g.z e p1 q1) (h12 : 0 ≤ g.z e p1 q2) (h21 : 0 ≤ g.z e p2 q1)
    (h22 : 0 ≤ g.z e p2 q2) : rho g (.fail e cyc) = true := by
  simp only [rho, List.any_eq_true]
  refine ⟨t, ht, ?_⟩
  simp only [Geo.yB, decide_eq_true_eq]
  obtain ⟨a, b⟩ := hm
  rcases a with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases b with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    simp only [a1, a2, b1, b2] <;> tauto

/-- **`fail` false and `AltCover2` give `RobUni`** of the depths `⟪x (c a), u⟫` along the cycle. -/
theorem robUni_of_alt {k : ℕ} [NeZero k] (g : Geo) {x : Fin 7 → ℝ³} (hx : ∀ i : Fin 7, g.x i.val = x i)
    {e : Nat} {u : ℝ³} (hu : g.vv e = u) {c : ZMod k → Fin 7} {cyc : List Nat} (hA : AltCover2 c cyc)
    (hf : rho g (.fail e cyc) = false) : RobUni (fun a : ZMod k => ⟪x (c a), u⟫) := by
  intro B b c' d h0 h1 h2 h3 ⟨e1, e2, e3, e4⟩
  obtain ⟨t, ht, hm⟩ := hA B b (by omega) c' (by omega) d h3 h0 h1 h2
  have hz : ∀ a b : Fin 7, ⟪x a, u⟫ ≤ ⟪x b, u⟫ → 0 ≤ g.z e b.val a.val := by
    intro a b hab
    simp only [Geo.z, hu, hx]
    have : ⟪u, x b - x a⟫ = ⟪x b, u⟫ - ⟪x a, u⟫ := by
      simp only [inner_sub_right, real_inner_comm]
    linarith
  have := rho_fail_of g ht hm (hz _ _ e1) (hz _ _ e3) (hz _ _ e2) (hz _ _ e4)
  rw [hf] at this
  exact absurd this (by simp)

/-! ### The rule clause -/

/-- Number of facets in a mask. -/
def popc (m : Nat) : Nat := ((List.range 9).filter fun t => m.testBit t).length

/-- The `Tp` signature in the clause (first `not Tp e mask _` literal). -/
def tpvOf (cl : List Lit) (e mask : Nat) : Nat :=
  (cl.findSome? fun l => match l with
    | (false, .tpv e' m' s') => if e' == e && m' == mask then some s' else none
    | _ => none).getD 0

/-- The encoder's cycle in the clause (first `fail e _` literal). -/
def failOf (cl : List Lit) (e : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (true, .fail e' c) => if e' == e then some c else none
    | _ => none).getD []

/-- The clause of the rule `(e, pp, mask)`. -/
def ruleLits (e pp mask sigp : Nat) (cyc : List Nat) : List Lit :=
  ((List.range 9).flatMap fun t =>
     if mask.testBit t then [(Fe e t).1, (Fe e t).2]
     else if pp.testBit t then [(Fe e t).1.neg] else [(Fe e t).2.neg]) ++
  (if 2 ≤ popc mask then [(false, V.tpv e mask sigp)] else []) ++
  (if 3 < (patCyc.getD pp []).length then [(true, V.fail e cyc)] else [])

/-- The signature `sigp` is the pattern on the mask, or its complement. -/
def sigOK (pp mask sigp : Nat) : Bool :=
  ((List.range 9).all fun t => !mask.testBit t || (pp.testBit t == sigp.testBit t)) ||
  ((List.range 9).all fun t => !mask.testBit t || (pp.testBit t != sigp.testBit t))

/-- The check of a rule row `(e, pp, mask)`. -/
def ruleOK (p : List Nat) (cl : List Lit) : Bool :=
  let e := prm p 0; let pp := prm p 1; let mask := prm p 2
  let L := patCyc.getD pp []
  let sigp := tpvOf cl e mask; let cyc := failOf cl e
  decide (e < 43 ∧ pp < 512 ∧ mask < 511) && sigOK pp mask sigp && cycChk pp L &&
  (L.length == 3 || altChk L cyc) && coversF cl (ruleLits e pp mask sigp cyc)

/-- For masks of at most one facet the tope exists. -/
theorem popc_le1 : ∀ m < 512, popc m < 2 →
    (∃ t0 : Fin 9, ∀ t : Fin 9, bits m t = true → t = t0) ∨ (∀ t : Fin 9, bits m t = false) := by
  decide +kernel


/-- A mask below 255 misses a facet. -/
theorem mask_miss : ∀ m < 511, ∃ t : Fin 9, bits m t = false := by decide +kernel

/-- The signature check gives the pattern on the mask, after complementing if needed. -/
theorem sig_exists {pp mask sigp : Nat} (h : sigOK pp mask sigp = true) :
    ∃ (sg : Fin 9 → Bool) (flip : Bool), (∀ t, bits mask t = true → bits pp t = sg t) ∧
      sg = (if flip then fun t => !bits sigp t else bits sigp) := by
  unfold sigOK at h
  simp only [Bool.or_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · refine ⟨bits sigp, false, fun t ht => ?_, by simp⟩
    rcases h t t.isLt with h1 | h1
    · simp [bits] at ht; simp [h1] at ht
    · simpa [bits] using h1
  · refine ⟨fun t => !bits sigp t, true, fun t ht => ?_, by simp⟩
    rcases h t t.isLt with h1 | h1
    · simp [bits] at ht; simp [h1] at ht
    · simp only [bits] at h1 ⊢
      cases h2 : pp.testBit t.val <;> cases h3 : sigp.testBit t.val <;> simp_all

/-- The cycle check gives a cycle of at least three. -/
theorem cycChk_len {pp : Nat} {L : List Nat} (h : cycChk pp L = true) : 3 ≤ L.length := by
  unfold cycChk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- **The core of the rule soundness**: all literals of the rule clause false gives a Rupert shape. -/
theorem rule_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hG : GeoOK (geoF F)) (e pp mask sigp : Nat) (cyc : List Nat) (he : e < 43) (hmask : mask < 511)
    (hsig : sigOK pp mask sigp = true) (hcyc : cycChk pp (patCyc.getD pp []) = true)
    (halt : ((patCyc.getD pp []).length == 3 || altChk (patCyc.getD pp []) cyc) = true)
    (hno : ∀ l ∈ ruleLits e pp mask sigp cyc, evalL (rho (geoF F)) l = false) :
    IsRupert (univ.image x) := by
  set L := patCyc.getD pp [] with hL
  have hlen := cycChk_len hcyc
  haveI : NeZero L.length := ⟨by omega⟩
  obtain ⟨h3, hinj, hcycOK⟩ := cycFacts (k := L.length) rfl hcyc
  set u := (geo0 F).vv e with hu
  have S : ∀ t : Fin 9, Sg3 (rho (geoF F)) (Fe e t.val) ⟪F.N t, u⟫ := fun t => by
    have := Fe_sound hG he t.isLt
    rwa [geoF_N] at this
  have mem1 : ∀ t : Fin 9, mask.testBit t.val = false → pp.testBit t.val = true →
      (Fe e t.val).1.neg ∈ ruleLits e pp mask sigp cyc := fun t h1 h2 => by
    simp only [ruleLits, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1, h2]⟩)
  have mem2 : ∀ t : Fin 9, mask.testBit t.val = false → pp.testBit t.val = false →
      (Fe e t.val).2.neg ∈ ruleLits e pp mask sigp cyc := fun t h1 h2 => by
    simp only [ruleLits, List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1, h2]⟩)
  have mem3 : ∀ t : Fin 9, mask.testBit t.val = true →
      (Fe e t.val).1 ∈ ruleLits e pp mask sigp cyc ∧ (Fe e t.val).2 ∈ ruleLits e pp mask sigp cyc :=
    fun t h1 => by
      simp only [ruleLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact ⟨Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1]⟩), Or.inl (Or.inl ⟨t.val, t.isLt, by simp [h1]⟩)⟩
  have neg_false : ∀ l : Lit, evalL (rho (geoF F)) l.neg = false → evalL (rho (geoF F)) l = true := by
    intro l h; rw [evalL_neg] at h; simpa using h
  have hoff : ∀ t, bits mask t = false → (bits pp t = true → 0 < ⟪F.N t, u⟫) ∧ (bits pp t = false → ⟪F.N t, u⟫ < 0) := by
    intro t ht
    have ht' : mask.testBit t.val = false := ht
    constructor
    · intro hp
      exact (S t).1.mp (neg_false _ (hno _ (mem1 t ht' hp)))
    · intro hp
      exact (S t).2.mp (neg_false _ (hno _ (mem2 t ht' hp)))
  obtain ⟨sg, flip, hsg, hsgdef⟩ := sig_exists hsig
  have hon : ∀ t, bits mask t = true → ⟪F.N t, u⟫ = 0 ∧ bits pp t = sg t := by
    intro t ht
    have ht' : mask.testBit t.val = true := ht
    obtain ⟨m1, m2⟩ := mem3 t ht'
    have a1 := hno _ m1
    have a2 := hno _ m2
    refine ⟨?_, hsg t ht⟩
    have n1 : ¬ 0 < ⟪F.N t, u⟫ := fun h' => by simp [(S t).1.mpr h'] at a1
    have n2 : ¬ ⟪F.N t, u⟫ < 0 := fun h' => by simp [(S t).2.mpr h'] at a2
    exact le_antisymm (not_lt.mp n1) (not_lt.mp n2)
  obtain ⟨t0, ht0⟩ := mask_miss mask hmask
  have htp : TpSem F u (bits mask) sg := by
    have conv : TpSem F u (bits mask) (bits sigp) → TpSem F u (bits mask) sg := by
      intro hT
      rw [hsgdef]
      cases flip
      · simpa using hT
      · simpa using TpSem.compl F hT
    by_cases pc : 2 ≤ popc mask
    · apply conv
      have hm : ((false, V.tpv e mask sigp) : Lit) ∈ ruleLits e pp mask sigp cyc := by
        simp [ruleLits, pc]
      have := hno _ hm
      have h2 : rho (geoF F) (V.tpv e mask sigp) = true := by simpa [evalL] using this
      rw [rho_tpv] at h2
      simpa using h2
    · have := popc_le1 mask (by omega) (by omega)
      rcases this with ⟨s0, hs0⟩ | hall
      · exact tpSem_of_tope F u (tope_single F (bits mask) sg s0 hs0 (by
          have := hG.hF.nn s0.val s0.isLt
          rw [geoF_N] at this
          exact this.ne'))
      · exact Or.inr (Or.inr ⟨0, fun t ht => by simp [hall t] at ht⟩)
  have hU : RobUni (fun a : ZMod L.length => ⟪x (cOf L a), u⟫) := by
    by_cases h3' : L.length = 3
    · intro B b c d h0 h1 h2 h3'' ; omega
    · have hf : 3 < L.length := by omega
      have hm : ((true, V.fail e cyc) : Lit) ∈ ruleLits e pp mask sigp cyc := by
        have hf' : 3 < (patCyc.getD pp []).length := hf
        simp only [ruleLits, List.mem_append]
        right; rw [ite_eq_left hf']; exact List.mem_singleton_self _
      have := hno _ hm
      have hrf : rho (geoF F) (V.fail e cyc) = false := by simpa [evalL] using this
      have hk3 : (L.length == 3) = false := by simpa using h3'
      rw [hk3, Bool.false_or] at halt
      have hA : AltCover2 (cOf (k := L.length) L) cyc := by
        refine altFacts rfl ?_ halt
        unfold cycChk at hcyc
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcyc
        exact fun v hv => hcyc.1.1.2 v hv
      exact robUni_of_alt (geoF F) (geoF_x F) rfl hA hrf
  exact rule_leaf' F hx hinj h3 hcycOK hoff hon ⟨t0, ht0⟩ htp hU

end Minimality.H24.SAT
