module

public import Minimality.Type21SAT.Rule2

@[expose] public section

/-!
# L3, part 19: the witness rows (family 19)

A witness row is `(e, mask, sig, d, eps, zero)` and the clause
`Tp(e, mask, sig') or (for s in mask: s in zero: Fe d s is nonzero; s not in zero: the sign of eps * Fe d s is not sig s)`.
`sig'` is `sig` or its complement on the mask (read off the clause).  Soundness: a view `d` that is zero on
the facets of `zero` (one or two of them) and signed on the rest of the mask gives a tope (`tpSem_witness0/1/2`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

/-- The `Tp` signature in the clause (first positive `tpv e mask _` literal). -/
def tpvPos (cl : List Lit) (e mask : Nat) : Nat :=
  (cl.findSome? fun l => match l with
    | (true, .tpv e' m' s') => if e' == e && m' == mask then some s' else none
    | _ => none).getD 0

/-- The literals of the witness clause. -/
def witLits (e mask sigp sig d eps zero : Nat) : List Lit :=
  [(true, V.tpv e mask sigp)] ++
  (List.range 8).flatMap fun s =>
    if mask.testBit s then
      (if zero.testBit s then [(Fe d s).1, (Fe d s).2]
       else if sig.testBit s == (eps == 1) then [(Fe d s).1.neg] else [(Fe d s).2.neg])
    else []

/-- The check of a witness row. -/
def witOK (p : List Nat) (cl : List Lit) : Bool :=
  let e := prm p 0; let mask := prm p 1; let sig := prm p 2; let d := prm p 3; let eps := prm p 4
  let zero := prm p 5
  let sigp := tpvPos cl e mask
  decide (e < 36 ∧ d < 36 ∧ mask < 256 ∧ sig < 256 ∧ zero < 256 ∧ (eps = 1 ∨ eps = 999)) &&
  sigOK sig mask sigp && decide (popc zero ≤ 2) && (popc zero ≤ 1 || decide (3 ≤ popc mask)) &&
  (List.range 8).all (fun s => !zero.testBit s || mask.testBit s) &&
  (List.range 8).all (fun s => (List.range 8).all fun t =>
    !zero.testBit s || !zero.testBit t || s == t || (sig.testBit s != sig.testBit t)) &&
  coversF cl (witLits e mask sigp sig d eps zero)

/-- A set of at most two facets is empty, one or two facets. -/
theorem zcase : ∀ z < 256, popc z ≤ 2 → (∀ t : Fin 8, bits z t = false) ∨
    (∃ t0 : Fin 8, ∀ t : Fin 8, bits z t = true ↔ t = t0) ∨
    (∃ t0 t1 : Fin 8, t0 ≠ t1 ∧ ∀ t : Fin 8, bits z t = true ↔ (t = t0 ∨ t = t1)) := by
  decide +kernel

/-- A set of at most one facet has no two distinct facets. -/
theorem popc1 : ∀ z < 256, popc z ≤ 1 → ∀ t0 t1 : Fin 8, bits z t0 = true → bits z t1 = true → t0 = t1 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- A mask with at least three facets has a third facet beside two of its facets. -/
theorem third_facet : ∀ m < 256, 3 ≤ popc m → ∀ t0 t1 : Fin 8, bits m t0 = true → bits m t1 = true →
    t0 ≠ t1 → ∃ s : Fin 8, bits m s = true ∧ s ≠ t0 ∧ s ≠ t1 := by
  decide +kernel

/-- Distinct facets of type 21: the vertex set of the first is nonempty and the second is not inside it. -/
theorem facet_pair : ∀ t0 t1 : Fin 8, t0 ≠ t1 → (S21 t0).Nonempty ∧ ¬ S21 t1 ⊆ S21 t0 := by
  decide +kernel

/-- **The core of the witness soundness**: all literals of the witness clause false is impossible. -/
theorem wit_core {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (hG : GeoOK (geoF F))
    (e d mask sig sigp zero eps : Nat) (he : e < 36) (hd : d < 36) (hmask : mask < 256)
    (hzero : zero < 256) (heps : eps = 1 ∨ eps = 999) (hsig : sigOK sig mask sigp = true)
    (hz2 : popc zero ≤ 2) (hz3 : popc zero ≤ 1 ∨ 3 ≤ popc mask)
    (hzm : ∀ s < 8, zero.testBit s = true → mask.testBit s = true)
    (hdiff : ∀ s < 8, ∀ t < 8, zero.testBit s = true → zero.testBit t = true → s ≠ t →
      sig.testBit s ≠ sig.testBit t)
    (hno : ∀ l ∈ witLits e mask sigp sig d eps zero, evalL (rho (geoF F)) l = false) : False := by
  set u := (geo0 F).vv e with hu
  set w := (geo0 F).vv d with hw
  have S : ∀ t : Fin 8, Sg3 (rho (geoF F)) (Fe d t.val) ⟪F.N t, w⟫ := fun t => by
    have := Fe_sound hG hd t.isLt
    rwa [geoF_N] at this
  -- the real sign of eps
  set er : ℝ := if eps = 1 then 1 else -1 with her
  have neg_false : ∀ l : Lit, evalL (rho (geoF F)) l.neg = false → evalL (rho (geoF F)) l = true := by
    intro l h; rw [evalL_neg] at h; simpa using h
  obtain ⟨sg, flip, hsg, hsgdef⟩ := sig_exists hsig
  -- the signs off the zero set
  have hs : ∀ t : Fin 8, bits mask t = true → bits zero t = false →
      (sg t = true → 0 < er * ⟪F.N t, w⟫) ∧ (sg t = false → er * ⟪F.N t, w⟫ < 0) := by
    intro t ht hzt
    have ht' : mask.testBit t.val = true := ht
    have hzt' : zero.testBit t.val = false := hzt
    have hsgt : bits sig t = sg t := hsg t ht
    have hsgt' : sig.testBit t.val = sg t := hsgt
    by_cases h1 : eps = 1
    · have her1 : er = 1 := by simp [her, h1]
      rw [her1]
      cases hs : sg t
      · refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
        have hm : (Fe d t.val).2.neg ∈ witLits e mask sigp sig d eps zero := by
          simp only [witLits, List.mem_append, List.mem_flatMap, List.mem_range]
          refine Or.inr ⟨t.val, t.isLt, ?_⟩
          simp [ht', hzt', hsgt', hs, h1]
        have := neg_false _ (hno _ hm)
        have := (S t).2.mp this
        linarith
      · refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
        have hm : (Fe d t.val).1.neg ∈ witLits e mask sigp sig d eps zero := by
          simp only [witLits, List.mem_append, List.mem_flatMap, List.mem_range]
          refine Or.inr ⟨t.val, t.isLt, ?_⟩
          simp [ht', hzt', hsgt', hs, h1]
        have := neg_false _ (hno _ hm)
        have := (S t).1.mp this
        linarith
    · have h999 : eps = 999 := by omega
      have her1 : er = -1 := by simp [her, h1]
      rw [her1]
      cases hs : sg t
      · refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
        have hm : (Fe d t.val).1.neg ∈ witLits e mask sigp sig d eps zero := by
          simp only [witLits, List.mem_append, List.mem_flatMap, List.mem_range]
          refine Or.inr ⟨t.val, t.isLt, ?_⟩
          simp [ht', hzt', hsgt', hs, h1]
        have := neg_false _ (hno _ hm)
        have := (S t).1.mp this
        linarith
      · refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
        have hm : (Fe d t.val).2.neg ∈ witLits e mask sigp sig d eps zero := by
          simp only [witLits, List.mem_append, List.mem_flatMap, List.mem_range]
          refine Or.inr ⟨t.val, t.isLt, ?_⟩
          simp [ht', hzt', hsgt', hs, h1]
        have := neg_false _ (hno _ hm)
        have := (S t).2.mp this
        linarith
  -- the zero set: the view is edge-on
  have hz : ∀ t : Fin 8, bits zero t = true → ⟪F.N t, w⟫ = 0 := by
    intro t ht
    have ht' : zero.testBit t.val = true := ht
    have hmt : mask.testBit t.val = true := hzm t.val t.isLt ht'
    have m1 : (Fe d t.val).1 ∈ witLits e mask sigp sig d eps zero := by
      simp only [witLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inr ⟨t.val, t.isLt, by simp [hmt, ht']⟩
    have m2 : (Fe d t.val).2 ∈ witLits e mask sigp sig d eps zero := by
      simp only [witLits, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inr ⟨t.val, t.isLt, by simp [hmt, ht']⟩
    have a1 := hno _ m1
    have a2 := hno _ m2
    have n1 : ¬ 0 < ⟪F.N t, w⟫ := fun h' => by simp [(S t).1.mpr h'] at a1
    have n2 : ¬ ⟪F.N t, w⟫ < 0 := fun h' => by simp [(S t).2.mpr h'] at a2
    exact le_antisymm (not_lt.mp n1) (not_lt.mp n2)
  -- Tp is false
  have hTp : ¬ TpSem F u (bits mask) (bits sigp) := by
    have hm : ((true, V.tpv e mask sigp) : Lit) ∈ witLits e mask sigp sig d eps zero := by
      simp [witLits]
    have := hno _ hm
    have h2 : rho (geoF F) (V.tpv e mask sigp) = false := by simpa [evalL] using this
    rw [rho_tpv] at h2
    simpa using h2
  have hTp' : ¬ TpSem F u (bits mask) sg := by
    intro hT
    apply hTp
    rw [hsgdef] at hT
    cases flip
    · simpa using hT
    · simpa using TpSem.compl F hT
  apply hTp'
  have hsr : ∀ t : Fin 8, bits mask t = true → bits zero t = false →
      (sg t = true → 0 < er * ⟪F.N t, w⟫) ∧ (sg t = false → er * ⟪F.N t, w⟫ < 0) := hs
  have hN : ∀ t : Fin 8, ⟪F.N t, F.N t⟫ ≠ 0 := fun t => by
    have := hG.hF.nn t.val t.isLt
    rw [geoF_N] at this
    exact this.ne'
  rcases zcase zero hzero hz2 with h0 | ⟨t0, h1⟩ | ⟨t0, t1, hne, h2⟩
  · exact tpSem_witness0 F u w (bits mask) sg er (fun t ht => hsr t ht (h0 t))
  · have ht0 : bits zero t0 = true := (h1 t0).mpr rfl
    have hm0 : bits mask t0 = true := hzm t0.val t0.isLt ht0
    refine tpSem_witness1 F u w (bits mask) sg er t0 hm0 (hN t0) (hz t0 ht0) ?_
    intro t ht hne
    exact hsr t ht (by
      by_contra hc
      exact hne ((h1 t).mp (by simpa using hc)))
  · have ht0 : bits zero t0 = true := (h2 t0).mpr (Or.inl rfl)
    have ht1 : bits zero t1 = true := (h2 t1).mpr (Or.inr rfl)
    have hm0 : bits mask t0 = true := hzm t0.val t0.isLt ht0
    have hm1 : bits mask t1 = true := hzm t1.val t1.isLt ht1
    have h3 : 3 ≤ popc mask := by
      rcases hz3 with h | h
      · exfalso
        exact absurd (popc1 zero hzero h t0 t1 ht0 ht1) hne
      · exact h
    obtain ⟨s, hsm, hs0, hs1⟩ := third_facet mask hmask h3 t0 t1 hm0 hm1 hne
    have hsg01 : sg t0 ≠ sg t1 := by
      have := hdiff t0.val t0.isLt t1.val t1.isLt (by exact ht0) (by exact ht1)
        (fun h => hne (Fin.ext h))
      have e0 : bits sig t0 = sg t0 := hsg t0 hm0
      have e1 : bits sig t1 = sg t1 := hsg t1 hm1
      simp only [bits] at e0 e1
      intro hh; apply this; rw [e0, e1, hh]
    obtain ⟨hS0, hsub⟩ := facet_pair t0 t1 hne
    exact tpSem_witness2 F u w (bits mask) sg er t0 t1 s hm0 hm1 hsm hs0 hs1 hne hsg01 (hN t0) (hN t1)
      (by simpa [S21] using hS0) (by simpa using hsub) (hz t0 ht0) (hz t1 ht1) (by
        intro t ht h0' h1'
        exact hsr t ht (by
          by_contra hc
          have := (h2 t).mp (by simpa using hc)
          rcases this with h | h
          · exact h0' h
          · exact h1' h))

/-- **A witness row that passes the check is true of the real data** (no hypothesis on the view). -/
theorem witOK_sound {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (hG : GeoOK (geoF F)) {p : List Nat}
    {cl : List Lit} (h : witOK p cl = true) : Holds (rho (geoF F)) cl := by
  by_contra hn
  unfold witOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨he, hd, hmask, hsg, hzero, heps⟩, hsig⟩, hz2⟩, hz3⟩, hzm⟩, hdiff⟩, hcov⟩ := h
  refine wit_core F hG _ _ _ _ _ _ _ he hd hmask hzero heps hsig hz2 ?_ ?_ ?_ ?_
  · rcases hz3 with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  · intro s hs hz
    rcases hzm s hs with h | h
    · rw [hz] at h; exact absurd h (by simp)
    · exact h
  · intro s hs t ht hzs hzt hst
    rcases hdiff s hs t ht with ((h | h) | h) | h
    · rw [hzs] at h; exact absurd h (by simp)
    · rw [hzt] at h; exact absurd h (by simp)
    · exact absurd (beq_iff_eq.mp h) hst
    · exact bne_iff_ne.mp h
  · intro l hl
    rw [coversF_eq] at hcov
    have := List.all_eq_true.mp hcov l hl
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
    rcases this with h0 | h0
    · subst h0
      have e : rho (geoF F) V.tru = true := rho_proper _
      simp [lfalse, evalL, e]
    · rw [← Bool.not_eq_true]; exact fun he' => hn ⟨l, h0, he'⟩

end Minimality.H21.SAT
