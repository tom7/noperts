module

public import Minimality.Type29SAT.Tll

@[expose] public section

/-!
# Type 29: the quad relations (family 23, `eq` rows with a K atom)

Let `F` be a facet and `I` an adjacent facet that share the edge `y`; let `x` be an edge in `F`.  Then
`K(x, y) = det3 (d x) (d y) (N F)` and the facing `<N I, d x>` satisfy
`<N I, d x> * <N F, N F> * <d y, d y> = K(x, y) * det3 (N F) (N I) (d y)`,
and `det3 (N F) (N I) (d y)` has the constant sign `-oriv F p q s'` (`kap_sound`).  So the facing has the sign of `K`
times a constant: the clauses `K > 0 => facing > 0` and so on.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The Gram identity behind the quad relation. -/
theorem krel_id (a e nF nI : ℝ³) (h1 : ⟪nF, a⟫ = 0) (h2 : ⟪nF, e⟫ = 0) (h3 : ⟪nI, e⟫ = 0) :
    ⟪nI, a⟫ * (⟪nF, nF⟫ * ⟪e, e⟫) = det3 a e nF * det3 nF nI e := by
  have g : det3 a e nF * det3 nI nF e =
      ⟪a, nI⟫ * (⟪e, nF⟫ * ⟪nF, e⟫ - ⟪e, e⟫ * ⟪nF, nF⟫) -
      ⟪a, nF⟫ * (⟪e, nI⟫ * ⟪nF, e⟫ - ⟪e, e⟫ * ⟪nF, nI⟫) +
      ⟪a, e⟫ * (⟪e, nI⟫ * ⟪nF, nF⟫ - ⟪e, nF⟫ * ⟪nF, nI⟫) := by
    simp only [det3_expand, inn3]; ring
  have s : det3 nF nI e = - det3 nI nF e := by simp only [det3_expand]; ring
  have c1 : ⟪a, nF⟫ = 0 := by rw [real_inner_comm]; exact h1
  have c2 : ⟪e, nF⟫ = 0 := by rw [real_inner_comm]; exact h2
  have c3 : ⟪e, nI⟫ = 0 := by rw [real_inner_comm]; exact h3
  rw [s, mul_neg, g, c1, c2, c3, real_inner_comm nI a]
  ring

/-- The signed entry of the quad relation: `K(x, y)` times the constant sign of `det3 (N F) (N I) (d y)`. -/
def krelS (F x y s' : Nat) : S3 := mul3 (atomS (V.kv F x y)) (cS (-(oriv F (EA y) (EB y) s')))

/-- **The facing of `I` at the edge `x` of `F` has the sign of `K(x, y)` times a constant.** -/
theorem krel_sign {g : Geo} (hF : FacOK g) (hO : OriOK g) (F I x y s' r' : Nat)
    (hx1 : inF F (EA x) = true) (hx2 : inF F (EB x) = true)
    (hp1 : inF F (EA y) = true) (hq1 : inF F (EB y) = true)
    (hp2 : inF I (EA y) = true) (hq2 : inF I (EB y) = true)
    (hrI : inF I r' = true) (hrF : inF F r' = false) (hsF : inF F s' = true) (hsI : inF I s' = false)
    (hr7 : r' < 7) (hs7 : s' < 7) (hF9 : F < 9) (ho : oriv F (EA y) (EB y) s' ≠ 0)
    (hxA : EA x < 7) (hxB : EB x < 7) (hyB : EB y < 7)
    (hf : ∃ f, inF f (EA y) = true ∧ inF f (EB y) = false) :
    Sg3 (rho g) (krelS F x y s') ⟪g.N I, g.dv x⟫ := by
  obtain ⟨f, hfA, hfB⟩ := hf
  have hd : g.x (EA y) - g.x (EB y) ≠ 0 := dne hF _ _ f hyB hfA hfB
  have dd : 0 < ⟪g.x (EA y) - g.x (EB y), g.x (EA y) - g.x (EB y)⟫ := real_inner_self_pos.mpr hd
  have nn : 0 < ⟪g.N F, g.N F⟫ := hF.nn F hF9
  have h1 : ⟪g.N F, g.dv x⟫ = 0 := hF.zero F _ _ hx1 hx2
  have h2 : ⟪g.N F, g.dv y⟫ = 0 := hF.zero F _ _ hp1 hq1
  have h3 : ⟪g.N I, g.dv y⟫ = 0 := hF.zero I _ _ hp2 hq2
  have ID := krel_id (g.dv x) (g.dv y) (g.N F) (g.N I) h1 h2 h3
  have K' := kap_sound hF hO F I (EA y) (EB y) r' s' hp1 hq1 hp2 hq2 hrI hrF hsF hsI hr7 hs7 ho hd
  have SK := Sg3_atomG g (v := V.kv F x y) (by simp [rho])
  have SD := Sg3_of_mulpos (rho_proper g) (n := -(oriv F (EA y) (EB y) s')) (r := det3 (g.N F) (g.N I) (g.dv y))
    (by push_cast; exact K')
  have P := Sg3.mul3 (rho_proper g) (rho_gateOK g) SK SD
  have ee : 0 < ⟪g.dv y, g.dv y⟫ := dd
  have pos : 0 < ⟪g.N F, g.N F⟫ * ⟪g.dv y, g.dv y⟫ := mul_pos nn ee
  have e : ⟪g.N I, g.dv x⟫ = (1 / (⟪g.N F, g.N F⟫ * ⟪g.dv y, g.dv y⟫)) * (g.atom (V.kv F x y) * det3 (g.N F) (g.N I) (g.dv y)) := by
    show _ = _ * (det3 (g.dv x) (g.dv y) (g.N F) * _)
    rw [← ID]; field_simp
  rw [e]
  exact Sg3.scale (by positivity) P

/-- The four implications between the entry and the facing. -/
def krelClauses (F I x y s' : Nat) : List (List Lit) :=
  let a := krelS F x y s'; let b := fup3 I (EA x) (EB x)
  [[a.1.neg, b.1], [a.2.neg, b.2], [b.1.neg, a.1], [b.2.neg, a.2]]

/-- Side conditions of a quad relation row (parameters `F I x y s' r'`). -/
def krelSide (F I x y s' r' : Nat) : Bool :=
  decide (F < 9 ∧ I < 9 ∧ x < 21 ∧ y < 21 ∧ s' < 7 ∧ r' < 7) &&
  inF F (EA x) && inF F (EB x) && inF F (EA y) && inF F (EB y) && inF I (EA y) && inF I (EB y) &&
  inF I r' && !inF F r' && inF F s' && !inF I s' && decide (oriv F (EA y) (EB y) s' ≠ 0) &&
  (List.range 9).any (fun f => inF f (EA y) && !inF f (EB y))

/-- The check of a quad relation row (the entry `K(x, y)` and the facing at the edge `x`). -/
def krelOK1 (p : List Nat) (cl : List Lit) : Bool :=
  krelSide (prm p 0) (prm p 1) (prm p 2) (prm p 3) (prm p 4) (prm p 5) &&
  anyCov cl (krelClauses (prm p 0) (prm p 1) (prm p 2) (prm p 3) (prm p 4))

/-- An implication between literals that follows from the semantics holds as a clause. -/
theorem holds_imp {ρ : V → Bool} {l m : Lit} (h : evalL ρ l = true → evalL ρ m = true) : Holds ρ [l.neg, m] := by
  by_cases hl : evalL ρ l = true
  · exact ⟨m, by simp, h hl⟩
  · exact ⟨l.neg, by simp, by rw [evalL_neg]; simp [hl]⟩

/-- **A quad relation row that passes the first check is true** of the real data. -/
theorem krelOK1_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : krelOK1 p cl = true) : Holds (rho g) cl := by
  unfold krelOK1 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hs, hc⟩ := h
  unfold krelSide at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hx1⟩, hx2⟩, hp1⟩, hq1⟩, hp2⟩, hq2⟩, hrI⟩, hrF⟩, hsF⟩, hsI⟩, ho⟩, ⟨f, -, hf⟩⟩ := hs
  obtain ⟨hF9, hI9, hx21, hy21, hs7, hr7⟩ := hb
  have hxAB := EAB_lt (prm p 2) hx21
  have hyAB := EAB_lt (prm p 3) hy21
  have SA := krel_sign hG.hF hG.hO (prm p 0) (prm p 1) (prm p 2) (prm p 3) (prm p 4) (prm p 5)
    hx1 hx2 hp1 hq1 hp2 hq2 hrI hrF hsF hsI hr7 hs7 hF9 ho hxAB.1 hxAB.2 hyAB.2 ⟨f, hf⟩
  have SB : Sg3 (rho g) (fup3 (prm p 1) (EA (prm p 2)) (EB (prm p 2))) ⟪g.N (prm p 1), g.dv (prm p 2)⟫ :=
    fup3_sound hG.hF (prm p 1) _ _ hxAB.1 hxAB.2
  apply anyCov_holds (rho_proper g) hc
  intro s hs
  simp only [krelClauses, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact holds_imp fun h' => SB.1.mpr (SA.1.mp h')
  · exact holds_imp fun h' => SB.2.mpr (SA.2.mp h')
  · exact holds_imp fun h' => SA.1.mpr (SB.1.mp h')
  · exact holds_imp fun h' => SA.2.mpr (SB.2.mp h')

/-- **The swapped quad relation**: the facing of `I` at the edge `X` of `F` has the sign of the atom `K(Y, X)` (entry with the
roles of the two edges exchanged) times the constant sign of `det3 (N F) (N I) (d Y)` (here `Y` is the edge shared by `F` and `I`);
this is `krel_sign` with `det3 (d Y) (d X) (N F) = - det3 (d X) (d Y) (N F)`. -/
theorem krel_sign2 {g : Geo} (hF : FacOK g) (hO : OriOK g) (F I X Y s' r' : Nat)
    (hx1 : inF F (EA X) = true) (hx2 : inF F (EB X) = true)
    (hp1 : inF F (EA Y) = true) (hq1 : inF F (EB Y) = true)
    (hp2 : inF I (EA Y) = true) (hq2 : inF I (EB Y) = true)
    (hrI : inF I r' = true) (hrF : inF F r' = false) (hsF : inF F s' = true) (hsI : inF I s' = false)
    (hr7 : r' < 7) (hs7 : s' < 7) (hF9 : F < 9) (ho : oriv F (EA Y) (EB Y) s' ≠ 0)
    (hxA : EA X < 7) (hxB : EB X < 7) (hyB : EB Y < 7)
    (hf : ∃ f, inF f (EA Y) = true ∧ inF f (EB Y) = false) :
    Sg3 (rho g) (mul3 (atomS (V.kv F Y X)) (cS (oriv F (EA Y) (EB Y) s'))) ⟪g.N I, g.dv X⟫ := by
  obtain ⟨f, hfA, hfB⟩ := hf
  have hd : g.x (EA Y) - g.x (EB Y) ≠ 0 := dne hF _ _ f hyB hfA hfB
  have dd : 0 < ⟪g.x (EA Y) - g.x (EB Y), g.x (EA Y) - g.x (EB Y)⟫ := real_inner_self_pos.mpr hd
  have nn : 0 < ⟪g.N F, g.N F⟫ := hF.nn F hF9
  have h1 : ⟪g.N F, g.dv X⟫ = 0 := hF.zero F _ _ hx1 hx2
  have h2 : ⟪g.N F, g.dv Y⟫ = 0 := hF.zero F _ _ hp1 hq1
  have h3 : ⟪g.N I, g.dv Y⟫ = 0 := hF.zero I _ _ hp2 hq2
  have ID := krel_id (g.dv X) (g.dv Y) (g.N F) (g.N I) h1 h2 h3
  have K' := kap_sound hF hO F I (EA Y) (EB Y) r' s' hp1 hq1 hp2 hq2 hrI hrF hsF hsI hr7 hs7 ho hd
  have SK := Sg3_atomG g (v := V.kv F Y X) (by simp [rho])
  have SD := Sg3_of_mulpos (rho_proper g) (n := (oriv F (EA Y) (EB Y) s')) (r := - det3 (g.N F) (g.N I) (g.dv Y))
    (by
      have K'' : 0 < -((oriv F (EA Y) (EB Y) s' : Int) : ℝ) * det3 (g.N F) (g.N I) (g.dv Y) := by
        exact K'
      nlinarith [K''])
  have P := Sg3.mul3 (rho_proper g) (rho_gateOK g) SK SD
  have ee : 0 < ⟪g.dv Y, g.dv Y⟫ := dd
  have pos : 0 < ⟪g.N F, g.N F⟫ * ⟪g.dv Y, g.dv Y⟫ := mul_pos nn ee
  have h4 : g.atom (V.kv F Y X) = - det3 (g.dv X) (g.dv Y) (g.N F) := by
    show det3 (g.dv Y) (g.dv X) (g.N F) = _
    simp only [det3_expand]; ring
  have e : ⟪g.N I, g.dv X⟫ = (1 / (⟪g.N F, g.N F⟫ * ⟪g.dv Y, g.dv Y⟫)) *
      (g.atom (V.kv F Y X) * (- det3 (g.N F) (g.N I) (g.dv Y))) := by
    rw [h4, neg_mul_neg, ← ID]; field_simp
  rw [e]
  exact Sg3.scale (by positivity) P

/-- The four implications of the swapped quad relation. -/
def krelClauses2 (F I Y X s' : Nat) : List (List Lit) :=
  let a := mul3 (atomS (V.kv F Y X)) (cS (oriv F (EA Y) (EB Y) s')); let b := fup3 I (EA X) (EB X)
  [[a.1.neg, b.1], [a.2.neg, b.2], [b.1.neg, a.1], [b.2.neg, a.2]]

/-- The check of a swapped quad relation row: the row parameters are `F I Y X s' r'` (`K(Y, X)`, facing at `X`). -/
def krelOK2 (p : List Nat) (cl : List Lit) : Bool :=
  krelSide (prm p 0) (prm p 1) (prm p 3) (prm p 2) (prm p 4) (prm p 5) &&
  anyCov cl (krelClauses2 (prm p 0) (prm p 1) (prm p 2) (prm p 3) (prm p 4))

/-- **A swapped quad relation row that passes the check is true** of the real data. -/
theorem krelOK2_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : krelOK2 p cl = true) : Holds (rho g) cl := by
  unfold krelOK2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hs, hc⟩ := h
  unfold krelSide at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hx1⟩, hx2⟩, hp1⟩, hq1⟩, hp2⟩, hq2⟩, hrI⟩, hrF⟩, hsF⟩, hsI⟩, ho⟩, ⟨f, -, hf⟩⟩ := hs
  obtain ⟨hF9, hI9, hx21, hy21, hs7, hr7⟩ := hb
  have hxAB := EAB_lt (prm p 3) hx21
  have hyAB := EAB_lt (prm p 2) hy21
  have SA := krel_sign2 hG.hF hG.hO (prm p 0) (prm p 1) (prm p 3) (prm p 2) (prm p 4) (prm p 5)
    hx1 hx2 hp1 hq1 hp2 hq2 hrI hrF hsF hsI hr7 hs7 hF9 ho hxAB.1 hxAB.2 hyAB.2 ⟨f, hf⟩
  have SB : Sg3 (rho g) (fup3 (prm p 1) (EA (prm p 3)) (EB (prm p 3))) ⟪g.N (prm p 1), g.dv (prm p 3)⟫ :=
    fup3_sound hG.hF (prm p 1) _ _ hxAB.1 hxAB.2
  apply anyCov_holds (rho_proper g) hc
  intro s hs
  simp only [krelClauses2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact holds_imp fun h' => SB.1.mpr (SA.1.mp h')
  · exact holds_imp fun h' => SB.2.mpr (SA.2.mp h')
  · exact holds_imp fun h' => SA.1.mpr (SB.1.mp h')
  · exact holds_imp fun h' => SA.2.mpr (SB.2.mp h')

/-- A quad relation row: the plain form or the swapped form. -/
def krelOK (p : List Nat) (cl : List Lit) : Bool := krelOK1 p cl || krelOK2 p cl

/-- **A quad relation row that passes the check is true** of the real data. -/
theorem krelOK_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : krelOK p cl = true) : Holds (rho g) cl := by
  unfold krelOK at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact krelOK1_sound hG h
  · exact krelOK2_sound hG h

end Minimality.H29.SAT
