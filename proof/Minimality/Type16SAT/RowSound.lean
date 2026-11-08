module

public import Minimality.Type16SAT.Row

@[expose] public section

/-!
# L3, part 14: soundness of the row check (all families but rules and witnesses)
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical
open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- Swapping the factors of the cross product negates it. -/
theorem cross_swap' (a b : ℝ³) : cross b a = -cross a b := by
  ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two] <;> ring

/-- Sign bookkeeping: `c d > 0` and the sign of `s c` give the sign of `s d`. -/
theorem kap_core (s c : Int) (d : ℝ) (hs : s = 1 ∨ s = -1) (hc : c ≠ 0) (S : 0 < (c : ℝ) * d)
    (hsc : s * c ≠ 0) : (0 < s * c → 0 < (s : ℝ) * d) ∧ (¬ 0 < s * c → (s : ℝ) * d < 0) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have e : ∀ _ : Unit, ((s : ℝ) * c) * ((c : ℝ) * d) = (c : ℝ) ^ 2 * ((s : ℝ) * d) := fun _ => by ring
  constructor
  · intro hp
    have hp' : (0 : ℝ) < (s : ℝ) * c := by exact_mod_cast hp
    have : 0 < ((s : ℝ) * c) * ((c : ℝ) * d) := mul_pos hp' S
    rw [e ()] at this
    exact (pos_iff_pos_of_mul_pos this).mp (by positivity)
  · intro hp
    have hp' : (s : ℝ) * c < 0 := by
      have : s * c < 0 := lt_of_le_of_ne (not_lt.mp hp) hsc
      exact_mod_cast this
    have : ((s : ℝ) * c) * ((c : ℝ) * d) < 0 := mul_neg_of_neg_of_pos hp' S
    rw [e ()] at this
    exact not_le.mp fun h => absurd this (not_lt.mpr (mul_nonneg (sq_nonneg _) h))

/-- The kappa sign of a line row is the sign of `s * det(d1, d2, N a)`, from the constant `Aconst`. -/
theorem kap_sign {g : Geo} (hO : OriOK g) (a x y : Nat) (s : Int) (hs : s = 1 ∨ s = -1)
    (hne : s * Aconst a x y ≠ 0) (kp : Bool) (hk : decide (0 < s * Aconst a x y) = kp) :
    (if kp then 0 < (s : ℝ) * det3 (g.dv x) (g.dv y) (g.N a)
      else (s : ℝ) * det3 (g.dv x) (g.dv y) (g.N a) < 0) := by
  have hc : Aconst a x y ≠ 0 := fun h0 => hne (by rw [h0]; simp)
  have K := kap_core s _ _ hs hc (Aconst_sound hO _ _ _ hc) hne
  cases kp
  · simp only [decide_eq_false_iff_not] at hk
    simpa using K.2 hk
  · simp only [decide_eq_true_eq] at hk
    simpa using K.1 hk

/-- The `cramer` rows are true. -/
theorem cramerOK_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : cramerOK p cl = true) : Holds (rho g) cl := by
  unfold cramerOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -, -, -, h1, h2⟩, k1⟩, k2⟩, k3⟩, k4⟩, hc⟩ := h
  exact anyCov_holds (rho_proper g) hc
    (cramer_sound hG.eok _ _ _ _ _ _ k1 k2 k3 k4 ⟨h1, h2⟩ ⟨h1, h2⟩ ⟨h1, h2⟩ ⟨h1, h2⟩)

/-- The `row3` rows are true. -/
theorem row3OK_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : row3OK p cl = true) : Holds (rho g) cl := by
  unfold row3OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨he, ha, hb, hc, h1, h2, h3⟩, hcov⟩ := h
  exact anyCov_holds (rho_proper g) hcov
    (row3_sound _ _ _ _ (fun h' => hG.hv _ h') (fun a b hab hb => vv_EI g hab hb) ha hb hc h1 h2 h3)

/-- The `row4` rows are true. -/
theorem row4OK_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : row4OK p cl = true) : Holds (rho g) cl := by
  unfold row4OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h0, h1, h2, h3⟩, k1⟩, k2⟩, k3⟩, k4⟩, hcov⟩ := h
  exact anyCov_holds (rho_proper g) hcov
    (row4_sound hG.eok _ _ _ _ _ (fun h' => hG.hv _ h') (fun f hf => vv_lt g hf) h0 h1 h2 h3 k1 k2 k3 k4)

/-- The lines of the encoder are pairs of distinct facets below 8. -/
theorem lines_ok : ∀ p ∈ lines, p.1 < 8 ∧ p.2 < 8 := by decide +kernel

/-- The `line` rows are true. -/
theorem lineOK_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : lineOK p cl = true) : Holds (rho g) cl := by
  unfold lineOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hside, hkap⟩, hcov⟩ := h
  refine anyCov_holds (rho_proper g) hcov ?_
  unfold lineSide at hside
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hside
  obtain ⟨⟨⟨⟨⟨hr, hL21, hL36, hsd, he1, he2, ha⟩, i1⟩, i2⟩, i3⟩, i4⟩ := hside
  unfold kapChk at hkap
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hkap
  obtain ⟨hne, hk⟩ := hkap
  set r := prm p 0; set L := prm p 1; set side := prm p 2; set e1 := prm p 3; set e2 := prm p 4
  have hlm : lineOf L ∈ lines := by
    unfold lineOf
    have : L - 21 < lines.length := by simp [lines]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact List.getElem_mem this
  have hvL : g.vv L = cross (g.N (lineOf L).1) (g.N (lineOf L).2) := by
    simp only [Geo.vv, show ¬ L < 21 by omega, ite_false]; rfl
  have hA : ∀ a, a < 8 → g.N a ≠ 0 := fun a ha h0 => by
    have := hG.hF.nn a ha; rw [h0] at this; simp at this
  have hEA1 := EAB_lt e1 he1
  have hEA2 := EAB_lt e2 he2
  have hbound := lines_ok _ hlm
  by_cases hs0 : side = 0
  · simp only [hs0, ite_true] at ha i1 i2 i3 i4 hne hk ⊢
    have hkk := kap_sign (g := g) hG.hO (lineOf L).1 e1 e2 1 (Or.inl rfl) (by simpa using hne) (prm p 5 == 1) (by
      simpa using hk)
    refine line_sound hG.eok (σ := ((1 : Int) : ℝ)) (a := (lineOf L).1) (b := (lineOf L).2) (by norm_num)
      (fun h' => hG.hv _ h') hL21 he1 he2 (by rw [hvL]; simp) (vv_lt g he1) (vv_lt g he2)
      (hG.hF.zero _ _ _ i1 i2) (hG.hF.zero _ _ _ i3 i4) (hA _ ha) ⟨hEA1.1, hEA1.2⟩ ⟨hEA2.1, hEA2.2⟩ ?_
    simpa using hkk
  · simp only [hs0, ite_false] at ha i1 i2 i3 i4 hne hk ⊢
    have hkk := kap_sign (g := g) hG.hO (lineOf L).2 e1 e2 (-1) (Or.inr rfl) (by simpa using hne) (prm p 5 == 1) (by
      simpa using hk)
    refine line_sound hG.eok (σ := ((-1 : Int) : ℝ)) (a := (lineOf L).2) (b := (lineOf L).1) (by norm_num)
      (fun h' => hG.hv _ h') hL21 he1 he2 (by rw [hvL, cross_swap']; simp) (vv_lt g he1) (vv_lt g he2)
      (hG.hF.zero _ _ _ i1 i2) (hG.hF.zero _ _ _ i3 i4) (hA _ ha) ⟨hEA1.1, hEA1.2⟩ ⟨hEA2.1, hEA2.2⟩ ?_
    simpa using hkk

/-- Every atom is true exactly when its entry is positive. -/
theorem rho_atom (g : Geo) {v : V} (h : isAtom v = true) : rho g v = decide (0 < g.atom v) := by
  cases v <;> simp_all [isAtom, rho]

/-- Sign exclusion rows are true. -/
theorem signOK_sound (g : Geo) {cl : List Lit} (h : signOK cl = true) : Holds (rho g) cl := by
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hl
  rw [coversF_eq] at hl
  exact Holds.of_covers (rho_proper g) hl.2 (sign_excl g l.2 (rho_atom g hl.1))

/-- `T` exclusion rows are true. -/
theorem texclOK_sound (g : Geo) {cl : List Lit} (h : texclOK cl = true) : Holds (rho g) cl := by
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
  obtain ⟨s, v⟩ := l
  cases v <;> simp only [Bool.false_eq_true] at hl
  rename_i e f
  rw [coversF_eq] at hl
  exact Holds.of_covers (rho_proper g) hl (texcl g e f)

/-- `y` rows are true. -/
theorem yOK_sound (g : Geo) (hG : GeoOK g) {cl : List Lit} (h : yOK cl = true) : Holds (rho g) cl := by
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
  obtain ⟨s, v⟩ := l
  cases s <;> cases v <;> simp only [Bool.false_eq_true] at hl
  rename_i e p1 p2 q1 q2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨he, h1, h2, h3, h4, n1, n2, n3, n4⟩, hcov⟩ := hl
  refine anyCov_holds (rho_proper g) hcov ?_
  intro s hs
  simp only [yS, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  exact y_rows g e p1 p2 q1 q2 (fun h' => hG.hv _ h') (fun a b hab hb => vv_EI g hab hb) h1 h2 h3 h4 n1 n2 n3 n4 a b
    (by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto)

/-- `fail` rows are true. -/
theorem failOK_sound (g : Geo) {cl : List Lit} (h : failOK cl = true) : Holds (rho g) cl := by
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
  obtain ⟨s, v⟩ := l
  cases s <;> cases v <;> simp only [Bool.false_eq_true] at hl
  rename_i e c
  rw [coversF_eq] at hl
  exact Holds.of_covers (rho_proper g) hl (failbig g e c)

/-- Gate rows are true. -/
theorem gateOK_sound (g : Geo) {cl : List Lit} (h : gateOK cl = true) : Holds (rho g) cl := by
  obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
  obtain ⟨s, v⟩ := l
  cases v <;> simp only [Bool.false_eq_true] at hl
  rename_i sa a sb b
  simp only [Bool.and_eq_true] at hl
  obtain ⟨he, hcov⟩ := hl
  rw [eqL_iff] at he
  have G := gate_rows g (sa, a) (sb, b)
  rw [he] at G
  refine anyCov_holds (rho_proper g) hcov ?_
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact G.1
  · exact G.2.1
  · exact G.2.2

/-- **Every row of these families that passes the check is true of the real data.** -/
theorem rowOK3_sound {g : Geo} (hG : GeoOK g) {fam : Nat} {p : List Nat} {cl : List Lit}
    (h : rowOK3 fam p cl = true) : Holds (rho g) cl := by
  unfold rowOK3 at h
  match fam, h with
  | 8, h => exact cramerOK_sound hG h
  | 11, h => exact texclOK_sound g h
  | 12, h => exact row3OK_sound hG h
  | 13, h => exact row4OK_sound hG h
  | 14, h => exact lineOK_sound hG h
  | 15, h => exact yOK_sound g hG h
  | 16, h => exact failOK_sound g h
  | 20, h => exact gateOK_sound g h
  | 21, h => exact signOK_sound g h
  | n + 22, h => simp at h
  | 0, h => simp at h
  | 1, h => simp at h
  | 2, h => simp at h
  | 3, h => simp at h
  | 4, h => simp at h
  | 5, h => simp at h
  | 6, h => simp at h
  | 7, h => simp at h
  | 9, h => simp at h
  | 10, h => simp at h
  | 17, h => simp at h
  | 18, h => simp at h
  | 19, h => simp at h

end Minimality.H16.SAT
