module

public import Minimality.Type21SAT.Rule2
public import Minimality.Type21SAT.LexRow

@[expose] public section

/-!
# L3, part 25: the lex rule rows (family 25) of core B

At a view `u = vv e` whose edge-on facets are `mask` (containing `D` = 3 and `H` = 7, parallel with opposite
facings in `pp`), tilt along `d' = eps * dv d` for an edge `d` in `D` or `H`, then along `w`: the facings are
`LP3 (N.u, N.d', N.w)`.  Soundness is `s0x_lex2_rupert` (Lex2) against `not IsRupert`.  Needs `D ∥ H` (`hpar`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H21.SAT

/-! ### Three levels -/

/-- First level strict decides the facing. -/
theorem lp3_a {p : Bool} {a b c : ℝ} (h : (p = true → 0 < a) ∧ (p = false → a < 0)) :
    (p = true → LP3 a b c) ∧ (p = false → LP3 (-a) (-b) (-c)) :=
  ⟨fun hp => Or.inl (h.1 hp), fun hp => Or.inl (by linarith [h.2 hp])⟩

/-- First level zero, second level strict decides the facing. -/
theorem lp3_b {p : Bool} {a b c : ℝ} (ha : a = 0) (h : (p = true → 0 < b) ∧ (p = false → b < 0)) :
    (p = true → LP3 a b c) ∧ (p = false → LP3 (-a) (-b) (-c)) :=
  ⟨fun hp => Or.inr ⟨ha, Or.inl (h.1 hp)⟩,
   fun hp => Or.inr ⟨by rw [ha]; ring, Or.inl (by linarith [h.2 hp])⟩⟩

/-- First two levels zero, third level strict decides the facing. -/
theorem lp3_c {p : Bool} {a b c : ℝ} (ha : a = 0) (hb : b = 0) (h : (p = true → 0 < c) ∧ (p = false → c < 0)) :
    (p = true → LP3 a b c) ∧ (p = false → LP3 (-a) (-b) (-c)) :=
  ⟨fun hp => Or.inr ⟨ha, Or.inr ⟨hb, h.1 hp⟩⟩,
   fun hp => Or.inr ⟨by rw [ha]; ring, Or.inr ⟨by rw [hb]; ring, by linarith [h.2 hp]⟩⟩⟩

/-! ### Geometry of `D ∥ H` -/

/-- A vector with zero cross product with a nonzero `a` is a multiple of `a`. -/
theorem prop_of_cross {a b : ℝ³} (ha : a ≠ 0) (h : cross a b = 0) : ∃ r : ℝ, b = r • a := by
  have haa : ⟪a, a⟫ ≠ 0 := (real_inner_self_pos.2 ha).ne'
  have c0 : a 1 * b 2 - a 2 * b 1 = 0 := by
    have := congrArg (fun v : ℝ³ => v 0) h
    simpa [cross_apply_zero] using this
  have c1 : a 2 * b 0 - a 0 * b 2 = 0 := by
    have := congrArg (fun v : ℝ³ => v 1) h
    simpa [cross_apply_one] using this
  have c2 : a 0 * b 1 - a 1 * b 0 = 0 := by
    have := congrArg (fun v : ℝ³ => v 2) h
    simpa [cross_apply_two] using this
  have haa' : a 0 * a 0 + a 1 * a 1 + a 2 * a 2 ≠ 0 := by rw [← inn3]; exact haa
  have hv : ⟪a, a⟫ • b = ⟪a, b⟫ • a := by
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, PiLp.smul_apply, smul_eq_mul, inn3]
    · linear_combination (-(a 1)) * c2 + (a 2) * c1
    · linear_combination (a 0) * c2 - (a 2) * c0
    · linear_combination (-(a 0)) * c1 + (a 1) * c0
  refine ⟨⟪a, b⟫ / ⟪a, a⟫, ?_⟩
  symm
  rw [div_eq_inv_mul, mul_smul, ← hv, smul_smul, inv_mul_cancel₀ haa, one_smul]

/-- The normal of a facet is not zero. -/
theorem N_ne {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (t : Fin 8) : F.N t ≠ 0 := by
  have key : ∀ t : Fin 8, ∃ j i : Fin 7, j ∈ S21 t ∧ i ∉ S21 t := by decide +kernel
  obtain ⟨j, i, hj, hi⟩ := key t
  intro h0
  have h1 := F.hN t (x i) (x j)
  rw [h0] at h1
  simp only [inner_zero_left] at h1
  have := F.zero t j hj
  have := F.neg t i hi
  linarith

/-- Two facets with a common vertex and a vertex outside both, the second not inside the first, have no proportional
normals (any constant). -/
theorem no_par {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) {t0 t1 : Fin 8} (r : ℝ) (hN : F.N t1 = r • F.N t0)
    (hsh : ∃ j : Fin 7, j ∈ S21 t0 ∧ j ∈ S21 t1) (hout : ∃ i : Fin 7, i ∉ S21 t0 ∧ i ∉ S21 t1)
    (hsub : ¬ S21 t1 ⊆ S21 t0) : False := by
  obtain ⟨j, hj0, hj1⟩ := hsh
  obtain ⟨i, hi0, hi1⟩ := hout
  have e1 := F.hN t1 (x i) (x j)
  have e0 := F.hN t0 (x i) (x j)
  rw [hN, inner_smul_left] at e1
  simp only [conj_trivial] at e1
  have z1 := F.zero t1 j hj1
  have z0 := F.zero t0 j hj0
  have n1 := F.neg t1 i hi1
  have n0 := F.neg t0 i hi0
  have hr : 0 < r := by
    by_contra hr
    push_neg at hr
    nlinarith
  exact no_same_dir F hr hN ⟨j, hj0⟩ hsub

/-- `D ∥ H`: the normal of `H` is a negative multiple of that of `D`. -/
theorem dh_neg {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) (hpar : ∃ r : ℝ, F.N 3 = r • F.N 7) :
    ∃ q : ℝ, q < 0 ∧ F.N 7 = q • F.N 3 := by
  obtain ⟨r, hr⟩ := hpar
  have h3 := N_ne F 3
  have h7 := N_ne F 7
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr; exact h3 hr
  have hq : F.N 7 = r⁻¹ • F.N 3 := by
    rw [hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have h33 : ⟪F.N 3, F.N 3⟫ ≠ 0 := (real_inner_self_pos.2 h3).ne'
  have h77 : ⟪F.N 7, F.N 7⟫ ≠ 0 := (real_inner_self_pos.2 h7).ne'
  have hne : (S21 3).Nonempty := ⟨0, by decide +kernel⟩
  have hsub : ¬ S21 7 ⊆ S21 3 := by decide +kernel
  have := neg_of_parallel F hq h33 h77 hne hsub
  rw [hq, inner_smul_left] at this
  simp only [conj_trivial] at this
  have hpos : 0 < ⟪F.N 3, F.N 3⟫ := (real_inner_self_pos.2 h3)
  refine ⟨r⁻¹, ?_, hq⟩
  by_contra hc
  push_neg at hc
  nlinarith

/-- A tilt `w` with prescribed signs on `D`, `H` (opposite) and on a facet `zi` among 0, 1, 2, 4, 5, 6. -/
theorem exists_w {x : Fin 7 → ℝ³} (F : S0xFac 8 S21 x) {q : ℝ} (hq : q < 0) (h7 : F.N 7 = q • F.N 3)
    (b3 b7 bz : Bool) (hb : b3 ≠ b7) (zi : Nat)
    (hz : zi = 999 ∨ zi = 0 ∨ zi = 1 ∨ zi = 2 ∨ zi = 4 ∨ zi = 5 ∨ zi = 6) :
    ∃ w : ℝ³, ((b3 = true → 0 < ⟪F.N 3, w⟫) ∧ (b3 = false → ⟪F.N 3, w⟫ < 0)) ∧
      ((b7 = true → 0 < ⟪F.N 7, w⟫) ∧ (b7 = false → ⟪F.N 7, w⟫ < 0)) ∧
      ∀ t : Fin 8, t.val = zi → ((bz = true → 0 < ⟪F.N t, w⟫) ∧ (bz = false → ⟪F.N t, w⟫ < 0)) := by
  have h3 := N_ne F 3
  have hq0 : q ≠ 0 := hq.ne
  have hcross : ∀ t : Fin 8, (t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 4 ∨ t.val = 5 ∨ t.val = 6) →
      cross (F.N 3) (F.N t) ≠ 0 := by
    intro t ht hc
    obtain ⟨r, hr⟩ := prop_of_cross h3 hc
    have hr7 : F.N t = (r * q⁻¹) • F.N 7 := by
      rw [hr, h7, smul_smul, mul_assoc, inv_mul_cancel₀ hq0, mul_one]
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by
      rcases ht with h | h | h | h | h | h <;> [left; (right; left); (right; right; left); (right; right; right; left);
        (right; right; right; right; left); (right; right; right; right; right)] <;> exact Fin.ext h
    rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_par F r hr (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact no_par F r hr (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact no_par F r hr (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact no_par F r hr (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact no_par F (r * q⁻¹) hr7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact no_par F r hr (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have key : ∃ w : ℝ³, ⟪F.N 3, w⟫ = (if b3 then 1 else -1) ∧
      ∀ t : Fin 8, t.val = zi → ⟪F.N t, w⟫ = (if bz then 1 else -1) := by
    rcases hz with h | h
    · obtain ⟨w, hw⟩ := s0x_exists_tilt_sign1 h3 (if b3 then 1 else -1)
      exact ⟨w, hw, fun t ht => by have := t.isLt; omega⟩
    · have hz8 : zi < 8 := by omega
      obtain ⟨w, hw1, hw2⟩ := s0x_exists_tilt_signs (hcross ⟨zi, hz8⟩ (by simp only; omega))
        (if b3 then 1 else -1) (if bz then 1 else -1)
      exact ⟨w, hw1, fun t ht => by
        have : t = ⟨zi, hz8⟩ := Fin.ext ht
        rw [this]; exact hw2⟩
  obtain ⟨w, hw3, hwz⟩ := key
  have hw7 : ⟪F.N 7, w⟫ = q * ⟪F.N 3, w⟫ := by rw [h7, inner_smul_left]; simp
  refine ⟨w, ?_, ?_, ?_⟩
  · constructor
    · intro h; rw [hw3]; simp [h]
    · intro h; rw [hw3]; simp [h]
  · rw [hw7, hw3]
    cases h3' : b3 <;> cases h7' : b7 <;> simp_all 
  · intro t ht
    rw [hwz t ht]
    constructor
    · intro h; simp [h]
    · intro h; simp [h]

/-! ### The rule row -/

/-- The clause of a lex rule `(e, pp, mask, d, ep, zi)`: the state of the view (as a rule), the signs of `d` on the
other edge-on facets (`zi` = the facet where `d` is zero, 999 for none), and the lex failure of the cycle. -/
def lexLits (e pp mask d ep zi : Nat) (cyc : List Nat) : List Lit :=
  ((List.range 8).flatMap fun t =>
     if mask.testBit t then [(Fe e t).1, (Fe e t).2]
     else if pp.testBit t then [(Fe e t).1.neg] else [(Fe e t).2.neg]) ++
  ((List.range 8).flatMap fun s =>
     if mask.testBit s && s != 3 && s != 7 then
       (if s = zi then [(fup3 s (EA d) (EB d)).1, (fup3 s (EA d) (EB d)).2]
        else [(if pp.testBit s == decide (ep = 1) then (fup3 s (EA d) (EB d)).1
               else (fup3 s (EA d) (EB d)).2).neg])
     else []) ++
  [(true, V.faill e d ep cyc)]

/-- The lex cycle in the clause (first `faill e d ep _` literal). -/
def failLOf (cl : List Lit) (e d ep : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (true, .faill e' d' ep' c) => if e' == e && d' == d && ep' == ep then some c else none
    | _ => none).getD []

/-- The edge `d` lies in the facet `D` (3) or in `H` (7). -/
def dinDH (d : Nat) : Bool := (inF 3 (EA d) && inF 3 (EB d)) || (inF 7 (EA d) && inF 7 (EB d))

/-- The check of a lex rule row: parameters `(e, pp, d, eps, zi, mask)` (`eps = 1` or 999, `zi` = 999 for none). -/
def lexOK (p : List Nat) (cl : List Lit) : Bool :=
  let e := prm p 0; let pp := prm p 1; let d := prm p 2
  let ep := if prm p 3 = 1 then 1 else 0
  let zi := prm p 4; let mask := prm p 5
  let L := patCyc.getD pp []; let cyc := failLOf cl e d ep
  decide (e < 36 ∧ pp < 256 ∧ mask < 255 ∧ d < 21 ∧ mask.testBit 3 = true ∧ mask.testBit 7 = true ∧
    pp.testBit 3 ≠ pp.testBit 7 ∧
    (zi = 999 ∨ ((zi = 0 ∨ zi = 1 ∨ zi = 2 ∨ zi = 4 ∨ zi = 5 ∨ zi = 6) ∧ mask.testBit zi = true)) ∧
    3 < L.length) &&
  dinDH d && cycChk pp L && altChk L cyc && coversF cl (lexLits e pp mask d ep zi cyc)

/-- Epsilon is plus or minus one. -/
theorem epR_sq (ep : Nat) : epR ep * epR ep = 1 := by unfold epR; split_ifs <;> norm_num

/-- **The failure of a cycle, lex form.**  Four lexicographic weak inequalities of an alternation make `faill` true. -/
theorem rho_failL_of (g : Geo) {e d ep : Nat} {cyc : List Nat} {t : Nat × Nat × Nat × Nat}
    (ht : t ∈ alts cyc) {p1 p2 q1 q2 : Nat} (hm : Mt t p1 p2 q1 q2)
    (h11 : ¬ g.lexLt e d ep p1 q1) (h12 : ¬ g.lexLt e d ep p1 q2) (h21 : ¬ g.lexLt e d ep p2 q1)
    (h22 : ¬ g.lexLt e d ep p2 q2) : rho g (.faill e d ep cyc) = true := by
  simp only [rho, List.any_eq_true]
  refine ⟨t, ht, ?_⟩
  simp only [Geo.yL, decide_eq_true_eq]
  obtain ⟨a, b⟩ := hm
  rcases a with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases b with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    simp only [a1, a2, b1, b2] <;> tauto

/-- **`faill` false and `AltCover2` give `RobUniL`** of the depths along the cycle, with the tie-break `eps * dv d`. -/
theorem robUniL_of_alt {k : ℕ} [NeZero k] (g : Geo) {x : Fin 7 → ℝ³} (hx : ∀ i : Fin 7, g.x i.val = x i)
    {e d ep : Nat} {u δ : ℝ³} (hu : g.vv e = u) (hδ : g.vv d = δ) {c : ZMod k → Fin 7} {cyc : List Nat}
    (hA : AltCover2 c cyc) (hf : rho g (.faill e d ep cyc) = false) :
    RobUniL (fun a : ZMod k => ⟪x (c a), u⟫) (fun a : ZMod k => ⟪x (c a), epR ep • δ⟫) := by
  intro B b c' d' h0 h1 h2 h3 ⟨e1, e2, e3, e4⟩
  obtain ⟨t, ht, hm⟩ := hA B b (by omega) c' (by omega) d' h3 h0 h1 h2
  have key : ∀ a b : Fin 7, (⟪x b, u⟫ < ⟪x a, u⟫ ∨ (⟪x b, u⟫ = ⟪x a, u⟫ ∧
      ⟪x b, epR ep • δ⟫ ≤ ⟪x a, epR ep • δ⟫)) → ¬ g.lexLt e d ep a.val b.val := by
    intro a b hab
    have z1 : g.z e a.val b.val = ⟪x a, u⟫ - ⟪x b, u⟫ := by
      simp only [Geo.z, hu, hx, inner_sub_right]
      rw [real_inner_comm (x a) u, real_inner_comm (x b) u]
    have z2 : epR ep * g.z d a.val b.val = ⟪x a, epR ep • δ⟫ - ⟪x b, epR ep • δ⟫ := by
      simp only [Geo.z, hδ, hx, real_inner_smul_right, inner_sub_right]
      rw [real_inner_comm (x a) δ, real_inner_comm (x b) δ]; ring
    unfold Geo.lexLt
    rw [z1, z2]
    rintro (h | ⟨h, h'⟩)
    · rcases hab with h2 | ⟨h2, _⟩ <;> linarith
    · rcases hab with h2 | ⟨h2, h3⟩ <;> linarith
  have := rho_failL_of g ht hm (key _ _ e1) (key _ _ e3) (key _ _ e2) (key _ _ e4)
  rw [hf] at this
  exact absurd this (by simp)

end Minimality.H21.SAT
