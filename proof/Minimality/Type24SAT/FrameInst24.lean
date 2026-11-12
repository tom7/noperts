module

public import Minimality.Type24SAT.Frame24

@[expose] public section

/-!
# Type 24, layer 3: the frames F24 and F24c for a configuration with `Convex24` and `QuadD`

F24 (frame export): P0 = 0, P3 = e1, P4 = e2, P5 = (al, be, 0), P1 = (0, 0, -1).  `det (c1, c2, -(x1 - x0)) = cv_{D,1} > 0`.
F24c: P3 = e1, P5 = e2, P4 = (p4a, p4b, 0), P2 = (0, 0, 1); the sign of `det (x3 - x0, x5 - x0, x2 - x0)` is not a
consequence of `Convex24` alone here: it is the hypothesis `hdet` (the reference configuration's sign).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

theorem sig3 : sig 3 = 1 := by decide
theorem fa3 : fa 3 = 0 := by decide
theorem fb3 : fb 3 = 3 := by decide
theorem fc3 : fc' 3 = 4 := by decide

/-! Evaluation of the facet tables at numerals. -/
theorem fa_0 : fa 0 = 0 := by decide
theorem fb_0 : fb 0 = 1 := by decide
theorem fc_0 : fc' 0 = 2 := by decide
theorem sg_0 : sig 0 = 1 := by decide
theorem fa_1 : fa 1 = 0 := by decide
theorem fb_1 : fb 1 = 1 := by decide
theorem fc_1 : fc' 1 = 6 := by decide
theorem sg_1 : sig 1 = -1 := by decide
theorem fa_2 : fa 2 = 0 := by decide
theorem fb_2 : fb 2 = 2 := by decide
theorem fc_2 : fc' 2 = 5 := by decide
theorem sg_2 : sig 2 = 1 := by decide
theorem fa_3 : fa 3 = 0 := by decide
theorem fb_3 : fb 3 = 3 := by decide
theorem fc_3 : fc' 3 = 4 := by decide
theorem sg_3 : sig 3 = 1 := by decide
theorem fa_4 : fa 4 = 0 := by decide
theorem fb_4 : fb 4 = 4 := by decide
theorem fc_4 : fc' 4 = 6 := by decide
theorem sg_4 : sig 4 = 1 := by decide
theorem fa_5 : fa 5 = 1 := by decide
theorem fb_5 : fb 5 = 2 := by decide
theorem fc_5 : fc' 5 = 6 := by decide
theorem sg_5 : sig 5 = -1 := by decide
theorem fa_6 : fa 6 = 2 := by decide
theorem fb_6 : fb 6 = 3 := by decide
theorem fc_6 : fc' 6 = 5 := by decide
theorem sg_6 : sig 6 = 1 := by decide
theorem fa_7 : fa 7 = 2 := by decide
theorem fb_7 : fb 7 = 3 := by decide
theorem fc_7 : fc' 7 = 6 := by decide
theorem sg_7 : sig 7 = -1 := by decide
theorem fa_8 : fa 8 = 3 := by decide
theorem fb_8 : fb 8 = 4 := by decide
theorem fc_8 : fc' 8 = 6 := by decide
theorem sg_8 : sig 8 = -1 := by decide

theorem cv3_D (P : Nat → V3 ℝ) (v : Nat) :
    cv3 P 3 v = -(V3.det (V3.sub (P 3) (P 0)) (V3.sub (P 4) (P 0)) (V3.sub (P v) (P 0))) := by
  simp only [cv3, nrm3, fa3, fb3, fc3, sig3, V3.smul, V3.cr, V3.dot, V3.sub, V3.det]
  push_cast; ring

theorem quadD_det (x : Nat → ℝ³) (hQ : QuadD x) :
    V3.det (V3.sub (pt x 3) (pt x 0)) (V3.sub (pt x 4) (pt x 0)) (V3.sub (pt x 5) (pt x 0)) = 0 := by
  have := hQ; unfold QuadD at this
  rw [det3_eq_det, toV3_sub, toV3_sub, toV3_sub] at this; exact this

theorem frame24F (x : Nat → ℝ³) (hC : Convex24 x) (hQ : QuadD x) :
    ∃ (U : Nat → V3 ℝ) (D : ℝ), IsFrame (pt x) U D ∧ U 0 = ⟨0, 0, 0⟩ ∧ U 3 = ⟨1, 0, 0⟩ ∧ U 4 = ⟨0, 1, 0⟩ ∧
      U 1 = ⟨0, 0, -1⟩ ∧ (U 5).z = 0 := by
  have hcv : 0 < cv x 3 1 := hC (3, 1) (by decide)
  rw [cv_eq_cv3, cv3_D] at hcv
  refine frame_exists (pt x) 3 4 1 5 (-1) (by norm_num) ?_ (quadD_det x hQ)
  have : V3.det (V3.sub (pt x 3) (pt x 0)) (V3.sub (pt x 4) (pt x 0)) (V3.smul (-1) (V3.sub (pt x 1) (pt x 0))) =
      -(V3.det (V3.sub (pt x 3) (pt x 0)) (V3.sub (pt x 4) (pt x 0)) (V3.sub (pt x 1) (pt x 0))) := by
    simp only [V3.smul, V3.sub, V3.det, V3.dot, V3.cr]; ring
  rw [this]; exact hcv

theorem frame24C (x : Nat → ℝ³) (hQ : QuadD x)
    (hdet : 0 < V3.det (V3.sub (pt x 3) (pt x 0)) (V3.sub (pt x 5) (pt x 0)) (V3.sub (pt x 2) (pt x 0))) :
    ∃ (U : Nat → V3 ℝ) (D : ℝ), IsFrame (pt x) U D ∧ U 0 = ⟨0, 0, 0⟩ ∧ U 3 = ⟨1, 0, 0⟩ ∧ U 5 = ⟨0, 1, 0⟩ ∧
      U 2 = ⟨0, 0, 1⟩ ∧ (U 4).z = 0 := by
  refine frame_exists (pt x) 3 5 2 4 1 (by norm_num) ?_ ?_
  · have : V3.smul (1 : ℝ) (V3.sub (pt x 2) (pt x 0)) = V3.sub (pt x 2) (pt x 0) := by
      simp [V3.smul, V3.sub]
    rw [this]; exact hdet
  · have h := quadD_det x hQ
    simp only [V3.det, V3.dot, V3.cr, V3.sub] at h ⊢; linarith

/-- A convexity value is positive in the frame. -/
theorem cv_frame {x : Nat → ℝ³} {U : Nat → V3 ℝ} {D : ℝ} (hF : IsFrame (pt x) U D) (hC : Convex24 x) (t v : Nat)
    (hm : (t, v) ∈ cvList) : 0 < cv3 U t v := by
  have h := hC (t, v) hm
  rw [cv_eq_cv3, hF.cv] at h
  exact pos_of_mul_pos_right h hF.pos.le

/-- A non-`kv` literal of a sign model, in the frame. -/
theorem lit_frame {x : Nat → ℝ³} {U : Nat → V3 ℝ} {D : ℝ} (hF : IsFrame (pt x) U D) (l : Lit24)
    (hl : ∀ t a b c d, l ≠ .kv t a b c d) (s : Int) (h : LitHolds x l s) : 0 < (s : ℝ) * val3 U l := by
  unfold LitHolds at h; rw [val_eq_val3] at h
  have hD := hF.pos
  have key : ∃ k : ℝ, 0 < k ∧ val3 (pt x) l = k * val3 U l := by
    cases l with
    | br a b c d => exact ⟨D, hD, hF.br a b c d⟩
    | lv a b c d e => exact ⟨D, hD, hF.lv a b c d e⟩
    | mv a b c d e f => exact ⟨D, hD, hF.mv a b c d e f⟩
    | fc t p q => exact ⟨D, hD, hF.fc t p q⟩
    | nv r s t => exact ⟨D ^ 2, by positivity, hF.nv r s t⟩
    | kv t a b c d => exact absurd rfl (hl t a b c d)
  obtain ⟨k, hk, e⟩ := key
  rw [e] at h
  have : (s : ℝ) * (k * val3 U l) = k * ((s : ℝ) * val3 U l) := by ring
  rw [this] at h
  exact pos_of_mul_pos_right h hk.le

/-- A `kv` literal in the frame. -/
theorem kv_frame {x : Nat → ℝ³} {U : Nat → V3 ℝ} {D : ℝ} (hF : IsFrame (pt x) U D) (t a b c d : Nat) (s : Int)
    (ha : (U a).z = 0) (hb : (U b).z = 0) (hc : (U c).z = 0) (hd : (U d).z = 0)
    (h1 : (U (fa t)).z = 0) (h2 : (U (fb t)).z = 0) (h3 : (U (fc' t)).z = 0)
    (h : LitHolds x (.kv t a b c d) s) : 0 < (s : ℝ) * val3 U (.kv t a b c d) := by
  unfold LitHolds at h; rw [val_eq_val3] at h
  obtain ⟨Q, hQ, hk⟩ := hF.kv
  rw [hk t a b c d ha hb hc hd h1 h2 h3] at h
  have : (s : ℝ) * (Q * val3 U (.kv t a b c d)) = Q * ((s : ℝ) * val3 U (.kv t a b c d)) := by ring
  rw [this] at h
  exact pos_of_mul_pos_right h hQ.le

/-- From a positive product to a positive factor. -/
theorem pos_sq {P f k q : ℝ} (hP : 0 < P) (hk : 0 < k) (e : P = k * q ^ 2 * f) : 0 < f := by
  by_contra hf
  have : k * q ^ 2 * f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hf)
  linarith

end Minimality.T24.SAT
