module

public import Minimality.Type08S.C2K17F1A
public import Minimality.Type08S.C2K17F2A

@[expose] public section


/-!
# K17GD / GD1: generic lex lemma and the slice `K6t4B11` (`β1 = 1`, `B = ⟪b-d,a-d⟫ = 0`, Ta not Touch).

View `a - d`, frame data of `k6t4_B11_core` (`γ4 = 1`).  With `C = ⟪c-d,a-d⟫`:
* `C > 0`: cell 1 `(a,d,b,a',b')` (the tie `z(b) = z(d)` is harmless: `b` is below `a'` in depth);
* `C < 0`: cell 2 `(a,d,c,a',c')` (single peak `c'`; `c, a'` tie at the bottom, either order);
* `C = 0`: leftover.  No `TouchT`, no Gram condition besides the sign of `C`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **Generic lex unimodality**: `m` is a lex peak and every other index has a lex-higher neighbour. -/
theorem k17gd_lexUni_nb {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (m : ZMod k) (hm : LexLt (z (m - 1), w (m - 1)) (z m, w m) ∧ LexLt (z (m + 1), w (m + 1)) (z m, w m))
    (hn : ∀ i, i ≠ m → LexLt (z i, w i) (z (i - 1), w (i - 1)) ∨ LexLt (z i, w i) (z (i + 1), w (i + 1))) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_eq_one]
  refine ⟨m, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hne
    rcases hn i hne with h1 | h1
    · exact lexLt_asymm h1 h.1
    · exact lexLt_asymm h1 h.2
  · rintro rfl; exact hm

theorem k17gd_z5 : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧ (3 : ZMod 5) - 1 = 2 ∧
    (4 : ZMod 5) - 1 = 3 ∧ (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide

/-- 5-cycle with a single lex peak at `4`: `0 < 4`, `3 < 4`, `1 < 0`, `2 < 1`; `3` arbitrary otherwise. -/
theorem k17gd_lexUni5_p4 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h04 : LexLt (z 0, w 0) (z 4, w 4)) (h34 : LexLt (z 3, w 3) (z 4, w 4))
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h21 : LexLt (z 2, w 2) (z 1, w 1)) : LexUni z w := by
  obtain ⟨t0, t1, t2, t3, t4, s0, s1, s2, s3, s4⟩ := k17gd_z5
  refine k17gd_lexUni_nb z w hinj 4 (by rw [t4, s4]; exact ⟨h34, h04⟩) (fun i hi => ?_)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
  · rw [t0]; left; exact h04
  · rw [t1]; left; exact h10
  · rw [t2]; left; exact h21
  · rw [s3]; right; exact h34
  · exact absurd rfl hi

/-- Cell 1 `(a, d, b, a', b')` of the `β1 = 1` frame at `B = 0`, `C > 0`. -/
theorem k17gd_b11_cell1_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j)
    {z A B C β6 α4 : ℝ} (hA : 0 < A) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (h0 : zz 0 = z + A) (h1 : zz 1 = z) (h2 : zz 2 = z + B) (h3 : zz 3 = z + β6 * B + C)
    (h4 : zz 4 = z + C + α4 * A) (hB : B = 0) (hC : 0 < C) : LexUni zz ww := by
  refine lexUni5_r2 zz ww hinj ?_ ?_ ?_
  · left; show zz 3 < zz 4; rw [h3, h4, hB]; nlinarith
  · left; show zz 1 < zz 0; rw [h0, h1]; linarith
  · left; left; show zz 2 < zz 3; rw [h2, h3, hB]; linarith

/-- Cell 2 `(a, d, c, a', c')` (frame `(q, p, r)`) at `B = 0`, `C < 0`, `1 < α1`. -/
theorem k17gd_b11_cell2_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j)
    {z A B C β6 α1 : ℝ} (hA : 0 < A) (hα1 : 1 < α1) (hβ6 : 0 < β6) (hB : B = 0) (hC : C < 0)
    (h0 : zz 0 = z + A) (h1 : zz 1 = z) (h2 : zz 2 = z + C) (h3 : zz 3 = z + 1 * C + β6 * B)
    (h4 : zz 4 = z + B + α1 * A) : LexUni zz ww := by
  refine k17gd_lexUni5_p4 zz ww hinj ?_ ?_ ?_ ?_
  · left; show zz 0 < zz 4; rw [h0, h4, hB]; nlinarith
  · left; show zz 3 < zz 4; rw [h3, h4, hB]; nlinarith
  · left; show zz 1 < zz 0; rw [h0, h1]; linarith
  · left; show zz 2 < zz 1; rw [h1, h2]; linarith

set_option maxHeartbeats 3200000 in
/-- **K6t4B11 (`β1 = 1`, `B = 0`)**: a cell at `a - d`, or the leftover `⟪a-d, c-d⟫ = 0`.  Needs `hfar` (`1 < α1`),
which `K6t4B11` does not give (derive it from `¬IsT'` with `k5z_far2`). -/
theorem k17gd_b11 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t4B11 a a' b b' c c' d)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, c - d⟫ = 0 := by
  obtain ⟨hT, hκ, hβ1, hB⟩ := h
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1p, hαβ, hα4, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ1
  have hβ1e : β1 = 1 := by
    have : β1 - 1 = 0 := by
      rcases mul_eq_zero.1 hβ1 with h | h
      · exact h
      · exact absurd h hdet
    linarith
  subst hβ1e
  have hγ4e : γ4 = 1 := by
    have : α1 * (1 - γ4) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hγ4e
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hcyc : ∀ x y z : ℝ³, det3 x y z = det3 z x y := by
    intro x y z; simp only [det3_expand]; ring
  have hΔ : det3 p q r ≠ 0 := by rw [hcyc]; exact hdet
  have hΔ' : det3 q p r ≠ 0 := by
    have : det3 q p r = - det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hΔ
  have hfp : ∀ (u v : ℝ³) (x y z : ℝ), fpoint u v r d (x, y, z) = d + x • u + y • v + z • r := by
    intro u v x y z; simp only [fpoint, fcomb]; module
  have P1a : fpoint p q r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P1d : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have P1b : fpoint p q r d (1, 0, 0) = b := by rw [hfp]; simp only [hp]; module
  have P1a' : fpoint p q r d (β6, 1, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P1b' : fpoint p q r d (0, 1, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  have P1c : fpoint p q r d (0, 1, 0) = c := by rw [hfp]; simp only [hq]; module
  have P1c' : fpoint p q r d (1, 0, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2a : fpoint q p r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P2d : fpoint q p r d (0, 0, 0) = d := by rw [hfp]; module
  have P2c : fpoint q p r d (1, 0, 0) = c := by rw [hfp]; simp only [hq]; module
  have P2a' : fpoint q p r d (1, β6, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P2c' : fpoint q p r d (0, 1, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2b : fpoint q p r d (0, 1, 0) = b := by rw [hfp]; simp only [hp]; module
  have P2b' : fpoint q p r d (1, 0, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  have hz : ∀ (u v : ℝ³) (t : ℝ × ℝ × ℝ), ⟪fpoint u v r d t, r⟫ =
      ⟪d, r⟫ + t.1 * ⟪u, r⟫ + t.2.1 * ⟪v, r⟫ + t.2.2 * ⟪r, r⟫ := fun u v t => inner_fpoint _ _ _ _ _ _
  have hBpr : ⟪p, r⟫ = 0 := hB
  rcases lt_trichotomy ⟪q, r⟫ 0 with hCn | hC0 | hCp
  · -- `C < 0`: cell 2 in the frame `(q, p, r)`
    left
    refine ⟨r, hr0, ?_⟩
    refine k6t4_core (V8 a a' b b' c c' d) q p r d hΔ' (α1 := α4) (α4 := α1) (β6 := 1) (γ6 := β6)
      hα4 (by linarith) one_pos hβ6 (by linarith) (lo := 0) (hi := 1) one_pos
      ?_ ?_ ?_ ?_
    · intro lam hl0 hl1
      refine ⟨hl0, by nlinarith, by nlinarith⟩
    · intro lam hl0 hl1 hinj
      refine k17gd_b11_cell2_lex _ _ hinj (z := ⟪d, r⟫) (A := ⟪r, r⟫) (B := ⟪p, r⟫) (C := ⟪q, r⟫) (β6 := β6)
        (α1 := α1) hA hα11 hβ6 hBpr hCn ?_ ?_ ?_ ?_ ?_
      · simp only [kCyc, pc5_0, hz]; ring
      · simp only [kCyc, pc5_1, hz]; ring
      · simp only [kCyc, pc5_2, hz]; ring
      · simp only [kCyc, pc5_3, hz]; ring
      · simp only [kCyc, pc5_4, hz]; ring
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kCyc, pc5_0, P2a]; simp [V8]
      · simp only [kCyc, pc5_1, P2d]; simp [V8]
      · simp only [kCyc, pc5_2, P2c]; simp [V8]
      · simp only [kCyc, pc5_3, P2a']; simp [V8]
      · simp only [kCyc, pc5_4, P2c']; simp [V8]
    · intro y hy
      rw [P2a, P2d, P2c, P2a', P2c', P2b, P2b']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · right
    rw [real_inner_comm]; exact hC0
  · -- `C > 0`: cell 1 in the frame `(p, q, r)`
    left
    refine ⟨r, hr0, ?_⟩
    refine k6t4_core (V8 a a' b b' c c' d) p q r d hΔ (α1 := α1) (α4 := α4) (β6 := β6) (γ6 := 1)
      (by linarith) hα4 hβ6 one_pos (by linarith) (lo := max 0 (1 - β6)) (hi := max 0 (1 - β6) + 1) (by linarith)
      ?_ ?_ ?_ ?_
    · intro lam hl0 hl1
      have := lt_of_le_of_lt (le_max_left _ _) hl0
      have := lt_of_le_of_lt (le_max_right _ _) hl0
      refine ⟨by linarith, by linarith, by nlinarith⟩
    · intro lam hl0 hl1 hinj
      refine k17gd_b11_cell1_lex _ _ hinj (z := ⟪d, r⟫) (A := ⟪r, r⟫) (B := ⟪p, r⟫) (C := ⟪q, r⟫) (β6 := β6)
        (α4 := α4) hA hα4 hβ6 ?_ ?_ ?_ ?_ ?_ hBpr hCp
      · simp only [kCyc, pc5_0, hz]; ring
      · simp only [kCyc, pc5_1, hz]; ring
      · simp only [kCyc, pc5_2, hz]; ring
      · simp only [kCyc, pc5_3, hz]; ring
      · simp only [kCyc, pc5_4, hz]; ring
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kCyc, pc5_0, P1a]; simp [V8]
      · simp only [kCyc, pc5_1, P1d]; simp [V8]
      · simp only [kCyc, pc5_2, P1b]; simp [V8]
      · simp only [kCyc, pc5_3, P1a']; simp [V8]
      · simp only [kCyc, pc5_4, P1b']; simp [V8]
    · intro y hy
      rw [P1a, P1d, P1b, P1a', P1b', P1c, P1c']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

end C2
end Type08Sp
end Minimality
