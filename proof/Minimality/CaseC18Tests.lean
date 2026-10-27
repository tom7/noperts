module

public import Minimality.CaseC18Bridge
public import Minimality.CaseC18Z

@[expose] public section

/-!
# Type 18, acute case (c): the crossing tests at the shape's own metric
(`FEWER-FACES-PROOFS.md` §27, continued (2) and (4))

Each test is a rim cycle of the seven points with a view `u` and a tilt `v` in frame coordinates,
the determinant tests `ST` (generated, one lemma per cycle / hidden point), and the open depth
condition at the frame's metric `diag(A, g)`.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

namespace Shape18
variable (S : Shape18)

/-- The upper roof `d+ < b+` cleared of denominators. -/
lemma roof_p' : S.kp * (1 - S.tp) < S.hp * (1 - S.sp) := by
  have h := S.dp_lt_bp
  have e1 := S.bp_mul; have e2 := S.dp_mul
  have hs := S.sp_lt; have ht := S.tp_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos (sub_pos.2 ht) (sub_pos.2 hs))]

/-- The lower roof `d- < b-` cleared of denominators. -/
lemma roof_m' : S.km * (1 - S.tm) < S.hm * (1 - S.sm) := by
  have h := S.dm_lt_bm
  have e1 := S.bm_mul; have e2 := S.dm_mul
  have hs := S.sm_lt; have ht := S.tm_lt
  nlinarith [mul_lt_mul_of_pos_right h (mul_pos (sub_pos.2 ht) (sub_pos.2 hs))]

/-- `c+ > a+` forces `s+ < t+` (roof). -/
lemma sp_lt_tp (Hp : S.hp * S.sp < S.kp * S.tp) : S.sp < S.tp := by
  have hr := S.roof_p'
  have hk := S.kp_pos
  have h1 : 0 < (S.kp * S.tp - S.hp * S.sp) * (1 - S.sp) :=
    mul_pos (sub_pos.2 Hp) (sub_pos.2 S.sp_lt)
  have h2 : 0 < S.sp * (S.hp * (1 - S.sp) - S.kp * (1 - S.tp)) :=
    mul_pos S.sp_pos (sub_pos.2 hr)
  have h3 : S.kp * (S.tp - S.sp) > 0 := by nlinarith
  exact lt_of_sub_pos (pos_of_mul_pos_right h3 hk.le |> fun h => h) 

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

noncomputable def a11 (_F : Frame18 x) : ℝ := ⟪x 3 - x 5, x 3 - x 5⟫
noncomputable def a12 (_F : Frame18 x) : ℝ := ⟪x 3 - x 5, x 4 - x 5⟫
noncomputable def a22 (_F : Frame18 x) : ℝ := ⟪x 4 - x 5, x 4 - x 5⟫
noncomputable def gg : ℝ := ⟪F.e, F.e⟫

lemma g_pos : 0 < F.gg := real_inner_self_pos.mpr F.e_ne

lemma GG_eq (a b : C3) : F.toFrame7.GG a b =
    F.a11 * (a.x * b.x) + F.a12 * (a.x * b.y + b.x * a.y) + F.a22 * (a.y * b.y) +
      F.gg * (a.z * b.z) := rfl

end Frame18

theorem A_of_pos4 {p q r s z0 z1 z2 z3 : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hT : p + q = r + s) (h : 0 < p * z1 + q * z3 - r * z2 - s * z0) :
    z0 < z1 ∨ z0 < z3 ∨ z2 < z1 ∨ z2 < z3 := by
  by_contra hc
  push Not at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have hq' : q = r + s - p := by linarith
  have iden : p * s * (z0 - z1) + p * r * (z2 - z1) + q * s * (z0 - z3) + q * r * (z2 - z3) =
      (r + s) * (r * z2 + s * z0 - p * z1 - q * z3) := by
    rw [hq']; ring
  have h' : (r + s) * (r * z2 + s * z0 - p * z1 - q * z3) < 0 := by
    have : r * z2 + s * z0 - p * z1 - q * z3 < 0 := by linarith
    exact mul_neg_of_pos_of_neg (add_pos hr hs) this
  nlinarith [mul_nonneg (mul_pos hp hs).le (sub_nonneg.2 c1),
    mul_nonneg (mul_pos hp hr).le (sub_nonneg.2 c3),
    mul_nonneg (mul_pos hq hs).le (sub_nonneg.2 c2),
    mul_nonneg (mul_pos hq hr).le (sub_nonneg.2 c4)]

theorem A_lex4 {z w : ZMod 4 → ℝ} {p q r s : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (hT : p + q = r + s) (h : 0 < p * z 1 + q * z 3 - r * z 2 - s * z 0) :
    (z 0 < z 1 ∨ (z 0 = z 1 ∧ w 0 < w 1)) ∨ (z 0 < z 3 ∨ (z 0 = z 3 ∧ w 0 < w 3)) ∨
      (z 2 < z 1 ∨ (z 2 = z 1 ∧ w 2 < w 1)) ∨ (z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3)) := by
  rcases A_of_pos4 hp hq hr hs hT h with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

lemma fin7_cases (j : Fin 7) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
  revert j; decide

theorem tB_cyc (S : Shape18) (B2 : S.hm * S.tp < S.hp * (1 - S.tm)) (B3 : S.km * S.tp < S.hp * (1 - S.sm)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tp, 0, S.hp⟩ ⟨-2 * S.tp + 1, S.sp, -2 * S.hp + S.kp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i))
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ j).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := (mul_pos S.hp_pos S.sp_pos)
  have a3 := S.kp_pos
  have a4 := (sub_pos.2 S.roof_p')
  have a5 := (mul_pos S.kp_pos S.tp_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5]⟩)

theorem tB_rest2 (S : Shape18) (B2 : S.hm * S.tp < S.hp * (1 - S.tm)) (B3 : S.km * S.tp < S.hp * (1 - S.sm)) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tp, 0, S.hp⟩ ⟨-2 * S.tp + 1, S.sp, -2 * S.hp + S.kp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i)) := by
  have a1 := (mul_pos S.hp_pos S.sm_pos)
  have a2 := (sub_pos.2 B3)
  have a3 := (mul_pos (mul_pos (sub_pos.2 S.sm_lt) S.kp_pos) S.tp_pos)
  have a4 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) S.km_pos) S.tp_pos)
  have a5 := (mul_pos (mul_pos S.km_pos S.sp_pos) S.tp_pos)
  have a6 := (mul_pos (mul_pos S.kp_pos S.sm_pos) S.tp_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6]⟩)

theorem tB_rest5 (S : Shape18) (B2 : S.hm * S.tp < S.hp * (1 - S.tm)) (B3 : S.km * S.tp < S.hp * (1 - S.sm)) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tp, 0, S.hp⟩ ⟨-2 * S.tp + 1, S.sp, -2 * S.hp + S.kp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i)) := by
  have a1 := (mul_pos S.hp_pos S.sp_pos)
  have a2 := S.hp_pos
  have a3 := (mul_pos S.kp_pos S.tp_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3]⟩)

theorem tB_rest6 (S : Shape18) (B2 : S.hm * S.tp < S.hp * (1 - S.tm)) (B3 : S.km * S.tp < S.hp * (1 - S.sm)) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tp, 0, S.hp⟩ ⟨-2 * S.tp + 1, S.sp, -2 * S.hp + S.kp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i))
        ((⟨S.tm, 0, -S.hm⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, S.sp, S.kp⟩ i)) := by
  have a1 := (mul_pos S.hm_pos S.sp_pos)
  have a2 := (mul_pos (sub_pos.2 B2) S.sp_pos)
  have a3 := (sub_pos.2 B2)
  have a4 := (mul_pos S.kp_pos S.tm_pos)
  have a5 := (mul_pos S.tm_pos (sub_pos.2 S.roof_p'))
  have a6 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos) S.tp_pos)
  have a7 := (mul_pos (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos) S.tp_pos)
  have a8 := (mul_pos (mul_pos S.hm_pos S.sp_pos) S.tp_pos)
  have a9 := (mul_pos (mul_pos S.hp_pos S.sp_pos) S.tm_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9]⟩)


namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **27.32 / 27.28, the edge crossing at `m1+ v`** (apex `m1+`; `B2`, `B3`) -/
theorem tB (hA : F.a12 < F.a11) (B2 : F.S.hm * F.S.tp < F.S.hp * (1 - F.S.tm))
    (B3 : F.S.km * F.S.tp < F.S.hp * (1 - F.S.sm)) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have hgg : 0 < F.gg := F.g_pos
  have roof := F.S.roof_p'
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim4 0 3 4 1 ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p3 p4 p1 1 (Or.inl rfl) ⟨F.S.tp, 0, F.S.hp⟩
    ⟨-2 * F.S.tp + 1, F.S.sp, -2 * F.S.hp + F.S.kp⟩ (Or.inl htp.ne') ?_ ?_ ?_
  · exact tB_cyc F.S B2 B3
  · intro j' h0 h1 h2 h3 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h3
    · rw [p2]; exact tB_rest2 F.S B2 B3 i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p5]; exact tB_rest5 F.S B2 B3 i
    · rw [p6]; exact tB_rest6 F.S B2 B3 i
  · set Pq : ZMod 4 → C3 := quad ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tp, 0, F.S.hp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-2 * F.S.tp + 1, F.S.sp, -2 * F.S.hp + F.S.kp⟩ with hww
    refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      (B_lex (z := zz) (w := ww) (p := F.S.tp * F.S.kp) (q := F.S.hp * (1 - F.S.sp)) (r := F.S.hp * F.S.sp)
        (mul_pos htp hkp) (mul_pos hhp (by linarith)) (mul_pos hhp hsp) ?_)
    · simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos htp (sub_pos.2 hA)]
    · simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos (sub_pos.2 roof) (add_pos (mul_pos (mul_pos htp htp) hA11) (mul_pos (mul_pos hhp hhp) hgg))]

end Frame18

theorem t31a_cyc (S : Shape18) (Hp : S.kp * S.tp < S.hp * S.sp) (Hm : S.km * S.tm < S.hm * S.sm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i))
        ((quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ j).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := (mul_pos S.hm_pos S.tp_pos)
  have a3 := (mul_pos S.hp_pos S.tm_pos)
  have a4 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a5 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a6 := S.hm_pos
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6]⟩)

theorem t31a_rest1 (S : Shape18) (Hp : S.kp * S.tp < S.hp * S.sp) (Hm : S.km * S.tm < S.hm * S.sm) :
    ∀ i : ZMod 4,
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i))
        ((⟨0, S.sp, S.kp⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i)) := by
  have a1 := (sub_pos.2 Hp)
  have a2 := (sub_pos.2 S.roof_p')
  have a3 := (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos)
  have a4 := (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos)
  have a5 := (mul_pos S.kp_pos S.tm_pos)
  have a6 := (mul_pos S.hm_pos S.sp_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6]⟩)

theorem t31a_rest2 (S : Shape18) (Hp : S.kp * S.tp < S.hp * S.sp) (Hm : S.km * S.tm < S.hm * S.sm) :
    ∀ i : ZMod 4,
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i)) := by
  have a1 := (mul_pos S.km_pos S.tp_pos)
  have a2 := (mul_pos S.hp_pos S.sm_pos)
  have a3 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have a4 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have a5 := (sub_pos.2 S.roof_m')
  have a6 := (sub_pos.2 Hm)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6]⟩)

theorem t31a_rest4 (S : Shape18) (Hp : S.kp * S.tp < S.hp * S.sp) (Hm : S.km * S.tm < S.hm * S.sm) :
    ∀ i : ZMod 4,
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ (i + 1)).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quad (⟨0, 0, 0⟩ : C3) ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a3 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a4 := S.hm_pos
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4]⟩)


namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **27.31, apex `xa`, chains `1`/`1`** (`c+ < a+`, `c- < a-`): the rim `(v, m1+, xa, m1-)`. -/
theorem t31a (hα : F.a12 < F.a11) (Hp : F.S.kp * F.S.tp < F.S.hp * F.S.sp)
    (Hm : F.S.km * F.S.tm < F.S.hm * F.S.sm) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim4 5 0 3 6 ⟨0, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩
    p5 p0 p3 p6 (-1) (Or.inr rfl) ⟨1, -1, 0⟩
    ⟨F.S.tm + F.S.tp - 2, 0, -F.S.hm + F.S.hp⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t31a_cyc F.S Hp Hm
  · intro j' h0 h1 h2 h3 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h1
    · rw [p1]; exact t31a_rest1 F.S Hp Hm i
    · rw [p2]; exact t31a_rest2 F.S Hp Hm i
    · exact absurd rfl h2
    · rw [p4]; exact t31a_rest4 F.S Hp Hm i
    · exact absurd rfl h0
    · exact absurd rfl h3
  · set Pq : ZMod 4 → C3 := quad ⟨0, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tm + F.S.tp - 2, 0, -F.S.hm + F.S.hp⟩ with hww
    have e1 : zz 0 < zz 1 := by
      simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos htp (sub_pos.2 hα)]
    have e2 : zz 1 < zz 2 := by
      simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos (sub_pos.2 htp1) (sub_pos.2 hα)]
    exact Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl e1)) (Or.inr (Or.inr (Or.inl (Or.inl e2))))

end Frame18
theorem t31b_cyc (S : Shape18) (Hp : S.hp * S.sp < S.kp * S.tp) (Hm : S.km * S.tm < S.hm * S.sm) (hts : S.sp < S.tp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (mul_pos S.kp_pos S.tm_pos)
  have a2 := (mul_pos S.hm_pos S.sp_pos)
  have a3 := (mul_pos S.hm_pos S.tp_pos)
  have a4 := (mul_pos S.hp_pos S.tm_pos)
  have a5 := S.hm_pos
  have a6 := (sub_pos.2 Hp)
  have a7 := S.kp_pos
  have a8 := (mul_pos S.tm_pos (sub_pos.2 S.roof_p'))
  have a9 := (mul_pos S.hm_pos (sub_pos.2 hts))
  have a10 := (mul_pos (sub_pos.2 Hp) (sub_pos.2 S.tm_lt))
  have a11 := (sub_pos.2 S.roof_p')
  have a12 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a13 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a14 := S.hp_pos
  have a15 := (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos)
  have a16 := (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]⟩)

theorem t31b_rest2 (S : Shape18) (Hp : S.hp * S.sp < S.kp * S.tp) (Hm : S.km * S.tm < S.hm * S.sm) (hts : S.sp < S.tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (sub_pos.2 Hm)
  have a2 := (mul_pos S.km_pos S.sp_pos)
  have a3 := (mul_pos S.kp_pos S.sm_pos)
  have a4 := (mul_pos S.sm_pos (sub_pos.2 S.roof_p'))
  have a5 := (mul_pos S.km_pos (sub_pos.2 hts))
  have a6 := (mul_pos (sub_pos.2 Hp) (sub_pos.2 S.sm_lt))
  have a7 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have a8 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have a9 := (sub_pos.2 S.roof_m')
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9]⟩)

theorem t31b_rest4 (S : Shape18) (Hp : S.hp * S.sp < S.kp * S.tp) (Hm : S.km * S.tm < S.hm * S.sm) (hts : S.sp < S.tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨S.tm + S.tp - 2, 0, -S.hm + S.hp⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := S.hm_pos
  have a2 := S.kp_pos
  have a3 := (sub_pos.2 S.roof_p')
  have a4 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a5 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5]⟩)


namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **27.31, apex `xa`, chains `21`/`1`** (`c+ > a+`, `c- < a-`): the rim `(m1-, v, m2+, m1+, xa)`. -/
theorem t31b (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (Hp : F.S.hp * F.S.sp < F.S.kp * F.S.tp)
    (Hm : F.S.km * F.S.tm < F.S.hm * F.S.sm) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos
  have hts := F.S.sp_lt_tp Hp
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim5 6 5 1 0 3 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩
    p6 p5 p1 p0 p3 (-1) (Or.inr rfl) ⟨1, -1, 0⟩
    ⟨F.S.tm + F.S.tp - 2, 0, -F.S.hm + F.S.hp⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact t31b_cyc F.S Hp Hm hts
  · intro j' h0 h1 h2 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h3
    · exact absurd rfl h2
    · rw [p2]; exact t31b_rest2 F.S Hp Hm hts i
    · exact absurd rfl h4
    · rw [p4]; exact t31b_rest4 F.S Hp Hm hts i
    · exact absurd rfl h1
    · exact absurd rfl h0
  · set Pq : ZMod 5 → C3 := quint ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tm + F.S.tp - 2, 0, -F.S.hm + F.S.hp⟩ with hww
    have e1 : zz 1 < zz 0 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos htm (sub_pos.2 hα)]
    have e2 : zz 2 < zz 1 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos hsp (sub_pos.2 hβ)]
    have e3 : zz 2 < zz 3 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos hsp (sub_pos.2 hβ), mul_pos htp (sub_pos.2 hα)]
    have e4 : zz 3 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 htp1) (sub_pos.2 hα)]
    have e5 : zz 0 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 htm1) (sub_pos.2 hα)]
    exact Q5c_eventually (z := zz) (w := ww) (Or.inl e1) (Or.inl e2) (Or.inl e3) (Or.inl e4) (Or.inl e5)

end Frame18
namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- `tB` for the `Z`-image: the edge crossing at `m1- v` (`a- > b+`, `a- > d+`). -/
theorem tBz (hA : F.a12 < F.a11) (B2 : F.S.hp * F.S.tm < F.S.hm * (1 - F.S.tp))
    (B3 : F.S.kp * F.S.tm < F.S.hm * (1 - F.S.sp)) : IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.tB hA B2 B3)

/-- **27.31, apex `xa`, chains `1`/`21`** (`c+ < a+`, `c- > a-`): the `Z`-image of `t31b`. -/
theorem t31c (hα : F.a12 < F.a11) (hβ : F.a12 < F.a22) (Hp : F.S.hm * F.S.sm < F.S.km * F.S.tm)
    (Hm : F.S.kp * F.S.tp < F.S.hp * F.S.sp) : IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.t31b hα hβ Hp Hm)

end Frame18

theorem tA1_cyc (S : Shape18) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tp - 1, 0, S.hp⟩ ⟨-2 * S.tp, 1, -2 * S.hp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i))
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ j).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i)) := by
  have a1 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have a2 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have a3 := S.hp_pos
  have a4 := (mul_pos S.hp_pos S.sm_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4]⟩)

theorem tA1_rest1 (S : Shape18) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tp - 1, 0, S.hp⟩ ⟨-2 * S.tp, 1, -2 * S.hp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i))
        ((⟨0, S.sp, S.kp⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i)) := by
  have a1 := (sub_pos.2 S.roof_p')
  have a2 := (mul_pos (mul_pos (sub_pos.2 S.sm_lt) (sub_pos.2 S.tp_lt)) S.kp_pos)
  have a3 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) (sub_pos.2 S.tp_lt)) S.km_pos)
  have a4 := (mul_pos (mul_pos (sub_pos.2 S.tp_lt) S.km_pos) S.sp_pos)
  have a5 := (mul_pos (mul_pos (sub_pos.2 S.tp_lt) S.kp_pos) S.sm_pos)
  have a6 := (mul_pos S.hp_pos S.sp_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6]⟩)

theorem tA1_rest3 (S : Shape18) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tp - 1, 0, S.hp⟩ ⟨-2 * S.tp, 1, -2 * S.hp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i))
        ((⟨1, 0, 0⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i)) := by
  have a1 := S.hp_pos
  have a2 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have a3 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have a4 := (mul_pos S.hp_pos S.sm_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4]⟩)

theorem tA1_rest6 (S : Shape18) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) :
    ∀ i : ZMod 4,
      ST 1 ⟨S.tp - 1, 0, S.hp⟩ ⟨-2 * S.tp, 1, -2 * S.hp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i))
        ((⟨S.tm, 0, -S.hm⟩ : C3).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, 1, 0⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 0, 0⟩ i)) := by
  have a1 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a2 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a3 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have a4 := (mul_pos (sub_pos.2 A1) (sub_pos.2 S.sm_lt))
  have a5 := (mul_pos (sub_pos.2 A1) S.sm_pos)
  have a6 := S.hm_pos
  have a7 := (sub_pos.2 A1)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7]⟩)


namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- The pairing `⟨u₁, u₂⟩_G` of the two views of family A (`u₁ = m1+ - xa`, `u₂ = m1+ - xb`). -/
noncomputable def g12 : ℝ :=
  F.a11 * (F.S.tp * (F.S.tp - 1)) - F.a12 * (F.S.tp - 1) + F.gg * F.S.hp ^ 2

/-- **Family A, `T1`** (the edge crossing at `m1+ xa`, apex `m1+`): unimodal when `⟨u₁, u₂⟩ > 0`.
The rim is `(m1+, xb, m2-, v)`. -/
theorem tA1 (A1 : F.S.hm * (1 - F.S.tp) < F.S.hp * F.S.tm) (hg : 0 < F.g12) :
    IsRupert (Finset.univ.image x) := by
  have hsm := F.S.sm_pos; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkm := F.S.km_pos; have hgg : 0 < F.gg := F.g_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim4 0 4 2 5 ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 0, 0⟩
    p0 p4 p2 p5 1 (Or.inl rfl) ⟨F.S.tp - 1, 0, F.S.hp⟩
    ⟨-2 * F.S.tp, 1, -2 * F.S.hp⟩ (Or.inl (sub_ne_zero.2 htp1.ne)) ?_ ?_ ?_
  · exact tA1_cyc F.S A1
  · intro j' h0 h1 h2 h3 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact tA1_rest1 F.S A1 i
    · exact absurd rfl h2
    · rw [p3]; exact tA1_rest3 F.S A1 i
    · exact absurd rfl h1
    · exact absurd rfl h3
    · rw [p6]; exact tA1_rest6 F.S A1 i
  · set Pq : ZMod 4 → C3 := quad ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 0, 0⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tp - 1, 0, F.S.hp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-2 * F.S.tp, 1, -2 * F.S.hp⟩ with hww
    have hB : zz 1 < zz 0 := by
      simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      unfold g12 at hg
      nlinarith
    refine Q4_eventually (z := zz) (w := ww)
      (A_lex4 (p := F.S.hp * F.S.sm) (q := F.S.hp + (1 - F.S.tp) * F.S.km - F.S.hp * F.S.sm)
        (r := F.S.hp) (s := (1 - F.S.tp) * F.S.km) (mul_pos hhp hsm)
        (by nlinarith [F.S.sm_lt, mul_pos (sub_pos.2 htp1) hkm]) hhp (mul_pos (sub_pos.2 htp1) hkm)
        (by ring) ?_) (Or.inl (Or.inl hB))
    simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
    nlinarith [mul_pos (mul_pos F.S.km_pos htp) (add_pos (mul_pos (mul_pos (sub_pos.2 htp1) (sub_pos.2 htp1)) hA11) (mul_pos (mul_pos hhp hhp) hgg))]

end Frame18
theorem tA2_cyc (S : Shape18) {b : ℝ} (hb : 0 < b) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) (A2 : S.km * S.tm < S.sm * (S.hp * S.tm + S.tp * S.hm)) (A3 : S.km * (1 - S.tm) < S.hp * S.sm * (1 - S.tm) + S.hm * (1 - S.tp * S.sm)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨S.tp, -1, S.hp⟩ ⟨-b * S.tp - S.tp + 1, b * S.sp, -b * S.hp + b * S.kp - S.hp⟩
        ((quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (mul_pos S.kp_pos S.tp_pos)
  have a2 := (mul_pos S.tm_pos (sub_pos.2 S.roof_p'))
  have a3 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos) S.tp_pos)
  have a4 := (mul_pos (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos) S.tp_pos)
  have a5 := (sub_pos.2 S.roof_p')
  have a6 := (mul_pos S.kp_pos S.tm_pos)
  have a7 := (mul_pos S.hm_pos S.sp_pos)
  have a8 := (mul_pos (sub_pos.2 A1) S.sp_pos)
  have a9 := S.kp_pos
  have a10 := (mul_pos S.hp_pos S.sp_pos)
  have a11 := S.hm_pos
  have a12 := (sub_pos.2 A1)
  have a13 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a14 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a15 := (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos)
  have a16 := (mul_pos (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos) S.sp_pos)
  have a17 := S.hp_pos
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]⟩)

theorem tA2_rest2 (S : Shape18) {b : ℝ} (hb : 0 < b) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) (A2 : S.km * S.tm < S.sm * (S.hp * S.tm + S.tp * S.hm)) (A3 : S.km * (1 - S.tm) < S.hp * S.sm * (1 - S.tm) + S.hm * (1 - S.tp * S.sm)) :
    ∀ i : ZMod 5,
      ST 1 ⟨S.tp, -1, S.hp⟩ ⟨-b * S.tp - S.tp + 1, b * S.sp, -b * S.hp + b * S.kp - S.hp⟩
        ((quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (mul_pos (mul_pos (sub_pos.2 S.sm_lt) S.kp_pos) S.tp_pos)
  have a2 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) S.km_pos) S.tp_pos)
  have a3 := (mul_pos (mul_pos S.km_pos S.sp_pos) S.tp_pos)
  have a4 := (mul_pos (mul_pos S.kp_pos S.sm_pos) S.tp_pos)
  have a5 := (sub_pos.2 A2)
  have a6 := (sub_pos.2 A3)
  have a7 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have a8 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7, a8])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7, a8]⟩)

theorem tA2_rest4 (S : Shape18) {b : ℝ} (hb : 0 < b) (A1 : S.hm * (1 - S.tp) < S.hp * S.tm) (A2 : S.km * S.tm < S.sm * (S.hp * S.tm + S.tp * S.hm)) (A3 : S.km * (1 - S.tm) < S.hp * S.sm * (1 - S.tm) + S.hm * (1 - S.tp * S.sm)) :
    ∀ i : ZMod 5,
      ST 1 ⟨S.tp, -1, S.hp⟩ ⟨-b * S.tp - S.tp + 1, b * S.sp, -b * S.hp + b * S.kp - S.hp⟩
        ((quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quint (⟨S.tp, 0, S.hp⟩ : C3) ⟨0, S.sp, S.kp⟩ ⟨0, 0, 0⟩ ⟨S.tm, 0, -S.hm⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (sub_pos.2 S.roof_p')
  have a2 := (mul_pos S.kp_pos S.tp_pos)
  have a3 := S.hm_pos
  have a4 := (sub_pos.2 A1)
  have a5 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a6 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a7 := (mul_pos hb (sub_pos.2 S.roof_p'))
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a6, a7])
    | (right; refine ⟨by ring, by linarith [a1, a2, a3, a4, a5, a6, a7]⟩)


namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

lemma A2_of (h : F.S.km < F.S.sm * (F.S.hp + F.S.tp * F.S.am)) :
    F.S.km * F.S.tm < F.S.sm * (F.S.hp * F.S.tm + F.S.tp * F.S.hm) := by
  have e := F.S.am_mul
  have := mul_lt_mul_of_pos_right h F.S.tm_pos
  have e' : F.S.sm * (F.S.hp + F.S.tp * F.S.am) * F.S.tm =
      F.S.sm * (F.S.hp * F.S.tm + F.S.tp * F.S.hm) := by rw [← e]; ring
  linarith

lemma A3_of (h : F.S.km < F.S.hp * F.S.sm + F.S.bm * (1 - F.S.tp * F.S.sm)) :
    F.S.km * (1 - F.S.tm) < F.S.hp * F.S.sm * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp * F.S.sm) := by
  have e := F.S.bm_mul
  have := mul_lt_mul_of_pos_right h (sub_pos.2 F.S.tm_lt)
  have e' : (F.S.hp * F.S.sm + F.S.bm * (1 - F.S.tp * F.S.sm)) * (1 - F.S.tm) =
      F.S.hp * F.S.sm * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp * F.S.sm) := by rw [← e]; ring
  linarith

lemma A1_of (h : F.S.am < F.S.bp) : F.S.hm * (1 - F.S.tp) < F.S.hp * F.S.tm := by
  have e1 := F.S.am_mul; have e2 := F.S.bp_mul
  have := mul_lt_mul_of_pos_right h (mul_pos F.S.tm_pos (sub_pos.2 F.S.tp_lt))
  have e3 : F.S.am * (F.S.tm * (1 - F.S.tp)) = F.S.hm * (1 - F.S.tp) := by rw [← e1]; ring
  have e4 : F.S.bp * (F.S.tm * (1 - F.S.tp)) = F.S.hp * F.S.tm := by rw [← e2]; ring
  linarith

/-- **Family A, `T2`** (the edge crossing at `m1+ xb`, apex `m1+`): unimodal when `⟨u₁, u₂⟩ ≤ 0`.
The rim is `(m1+, m2+, v, m1-, xa)`; the tilt `(xa - m1+) + b (m2+ - m1+)`. -/
theorem tA2 (A1 : F.S.hm * (1 - F.S.tp) < F.S.hp * F.S.tm)
    (A2 : F.S.km * F.S.tm < F.S.sm * (F.S.hp * F.S.tm + F.S.tp * F.S.hm))
    (A3 : F.S.km * (1 - F.S.tm) < F.S.hp * F.S.sm * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp * F.S.sm))
    (hg : F.g12 ≤ 0) : IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos
  have hgg : 0 < F.gg := F.g_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hA12 : 0 < F.a12 := F.A12_pos
  have hle22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have hA22 : F.a12 < F.a22 ∨ F.a12 = F.a22 := lt_or_eq_of_le F.A12_le_A22
  have hA22' : 0 < F.a22 := lt_of_lt_of_le F.A12_pos F.A12_le_A22
  have roof := F.S.roof_p'
  -- the tilt parameter
  set nu : ℝ := F.toFrame7.GG ⟨1 - F.S.tp, 0, -F.S.hp⟩ ⟨1 - F.S.tp, 0, -F.S.hp⟩ with hnu
  set X : ℝ := F.toFrame7.GG ⟨1 - F.S.tp, 0, -F.S.hp⟩ ⟨-F.S.tp, F.S.sp, F.S.kp - F.S.hp⟩ with hX
  have hnu0 : 0 < nu := by
    simp only [hnu, GG_eq]
    nlinarith [mul_pos (mul_pos (sub_pos.2 htp1) (sub_pos.2 htp1)) hA11, mul_pos (mul_pos hhp hhp) hgg]
  obtain ⟨b, hb, hbX⟩ : ∃ b : ℝ, 0 < b ∧ -(b * X) < nu := by
    refine ⟨nu / (2 * (|X| + 1)), by positivity, ?_⟩
    have h1 : -(nu / (2 * (|X| + 1)) * X) ≤ nu / (2 * (|X| + 1)) * |X| := by
      have := neg_abs_le X
      nlinarith [div_pos hnu0 (by positivity : (0:ℝ) < 2 * (|X| + 1))]
    have h2 : nu / (2 * (|X| + 1)) * |X| < nu := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg X]
    linarith
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim5p 0 1 5 6 3 ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩
    p0 p1 p5 p6 p3 1 (Or.inl rfl) ⟨F.S.tp, -1, F.S.hp⟩
    ⟨-b * F.S.tp - F.S.tp + 1, b * F.S.sp, -b * F.S.hp + b * F.S.kp - F.S.hp⟩ (Or.inl htp.ne') ?_ ?_ ?_
  · exact tA2_cyc F.S hb A1 A2 A3
  · intro j' h0 h1 h2 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · rw [p2]; exact tA2_rest2 F.S hb A1 A2 A3 i
    · exact absurd rfl h4
    · rw [p4]; exact tA2_rest4 F.S hb A1 A2 A3 i
    · exact absurd rfl h2
    · exact absurd rfl h3
  · set Pq : ZMod 5 → C3 := quint ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 0, 0⟩
      ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tp, -1, F.S.hp⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-b * F.S.tp - F.S.tp + 1, b * F.S.sp, -b * F.S.hp + b * F.S.kp - F.S.hp⟩ with hww
    have hz04 : zz 0 < zz 4 ∨ (zz 0 = zz 4 ∧ ww 0 < ww 4) := by
      have hdiff : zz 4 - zz 0 = -F.g12 := by
        simp only [hzz, hPq, GG_eq, quint_0, quint_4, g12]; ring
      have hw : ww 4 - ww 0 = nu + b * X := by
        simp only [hww, hPq, hnu, hX, GG_eq, quint_0, quint_4]; ring
      rcases lt_or_eq_of_le hg with h | h
      · left; linarith
      · right; constructor
        · linarith
        · linarith
    have hAA : 0 < F.a22 - F.S.tp * F.a12 := by nlinarith [hle22, mul_pos hA12 (sub_pos.2 htp1)]
    have p13 : zz 1 < zz 0 ∨ zz 1 < zz 2 ∨ zz 3 < zz 2 ∨ zz 3 < zz 4 := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4] at c1 c2 c3 c4
      linarith [mul_nonneg (mul_pos htm hhm).le (sub_nonneg.2 c1),
        mul_nonneg (add_pos (mul_pos hhm htp) (mul_pos (mul_pos htm hkp) (sub_pos.2 htm1))).le
          (sub_nonneg.2 c3),
        mul_nonneg (mul_pos (mul_pos htm htm) hkp).le (sub_nonneg.2 c4),
        mul_pos (mul_pos (mul_pos htm hhm) hsp) hAA,
        mul_pos (mul_pos (mul_pos hgg hhp) hhm) (add_pos (mul_pos htm hhp) (mul_pos hhm htp))]
    have p24 : zz 2 < zz 1 ∨ zz 2 < zz 3 ∨ zz 4 < zz 3 ∨ zz 4 < zz 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4] at c1 c2 c3 c4
      linarith [mul_nonneg (sub_pos.2 htp1).le (sub_nonneg.2 c2), mul_nonneg htm.le (sub_nonneg.2 c4),
        mul_pos (mul_pos hgg hhp) (sub_pos.2 A1)]
    have p41 : zz 4 < zz 3 ∨ zz 4 < zz 0 ∨ zz 1 < zz 0 ∨ zz 1 < zz 2 := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      simp only [hzz, hPq, GG_eq, quint_0, quint_1, quint_2, quint_3, quint_4] at c1 c2 c3 c4
      linarith [mul_nonneg htp.le (sub_nonneg.2 c2), mul_nonneg (sub_pos.2 htp1).le (sub_nonneg.2 c3),
        mul_pos (mul_pos (sub_pos.2 htp1) hsp) hAA,
        mul_pos (mul_pos hgg hhp) (sub_pos.2 (roof.trans_le (by nlinarith) : F.S.kp * (1 - F.S.tp) < F.S.hp))]
    exact Q5p_eventually (z := zz) (w := ww) (Or.inl hz04) (lex_wrap p13) (lex_wrap p24)
      (Or.inr (Or.inr (Or.inl hz04))) (lex_wrap p41)

/-- **Corollary 27.29, family A** (type 18): at the frame's metric, the pair of tests at `m1+`
(`T1` at `m1+ xa`, `T2` at `m1+ xb`) — one of them is unimodal according to the sign of
`⟨u₁, u₂⟩_G`.  No acuteness is needed. -/
theorem famA (A1 : F.S.hm * (1 - F.S.tp) < F.S.hp * F.S.tm)
    (A2 : F.S.km * F.S.tm < F.S.sm * (F.S.hp * F.S.tm + F.S.tp * F.S.hm))
    (A3 : F.S.km * (1 - F.S.tm) < F.S.hp * F.S.sm * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp * F.S.sm)) :
    IsRupert (Finset.univ.image x) := by
  by_cases hg : 0 < F.g12
  · exact F.tA1 A1 hg
  · exact F.tA2 A1 A2 A3 (not_lt.mp hg)

end Frame18
/-! ### Theorem 5 with `W = F2` (27.17; type 18) -/

/-- The open quad `F2` in the `(y, z)`-projection: `(Y, Z)` strictly inside. -/
def InQuad2 (S : Shape18) (Y Z : ℝ) : Prop :=
  Z < S.cp * Y ∧ Z < S.dp * (1 - Y) ∧ -Z < S.cm * Y ∧ -Z < S.dm * (1 - Y)

lemma quad2_weights (S : Shape18) {Y Z : ℝ} (h : InQuad2 S Y Z) :
    ∃ m0 m1 m3 m4 : ℝ, 0 < m0 ∧ 0 < m1 ∧ 0 < m3 ∧ 0 < m4 ∧ m0 + m1 + m3 + m4 = 1 ∧
      m3 + S.sp * m1 + S.sm * m4 = Y ∧ S.kp * m1 - S.km * m4 = Z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have htp := S.sp_pos; have htp1 := S.sp_lt; have htm := S.sm_pos; have htm1 := S.sm_lt
  have hhp := S.kp_pos; have hhm := S.km_pos
  have e1 := S.cp_mul; have e2 := S.dp_mul; have e3 := S.cm_mul; have e4 := S.dm_mul
  rcases le_or_gt 0 Z with hZ | hZ
  · refine weights_core htp htp1 htm htm1 hhp hhm (u0 := Z / S.kp) (l0 := 0)
      (div_nonneg hZ hhp.le) le_rfl (by field_simp; ring) ?_ ?_
    · rw [mul_zero, add_zero, ← sub_pos]
      have : S.kp * Y - S.sp * Z > 0 := by
        have := mul_lt_mul_of_pos_left h1 htp
        have e : S.sp * (S.cp * Y) = S.kp * Y := by rw [← e1]; ring
        linarith
      have : Y - S.sp * (Z / S.kp) = (S.kp * Y - S.sp * Z) / S.kp := by field_simp
      rw [this]; positivity
    · rw [mul_zero, add_zero, ← sub_pos]
      have : S.kp * (1 - Y) - (1 - S.sp) * Z > 0 := by
        have := mul_lt_mul_of_pos_left h2 (sub_pos.2 htp1)
        have e : (1 - S.sp) * (S.dp * (1 - Y)) = S.kp * (1 - Y) := by rw [← e2]; ring
        linarith
      have : 1 - Y - (1 - S.sp) * (Z / S.kp) = (S.kp * (1 - Y) - (1 - S.sp) * Z) / S.kp := by
        field_simp
      rw [this]; positivity
  · refine weights_core htp htp1 htm htm1 hhp hhm (u0 := 0) (l0 := -Z / S.km)
      le_rfl (div_nonneg (by linarith) hhm.le) (by field_simp; ring) ?_ ?_
    · rw [mul_zero, zero_add, ← sub_pos]
      have : S.km * Y - S.sm * (-Z) > 0 := by
        have := mul_lt_mul_of_pos_left h3 htm
        have e : S.sm * (S.cm * Y) = S.km * Y := by rw [← e3]; ring
        linarith
      have : Y - S.sm * (-Z / S.km) = (S.km * Y - S.sm * (-Z)) / S.km := by field_simp
      rw [this]; positivity
    · rw [mul_zero, zero_add, ← sub_pos]
      have : S.km * (1 - Y) - (1 - S.sm) * (-Z) > 0 := by
        have := mul_lt_mul_of_pos_left h4 (sub_pos.2 htm1)
        have e : (1 - S.sm) * (S.dm * (1 - Y)) = S.km * (1 - Y) := by rw [← e4]; ring
        linarith
      have : 1 - Y - (1 - S.sm) * (-Z / S.km) = (S.km * (1 - Y) - (1 - S.sm) * (-Z)) / S.km := by
        field_simp
      rw [this]; positivity

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

lemma cross_F2 (hx : Function.Injective x) (i : Fin 7) {τ p q r Y Z : ℝ}
    (hp : (F.toFrame7.ptC i).x + τ * p = 0)
    (hY : (F.toFrame7.ptC i).y + τ * q = Y) (hZ : (F.toFrame7.ptC i).z + τ * r = Z)
    (hin : InQuad2 F.S Y Z) :
    ∃ (τ : ℝ) (m : Fin 7 → ℝ), (∀ j ∈ ({5, 1, 4, 2} : Finset (Fin 7)), 0 < m j) ∧
      ∑ j ∈ ({5, 1, 4, 2} : Finset (Fin 7)), m j = 1 ∧
      ∑ j ∈ ({5, 1, 4, 2} : Finset (Fin 7)), m j * (F.toFrame7.ptC j).x =
        (F.toFrame7.ptC i).x + τ * p ∧
      ∑ j ∈ ({5, 1, 4, 2} : Finset (Fin 7)), m j * (F.toFrame7.ptC j).y =
        (F.toFrame7.ptC i).y + τ * q ∧
      ∑ j ∈ ({5, 1, 4, 2} : Finset (Fin 7)), m j * (F.toFrame7.ptC j).z =
        (F.toFrame7.ptC i).z + τ * r := by
  obtain ⟨m0, m1, m3, m4, p0, p1, p3, p4, hs, hxx, hzz⟩ := quad2_weights F.S hin
  have q5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [toFrame7, pt]
  have q1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [toFrame7, pt]
  have q4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [toFrame7, pt]
  have q2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [toFrame7, pt]
  refine ⟨τ, fun j => if j = 5 then m0 else if j = 1 then m1 else if j = 4 then m3 else m4,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [p0, p1, p3, p4]
  · simp [Finset.sum_insert]; linarith
  · rw [hp]; simp [Finset.sum_insert, q5, q1, q4, q2]
  · rw [hY]; simp [Finset.sum_insert, q5, q1, q4, q2]; linarith
  · rw [hZ]; simp [Finset.sum_insert, q5, q1, q4, q2]; linarith

/-- **Theorem 5 with `W = F2`, from a view** `u₀ = u₁ - α u₂ - γ e` (27.17's proof): the three
points `xa, m1+, m1-` land in the open quad of `F2`. -/
theorem rupert_of_F2_view (hx : Function.Injective x) (α γ : ℝ)
    (h3 : InQuad2 F.S α γ) (h0 : InQuad2 F.S (F.S.tp * α) (F.S.hp + F.S.tp * γ))
    (h6 : InQuad2 F.S (F.S.tm * α) (-F.S.hm + F.S.tm * γ)) :
    IsRupert (Finset.univ.image x) := by
  classical
  have q0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [toFrame7, pt]
  have q3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [toFrame7, pt]
  have q6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [toFrame7, pt]
  have q5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [toFrame7, pt]
  have q1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [toFrame7, pt]
  have q4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [toFrame7, pt]
  have q2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [toFrame7, pt]
  refine F.toFrame7.rupert_crossing hx {5, 1, 4, 2} 5 1 4 (by decide) (by decide) (by decide) ?_
    1 0 0 0 ?_ 1 (-α) (-γ) (by norm_num) ?_
  · intro s t h1 h2 h3'
    rw [q5, q1, q4] at h2 h3'
    simp only [] at h1 h2 h3'
    have hk := F.S.kp_pos
    have hs : s = 0 := by
      have : s * F.S.kp = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hk.ne'
    subst hs
    exact ⟨rfl, by linarith⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [q5, q1, q4, q2]
  · intro i hi
    fin_cases i
    · exact F.cross_F2 hx 0 (τ := -F.S.tp) (by rw [q0]; simp) (by rw [q0]; simp <;> linarith)
        (by rw [q0]; simp <;> linarith) h0
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · exact F.cross_F2 hx 3 (τ := -1) (by rw [q3]; simp) (by rw [q3]; simp)
        (by rw [q3]; simp) h3
    · exact absurd (by decide) hi
    · exact absurd (by decide) hi
    · exact F.cross_F2 hx 6 (τ := -F.S.tm) (by rw [q6]; simp) (by rw [q6]; simp <;> linarith)
        (by rw [q6]; simp <;> linarith) h6

end Frame18


end Minimality.CaseC18

end
