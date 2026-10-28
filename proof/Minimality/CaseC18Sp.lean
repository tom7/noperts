module

public import Minimality.CaseC18Level

@[expose] public section

/-!
# Type 18, acute case (c): the special positions after PROOFS section 35 

Paper: `FEWER-FACES-PROOFS.md` section 35 (Lemma B, Theorems 1-4), referee fixes at its top.
All groups are proved; see `nopert229/out/bottleneck/sp18/handoff_lean.md` for the plan.

Final special set (`CaseC18Special'`):
```
  (a12 = a11 ∧ bp ≤ am ∧ bm ≤ ap ∧ ¬(cp < ap ∧ cm < am))
  ∨ (am = bp ∧ am = cm) ∨ (ap = bm ∧ ap = cp)
  ∨ ((dp = A1 tp ∨ dm = A1 tm ∨ D2p = 0) ∧ ap < cp ∧ am < cm)
```

Test summary (all at the view `u = xa - xb = (1,-1,0)` unless noted; `Z` = `rupert_of_z (zFrame ..)`):
* Group 0 (Theorem 1): `t31b_le`, `t31c_le` (no `hβ`, via the open depth predicate `Q5v`).
* Group 1 (Theorem 2, C4): `t31_C4`, `t31_C4z`.
* Group 2 (Theorem 2, C5/C6): `t31_C5z`, `t31_C5`, `t31_C6`, `t31_C6z`.
* Group 3 (Theorem 3): `tB_merged`, `tBz_merged`.
* Group 4 (Theorem 4): `g12_pos_of_eq`, `tA1_of_eq`, `tA1z_of_eq`, `t31a_eq`, `rupert_of_a12_eq_a11`.
* Group 5 (assembly): `rupert_or_V'`, `CaseC18Special'`, `isRupert_of_not_special'`.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-! ### Group 0: the open depth predicate with a free bottom pair, and Theorem 1 -/

/-- The open depth condition of a five-corner rim `(c0, .., c4)` with the unique top `c4` where the
two bottom corners `c1`, `c2` may be in either order (a level bottom edge is allowed):
`z1 < z0`, `z2 < z3`, `z3 < z4`, `z0 < z4`.  Weaker than `Q5c` (which also asks `z2 < z1`). -/
def Q5v (z : ZMod 5 → ℝ) : Prop := z 1 < z 0 ∧ z 2 < z 3 ∧ z 3 < z 4 ∧ z 0 < z 4

theorem Q5v_open : IsOpen {z : ZMod 5 → ℝ | Q5v z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q5v, Set.ofPred_and]
  exact (hlt 1 0).inter ((hlt 2 3).inter ((hlt 3 4).inter (hlt 0 4)))

theorem Q5v_smul {z : ZMod 5 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q5v z) : Q5v fun i => a * z i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 ha,
    mul_lt_mul_of_pos_left h3 ha, mul_lt_mul_of_pos_left h4 ha⟩

theorem Q5v_shift {z : ZMod 5 → ℝ} (a : ℝ) (h : Q5v z) : Q5v fun i => z i + a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Injective + `Q5v` is cyclic unimodal (`isCyclicUnimodal_of_top` with the top `4`). -/
theorem Q5v_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5v z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine isCyclicUnimodal_of_top (by norm_num) hinj 4 ?_
  intro i hi
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
  · left; rw [b0]; exact h4
  · left; rw [b1]; exact h1
  · right; rw [a2]; exact h2
  · right; rw [a3]; exact h3
  · exact absurd rfl hi

theorem Q5v_eventually {z w : ZMod 5 → ℝ}
    (h1 : z 1 < z 0 ∨ (z 1 = z 0 ∧ w 1 < w 0)) (h3 : z 2 < z 3 ∨ (z 2 = z 3 ∧ w 2 < w 3))
    (h4 : z 3 < z 4 ∨ (z 3 = z 4 ∧ w 3 < w 4)) (h5 : z 0 < z 4 ∨ (z 0 = z 4 ∧ w 0 < w 4)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5v fun i => z i + s * w i := by
  filter_upwards [ev_lt h1, ev_lt h3, ev_lt h4, ev_lt h5] with s a b c d
  exact ⟨a, b, c, d⟩

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- `rupert_rim5` with the depth predicate `Q5v` (template: `Frame7.rupert_rim5`, `CaseC18Bridge`). -/
theorem rupert_rim5v (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 → ∀ i : ZMod 5,
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((F.ptC j').sub (quint P0 P1 P2 P3 P4 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5v fun i => F.GG (quint P0 P1 P2 P3 P4 i) u +
      s * F.GG (quint P0 P1 P2 P3 P4 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quint c0 c1 c2 c3 c4 i) = quint P0 P1 P2 P3 P4 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, e0, e1, e2, e3, e4]
  refine F.rupert_rim (k := 5) (by norm_num) (quint c0 c1 c2 c3 c4) σ hσ u v hu ?_ ?_ Q5v
    Q5v_open (fun z a ha => Q5v_smul ha) (fun z a => Q5v_shift a) ?_
    (fun z hz hq => Q5v_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quint_0, h])
    · exact fun h => hj' 1 (by simp [quint_1, h])
    · exact fun h => hj' 2 (by simp [quint_2, h])
    · exact fun h => hj' 3 (by simp [quint_3, h])
    · exact fun h => hj' 4 (by simp [quint_4, h])
  · simpa only [hc] using hQe

end Frame7

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **Theorem 1** (`t31b` without `hβ`; `A12 = A22` allowed): rim `(m1-, v, m2+, m1+, xa)`, the
tilt and the shape-only rim lemmas of `t31b`, depths by `Q5v` (the bottom pair `v`, `m2+`). -/
theorem t31b_le (hα : F.a12 < F.a11) (Hp : F.S.hp * F.S.sp < F.S.kp * F.S.tp)
    (Hm : F.S.km * F.S.tm < F.S.hm * F.S.sm) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos
  have hle22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have hts := F.S.sp_lt_tp Hp
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim5v 6 5 1 0 3 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩
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
      simp only [hzz, hPq, GG_eq, quint_0, quint_1]
      nlinarith [mul_pos htm (sub_pos.2 hα)]
    have e3 : zz 2 < zz 3 := by
      simp only [hzz, hPq, GG_eq, quint_2, quint_3]
      nlinarith [mul_nonneg hsp.le (sub_nonneg.2 hle22), mul_pos htp (sub_pos.2 hα)]
    have e4 : zz 3 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 htp1) (sub_pos.2 hα)]
    have e5 : zz 0 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_4]
      nlinarith [mul_pos (sub_pos.2 htm1) (sub_pos.2 hα)]
    exact Q5v_eventually (z := zz) (w := ww) (Or.inl e1) (Or.inl e3) (Or.inl e4) (Or.inl e5)

/-- **Theorem 1**, `Z`-image (`t31c` without `hβ`). -/
theorem t31c_le (hα : F.a12 < F.a11) (Hp : F.S.hm * F.S.sm < F.S.km * F.S.tm)
    (Hm : F.S.kp * F.S.tp < F.S.hp * F.S.sp) : IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.t31b_le hα Hp Hm)


/-! ### Group 1 helper lemmas: the ST tests of C4 (`a+ = c+`) -/

theorem C4_cyc (S : Shape18) (Hpe : S.hp * S.sp = S.kp * S.tp) (Hm : S.km * S.tm < S.hm * S.sm) (hts : S.sp < S.tp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨1, -1, 0⟩ ⟨-1, 0, S.hp / 2⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (mul_pos S.kp_pos S.tm_pos)
  have a2 := (mul_pos S.hm_pos S.sp_pos)
  have a3 := (mul_pos S.hm_pos S.tp_pos)
  have a4 := (mul_pos S.hp_pos S.tm_pos)
  have a5 := S.hm_pos
  have a7 := S.kp_pos
  have a8 := (mul_pos S.tm_pos (sub_pos.2 S.roof_p'))
  have a9 := (mul_pos S.hm_pos (sub_pos.2 hts))
  have a11 := (sub_pos.2 S.roof_p')
  have a12 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a13 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a14 := S.hp_pos
  have a15 := (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos)
  have a16 := (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos)
  have d1 : S.kp < S.hp := by
    by_contra hh
    push Not at hh
    nlinarith [mul_le_mul_of_nonneg_right hh S.tp_pos.le, mul_pos S.hp_pos (sub_pos.2 hts)]
  have d2 := mul_pos S.tm_pos (sub_pos.2 d1)
  have d3 := mul_pos (sub_pos.2 hts) S.hm_pos
  have d4 := (sub_pos.2 Hm)
  have d5 := (mul_pos S.km_pos S.sp_pos)
  have d6 := (mul_pos S.kp_pos S.sm_pos)
  have d7 := (mul_pos S.sm_pos (sub_pos.2 S.roof_p'))
  have d8 := (mul_pos S.km_pos (sub_pos.2 hts))
  have d9 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have d10 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have d11 := (sub_pos.2 S.roof_m')
  have d12 := mul_pos S.hp_pos S.sm_pos
  have d13 := mul_pos S.hp_pos S.km_pos
  have d14 := mul_pos S.hp_pos S.sp_pos
  have d15 := mul_pos (mul_pos S.hp_pos S.sm_pos) S.hp_pos
  have d16 : 0 < (S.tp - S.sp) * (S.km + S.kp) + (S.hp - S.kp) * (S.sm - S.sp) := by
    have h0 : S.sp * ((S.tp - S.sp) * (S.km + S.kp) + (S.hp - S.kp) * (S.sm - S.sp)) =
        (S.tp - S.sp) * (S.km * S.sp + S.kp * S.sm) := by linear_combination (S.sm - S.sp) * Hpe
    by_contra hh
    have h1 := mul_nonpos_of_nonneg_of_nonpos S.sp_pos.le (not_lt.1 hh)
    have h2 := mul_pos (sub_pos.2 hts) (add_pos d5 d6)
    linarith
  have c1 := mul_pos S.hp_pos S.hp_pos
  have c2 := mul_pos S.hp_pos S.sp_pos
  have c3 := mul_pos (mul_pos S.hp_pos S.sp_pos) S.tp_pos
  have c4 := mul_pos S.hp_pos S.tp_pos
  have c5 := mul_pos S.hp_pos S.tm_pos
  have c6 := mul_pos S.hp_pos S.hm_pos
  have c7 := mul_pos S.hp_pos S.kp_pos
  have c8 := mul_pos S.hp_pos (sub_pos.2 S.tp_lt)
  have c9 := mul_pos S.hp_pos (sub_pos.2 S.tm_lt)
  have c10 := mul_pos (mul_pos S.hp_pos S.hp_pos) (sub_pos.2 S.tm_lt)
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
    | (left; linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe])
    | (right; refine ⟨by linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe], by linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe]⟩)

theorem C4_rest2 (S : Shape18) (Hpe : S.hp * S.sp = S.kp * S.tp) (Hm : S.km * S.tm < S.hm * S.sm) (hts : S.sp < S.tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨-1, 0, S.hp / 2⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (mul_pos S.kp_pos S.tm_pos)
  have a2 := (mul_pos S.hm_pos S.sp_pos)
  have a3 := (mul_pos S.hm_pos S.tp_pos)
  have a4 := (mul_pos S.hp_pos S.tm_pos)
  have a5 := S.hm_pos
  have a7 := S.kp_pos
  have a8 := (mul_pos S.tm_pos (sub_pos.2 S.roof_p'))
  have a9 := (mul_pos S.hm_pos (sub_pos.2 hts))
  have a11 := (sub_pos.2 S.roof_p')
  have a12 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a13 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a14 := S.hp_pos
  have a15 := (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos)
  have a16 := (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos)
  have d1 : S.kp < S.hp := by
    by_contra hh
    push Not at hh
    nlinarith [mul_le_mul_of_nonneg_right hh S.tp_pos.le, mul_pos S.hp_pos (sub_pos.2 hts)]
  have d2 := mul_pos S.tm_pos (sub_pos.2 d1)
  have d3 := mul_pos (sub_pos.2 hts) S.hm_pos
  have d4 := (sub_pos.2 Hm)
  have d5 := (mul_pos S.km_pos S.sp_pos)
  have d6 := (mul_pos S.kp_pos S.sm_pos)
  have d7 := (mul_pos S.sm_pos (sub_pos.2 S.roof_p'))
  have d8 := (mul_pos S.km_pos (sub_pos.2 hts))
  have d9 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have d10 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have d11 := (sub_pos.2 S.roof_m')
  have d12 := mul_pos S.hp_pos S.sm_pos
  have d13 := mul_pos S.hp_pos S.km_pos
  have d14 := mul_pos S.hp_pos S.sp_pos
  have d15 := mul_pos (mul_pos S.hp_pos S.sm_pos) S.hp_pos
  have d16 : 0 < (S.tp - S.sp) * (S.km + S.kp) + (S.hp - S.kp) * (S.sm - S.sp) := by
    have h0 : S.sp * ((S.tp - S.sp) * (S.km + S.kp) + (S.hp - S.kp) * (S.sm - S.sp)) =
        (S.tp - S.sp) * (S.km * S.sp + S.kp * S.sm) := by linear_combination (S.sm - S.sp) * Hpe
    by_contra hh
    have h1 := mul_nonpos_of_nonneg_of_nonpos S.sp_pos.le (not_lt.1 hh)
    have h2 := mul_pos (sub_pos.2 hts) (add_pos d5 d6)
    linarith
  have c1 := mul_pos S.hp_pos S.hp_pos
  have c2 := mul_pos S.hp_pos S.sp_pos
  have c3 := mul_pos (mul_pos S.hp_pos S.sp_pos) S.tp_pos
  have c4 := mul_pos S.hp_pos S.tp_pos
  have c5 := mul_pos S.hp_pos S.tm_pos
  have c6 := mul_pos S.hp_pos S.hm_pos
  have c7 := mul_pos S.hp_pos S.kp_pos
  have c8 := mul_pos S.hp_pos (sub_pos.2 S.tp_lt)
  have c9 := mul_pos S.hp_pos (sub_pos.2 S.tm_lt)
  have c10 := mul_pos (mul_pos S.hp_pos S.hp_pos) (sub_pos.2 S.tm_lt)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe])
    | (right; refine ⟨by linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe], by linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe]⟩)

theorem C4_rest4 (S : Shape18) (Hpe : S.hp * S.sp = S.kp * S.tp) (Hm : S.km * S.tm < S.hm * S.sm) (hts : S.sp < S.tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨-1, 0, S.hp / 2⟩
        ((quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quint (⟨S.tm, 0, -S.hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, S.sp, S.kp⟩ ⟨S.tp, 0, S.hp⟩ ⟨1, 0, 0⟩ i)) := by
  have a1 := (mul_pos S.kp_pos S.tm_pos)
  have a2 := (mul_pos S.hm_pos S.sp_pos)
  have a3 := (mul_pos S.hm_pos S.tp_pos)
  have a4 := (mul_pos S.hp_pos S.tm_pos)
  have a5 := S.hm_pos
  have a7 := S.kp_pos
  have a8 := (mul_pos S.tm_pos (sub_pos.2 S.roof_p'))
  have a9 := (mul_pos S.hm_pos (sub_pos.2 hts))
  have a11 := (sub_pos.2 S.roof_p')
  have a12 := (mul_pos (sub_pos.2 S.tm_lt) S.hp_pos)
  have a13 := (mul_pos (sub_pos.2 S.tp_lt) S.hm_pos)
  have a14 := S.hp_pos
  have a15 := (mul_pos (sub_pos.2 S.sp_lt) S.hm_pos)
  have a16 := (mul_pos (sub_pos.2 S.tm_lt) S.kp_pos)
  have d1 : S.kp < S.hp := by
    by_contra hh
    push Not at hh
    nlinarith [mul_le_mul_of_nonneg_right hh S.tp_pos.le, mul_pos S.hp_pos (sub_pos.2 hts)]
  have d2 := mul_pos S.tm_pos (sub_pos.2 d1)
  have d3 := mul_pos (sub_pos.2 hts) S.hm_pos
  have d4 := (sub_pos.2 Hm)
  have d5 := (mul_pos S.km_pos S.sp_pos)
  have d6 := (mul_pos S.kp_pos S.sm_pos)
  have d7 := (mul_pos S.sm_pos (sub_pos.2 S.roof_p'))
  have d8 := (mul_pos S.km_pos (sub_pos.2 hts))
  have d9 := (mul_pos (sub_pos.2 S.sm_lt) S.hp_pos)
  have d10 := (mul_pos (sub_pos.2 S.tp_lt) S.km_pos)
  have d11 := (sub_pos.2 S.roof_m')
  have d12 := mul_pos S.hp_pos S.sm_pos
  have d13 := mul_pos S.hp_pos S.km_pos
  have d14 := mul_pos S.hp_pos S.sp_pos
  have d15 := mul_pos (mul_pos S.hp_pos S.sm_pos) S.hp_pos
  have d16 : 0 < (S.tp - S.sp) * (S.km + S.kp) + (S.hp - S.kp) * (S.sm - S.sp) := by
    have h0 : S.sp * ((S.tp - S.sp) * (S.km + S.kp) + (S.hp - S.kp) * (S.sm - S.sp)) =
        (S.tp - S.sp) * (S.km * S.sp + S.kp * S.sm) := by linear_combination (S.sm - S.sp) * Hpe
    by_contra hh
    have h1 := mul_nonpos_of_nonneg_of_nonpos S.sp_pos.le (not_lt.1 hh)
    have h2 := mul_pos (sub_pos.2 hts) (add_pos d5 d6)
    linarith
  have c1 := mul_pos S.hp_pos S.hp_pos
  have c2 := mul_pos S.hp_pos S.sp_pos
  have c3 := mul_pos (mul_pos S.hp_pos S.sp_pos) S.tp_pos
  have c4 := mul_pos S.hp_pos S.tp_pos
  have c5 := mul_pos S.hp_pos S.tm_pos
  have c6 := mul_pos S.hp_pos S.hm_pos
  have c7 := mul_pos S.hp_pos S.kp_pos
  have c8 := mul_pos S.hp_pos (sub_pos.2 S.tp_lt)
  have c9 := mul_pos S.hp_pos (sub_pos.2 S.tm_lt)
  have c10 := mul_pos (mul_pos S.hp_pos S.hp_pos) (sub_pos.2 S.tm_lt)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe])
    | (right; refine ⟨by linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe], by linarith [a1, a2, a3, a4, a5, a7, a8, a9, a11, a12, a13, a14, a15, a16, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, Hpe]⟩)

/-! ### Group 1: Theorem 2, C4 (`a+ = c+`, `c- < a-`) -/

/-- **C4**: tilt `d = (-1, 0, h+/2)`, rim `(m1-, v, m2+, m1+, xa)` (`t31b`'s), depths by `Q5v`. -/
theorem t31_C4 (hα : F.a12 < F.a11) (hp : F.S.ap = F.S.cp) (hm : F.S.cm < F.S.am) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos
  have hle22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have Hpe : F.S.hp * F.S.sp = F.S.kp * F.S.tp := by
    have h := hp
    simp only [Shape18.ap, Shape18.cp] at h
    exact (div_eq_div_iff F.S.tp_pos.ne' F.S.sp_pos.ne').1 h
  have Hm : F.S.km * F.S.tm < F.S.hm * F.S.sm := Shape18.slope_lt F.S.sm_pos F.S.tm_pos hm
  have hts : F.S.sp < F.S.tp := by
    have h1 := mul_lt_mul_of_pos_right F.S.roof_p' F.S.tp_pos
    have e : F.S.kp * F.S.tp * (1 - F.S.tp) = F.S.hp * F.S.sp * (1 - F.S.tp) := by rw [Hpe]
    by_contra hh
    push Not at hh
    nlinarith [mul_nonneg F.S.hp_pos.le (sub_nonneg.2 hh)]
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim5v 6 5 1 0 3 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩
    p6 p5 p1 p0 p3 (-1) (Or.inr rfl) ⟨1, -1, 0⟩
    ⟨-1, 0, F.S.hp / 2⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact C4_cyc F.S Hpe Hm hts
  · intro j' h0 h1 h2 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h3
    · exact absurd rfl h2
    · rw [p2]; exact C4_rest2 F.S Hpe Hm hts i
    · exact absurd rfl h4
    · rw [p4]; exact C4_rest4 F.S Hpe Hm hts i
    · exact absurd rfl h1
    · exact absurd rfl h0
  · set Pq : ZMod 5 → C3 := quint ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-1, 0, F.S.hp / 2⟩ with hww
    have e1 : zz 1 < zz 0 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1]
      nlinarith [mul_pos htm (sub_pos.2 hα)]
    have e3 : zz 2 < zz 3 := by
      simp only [hzz, hPq, GG_eq, quint_2, quint_3]
      nlinarith [mul_nonneg hsp.le (sub_nonneg.2 hle22), mul_pos htp (sub_pos.2 hα)]
    have e4 : zz 3 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 htp1) (sub_pos.2 hα)]
    have e5 : zz 0 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_4]
      nlinarith [mul_pos (sub_pos.2 htm1) (sub_pos.2 hα)]
    exact Q5v_eventually (z := zz) (w := ww) (Or.inl e1) (Or.inl e3) (Or.inl e4) (Or.inl e5)

/-- **C4^Z** (`a- = c-`, `c+ < a+`). -/
theorem t31_C4z (hα : F.a12 < F.a11) (hm : F.S.am = F.S.cm) (hp : F.S.cp < F.S.ap) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.t31_C4 hα hm hp)

/-! ### Group 2 helper lemmas: ST tests of C6 / C5^Z (explicit tilt, ratio variables `r = a+`, `q = a-`) -/

theorem G2_C6_cyc (tp tm sp sm hp hm kp km r q : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hr : 0 < r) (hq : 0 < q)
    (ehp : hp = r * tp) (ehm : hm = q * tm) (ekp : kp = r * sp) (ekm : km = q * sm)
    (roofp : kp * (1 - tp) < hp * (1 - sp)) (roofm : km * (1 - tm) < hm * (1 - sm))
    (hb : q * (1 - tp) < r * tp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨1, -1, 0⟩ ⟨-(r * tp + q * (1 - tp)), 0, 2 * q * r * tp⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  subst ehp ehm ekp ekm
  have hip : 0 < 1 - tp := sub_pos.2 htp1
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hR := sub_pos.2 roofp
  have hB := sub_pos.2 hb
  have hM : 0 < tm - sm := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hq.le (neg_nonneg.2 h), roofm]
  have hT : 0 < tp - sp := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hr.le (neg_nonneg.2 h), hR]
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
    | (left; linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)])
    | (right; refine ⟨by ring, by linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)]⟩)

theorem G2_C6_rest2 (tp tm sp sm hp hm kp km r q : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hr : 0 < r) (hq : 0 < q)
    (ehp : hp = r * tp) (ehm : hm = q * tm) (ekp : kp = r * sp) (ekm : km = q * sm)
    (roofp : kp * (1 - tp) < hp * (1 - sp)) (roofm : km * (1 - tm) < hm * (1 - sm))
    (hb : q * (1 - tp) < r * tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨-(r * tp + q * (1 - tp)), 0, 2 * q * r * tp⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  subst ehp ehm ekp ekm
  have hip : 0 < 1 - tp := sub_pos.2 htp1
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hR := sub_pos.2 roofp
  have hB := sub_pos.2 hb
  have hM : 0 < tm - sm := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hq.le (neg_nonneg.2 h), roofm]
  have hT : 0 < tp - sp := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hr.le (neg_nonneg.2 h), hR]
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · 
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)])
    | (right; refine ⟨by ring, by linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)]⟩)

theorem G2_C6_rest4 (tp tm sp sm hp hm kp km r q : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hr : 0 < r) (hq : 0 < q)
    (ehp : hp = r * tp) (ehm : hm = q * tm) (ekp : kp = r * sp) (ekm : km = q * sm)
    (roofp : kp * (1 - tp) < hp * (1 - sp)) (roofm : km * (1 - tm) < hm * (1 - sm))
    (hb : q * (1 - tp) < r * tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨-(r * tp + q * (1 - tp)), 0, 2 * q * r * tp⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  subst ehp ehm ekp ekm
  have hip : 0 < 1 - tp := sub_pos.2 htp1
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hR := sub_pos.2 roofp
  have hB := sub_pos.2 hb
  have hM : 0 < tm - sm := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hq.le (neg_nonneg.2 h), roofm]
  have hT : 0 < tp - sp := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hr.le (neg_nonneg.2 h), hR]
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · 
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)])
    | (right; refine ⟨by ring, by linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)]⟩)

theorem G2_C5z_cyc (tp tm sp sm hp hm kp km r q e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hr : 0 < r) (hq : 0 < q) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = q * tm) (ekp : kp = (r + e) * sp) (ekm : km = q * sm)
    (roofp : kp * (1 - tp) < hp * (1 - sp)) (roofm : km * (1 - tm) < hm * (1 - sm))
    (hb : q * (1 - tp) < r * tp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨1, -1, 0⟩ ⟨-(r * tp + q * (1 - tp)), 0, 2 * q * r * tp⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ j).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  subst ehp ehm ekp ekm
  have hip : 0 < 1 - tp := sub_pos.2 htp1
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hR := sub_pos.2 roofp
  have hB := sub_pos.2 hb
  have hM : 0 < tm - sm := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hq.le (neg_nonneg.2 h), roofm]
  have hT : 0 < tp - sp := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hr.le (neg_nonneg.2 h), hR, mul_nonneg (mul_nonneg he.le hsp.le) hip.le]
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
    | (left; linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos he htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos he hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos he hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) him), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) hism), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos he hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos he htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)])
    | (right; refine ⟨by ring, by linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos he htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos he hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos he hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) him), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) hism), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos he hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos he htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)]⟩)

theorem G2_C5z_rest2 (tp tm sp sm hp hm kp km r q e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hr : 0 < r) (hq : 0 < q) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = q * tm) (ekp : kp = (r + e) * sp) (ekm : km = q * sm)
    (roofp : kp * (1 - tp) < hp * (1 - sp)) (roofm : km * (1 - tm) < hm * (1 - sm))
    (hb : q * (1 - tp) < r * tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨-(r * tp + q * (1 - tp)), 0, 2 * q * r * tp⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  subst ehp ehm ekp ekm
  have hip : 0 < 1 - tp := sub_pos.2 htp1
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hR := sub_pos.2 roofp
  have hB := sub_pos.2 hb
  have hM : 0 < tm - sm := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hq.le (neg_nonneg.2 h), roofm]
  have hT : 0 < tp - sp := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hr.le (neg_nonneg.2 h), hR, mul_nonneg (mul_nonneg he.le hsp.le) hip.le]
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · 
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos he htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos he hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos he hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) him), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) hism), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos he hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos he htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)])
    | (right; refine ⟨by ring, by linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos he htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos he hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos he hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) him), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) hism), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos he hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos he htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)]⟩)

theorem G2_C5z_rest4 (tp tm sp sm hp hm kp km r q e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hr : 0 < r) (hq : 0 < q) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = q * tm) (ekp : kp = (r + e) * sp) (ekm : km = q * sm)
    (roofp : kp * (1 - tp) < hp * (1 - sp)) (roofm : km * (1 - tm) < hm * (1 - sm))
    (hb : q * (1 - tp) < r * tp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨1, -1, 0⟩ ⟨-(r * tp + q * (1 - tp)), 0, 2 * q * r * tp⟩
        ((quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ (i + 1)).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub
          (quint (⟨tm, 0, -hm⟩ : C3) ⟨0, 0, 0⟩ ⟨0, sp, kp⟩ ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ i)) := by
  subst ehp ehm ekp ekm
  have hip : 0 < 1 - tp := sub_pos.2 htp1
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hR := sub_pos.2 roofp
  have hB := sub_pos.2 hb
  have hM : 0 < tm - sm := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hq.le (neg_nonneg.2 h), roofm]
  have hT : 0 < tp - sp := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hr.le (neg_nonneg.2 h), hR, mul_nonneg (mul_nonneg he.le hsp.le) hip.le]
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · 
    simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos he htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos he hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos he hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) him), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) hism), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos he hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos he htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)])
    | (right; refine ⟨by ring, by linarith [(mul_pos (mul_pos hr htm) hsp), (mul_pos (mul_pos he htm) hsp), (mul_pos (mul_pos hq htm) hsp), (mul_pos (mul_pos hr htp) htm), (mul_pos (mul_pos hq htp) htm), (mul_pos hq htm), (mul_pos hr hsp), (mul_pos he hsp), (mul_pos (mul_pos hr hsp) hsm), (mul_pos (mul_pos he hsp) hsm), (mul_pos (mul_pos hq hsp) hsm), (mul_pos (mul_pos hq htm) hT), (mul_pos htm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) him), hR, (mul_pos (mul_pos hq hsm) hT), (mul_pos hsm hR), (mul_pos (mul_pos (mul_pos he hsp) htp) hism), (mul_pos (mul_pos hr htp) him), (mul_pos (mul_pos hq htm) hip), (mul_pos hr htp), (mul_pos (mul_pos hr htp) hism), (mul_pos (mul_pos hq hsm) hip), (mul_pos (mul_pos hr hsp) him), (mul_pos (mul_pos he hsp) him), (mul_pos (mul_pos hq htm) his), (mul_pos hq hM), (mul_pos (mul_pos he htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hr) htp) htp) hsp), (mul_pos (mul_pos (mul_pos (mul_pos hr hq) htp) htp) hsp), (mul_pos (mul_pos (mul_pos hr hq) htp) hsp), (mul_pos (mul_pos (mul_pos hq htm) hsm) hB), (mul_pos (mul_pos hr htp) hB), (mul_pos (mul_pos (mul_pos hr hq) htp) him), (mul_pos (mul_pos hr hq) htp), (mul_pos (mul_pos (mul_pos hq hq) htm) hip)]⟩)


/-! ### Group 2: Theorem 2, C5 and C6 -/

/-- **C5^Z** (`a- = c-`, `a+ < c+`, `a- < b+`): tilt `Z`-image of `d = (p, 0, -1)`,
`p = ½(-t+/h+ - (1-t-)/h-)`; i.e. here (`t31b`'s rim) the tilt `(p', 0, +1)` with the mirrored `p'`
(derive it; `a- < b+` is exactly the non-emptiness of the interval of `p`). -/
theorem t31_C5z (hα : F.a12 < F.a11) (hm : F.S.am = F.S.cm) (hp : F.S.ap < F.S.cp)
    (hb : F.S.am < F.S.bp) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos
  have hle22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have hb' : F.S.am * (1 - F.S.tp) < F.S.ap * F.S.tp := by
    have h := mul_lt_mul_of_pos_right hb (sub_pos.2 F.S.tp_lt)
    rwa [F.S.bp_mul, ← F.S.ap_mul] at h
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim5v 6 5 1 0 3 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩
    p6 p5 p1 p0 p3 (-1) (Or.inr rfl) ⟨1, -1, 0⟩
    ⟨-(F.S.ap * F.S.tp + F.S.am * (1 - F.S.tp)), 0, 2 * F.S.am * F.S.ap * F.S.tp⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact G2_C5z_cyc F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap F.S.am (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos (sub_pos.2 hp) F.S.ap_mul.symm F.S.am_mul.symm (by rw [add_sub_cancel]; exact F.S.cp_mul.symm) (by rw [hm]; exact F.S.cm_mul.symm) F.S.roof_p' F.S.roof_m' hb'
  · intro j' h0 h1 h2 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h3
    · exact absurd rfl h2
    · rw [p2]; exact G2_C5z_rest2 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap F.S.am (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos (sub_pos.2 hp) F.S.ap_mul.symm F.S.am_mul.symm (by rw [add_sub_cancel]; exact F.S.cp_mul.symm) (by rw [hm]; exact F.S.cm_mul.symm) F.S.roof_p' F.S.roof_m' hb' i
    · exact absurd rfl h4
    · rw [p4]; exact G2_C5z_rest4 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap F.S.am (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos (sub_pos.2 hp) F.S.ap_mul.symm F.S.am_mul.symm (by rw [add_sub_cancel]; exact F.S.cp_mul.symm) (by rw [hm]; exact F.S.cm_mul.symm) F.S.roof_p' F.S.roof_m' hb' i
    · exact absurd rfl h1
    · exact absurd rfl h0
  · set Pq : ZMod 5 → C3 := quint ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-(F.S.ap * F.S.tp + F.S.am * (1 - F.S.tp)), 0, 2 * F.S.am * F.S.ap * F.S.tp⟩ with hww
    have e1 : zz 1 < zz 0 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1]
      nlinarith [mul_pos htm (sub_pos.2 hα)]
    have e3 : zz 2 < zz 3 := by
      simp only [hzz, hPq, GG_eq, quint_2, quint_3]
      nlinarith [mul_nonneg hsp.le (sub_nonneg.2 hle22), mul_pos htp (sub_pos.2 hα)]
    have e4 : zz 3 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 htp1) (sub_pos.2 hα)]
    have e5 : zz 0 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_4]
      nlinarith [mul_pos (sub_pos.2 htm1) (sub_pos.2 hα)]
    exact Q5v_eventually (z := zz) (w := ww) (Or.inl e1) (Or.inl e3) (Or.inl e4) (Or.inl e5)

/-- **C5** (`a+ = c+`, `a- < c-`, `a+ < b-`). -/
theorem t31_C5 (hα : F.a12 < F.a11) (hp : F.S.ap = F.S.cp) (hm : F.S.am < F.S.cm)
    (hb : F.S.ap < F.S.bm) : IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.t31_C5z hα hp hm hb)

/-- **C6** (`a+ = c+`, `a- = c-`, `a- < b+`): tilt `d = (p, 0, 1)`, `p = ½(-(t-)/(h-) - (1-t+)/h+)`. -/
theorem t31_C6 (hα : F.a12 < F.a11) (hp : F.S.ap = F.S.cp) (hm : F.S.am = F.S.cm)
    (hb : F.S.am < F.S.bp) : IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos
  have hle22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have hb' : F.S.am * (1 - F.S.tp) < F.S.ap * F.S.tp := by
    have h := mul_lt_mul_of_pos_right hb (sub_pos.2 F.S.tp_lt)
    rwa [F.S.bp_mul, ← F.S.ap_mul] at h
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim5v 6 5 1 0 3 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩
    p6 p5 p1 p0 p3 (-1) (Or.inr rfl) ⟨1, -1, 0⟩
    ⟨-(F.S.ap * F.S.tp + F.S.am * (1 - F.S.tp)), 0, 2 * F.S.am * F.S.ap * F.S.tp⟩ (Or.inl one_ne_zero) ?_ ?_ ?_
  · exact G2_C6_cyc F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap F.S.am F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos F.S.ap_mul.symm F.S.am_mul.symm (by rw [hp]; exact F.S.cp_mul.symm) (by rw [hm]; exact F.S.cm_mul.symm) F.S.roof_p' F.S.roof_m' hb'
  · intro j' h0 h1 h2 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h3
    · exact absurd rfl h2
    · rw [p2]; exact G2_C6_rest2 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap F.S.am F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos F.S.ap_mul.symm F.S.am_mul.symm (by rw [hp]; exact F.S.cp_mul.symm) (by rw [hm]; exact F.S.cm_mul.symm) F.S.roof_p' F.S.roof_m' hb' i
    · exact absurd rfl h4
    · rw [p4]; exact G2_C6_rest4 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap F.S.am F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.ap_pos F.S.am_pos F.S.ap_mul.symm F.S.am_mul.symm (by rw [hp]; exact F.S.cp_mul.symm) (by rw [hm]; exact F.S.cm_mul.symm) F.S.roof_p' F.S.roof_m' hb' i
    · exact absurd rfl h1
    · exact absurd rfl h0
  · set Pq : ZMod 5 → C3 := quint ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨1, -1, 0⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-(F.S.ap * F.S.tp + F.S.am * (1 - F.S.tp)), 0, 2 * F.S.am * F.S.ap * F.S.tp⟩ with hww
    have e1 : zz 1 < zz 0 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_1]
      nlinarith [mul_pos htm (sub_pos.2 hα)]
    have e3 : zz 2 < zz 3 := by
      simp only [hzz, hPq, GG_eq, quint_2, quint_3]
      nlinarith [mul_nonneg hsp.le (sub_nonneg.2 hle22), mul_pos htp (sub_pos.2 hα)]
    have e4 : zz 3 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_3, quint_4]
      nlinarith [mul_pos (sub_pos.2 htp1) (sub_pos.2 hα)]
    have e5 : zz 0 < zz 4 := by
      simp only [hzz, hPq, GG_eq, quint_0, quint_4]
      nlinarith [mul_pos (sub_pos.2 htm1) (sub_pos.2 hα)]
    exact Q5v_eventually (z := zz) (w := ww) (Or.inl e1) (Or.inl e3) (Or.inl e4) (Or.inl e5)

/-- **C6^Z** (`a+ = c+`, `a- = c-`, `a+ < b-`). -/
theorem t31_C6z (hα : F.a12 < F.a11) (hp : F.S.ap = F.S.cp) (hm : F.S.am = F.S.cm)
    (hb : F.S.ap < F.S.bm) : IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.t31_C6 hα hm hp hb)

/-! ### Group 3: Theorem 3 (parallel edges, merged view) -/

/-- Statement helper for `tB_merged`: the points of the rim and the tilt, in raw reals
(`hp = r tp`, `hm = r (1 - tm)`, `kp = (r + e) sp`). -/
theorem G3_cyc (tp tm sp sm hp hm kp km r e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (hr : 0 < r) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = r * (1 - tm)) (ekp : kp = (r + e) * sp)
    (roofm : km * (1 - tm) < hm * (1 - sm)) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨tp, 0, hp⟩ ⟨-(2 * r + e), 2 * r, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  subst ehp ehm ekp
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hK : 0 < r * (1 - sm) - km := by
    have := mul_lt_mul_of_pos_left (show km < r * (1 - sm) from ?_) him
    · nlinarith
    · by_contra h; push Not at h; nlinarith [mul_nonneg him.le (sub_nonneg.2 h)]
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
    | (left; linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)])
    | (right; refine ⟨by ring, by linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)]⟩)

theorem G3_rest2 (tp tm sp sm hp hm kp km r e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (hr : 0 < r) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = r * (1 - tm)) (ekp : kp = (r + e) * sp)
    (roofm : km * (1 - tm) < hm * (1 - sm)) :
    ∀ i : ZMod 4,
      ST 1 ⟨tp, 0, hp⟩ ⟨-(2 * r + e), 2 * r, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  subst ehp ehm ekp
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hK : 0 < r * (1 - sm) - km := by
    have := mul_lt_mul_of_pos_left (show km < r * (1 - sm) from ?_) him
    · nlinarith
    · by_contra h; push Not at h; nlinarith [mul_nonneg him.le (sub_nonneg.2 h)]
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)])
    | (right; refine ⟨by ring, by linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)]⟩)

theorem G3_rest5 (tp tm sp sm hp hm kp km r e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (hr : 0 < r) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = r * (1 - tm)) (ekp : kp = (r + e) * sp)
    (roofm : km * (1 - tm) < hm * (1 - sm)) :
    ∀ i : ZMod 4,
      ST 1 ⟨tp, 0, hp⟩ ⟨-(2 * r + e), 2 * r, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  subst ehp ehm ekp
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hK : 0 < r * (1 - sm) - km := by
    have := mul_lt_mul_of_pos_left (show km < r * (1 - sm) from ?_) him
    · nlinarith
    · by_contra h; push Not at h; nlinarith [mul_nonneg him.le (sub_nonneg.2 h)]
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)])
    | (right; refine ⟨by ring, by linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)]⟩)

theorem G3_rest6 (tp tm sp sm hp hm kp km r e : ℝ)
    (htp : 0 < tp) (htp1 : tp < 1) (htm : 0 < tm) (htm1 : tm < 1) (hsp : 0 < sp) (hsp1 : sp < 1)
    (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (hr : 0 < r) (he : 0 < e)
    (ehp : hp = r * tp) (ehm : hm = r * (1 - tm)) (ekp : kp = (r + e) * sp)
    (roofm : km * (1 - tm) < hm * (1 - sm)) :
    ∀ i : ZMod 4,
      ST 1 ⟨tp, 0, hp⟩ ⟨-(2 * r + e), 2 * r, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨tm, 0, -hm⟩ : C3).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  subst ehp ehm ekp
  have him : 0 < 1 - tm := sub_pos.2 htm1
  have his : 0 < 1 - sp := sub_pos.2 hsp1
  have hism : 0 < 1 - sm := sub_pos.2 hsm1
  have hK : 0 < r * (1 - sm) - km := by
    have := mul_lt_mul_of_pos_left (show km < r * (1 - sm) from ?_) him
    · nlinarith
    · by_contra h; push Not at h; nlinarith [mul_nonneg him.le (sub_nonneg.2 h)]
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [CaseC09.ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)])
    | (right; refine ⟨by ring, by linarith [(mul_pos htp hr), (mul_pos (mul_pos htp hsp) hr), (mul_pos (mul_pos htp hsp) he), (mul_pos (mul_pos htp hsm) hr), (mul_pos htp hK), (mul_pos (mul_pos (mul_pos htp hsp) hr) hism), (mul_pos (mul_pos (mul_pos htp hsp) he) hism), (mul_pos (mul_pos htp hkm) his), (mul_pos (mul_pos (mul_pos htp hsp) hsm) hr), (mul_pos (mul_pos (mul_pos htp hsp) hsm) he), (mul_pos (mul_pos htp hsp) hkm), (mul_pos (mul_pos htp hr) hr), (mul_pos (mul_pos hr hr) him), (mul_pos (mul_pos hr he) him), (mul_pos (mul_pos (mul_pos htp hsp) hr) he), (mul_pos (mul_pos htp hsm) (mul_pos hr hr)), (mul_pos (mul_pos htp hsm) (mul_pos hr he)), (mul_pos (mul_pos htp hr) hkm), (mul_pos hr hkm), (mul_pos (mul_pos htp hr) he), (mul_pos htp (mul_pos hr hr)), (mul_pos (mul_pos htp hr) hr), (mul_pos hr hr), (mul_pos htm hr), (mul_pos (mul_pos htm hsp) (mul_pos hr he)), (mul_pos (mul_pos htm hr) he)]⟩)

/-- **Theorem 3, `Z`-image form** (`a+ = b-`, `a+ < c+`): view `u = m1+ = (t+, 0, h+)` (that of `tB`),
rim `(m1+, xa, xb, m2+)`, tilt `(-(h+ + t+ c+)/(2h+), 1, 0)` (scaled: `(-(2 a+ + e), 2 a+, 0)`,
`e = c+ - a+`); depths: `z(xb) < z(xa)` from `A12 < A11` and the roof identity, exactly as in `tB`
(no `B2`, `B3`).  The ST tests are `G3_cyc`, `G3_rest2/5/6`. -/
theorem tB_merged (hα : F.a12 < F.a11) (hab : F.S.ap = F.S.bm) (hc : F.S.ap < F.S.cp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have hgg : 0 < F.gg := F.g_pos
  have roof := F.S.roof_p'
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have ehm : F.S.hm = F.S.ap * (1 - F.S.tm) := by rw [hab]; exact F.S.bm_mul.symm
  have ekp : F.S.kp = (F.S.ap + (F.S.cp - F.S.ap)) * F.S.sp := by
    rw [add_sub_cancel]; exact F.S.cp_mul.symm
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim4 0 3 4 1 ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p3 p4 p1 1 (Or.inl rfl) ⟨F.S.tp, 0, F.S.hp⟩
    ⟨-(2 * F.S.ap + (F.S.cp - F.S.ap)), 2 * F.S.ap, 0⟩ (Or.inl htp.ne') ?_ ?_ ?_
  · exact G3_cyc F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.km_pos F.S.ap_pos (sub_pos.2 hc) F.S.ap_mul.symm ehm ekp F.S.roof_m'
  · intro j' h0 h1 h2 h3 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h3
    · rw [p2]; exact G3_rest2 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.km_pos F.S.ap_pos (sub_pos.2 hc) F.S.ap_mul.symm ehm ekp F.S.roof_m' i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rw [p5]; exact G3_rest5 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.km_pos F.S.ap_pos (sub_pos.2 hc) F.S.ap_mul.symm ehm ekp F.S.roof_m' i
    · rw [p6]; exact G3_rest6 F.S.tp F.S.tm F.S.sp F.S.sm F.S.hp F.S.hm F.S.kp F.S.km F.S.ap (F.S.cp - F.S.ap) F.S.tp_pos F.S.tp_lt F.S.tm_pos F.S.tm_lt F.S.sp_pos F.S.sp_lt F.S.sm_pos F.S.sm_lt F.S.km_pos F.S.ap_pos (sub_pos.2 hc) F.S.ap_mul.symm ehm ekp F.S.roof_m' i
  · set Pq : ZMod 4 → C3 := quad ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tp, 0, F.S.hp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-(2 * F.S.ap + (F.S.cp - F.S.ap)), 2 * F.S.ap, 0⟩ with hww
    refine Q4_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      (B_lex (z := zz) (w := ww) (p := F.S.tp * F.S.kp) (q := F.S.hp * (1 - F.S.sp)) (r := F.S.hp * F.S.sp)
        (mul_pos htp hkp) (mul_pos hhp (by linarith)) (mul_pos hhp hsp) ?_)
    · simp only [hzz, hPq, GG_eq, quad_1, quad_2]
      nlinarith [mul_pos htp (sub_pos.2 hα)]
    · simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos (sub_pos.2 roof) (add_pos (mul_pos (mul_pos htp htp) hA11) (mul_pos (mul_pos hhp hhp) hgg))]

/-- **Theorem 3** (`a- = b+`, `a- < c-`): the `Z`-image. -/
theorem tBz_merged (hα : F.a12 < F.a11) (hab : F.S.am = F.S.bp) (hc : F.S.am < F.S.cm) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.tB_merged hα hab hc)

/-! ### Group 4: Theorem 4 (`A12 = A11`) -/

/-- At `A12 = A11`, `g12 = A11 (1 - t+)^2 + g h+^2 > 0`. -/
theorem g12_pos_of_eq (heq : F.a12 = F.a11) : 0 < F.g12 := by
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hgg : 0 < F.gg := F.g_pos
  have h1 := F.S.tp_lt; have h2 := F.S.hp_pos
  unfold g12
  rw [heq]
  nlinarith [mul_pos hA11 (mul_pos (sub_pos.2 h1) (sub_pos.2 h1)), mul_pos hgg (mul_pos h2 h2)]

/-- `g12` of the `Z`-image at `A12 = A11`. -/
theorem zFrame_g12_pos_of_eq (heq : F.a12 = F.a11) : 0 < F.zFrame.g12 :=
  F.zFrame.g12_pos_of_eq heq

/-- `tA1` at `A12 = A11`, `a- < b+`. -/
theorem tA1_of_eq (heq : F.a12 = F.a11) (h : F.S.am < F.S.bp) :
    IsRupert (Finset.univ.image x) :=
  F.tA1 (F.A1_of h) (F.g12_pos_of_eq heq)

/-- `tA1^Z` at `A12 = A11`, `a+ < b-`. -/
theorem tA1z_of_eq (heq : F.a12 = F.a11) (h : F.S.ap < F.S.bm) :
    IsRupert (Finset.univ.image x) :=
  rupert_of_z (F.zFrame.tA1 (F.zFrame.A1_of h) (F.zFrame_g12_pos_of_eq heq))

/-- `t31a` at `A12 = A11` (`c+ < a+`, `c- < a-`): all four depths are 0; `Q4_eventually` with the
tie alternatives from `w` (tilt `(t- + t+ - 2, 0, h+ - h-)`, `w(v) = 0`, `w(xa) = A11 d1`,
`hm w(m1+) + hp w(m1-) = A11 d1 (hm tp + hp tm) < 0`, ...). -/
theorem t31a_eq (heq : F.a12 = F.a11) (hp : F.S.cp < F.S.ap) (hm : F.S.cm < F.S.am) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have Hp : F.S.kp * F.S.tp < F.S.hp * F.S.sp := Shape18.slope_lt hsp htp hp
  have Hm : F.S.km * F.S.tm < F.S.hm * F.S.sm := Shape18.slope_lt hsm htm hm
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
    have z01 : zz 0 = zz 1 := by
      simp only [hzz, hPq, GG_eq, quad_0, quad_1, heq]; ring
    have z03 : zz 0 = zz 3 := by
      simp only [hzz, hPq, GG_eq, quad_0, quad_3, heq]; ring
    have z21 : zz 2 = zz 1 := by
      simp only [hzz, hPq, GG_eq, quad_2, quad_1, heq]; ring
    have z23 : zz 2 = zz 3 := by
      simp only [hzz, hPq, GG_eq, quad_2, quad_3, heq]; ring
    have hd1 : F.S.tm + F.S.tp - 2 < 0 := by linarith
    have hA : ww 2 < ww 1 ∨ ww 2 < ww 3 := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2⟩ := hc
      simp only [hww, hPq, GG_eq, quad_1, quad_2, quad_3, heq] at c1 c2
      nlinarith [mul_nonneg hhm.le (sub_nonneg.2 c1), mul_nonneg hhp.le (sub_nonneg.2 c2),
        mul_pos hA11 (mul_pos (neg_pos.2 hd1) (add_pos (mul_pos hhm (sub_pos.2 htp1)) (mul_pos hhp (sub_pos.2 htm1))))]
    have hB : ww 1 < ww 0 ∨ ww 3 < ww 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2⟩ := hc
      simp only [hww, hPq, GG_eq, quad_0, quad_1, quad_3, heq] at c1 c2
      nlinarith [mul_nonneg hhm.le (sub_nonneg.2 c1), mul_nonneg hhp.le (sub_nonneg.2 c2),
        mul_pos hA11 (mul_pos (neg_pos.2 hd1) (add_pos (mul_pos hhm htp) (mul_pos hhp htm)))]
    refine Q4_eventually (z := zz) (w := ww) ?_ ?_
    · rcases hA with h | h
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨z21, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨z23, h⟩)))
    · rcases hB with h | h
      · exact Or.inl (Or.inr ⟨z01.symm, h⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨z03.symm, h⟩))

/-- **Theorem 4**: on `A12 = A11`, outside `R1'`, `K` is Rupert. -/
theorem rupert_of_a12_eq_a11 (heq : F.a12 = F.a11)
    (h : F.S.am < F.S.bp ∨ F.S.ap < F.S.bm ∨ (F.S.cp < F.S.ap ∧ F.S.cm < F.S.am)) :
    IsRupert (Finset.univ.image x) := by
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hsm := F.S.sm_pos; have hsp := F.S.sp_pos
  rcases h with h | h | ⟨h1, h2⟩
  · exact F.tA1_of_eq heq h
  · exact F.tA1z_of_eq heq h
  · exact F.t31a_eq heq h1 h2

/-! ### Group 5: the new chain and the new special set -/

/-- `rupert_or_V` after section 35: no `hβ`, `a12 < a11` only; the equalities `a∓ = b±`, `a± = c±`
survive only as the two corners; in the V case the result also records `a+ < c+`, `a- < c-`.
Proof (case tree): `cm < am ∨ cp < ap` -> `t31a`/`t31b_le`/`t31c_le`/`t31_C4`/`t31_C4z`; then
`tBz`/`tB` (`bp < am`, `bm < ap`); then `am = bp` -> `tBz_merged` (`am < cm` by `c1`), `ap = bm` ->
`tB_merged` (by `c2`); then `ap = cp` -> `t31_C5` (`am < cm`) / `t31_C6` (`am = cm`); `am = cm` ->
`t31_C5z`; then the V test, then `famA`/`famAz`/`rupert_of_F2_view` as in `rupert_or_V`. -/
theorem rupert_or_V' (hx : Function.Injective x) (hα : F.a12 < F.a11)
    (c1 : ¬ (F.S.am = F.S.bp ∧ F.S.am = F.S.cm)) (c2 : ¬ (F.S.ap = F.S.bm ∧ F.S.ap = F.S.cp)) :
    IsRupert (Finset.univ.image x) ∨
      (F.S.am < F.S.bp ∧ F.S.ap < F.S.bm ∧ F.S.ap < F.S.cp ∧ F.S.am < F.S.cm ∧
        (F.S.dp ≤ F.S.A1 * F.S.tp ∨ F.S.dm ≤ F.S.A1 * F.S.tm)) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt
  have o_tp : 0 < 1 - F.S.tp := sub_pos.2 htp1
  have o_tm : 0 < 1 - F.S.tm := sub_pos.2 htm1
  have o_sp : 0 < 1 - F.S.sp := sub_pos.2 hsp1
  have o_sm : 0 < 1 - F.S.sm := sub_pos.2 hsm1
  -- step 1: the 27.31 tests
  by_cases hc : F.S.ap ≤ F.S.cp ∧ F.S.am ≤ F.S.cm
  swap
  · left
    rcases not_and_or.1 hc with h | h
    · have h' : F.S.cp < F.S.ap := not_le.1 h
      rcases lt_trichotomy F.S.am F.S.cm with h'' | h'' | h''
      · exact F.t31c_le hα (Shape18.slope_lt htm hsm h'') (Shape18.slope_lt hsp htp h')
      · exact F.t31_C4z hα h'' h'
      · exact F.t31a hα (Shape18.slope_lt hsp htp h') (Shape18.slope_lt hsm htm h'')
    · have h3 : F.S.cm < F.S.am := not_le.1 h
      rcases lt_trichotomy F.S.ap F.S.cp with h'' | h'' | h''
      · exact F.t31b_le hα (Shape18.slope_lt htp hsp h'') (Shape18.slope_lt hsm htm h3)
      · exact F.t31_C4 hα h'' h3
      · exact F.t31a hα (Shape18.slope_lt hsp htp h'') (Shape18.slope_lt hsm htm h3)
  obtain ⟨hcp0, hcm0⟩ := hc
  -- step 2: the edge crossings
  by_cases h1 : F.S.bp < F.S.am
  · left
    have h1d : F.S.dp < F.S.am := lt_trans F.S.dp_lt_bp h1
    exact F.tBz hα (Shape18.slope_lt o_tp htm h1) (Shape18.slope_lt o_sp htm h1d)
  by_cases h2 : F.S.bm < F.S.ap
  · left
    have h2d : F.S.dm < F.S.ap := lt_trans F.S.dm_lt_bm h2
    exact F.tB hα (Shape18.slope_lt o_tm htp h2) (Shape18.slope_lt o_sm htp h2d)
  have h1' := not_lt.1 h1
  have h2' := not_lt.1 h2
  -- step 3: the merged views
  rcases h1'.lt_or_eq with h1' | h1e
  swap
  · left
    exact F.tBz_merged hα h1e (lt_of_le_of_ne hcm0 (fun e => c1 ⟨h1e, e⟩))
  rcases h2'.lt_or_eq with h2' | h2e
  swap
  · left
    exact F.tB_merged hα h2e (lt_of_le_of_ne hcp0 (fun e => c2 ⟨h2e, e⟩))
  -- step 4: the corners
  rcases hcp0.lt_or_eq with hcp | hcpe
  swap
  · left
    rcases hcm0.lt_or_eq with hcm | hcme
    · exact F.t31_C5 hα hcpe hcm h2'
    · exact F.t31_C6 hα hcpe hcme h1'
  rcases hcm0.lt_or_eq with hcm | hcme
  swap
  · left
    exact F.t31_C5z hα hcme hcp h1'
  -- step 5: the V test and the remaining families
  by_cases hd : F.S.dp ≤ F.S.A1 * F.S.tp ∨ F.S.dm ≤ F.S.A1 * F.S.tm
  · exact Or.inr ⟨h1', h2', hcp, hcm, hd⟩
  left
  push Not at hd
  obtain ⟨hVp, hVm⟩ := hd
  have hst : F.S.sm < F.S.tm := F.S.swap.sp_lt_tp (Shape18.slope_lt htm hsm hcm)
  have hst' : F.S.sp < F.S.tp := F.S.sp_lt_tp (Shape18.slope_lt htp hsp hcp)
  by_cases hfA : F.S.km * F.S.tm < F.S.sm * (F.S.hp * F.S.tm + F.S.tp * F.S.hm) ∧
      F.S.km * (1 - F.S.tm) < F.S.hp * F.S.sm * (1 - F.S.tm) + F.S.hm * (1 - F.S.tp * F.S.sm)
  · exact F.famA (F.A1_of h1') hfA.1 hfA.2
  by_cases hfZ : F.S.kp * F.S.tp < F.S.sp * (F.S.hm * F.S.tp + F.S.tm * F.S.hp) ∧
      F.S.kp * (1 - F.S.tp) < F.S.hm * F.S.sp * (1 - F.S.tp) + F.S.hp * (1 - F.S.tm * F.S.sp)
  · exact F.famAz (F.zFrame.A1_of h2') hfZ.1 hfZ.2
  have hCm := F.S.cm_ge hst hfA
  have hCp := F.S.swap.cm_ge hst' hfZ
  obtain ⟨α, γ, k1, k2, k3⟩ := F.S.exists_view_F2 hVp hVm hCm hCp
  exact F.rupert_of_F2_view hx α γ k1 k2 k3

end Frame18

/-- **The special positions of type 18 after section 35**. -/
def CaseC18Special' (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame18 x,
    (F.a12 = F.a11 ∧ F.S.bp ≤ F.S.am ∧ F.S.bm ≤ F.S.ap ∧ ¬ (F.S.cp < F.S.ap ∧ F.S.cm < F.S.am))
    ∨ (F.S.am = F.S.bp ∧ F.S.am = F.S.cm) ∨ (F.S.ap = F.S.bm ∧ F.S.ap = F.S.cp)
    ∨ ((F.S.dp = F.S.A1 * F.S.tp ∨ F.S.dm = F.S.A1 * F.S.tm ∨ F.S.D2p = 0) ∧
        F.S.ap < F.S.cp ∧ F.S.am < F.S.cm)

/-- **Off the special positions of type 18, a frame is Rupert.**  `A12 = A11` is Theorem 4
(`rupert_of_a12_eq_a11`); otherwise `rupert_or_V'`, then the V-side calls
(`Vside_classH_any`/`Vside_slide`, and `zFrame` for `V^Z`) with `nVp`, `nVm`, `nD` from the last
disjunct and `ap < cp`, `am < cm`. -/
theorem Frame18.isRupert_of_not_special' {x : Fin 7 → ℝ³} (F : Frame18 x)
    (hx : Function.Injective x) (h : ¬ CaseC18Special' x) :
    IsRupert (Finset.univ.image x) := by
  have nR : ¬ (F.a12 = F.a11 ∧ F.S.bp ≤ F.S.am ∧ F.S.bm ≤ F.S.ap ∧
        ¬ (F.S.cp < F.S.ap ∧ F.S.cm < F.S.am)) := fun h' => h ⟨F, Or.inl h'⟩
  have c1 : ¬ (F.S.am = F.S.bp ∧ F.S.am = F.S.cm) := fun h' => h ⟨F, Or.inr (Or.inl h')⟩
  have c2 : ¬ (F.S.ap = F.S.bm ∧ F.S.ap = F.S.cp) :=
    fun h' => h ⟨F, Or.inr (Or.inr (Or.inl h'))⟩
  have nV : ¬ ((F.S.dp = F.S.A1 * F.S.tp ∨ F.S.dm = F.S.A1 * F.S.tm ∨ F.S.D2p = 0) ∧
        F.S.ap < F.S.cp ∧ F.S.am < F.S.cm) := fun h' => h ⟨F, Or.inr (Or.inr (Or.inr h'))⟩
  by_cases heq : F.a12 = F.a11
  · apply F.rupert_of_a12_eq_a11 heq
    by_contra hn
    push Not at hn
    obtain ⟨n1, n2, n3⟩ := hn
    exact nR ⟨heq, n1, n2, fun hh => absurd (n3 hh.1) (not_le.2 hh.2)⟩
  have hα : F.a12 < F.a11 := lt_of_le_of_ne F.A12_le_A11 heq
  rcases F.rupert_or_V' hx hα c1 c2 with h | ⟨h1, h2, hcp, hcm, hV⟩
  · exact h
  have nVp : F.S.dp ≠ F.S.A1 * F.S.tp := fun e => nV ⟨Or.inl e, hcp, hcm⟩
  have nVm : F.S.dm ≠ F.S.A1 * F.S.tm := fun e => nV ⟨Or.inr (Or.inl e), hcp, hcm⟩
  have nD : F.S.D2p ≠ 0 := fun e => nV ⟨Or.inr (Or.inr e), hcp, hcm⟩
  rcases hV with hV | hV
  · by_cases hH : F.ClassH
    · exact F.Vside_classH_any hx (lt_of_le_of_ne hV nVp) h1 h2 nD hH
    · exact F.Vside_slide hx (lt_of_le_of_ne hV nVp) h1 h2 nD hH
  · apply rupert_of_z
    have hxz : Function.Injective (x ∘ zperm) := hx.comp zperm_bijective.1
    have hdp : F.zFrame.S.dp < F.zFrame.S.A1 * F.zFrame.S.tp := by
      have : F.zFrame.S.dp = F.S.dm := rfl
      have hA : F.zFrame.S.A1 = F.S.A1 := by
        show F.S.am + F.S.ap = F.S.ap + F.S.am
        ring
      show F.S.dm < F.zFrame.S.A1 * F.S.tm
      rw [hA]
      exact lt_of_le_of_ne hV nVm
    have hD : F.zFrame.S.D2p ≠ 0 := by
      intro h0
      apply nD
      have e : F.zFrame.S = F.S.swap := rfl
      rw [e] at h0
      simp only [Shape18.D2p, Shape18.swap] at h0 ⊢
      linarith
    by_cases hH : F.ClassH
    · exact F.zFrame.Vside_classH_any hxz hdp h2 h1 hD ((F.classH_zFrame_iff).2 hH)
    · exact F.zFrame.Vside_slide hxz hdp h2 h1 hD (fun hz => hH ((F.classH_zFrame_iff).1 hz))

end Minimality.CaseC18

end
