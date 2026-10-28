module

public import Minimality.CaseC09Cross

@[expose] public section

/-!
# Type 09, acute case (c): Theorem 27.48 in the frame (`FEWER-FACES-PROOFS.md` §27, continued (4))

The pair `P09 = (T1, T2)`:

* `T1 = 0134/046-0`, the edge crossing at `v m1-`, apex `m1-`, view `u = m1- - v`; the rim is the
  5-cycle `(m1-, xa, m2+, xb, m2-)`, the tilt `+e₂` (frame coordinates), `σ = -1`.  Unimodal
  when `g h- k- > A12 t- (1 - s-)`.
* `T2 = 0256/046-6`, the edge crossing at `v m2-`, apex `v`, view `u = m2- - v`; the rim is the
  4-cycle `(v, m1-, xa, m2+)`, the tilt `-e₁`, `σ = -1`.  Unimodal when
  `g h- k- < A12 s- (1 - t-)`.

Under `t- < s-` the two conditions cover everything (`t48_contra`, i.e. the two failure
inequalities sum to `A12 (t- - s-) ≥ 0`), so one of the tests is unimodal:
`Frame09.rupert_of_27_48`.  Then `Frame09.isRupert_caseC` combines this with
`rupert_or_27_48'`.  The special positions (`CaseC09Special`, `isRupert_of_not_special`) and the
sector tests that remove most of them (§34.4.2) are in `Minimality/CaseC09Special.lean` and `CaseC09TS.lean`.
-/

namespace Minimality.CaseC09

open Finset Filter
open scoped RealInnerProductSpace Topology

/-! ### The rim cycles -/

/-- `T1`'s rim `(m1-, xa, m2+, xb, m2-)`. -/
def t1P (tm hm sp kp sm km : ℝ) : ZMod 5 → C3 :=
  quint (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩

/-- `T2`'s rim `(v, m1-, xa, m2+)`. -/
def t2P (tm hm sp kp : ℝ) : ZMod 4 → C3 :=
  quad (⟨0, 0, 0⟩ : C3) ⟨tm, 0, -hm⟩ ⟨1, 0, 0⟩ ⟨0, sp, kp⟩

section T48
variable {tp hp tm hm sp kp sm km : ℝ}

theorem t1_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (H2 : hm * (1 - sp) < tm * kp) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((t1P tm hm sp kp sm km j).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have q2 := sub_pos.2 H2
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos htm hkm
  have a5 := mul_pos (mul_pos htm hsp) hkm
  have a6 := mul_pos (mul_pos htm hsm) hkp
  have a7 := mul_pos hsm' hkp
  have a8 := mul_pos hsp' hkm
  have a9 := mul_pos htm (add_pos a7 a8)
  have a10 := mul_pos hsp (add_pos (mul_pos hsm' hhm) a4)
  have a11 := mul_pos hsm q2
  have a12 := mul_pos hsm' hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t1_rest0 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) :
    ∀ i : ZMod 5,
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((⟨0, 0, 0⟩ : C3).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos htm hkm
  have a5 := mul_pos (mul_pos htm hsp) hkm
  have a6 := mul_pos (mul_pos htm hsm) hkp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t1_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (H1 : hp * tm + hm * tp < hm) (H2 : hm * (1 - sp) < tm * kp) :
    ∀ i : ZMod 5,
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((t1P tm hm sp kp sm km (i + 1)).sub (t1P tm hm sp kp sm km i))
        ((⟨tp, 0, hp⟩ : C3).sub (t1P tm hm sp kp sm km i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have q1 := sub_pos.2 H1
  have q2 := sub_pos.2 H2
  have a1 := mul_pos hsp hhm
  have a2 := mul_pos htm hkp
  have a4 := mul_pos htm hkm
  have a9 := mul_pos hsp q1
  have a10 := mul_pos hsp' q1
  have a11 := mul_pos hsp' hhm
  have a12 := mul_pos htp hhm
  have a13 := mul_pos htm hhp
  have a14 := mul_pos hsm' (mul_pos htp hhm)
  have a15 := mul_pos hsm' (mul_pos htm hhp)
  have a16 := mul_pos hsm (mul_pos htp hhm)
  have a17 := mul_pos hsm (mul_pos htm hhp)
  have a18 := mul_pos hsm hhm
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t1P, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
      quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t2_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨0, sm, -km⟩ ⟨-1, 0, 0⟩
        ((t2P tm hm sp kp (i + 1)).sub (t2P tm hm sp kp i))
        ((t2P tm hm sp kp j).sub (t2P tm hm sp kp i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hhm
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm hkp
  have a4 := mul_pos htm (add_pos a2 a3)
  have a5 := mul_pos htm' (add_pos a2 a3)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, t2P, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t2_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1)
    (hkm : 0 < km) (H3 : sm * hp < (km * sp + sm * kp) * (1 - tp)) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sm, -km⟩ ⟨-1, 0, 0⟩
        ((t2P tm hm sp kp (i + 1)).sub (t2P tm hm sp kp i))
        ((⟨tp, 0, hp⟩ : C3).sub (t2P tm hm sp kp i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have q3 := sub_pos.2 H3
  have a1 := mul_pos hsm (mul_pos htp hhm)
  have a2 := mul_pos hsm (mul_pos htm hhp)
  have a3 := mul_pos hsm (mul_pos htp' hhm)
  have a4 := mul_pos hsm (mul_pos htm' hhp)
  have a5 := mul_pos hsm hhp
  have a6 := mul_pos hsm hhm
  have a7 := mul_pos hsp hkm
  have a8 := mul_pos hsm hkp
  have a9 := mul_pos htp (add_pos a7 a8)
  have a10 := mul_pos htp' (add_pos a7 a8)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t2P, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t2_rest5 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (H4 : (1 - sp) * km < sm * kp) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sm, -km⟩ ⟨-1, 0, 0⟩
        ((t2P tm hm sp kp (i + 1)).sub (t2P tm hm sp kp i))
        ((⟨0, 1, 0⟩ : C3).sub (t2P tm hm sp kp i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have q4 := sub_pos.2 H4
  have a1 := mul_pos hsm hhm
  have a2 := mul_pos htm hkm
  have a3 := mul_pos htm' hkm
  have a4 := mul_pos hsp hkm
  have a5 := mul_pos hsm hkp
  have a6 := mul_pos htm (add_pos a4 a5)
  have a7 := mul_pos htm' (add_pos a4 a5)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t2P, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

theorem t2_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) :
    ∀ i : ZMod 4,
      ST (-1) ⟨0, sm, -km⟩ ⟨-1, 0, 0⟩
        ((t2P tm hm sp kp (i + 1)).sub (t2P tm hm sp kp i))
        ((⟨0, sm, -km⟩ : C3).sub (t2P tm hm sp kp i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hhm
  have a2 := mul_pos hsp hkm
  have a3 := mul_pos hsm hkp
  have a4 := mul_pos htm (add_pos a2 a3)
  have a5 := mul_pos htm' (add_pos a2 a3)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, t2P, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring, by nlinarith⟩)

end T48

/-! ### The 5-cycle depth condition of `T1` -/

/-- The depth condition of `T1`'s rim: the valley `z 2` below both neighbours, and the chain
`z 3 < z 4 < z 0` (so the top is `z 0` or `z 1`). -/
def Q5t (z : ZMod 5 → ℝ) : Prop :=
  z 2 < z 1 ∧ z 2 < z 3 ∧ z 3 < z 4 ∧ z 4 < z 0

theorem Q5t_open : IsOpen {z : ZMod 5 → ℝ | Q5t z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q5t, Set.ofPred_and]
  exact (hlt 2 1).inter ((hlt 2 3).inter ((hlt 3 4).inter (hlt 4 0)))

theorem Q5t_smul {z : ZMod 5 → ℝ} {a : ℝ} (ha : 0 < a) (h : Q5t z) : Q5t fun i => a * z i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 ha,
    mul_lt_mul_of_pos_left h3 ha, mul_lt_mul_of_pos_left h4 ha⟩

theorem Q5t_shift {z : ZMod 5 → ℝ} (a : ℝ) (h : Q5t z) : Q5t fun i => z i + a := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem Q5t_unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5t z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  by_cases h5 : z 1 < z 0
  · refine isCyclicUnimodal_of_top (by norm_num) hinj 0 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hi
    · left; rw [b1]; exact h5
    · left; rw [b2]; exact h1
    · right; rw [a3]; exact h3
    · right; rw [a4]; exact h4
  · have h6 : z 0 < z 1 := lt_of_le_of_ne (not_lt.mp h5) (fun e => by
      have := hinj e; revert this; decide)
    refine isCyclicUnimodal_of_top (by norm_num) hinj 1 ?_
    intro i hi
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    · right; rw [a0]; exact h6
    · exact absurd rfl hi
    · left; rw [b2]; exact h1
    · right; rw [a3]; exact h3
    · right; rw [a4]; exact h4

theorem Q5t_eventually {z w : ZMod 5 → ℝ} (h1 : z 2 < z 1) (h2 : z 2 < z 3) (h3 : z 3 < z 4)
    (h4 : z 4 < z 0) : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5t fun i => z i + s * w i := by
  filter_upwards [ev_lt (a' := w 2) (b' := w 1) (Or.inl h1), ev_lt (a' := w 2) (b' := w 3) (Or.inl h2),
    ev_lt (a' := w 3) (b' := w 4) (Or.inl h3), ev_lt (a' := w 4) (b' := w 0) (Or.inl h4)]
    with s a b c d
  exact ⟨a, b, c, d⟩

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The bridge for the five-corner rim of `T1`. -/
theorem rupert_rim5t (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 → ∀ i : ZMod 5,
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((F.ptC j').sub (quint P0 P1 P2 P3 P4 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5t fun i => F.GG (quint P0 P1 P2 P3 P4 i) u +
      s * F.GG (quint P0 P1 P2 P3 P4 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quint c0 c1 c2 c3 c4 i) = quint P0 P1 P2 P3 P4 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, e0, e1, e2, e3, e4]
  refine F.rupert_rim (k := 5) (by norm_num) (quint c0 c1 c2 c3 c4) σ hσ u v hu ?_ ?_ Q5t
    Q5t_open (fun z a ha => Q5t_smul ha) (fun z a => Q5t_shift a) ?_
    (fun z hz hq => Q5t_unimodal hz hq)
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

end Frame09

/-- `T1`: the last depth comparison.  If `g h- k- > A12 t- (1 - s-)`, `A12 ≤ A11`,
`t- < s-` and `k-(1 - t-) = (1 - s-)h-`, then `D(m2-) < D(m1-)`. -/
theorem t1_z4_lt_z0 {A11 A12 g tm sm hm km : ℝ} (hA : 0 < A12) (hA11 : A12 ≤ A11)
    (htm : 0 < tm) (htm1 : tm < 1) (hsm1 : sm < 1) (hts : tm < sm) (hhm : 0 < hm)
    (hrel : km * (1 - tm) = (1 - sm) * hm) (hS : A12 * tm * (1 - sm) < g * hm * km) :
    A12 * tm * sm + g * hm * km < A11 * tm * tm + g * hm * hm := by
  have h1 : 0 < 1 - tm := by linarith
  have h2 : 0 < 1 - sm := by linarith
  have key : A12 * tm * (1 - tm) < g * hm * hm := by
    have e : g * hm * km * (1 - tm) = (g * hm * hm) * (1 - sm) := by
      linear_combination (g * hm) * hrel
    have : A12 * tm * (1 - sm) * (1 - tm) < (g * hm * hm) * (1 - sm) := by
      rw [← e]; exact mul_lt_mul_of_pos_right hS h1
    have h3 : (A12 * tm * (1 - tm)) * (1 - sm) < (g * hm * hm) * (1 - sm) := by linarith
    exact lt_of_mul_lt_mul_right h3 h2.le
  have R : 0 < (A12 * tm * tm + g * hm * hm - A12 * tm * sm - g * hm * km) * (1 - tm) := by
    have e : (A12 * tm * tm + g * hm * hm - A12 * tm * sm - g * hm * km) * (1 - tm) =
        (sm - tm) * (g * hm * hm - A12 * tm * (1 - tm)) := by
      linear_combination (-(g * hm)) * hrel
    rw [e]
    exact mul_pos (sub_pos.2 hts) (sub_pos.2 key)
  have R' := (mul_pos_iff_of_pos_right h1).1 R
  nlinarith [mul_nonneg (mul_nonneg htm.le htm.le) (sub_nonneg.2 hA11)]

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **`T1` is unimodal** when `g h- k- > A12 t- (1 - s-)` (and `t- < s-`, `A12 ≤ A11`). -/
theorem rimT1 (hts : F.S.tm < F.S.sm) (H1 : F.S.hp * F.S.tm + F.S.hm * F.S.tp < F.S.hm)
    (H2 : F.S.hm * (1 - F.S.sp) < F.S.tm * F.S.kp)
    (hS : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hA : 0 < F.a12 := F.A12_pos
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have hg : 0 < F.gg := F.g_pos
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim5t 4 3 2 5 6 ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩
    ⟨0, F.S.sm, -F.S.km⟩ p4 p3 p2 p5 p6 (-1) (Or.inr rfl) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 1, 0⟩
    (Or.inl (ne_of_gt htm)) ?_ ?_ ?_
  · exact t1_cyc hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm H2
  · intro j' h4 h3 h2 h5 h6 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact t1_rest0 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm i
    · rw [p1]; exact t1_rest1 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm H1 H2 i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set zz : ZMod 5 → ℝ := fun i => F.GG (t1P F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km i)
      ⟨F.S.tm, 0, -F.S.hm⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (t1P F.S.tm F.S.hm F.S.sp F.S.kp F.S.sm F.S.km i)
      ⟨0, 1, 0⟩ with hww
    have e0 : zz 0 = F.a11 * F.S.tm * F.S.tm + F.gg * F.S.hm * F.S.hm := by
      simp only [hzz, t1P, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a11 * F.S.tm := by
      simp only [hzz, t1P, GG, Gf, quint_1]; ring
    have e2 : zz 2 = F.a12 * F.S.tm * F.S.sp - F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, t1P, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * F.S.tm := by
      simp only [hzz, t1P, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km := by
      simp only [hzz, t1P, GG, Gf, quint_4]; ring
    have hz40 := t1_z4_lt_z0 (g := F.gg) hA hA11 htm htm1 hsm1 hts hhm F.Km_eq hS
    have m1 := mul_pos hA htm
    have m2 := mul_pos hg hhm
    have m3 := mul_pos m2 hkp
    have m4 := mul_pos m1 hsp
    have m5 := mul_nonneg m1.le (sub_nonneg.2 hA11)
    refine Q5t_eventually (z := zz) (w := ww) ?_ ?_ ?_ ?_
    · rw [e1, e2]; nlinarith [mul_pos m1 (sub_pos.2 hsp1), mul_le_mul_of_nonneg_left hA11 htm.le]
    · rw [e2, e3]; nlinarith [mul_pos m1 (sub_pos.2 hsp1)]
    · rw [e3, e4]; nlinarith
    · rw [e4, e0]; nlinarith

/-- **`T2` is unimodal** when `g h- k- < A12 s- (1 - t-)`. -/
theorem rimT2 (H3 : F.S.sm * F.S.hp < (F.S.km * F.S.sp + F.S.sm * F.S.kp) * (1 - F.S.tp))
    (H4 : (1 - F.S.sp) * F.S.km < F.S.sm * F.S.kp)
    (hS : F.gg * F.S.hm * F.S.km < F.a12 * F.S.sm * (1 - F.S.tm)) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hA : 0 < F.a12 := F.A12_pos
  have hg : 0 < F.gg := F.g_pos
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 0 4 3 2 ⟨0, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨1, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
    p0 p4 p3 p2 (-1) (Or.inr rfl) ⟨0, F.S.sm, -F.S.km⟩ ⟨-1, 0, 0⟩
    (Or.inr (Or.inl (ne_of_gt hsm))) ?_ ?_ ?_
  · exact t2_cyc hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm
  · intro j' h0 h4 h3 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact t2_rest1 hsp hsp1 htp htp1 hhp hkp htm htm1 hhm hsm hsm1 hkm H3 i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact t2_rest5 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm H4 i
    · rw [p6]; exact t2_rest6 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm i
  · set zz : ZMod 4 → ℝ := fun i => F.GG (t2P F.S.tm F.S.hm F.S.sp F.S.kp i)
      ⟨0, F.S.sm, -F.S.km⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (t2P F.S.tm F.S.hm F.S.sp F.S.kp i)
      ⟨-1, 0, 0⟩ with hww
    have e0 : zz 0 = 0 := by
      simp only [hzz, t2P, GG, Gf, quad_0]; ring
    have e1 : zz 1 = F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km := by
      simp only [hzz, t2P, GG, Gf, quad_1]; ring
    have e2 : zz 2 = F.a12 * F.S.sm := by
      simp only [hzz, t2P, GG, Gf, quad_2]; ring
    have m1 := mul_pos (mul_pos hA htm) hsm
    have m2 := mul_pos (mul_pos hg hhm) hkm
    refine Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl ?_))
      (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
    · rw [e0, e1]; linarith
    · rw [e1, e2]; nlinarith

/-- **Theorem 27.48 (P09; type 09) in the frame, at the frame's own metric.**  If
`t- < s-`, `b+ < a- < d+`, `c- < d+` and `b+ < s+ A2`, then one of the tests `T1`, `T2` is
unimodal, so the shape is Rupert (no acuteness is needed here beyond the frame's own
`A12 ≤ A11`). -/
theorem rupert_of_27_48 (hts : F.S.tm < F.S.sm) (h1 : F.S.bp < F.S.am) (h2 : F.S.am < F.S.dp)
    (h3 : F.S.cm < F.S.dp) (h4 : F.S.bp < F.S.sp * F.S.A2) :
    IsRupert (Finset.univ.image x) := by
  have H1 := F.S.t48_T1_m1p_inside.2 h1
  have H2 := F.S.t48_T1_m2p_above.2 h2
  have H3 := F.S.t48_T2_m1p_below.2 (by rw [← F.S.sp_A2]; exact h4)
  have H4 := F.A1_of h3
  have hA : 0 < F.a12 := F.A12_pos
  by_cases hc : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km
  · exact F.rimT1 hts H1 H2 hc
  · refine F.rimT2 H3 H4 ?_
    by_contra hn
    refine F.S.t48_contra hA hts (not_lt.mp hc) ?_
    nlinarith [not_lt.mp hn]

/-- **Type 09, acute case (c), in the frame**: at the frame's own metric, off the special
positions, with the far angle at `xb` acute, the shape is Rupert. -/
theorem isRupert_caseC (hx : Function.Injective x) (hA : F.a12 < F.a22)
    (sp0 : F.S.tm ≠ F.S.sm) (sp4 : F.S.ap ≠ F.S.cp) (sp5 : F.S.cp ≠ F.S.bm)
    (sp1 : F.S.am ≠ F.S.bp) (sp2 : F.S.am ≠ F.S.dp) (sp3 : F.S.bp ≠ F.S.sp * F.S.A2) :
    IsRupert (Finset.univ.image x) := by
  rcases F.rupert_or_27_48' hx hA sp0 sp4 sp5 sp1 sp2 sp3 with h | ⟨a, b, c, d, e⟩
  · exact h
  · exact F.rupert_of_27_48 a b c d e

end Frame09

end Minimality.CaseC09

end
