module

public import Minimality.CaseC09Ac
public import Minimality.QuadRect09
public import Minimality.CaseC18M

@[expose] public section

/-!
# Type 09, acute case (c): the special positions are closed (PROOFS sections 39-40)

`CaseC09Special x` is Rupert: Theorem K1 (`t- = s- ∧ a- = d+`), Theorem K2
(`a- = b+ ∧ b+ = s+A2`) and the right angle `A12 = A22` (Theorem 09.6 with Lemma W″ replacing
Lemmas V, X and the corner E′).  Paper: `FEWER-FACES-PROOFS.md` "## 39." and "## 40.";
map, rim/tilt table, templates and risks: `nopert229/out/bottleneck/sp09b/handoff_lean.md`.

All sector tests are proved (groups 1a-4); the case tree
(`rupert_K1`, `rupert_K2`, `rupert_a12_eq_a22`, `CaseC09Special.isRupert`) are proved from them.
Labels: `(v, xa, m1+, m1-, xb, m2+, m2-) = (0, 3, 1, 4, 5, 2, 6)` as `Fin 7`; frame coordinates
`(x, y, z)` in `(xa - v, xb - v, e)`.
-/

namespace Minimality.CaseC09

open Finset Filter Minimality.CaseC18
open scoped RealInnerProductSpace Topology

/-! ### Group 0: helpers (small, proved or elementary) -/

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- `rupert_rim` with a robustly unimodal limit depth cycle, for `Frame09` (copy of
`Frame7.rupert_rim_rob`, `CaseC18M.lean`). -/
theorem rupert_rim_rob {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → Fin 7) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (hz : IsRobustUnimodal fun i => F.GG (F.ptC (c i)) u) :
    IsRupert (Finset.univ.image x) := by
  refine F.rupert_rim hk c σ hσ u v hu hcyc hrest QRob QRob_open (fun z a ha => QRob_smul ha)
    (fun z a => QRob_shift a) ?_ (fun z hz hq => QRob_unimodal hz hq)
  have hQ : QRob fun i => F.GG (F.ptC (c i)) u := QRob_of_robust (by omega) hz
  have hcont : Continuous fun s : ℝ =>
      (fun i : ZMod k => F.GG (F.ptC (c i)) u + s * F.GG (F.ptC (c i)) v) := by
    refine continuous_pi fun i => ?_
    fun_prop
  have h0 : (0 : ℝ) ∈ (fun s : ℝ => (fun i : ZMod k => F.GG (F.ptC (c i)) u +
      s * F.GG (F.ptC (c i)) v)) ⁻¹' {z | QRob z} := by
    simpa using hQ
  exact nhdsWithin_le_nhds ((QRob_open.preimage hcont).mem_nhds h0)

/-- `A12 = A22` forces `A12 < A11` (otherwise the Gram matrix `A` is singular). -/
theorem a12_lt_a11_of_eq (hA : F.a12 = F.a22) : F.a12 < F.a11 := by
  have h0 : 0 < F.a12 := F.A12_pos
  have h1 : F.a12 ≤ F.a11 := F.A12_le_A11
  have h2 := F.A_det_pos
  change 0 < F.a11 * F.a22 - F.a12 ^ 2 at h2
  rw [← hA] at h2
  by_contra hn
  have : F.a11 = F.a12 := le_antisymm (not_lt.1 hn) h1
  rw [this] at h2
  nlinarith

/-- The `K1` discriminant `Δ = g k+ h - A12 (1 - s+)(1 - t)` (`t = t- = s-`, `h = h- = k-`);
its sign is that of `g k+ d- - A12 (1 - s+)`. -/
noncomputable def K1Delta : ℝ :=
  F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm)

end Frame09

/-- An interval minus two points is nonempty (the "off finitely many tilt values" device). -/
theorem exists_Ioo_avoid {lo hi : ℝ} (h : lo < hi) (a b : ℝ) :
    ∃ D, lo < D ∧ D < hi ∧ D ≠ a ∧ D ≠ b := by
  have hinf : (Set.Ioo lo hi).Infinite := Set.Ioo_infinite h
  obtain ⟨D, hD, hD'⟩ := (hinf.diff (Set.toFinite ({a, b} : Set ℝ))).nonempty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hD'
  exact ⟨D, hD.1, hD.2, hD'.1, hD'.2⟩

namespace Shape09
variable (S : Shape09)

/-- `c- = a-` exactly when `t- = s-`; used to exclude the K1 corner. -/
theorem cm_eq_am_of_eq (hts : S.tm = S.sm) : S.cm = S.am := by
  have htm := S.tm_pos
  have h1 := S.am_mul; have h2 := S.cm_mul'; have h3 := S.bm_mul
  have key : (S.am - S.cm) * (S.tm * S.sm) = S.bm * (S.sm - S.tm) := by
    have : S.am * S.tm = S.bm * (1 - S.tm) := by rw [h1, h3]
    linear_combination S.sm * this - S.tm * h2
  have hsm := S.sm_pos
  rw [hts, sub_self, mul_zero] at key
  have : S.am - S.cm = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · exact h
    · exact absurd h (by rw [← hts]; positivity)
  linarith

/-- On `K2` (`a- = b+ ∧ b+ = s+A2`): `c- < d+` (the roof). -/
theorem cm_lt_dp_of_K2 (H1 : S.am = S.bp) (H2 : S.bp = S.sp * S.A2) : S.cm < S.dp := by
  have h3 : S.bp = S.kp + S.sp * S.cm := by rw [H2, S.sp_A2]
  have hr := S.bp_lt_dp
  have hd := S.dp_mul
  have hsp := S.sp_pos
  have : S.sp * S.cm < S.sp * S.dp := by nlinarith
  exact lt_of_mul_lt_mul_left this hsp.le

/-- On `K2`: `c- < a-`, hence `t- < s-` (the roof is `t- < s-`, Lemma K2.0). -/
theorem tm_lt_sm_of_K2 (H1 : S.am = S.bp) (H2 : S.bp = S.sp * S.A2) : S.tm < S.sm := by
  have hcd := S.cm_lt_dp_of_K2 H1 H2
  have h3 : S.bp = S.kp + S.sp * S.cm := by rw [H2, S.sp_A2]
  have hd := S.dp_mul
  have hsp1 := S.sp_lt
  have hcm : S.cm < S.am := by
    rw [H1, h3]; nlinarith
  have htm := S.tm_pos; have hsm := S.sm_pos
  have h1 := S.am_mul; have h2 := S.cm_mul'; have h4 := S.bm_mul; have h5 := S.bm_pos
  have key : (S.am - S.cm) * (S.tm * S.sm) = S.bm * (S.sm - S.tm) := by
    have : S.am * S.tm = S.bm * (1 - S.tm) := by rw [h1, h4]
    linear_combination S.sm * this - S.tm * h2
  have hpos : 0 < (S.am - S.cm) * (S.tm * S.sm) := mul_pos (sub_pos.2 hcm) (mul_pos htm hsm)
  rw [key] at hpos
  have := (pos_iff_pos_of_mul_pos hpos).1 h5
  linarith

end Shape09

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
/-- The robust depth cycle of K2's test `T1'`, in the Lean order `(m1-, xa, m1+, m2+, xb, m2-)`
(= `z0 … z5`): `m1+ < xa`, `m2+ < xb < m2-`, and `m1-` above `xa` or above `m2-`.
(Checked on all 498 weak orders in `{0..5}^6`, `scratchpad/c09C/rob.cc`: 0 failures.) -/
theorem robust_cycT1p {z0 z1 z2 z3 z4 z5 : ℝ} (h21 : z2 < z1) (h34 : z3 < z4) (h45 : z4 < z5)
    (h0 : z1 < z0 ∨ z5 < z0) :
    IsRobustUnimodal (k := 6) (fun i : ZMod 6 => ![z0, z1, z2, z3, z4, z5] i) := by
  have hB : ∀ B : ZMod 6, B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro B a b c d hab hbc hcd hdk
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> intros <;> rcases h0 with h0 | h0 <;> linarith
  · intro i j l hij hjl hil e1 e2
    rcases hB i with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB j with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hB l with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hij hjl hil <;> norm_num at e1 e2 <;> rcases h0 with h0 | h0 <;> linarith
  · intro B a b c d hab hbc hcd hdk e
    interval_cases d <;> interval_cases c <;> (try omega) <;> interval_cases b <;> (try omega) <;> interval_cases a <;> (try omega) <;> rcases hB B with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at e ⊢ <;> intros <;> rcases h0 with h0 | h0 <;> constructor <;> intro hh <;> linarith

/-! ### Group 1: the right angle `A12 = A22` -- edge views of F2 (Lemma W, Lemma T2', Lemma W″)

Rims are written in the paper's ccw order: use `σ = 1` with that order (`ST 1 u v a b` is
`det(a, b, u) > 0`, the paper's "ccw w.r.t. u"); the reversed order needs `σ = -1`. -/

section G1a
variable {tp hp tm hm sp kp sm km : ℝ}

/-! #### Group 1a: ST tables of `rimW` and `rimT2p` -/

theorem rimW_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 2, 0⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i))
        ((quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ j).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp htm
  have a3 := mul_pos hsp' hhm
  have a4 := mul_pos hkp hhm
  have a5 := mul_pos hsp hkp
  have a6 := mul_pos hsp hhm
  have a7 := mul_pos hsp' htm
  have a8 := mul_pos hkp htm'
  have a9 := mul_pos hsp htm
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    left; nlinarith


theorem rimW_rest5 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm)  :
    ∀ i : ZMod 4,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 2, 0⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp htm
  have a3 := mul_pos hsp' hhm
  have a4 := mul_pos hkp hhm
  have a5 := mul_pos hsp hkp
  have a6 := mul_pos hsp hhm
  have a7 := mul_pos hsp' htm
  have a8 := mul_pos hkp htm'
  have a9 := mul_pos hsp htm

  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem rimW_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (H : km * (1 - sp) < kp * sm) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 2, 0⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i))
        ((⟨0, sm, -km⟩ : C3).sub (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp htm
  have a3 := mul_pos hsp' hhm
  have a4 := mul_pos hkp hhm
  have a5 := mul_pos hsp hkp
  have a6 := mul_pos hsp hhm
  have a7 := mul_pos hsp' htm
  have a8 := mul_pos hkp htm'
  have a9 := mul_pos hsp htm
  have q1 := sub_pos.2 H
  have c1 := mul_pos hhm q1
  have c2 := mul_pos htm q1
  have c5 := mul_pos hsp q1

  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem rimW_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp) (R : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 2, 0⟩
        ((quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ (i + 1)).sub
          (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub (quad (⟨0, sp, kp⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, 0, 0⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp htm
  have a3 := mul_pos hsp' hhm
  have a4 := mul_pos hkp hhm
  have a5 := mul_pos hsp hkp
  have a6 := mul_pos hsp hhm
  have a7 := mul_pos hsp' htm
  have a8 := mul_pos hkp htm'
  have a9 := mul_pos hsp htm
  have htp' : 0 < 1 - tp := by linarith
  have q2 := sub_pos.2 R
  have c3 := mul_pos hhm q2
  have c4 := mul_pos htm q2
  have c6 := mul_pos hsp q2
  have c7 := mul_pos htm' q2
  have d1 := mul_pos (mul_pos hhm htp') hsp'
  have d2 := mul_pos (mul_pos hhp htm') hsp'
  have d3 := mul_pos (mul_pos hkp htp) hsp
  have d4 := mul_pos (mul_pos hhp htm) hsp'
  have d5 := mul_pos (mul_pos hhp hsp') hkp
  have d6 := mul_pos (mul_pos hhp htm') hkp

  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)


theorem rimT2p_cyc (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨0, sm, -km⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ j).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hkm
  have a2 := mul_pos hsm hhm
  have a3 := mul_pos hsm' hhm
  have a4 := mul_pos hkm htm
  have a5 := mul_pos hkm htm'
  have a6 := mul_pos hsm htm
  have a7 := mul_pos hsm' htm
  have a8 := mul_pos hhm htm
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    left; nlinarith

theorem rimT2p_rest0 (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm)  :
    ∀ i : ZMod 4,
      ST 1 ⟨0, sm, -km⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hkm
  have a2 := mul_pos hsm hhm
  have a3 := mul_pos hsm' hhm
  have a4 := mul_pos hkm htm
  have a5 := mul_pos hkm htm'
  have a6 := mul_pos hsm htm
  have a7 := mul_pos hsm' htm
  have a8 := mul_pos hhm htm

  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem rimT2p_rest2 (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (H : kp * sm < km * (1 - sp)) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, sm, -km⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((⟨0, sp, kp⟩ : C3).sub (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hkm
  have a2 := mul_pos hsm hhm
  have a3 := mul_pos hsm' hhm
  have a4 := mul_pos hkm htm
  have a5 := mul_pos hkm htm'
  have a6 := mul_pos hsm htm
  have a7 := mul_pos hsm' htm
  have a8 := mul_pos hhm htm
  have hsp' : 0 < 1 - sp := by linarith
  have q1 := sub_pos.2 H
  have c1 := mul_pos hhm q1
  have c2 := mul_pos htm q1
  have c3 := mul_pos hsm q1
  have c4 := mul_pos htm' q1
  have c5 := mul_pos hsm' q1
  have c6 := mul_pos (mul_pos htm' hsm) hkp
  have c7 := mul_pos (mul_pos htm' hsp) hkm

  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

theorem rimT2p_rest1 (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp) (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (H : kp * sm < km * (1 - sp)) (R : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 4,
      ST 1 ⟨0, sm, -km⟩ ⟨1, 0, 0⟩
        ((quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have a1 := mul_pos hsm hkm
  have a2 := mul_pos hsm hhm
  have a3 := mul_pos hsm' hhm
  have a4 := mul_pos hkm htm
  have a5 := mul_pos hkm htm'
  have a6 := mul_pos hsm htm
  have a7 := mul_pos hsm' htm
  have a8 := mul_pos hhm htm
  have htp' : 0 < 1 - tp := by linarith
  have hsp' : 0 < 1 - sp := by linarith
  have q2 := sub_pos.2 R
  have S1 : hp * sm < km * (1 - tp) := by
    refine lt_of_mul_lt_mul_right (a := 1 - sp) ?_ hsp'.le
    nlinarith [mul_lt_mul_of_pos_left H htp', mul_lt_mul_of_pos_left R hsm]
  have c1 := mul_pos hsm q2
  have c2 := mul_pos hkm htp
  have c3 := mul_pos hkm htp'
  have c4 := mul_pos hsm hhp
  have c5 := mul_pos hsm htp
  have c6 := mul_pos hhm htp'
  have c7 := mul_pos htm hhp

  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

end G1a

section G1b

/-! #### Group 1b: ST tables of `rimWpp` and `rimK1d` (rim `(v, m2+, xa, m1-, m2-)`, view `u_W`, tilt `(-1, 0, D)`) -/

variable {tp hp tm hm sp kp sm km D : ℝ}

set_option maxHeartbeats 4000000 in

set_option maxHeartbeats 4000000 in
theorem rimWpp_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (hkc : kp * sm = km * (1 - sp)) (hD1 : kp < (1 - sp) * D) (hD2 : hm < tm * D) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 0, D⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have q1 := sub_pos.2 hD1
  have q2 := sub_pos.2 hD2
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hhm
  have a3 := mul_pos hsm hkp
  have a4 := mul_pos hsm hhm
  have a5 := mul_pos hsp' hkm
  have a6 := mul_pos hsm q1
  have a7 := mul_pos hsm q2
  have a8 := mul_pos hsp' q2
  have a9 := mul_pos hkp q2
  have a10 := mul_pos hsp q2
  have a11 := mul_pos hsm' q2
  have a12 := mul_pos hsm' q1
  have a13 := mul_pos hsp q1
  have a14 := mul_pos hsm hkm
  have a15 := mul_pos hkm q2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimWpp_rest5 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (hkc : kp * sm = km * (1 - sp)) (hD1 : kp < (1 - sp) * D) (hD2 : hm < tm * D) :
    ∀ i : ZMod 5,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 0, D⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((⟨0, 1, 0⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have q1 := sub_pos.2 hD1
  have q2 := sub_pos.2 hD2
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hhm
  have a3 := mul_pos hsm hkp
  have a4 := mul_pos hsm hhm
  have a5 := mul_pos hsp' hkm
  have a6 := mul_pos hsm q1
  have a7 := mul_pos hsm q2
  have a8 := mul_pos hsp' q2
  have a9 := mul_pos hkp q2
  have a10 := mul_pos hsp q2
  have a11 := mul_pos hsm' q2
  have a12 := mul_pos hsm' q1
  have a13 := mul_pos hsp q1
  have a14 := mul_pos hsm hkm
  have a15 := mul_pos hkm q2
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimWpp_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (htm : 0 < tm) (htm1 : tm < 1)
    (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (hkc : kp * sm = km * (1 - sp)) (hD1 : kp < (1 - sp) * D) (hD2 : hm < tm * D) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (R : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 5,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 0, D⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨tm, 0, -hm⟩ ⟨0, sm, -km⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have q1 := sub_pos.2 hD1
  have q2 := sub_pos.2 hD2
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hhm
  have a3 := mul_pos hsm hkp
  have a4 := mul_pos hsm hhm
  have a5 := mul_pos hsp' hkm
  have a6 := mul_pos hsm q1
  have a7 := mul_pos hsm q2
  have a8 := mul_pos hsp' q2
  have a9 := mul_pos hkp q2
  have a10 := mul_pos hsp q2
  have a11 := mul_pos hsm' q2
  have a12 := mul_pos hsm' q1
  have a13 := mul_pos hsp q1
  have a14 := mul_pos hsm hkm
  have a15 := mul_pos hkm q2
  have c1 := sub_pos.2 R
  have c2 := mul_pos htp hhm
  have c3 := mul_pos hhp htm
  have c4 := mul_pos hhp hsm
  have c5 := mul_pos hhp q2
  have htp' : 0 < 1 - tp := by linarith
  have c6 := mul_pos hsp' (mul_pos hhm htp')
  have c7 := mul_pos hsp' (mul_pos hhp htm')
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)
end G1b

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **Lemma W** (§39.3), the edge view `u_W = xb - m2+ = (0, 1 - s+, -k+)`, tilt `(-1, 2, 0)`,
rim `(m2+, xa, m1-, v) = (2, 3, 4, 0)`, rest `{xb, m2-, m1+}`; 4-cycle, `rupert_rim4` with `Q4`
(robust: `{xa, v}` is never weakly above `{m2+, m1-}` since `z(m1-) > 0`, and `{m2+, m1-}` is not
above `{xa, v}` as `z(m2+) = A22(1-s+)s+ - g k+² < A12(1-s+) = z(xa)` once `A22 s+ ≤ A12`).
Needs `d+ > c-` (so `m2-` lies on the open side `(v, m2+)`). -/
theorem rimW (hdc : F.S.cm < F.S.dp) (hA : F.a22 * F.S.sp ≤ F.a12) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have H : F.S.km * (1 - F.S.sp) < F.S.kp * F.S.sm := by
    have h1 := F.S.cm_mul; have h2 := F.S.dp_mul
    have : F.S.cm * (1 - F.S.sp) < F.S.dp * (1 - F.S.sp) :=
      mul_lt_mul_of_pos_right hdc (by linarith)
    nlinarith
  have R : F.S.hp * (1 - F.S.sp) < F.S.kp * (1 - F.S.tp) := by
    have h1 := F.S.bp_mul; have h2 := F.S.dp_mul
    have : F.S.bp * (1 - F.S.tp) * (1 - F.S.sp) < F.S.dp * (1 - F.S.sp) * (1 - F.S.tp) := by
      have := mul_lt_mul_of_pos_right F.S.bp_lt_dp (mul_pos (sub_pos.2 htp1) (sub_pos.2 hsp1))
      nlinarith
    rw [h1, h2] at this
    linarith
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 2 3 4 0 ⟨0, F.S.sp, F.S.kp⟩ ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩
    p2 p3 p4 p0 1 (Or.inl rfl) ⟨0, 1 - F.S.sp, -F.S.kp⟩ ⟨-1, 2, 0⟩
    (Or.inr (Or.inl (by linarith))) ?_ ?_ ?_
  · exact rimW_cyc hsp hsp1 hkp htm htm1 hhm
  · intro j' h2 h3 h4 h0 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact rimW_rest1 hsp hsp1 hkp htm htm1 hhm htp htp1 hhp R i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact rimW_rest5 hsp hsp1 hkp htm htm1 hhm i
    · rw [p6]; exact rimW_rest6 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm H i
  · set zz : ZMod 4 → ℝ := fun i => F.GG (quad (⟨0, F.S.sp, F.S.kp⟩ : C3) ⟨1, 0, 0⟩
      ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ i) ⟨0, 1 - F.S.sp, -F.S.kp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (quad (⟨0, F.S.sp, F.S.kp⟩ : C3) ⟨1, 0, 0⟩
      ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 0, 0⟩ i) ⟨-1, 2, 0⟩ with hww
    have e0 : zz 0 = F.a22 * F.S.sp * (1 - F.S.sp) - F.gg * F.S.kp * F.S.kp := by
      simp only [hzz, GG, Gf, quad_0]; ring
    have e1 : zz 1 = F.a12 * (1 - F.S.sp) := by
      simp only [hzz, GG, Gf, quad_1]; ring
    have e2 : zz 2 = F.a12 * F.S.tm * (1 - F.S.sp) + F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, GG, Gf, quad_2]; ring
    have e3 : zz 3 = 0 := by
      simp only [hzz, GG, Gf, quad_3]; ring
    have m1 := mul_pos hg (mul_pos hkp hkp)
    have m2 := mul_pos hA0 (sub_pos.2 hsp1)
    have m3 := mul_pos (mul_pos hA0 htm) (sub_pos.2 hsp1)
    have m4 := mul_pos (mul_pos hg hhm) hkp
    refine Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl ?_))
      (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    · rw [e0, e1]; nlinarith [mul_le_mul_of_nonneg_right hA (sub_pos.2 hsp1).le]
    · rw [e3, e2]; linarith

/-- **Lemma T2'** (§39.3, with the referee's tie), the edge view `u2 = m2- - v = (0, s-, -k-)`,
tilt `e_x = (1, 0, 0)`, rim `(xb, xa, m1-, m2-) = (5, 3, 4, 6)`, rest `{v, m2+, m1+}`; `rupert_rim4`
with `Q4_eventually` (lex).  At `A12 = A22`: `z(xb) = z(xa)` and `w(xa) - w(xb) = A11 - A12 > 0`
(`a12_lt_a11_of_eq`), so `xb` is below `xa`; with `Θ = g b- k- - A12 s-`:
`z(m2-) - z(xb) = (1-s-)Θ`, `z(m1-) - z(xa) = (1-t-)Θ`, so `m2- < xb` if `Θ < 0`, `xa < m1-` if
`Θ > 0`, and `Θ = 0` has `w(m2-) = A12 s- < A12 = w(xb)`.  No tie hypothesis. -/
theorem rimT2p (hA : F.a12 = F.a22) (hdc : F.S.dp < F.S.cm) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have hlt := F.a12_lt_a11_of_eq hA
  have H : F.S.kp * F.S.sm < F.S.km * (1 - F.S.sp) := by
    have h1 := F.S.cm_mul; have h2 := F.S.dp_mul
    have : F.S.dp * (1 - F.S.sp) * F.S.sm < F.S.cm * F.S.sm * (1 - F.S.sp) := by
      have := mul_lt_mul_of_pos_right hdc (mul_pos hsm (sub_pos.2 hsp1))
      nlinarith
    rw [h1, h2] at this
    linarith
  have R : F.S.hp * (1 - F.S.sp) < F.S.kp * (1 - F.S.tp) := by
    have h1 := F.S.bp_mul; have h2 := F.S.dp_mul
    have : F.S.bp * (1 - F.S.tp) * (1 - F.S.sp) < F.S.dp * (1 - F.S.sp) * (1 - F.S.tp) := by
      have := mul_lt_mul_of_pos_right F.S.bp_lt_dp (mul_pos (sub_pos.2 htp1) (sub_pos.2 hsp1))
      nlinarith
    rw [h1, h2] at this
    linarith
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim4 5 3 4 6 ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, F.S.sm, -F.S.km⟩
    p5 p3 p4 p6 1 (Or.inl rfl) ⟨0, F.S.sm, -F.S.km⟩ ⟨1, 0, 0⟩
    (Or.inr (Or.inl (ne_of_gt hsm))) ?_ ?_ ?_
  · exact rimT2p_cyc hsm hsm1 hkm htm htm1 hhm
  · intro j' h5 h3 h4 h6 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact rimT2p_rest0 hsm hsm1 hkm htm htm1 hhm i
    · rw [p1]; exact rimT2p_rest1 hsm hsm1 hkm htm htm1 hhm htp htp1 hhp hsp hsp1 hkp H R i
    · rw [p2]; exact rimT2p_rest2 hsm hsm1 hkm htm htm1 hhm hsp hsp1 hkp H i
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
  · have Km := F.Km_eq
    set zz : ZMod 4 → ℝ := fun i => F.GG (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩
      ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, F.S.sm, -F.S.km⟩ i) ⟨0, F.S.sm, -F.S.km⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (quad (⟨0, 1, 0⟩ : C3) ⟨1, 0, 0⟩
      ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, F.S.sm, -F.S.km⟩ i) ⟨1, 0, 0⟩ with hww
    have e0 : zz 0 = F.a12 * F.S.sm := by
      simp only [hzz, GG, Gf, quad_0]; rw [← hA]; ring
    have e1 : zz 1 = F.a12 * F.S.sm := by
      simp only [hzz, GG, Gf, quad_1]; ring
    have e2 : zz 2 = F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km := by
      simp only [hzz, GG, Gf, quad_2]; ring
    have e3 : zz 3 = F.a12 * F.S.sm * F.S.sm + F.gg * F.S.km * F.S.km := by
      simp only [hzz, GG, Gf, quad_3]; rw [← hA]; ring
    have f0 : ww 0 = F.a12 := by
      simp only [hww, GG, Gf, quad_0]; ring
    have f1 : ww 1 = F.a11 := by
      simp only [hww, GG, Gf, quad_1]; ring
    have f3 : ww 3 = F.a12 * F.S.sm := by
      simp only [hww, GG, Gf, quad_3]; ring
    have hbm := F.S.bm_mul
    have hkb := F.S.km_eq
    set Θ := F.gg * F.S.bm * F.S.km - F.a12 * F.S.sm with hΘ
    have d3 : zz 3 - zz 0 = (1 - F.S.sm) * Θ := by
      rw [e3, e0, hΘ]; linear_combination (F.gg * F.S.km) * hkb
    have d2 : zz 2 - zz 1 = (1 - F.S.tm) * Θ := by
      rw [e2, e1, hΘ]; linear_combination (-(F.gg * F.S.km)) * hbm
    have hs1 : 0 < 1 - F.S.sm := by linarith
    have ht1 : 0 < 1 - F.S.tm := by linarith
    have hA1 : (zz 0 < zz 1 ∨ (zz 0 = zz 1 ∧ ww 0 < ww 1)) :=
      Or.inr ⟨by rw [e0, e1], by rw [f0, f1]; exact hlt⟩
    rcases lt_trichotomy Θ 0 with h | h | h
    · refine Q4_eventually (z := zz) (w := ww) (Or.inl hA1)
        (Or.inr (Or.inl (Or.inl ?_)))
      have := mul_neg_of_pos_of_neg hs1 h
      linarith
    · refine Q4_eventually (z := zz) (w := ww) (Or.inl hA1)
        (Or.inr (Or.inl (Or.inr ⟨?_, ?_⟩)))
      · rw [h, mul_zero] at d3; linarith
      · rw [f3, f0]; nlinarith
    · refine Q4_eventually (z := zz) (w := ww) (Or.inl hA1)
        (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      have := mul_pos ht1 h
      linarith

/-- Shared core of `rimWpp` and `rimK1d`: the 5-rim `(v, m2+, xa, m1-, m2-)`, view `u_W`, tilt
`(-1, 0, D)`, `d+ < D`, `A12 (1-s+) D < A11 k+`. -/
theorem rimWpp_core (hA : F.a12 = F.a22) (hdc : F.S.dp = F.S.cm) (hamd : F.S.am ≤ F.S.dp)
    (hcase : F.S.sm < F.S.tm ∨ F.K1Delta = 0) (D : ℝ) (hD : F.S.dp < D)
    (hD3 : F.a12 * (1 - F.S.sp) * D < F.a11 * F.S.kp) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have hsp' : 0 < 1 - F.S.sp := by linarith
  have hkc : F.S.kp * F.S.sm = F.S.km * (1 - F.S.sp) := by
    have h1 := F.S.cm_mul; have h2 := F.S.dp_mul
    rw [← h1, ← h2, hdc]; ring
  have hD1 : F.S.kp < (1 - F.S.sp) * D := by
    have h2 := F.S.dp_mul
    nlinarith [mul_pos (sub_pos.2 hD) hsp']
  have hD2 : F.S.hm < F.S.tm * D := by
    have h1 := F.S.am_mul
    nlinarith [mul_pos (sub_pos.2 (lt_of_le_of_lt hamd hD)) htm]
  have R : F.S.hp * (1 - F.S.sp) < F.S.kp * (1 - F.S.tp) := by
    have h1 := F.S.bp_mul; have h2 := F.S.dp_mul
    have : F.S.bp * (1 - F.S.tp) * (1 - F.S.sp) < F.S.dp * (1 - F.S.sp) * (1 - F.S.tp) := by
      have := mul_lt_mul_of_pos_right F.S.bp_lt_dp (mul_pos (sub_pos.2 htp1) (sub_pos.2 hsp1))
      nlinarith
    rw [h1, h2] at this
    linarith
  have Km := F.Km_eq
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  refine F.rupert_rim5p 0 2 3 4 6 ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩
    ⟨0, F.S.sm, -F.S.km⟩ p0 p2 p3 p4 p6 1 (Or.inl rfl) ⟨0, 1 - F.S.sp, -F.S.kp⟩ ⟨-1, 0, D⟩
    (Or.inr (Or.inl (by linarith))) ?_ ?_ ?_
  · exact rimWpp_cyc hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm hkc hD1 hD2
  · intro j' h0 h2 h3 h4 h6 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact rimWpp_rest1 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm hkc hD1 hD2 htp htp1 hhp R i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · rw [p5]; exact rimWpp_rest5 hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm hkc hD1 hD2 i
    · exact absurd rfl h6
  · set Pq : ZMod 5 → C3 := quint (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sp, F.S.kp⟩ ⟨1, 0, 0⟩
      ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, F.S.sm, -F.S.km⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨0, 1 - F.S.sp, -F.S.kp⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨-1, 0, D⟩ with hww
    have e0 : zz 0 = 0 := by simp only [hzz, hPq, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a12 * F.S.sp * (1 - F.S.sp) - F.gg * F.S.kp * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_1]; rw [← hA]; ring
    have e2 : zz 2 = F.a12 * (1 - F.S.sp) := by
      simp only [hzz, hPq, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * F.S.tm * (1 - F.S.sp) + F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * F.S.sm * (1 - F.S.sp) + F.gg * F.S.km * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_4]; rw [← hA]; ring
    have f2 : ww 2 = -F.a11 := by
      simp only [hww, hPq, GG, Gf, quint_2]; ring
    have f3 : ww 3 = -F.a11 * F.S.tm - F.gg * F.S.hm * D := by
      simp only [hww, hPq, GG, Gf, quint_3]; ring
    have hs1 : 0 < 1 - F.S.sm := by linarith
    have ht1 : 0 < 1 - F.S.tm := by linarith
    have z2pos : 0 < zz 2 := by rw [e2]; exact mul_pos hA0 hsp'
    have z4pos : 0 < zz 4 := by
      rw [e4]; have := mul_pos (mul_pos hA0 hsm) hsp'; have := mul_pos (mul_pos hg hkm) hkp; linarith
    have z12 : zz 1 < zz 2 := by
      rw [e1, e2]; nlinarith [mul_pos hA0 (mul_pos hsp' hsp'), mul_pos hg (mul_pos hkp hkp)]
    set Θ := F.K1Delta with hΘ
    have eΘ : Θ = F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) := rfl
    have d3 : zz 3 - zz 2 = Θ := by rw [e3, e2, eΘ]; ring
    have d4 : (1 - F.S.tm) * (zz 4 - zz 2) = (1 - F.S.sm) * Θ := by
      rw [e4, e2, eΘ]; linear_combination (F.gg * F.S.kp) * Km
    have d43 : (1 - F.S.tm) * (zz 4 - zz 3) = (F.S.tm - F.S.sm) * Θ := by
      have : zz 4 - zz 3 = (zz 4 - zz 2) - (zz 3 - zz 2) := by ring
      rw [this, mul_sub, d4, d3]; ring
    have w0 : zz 0 < zz 4 := by rw [e0]; exact z4pos
    rcases lt_trichotomy Θ 0 with h | h | h
    · -- Θ < 0
      have hlt : F.S.sm < F.S.tm := hcase.resolve_right h.ne
      have l3 : zz 3 < zz 2 := by linarith
      have l43 : zz 4 < zz 3 := by
        have : (1 - F.S.tm) * (zz 4 - zz 3) < 0 := by
          rw [d43]; exact mul_neg_of_pos_of_neg (sub_pos.2 hlt) h
        by_contra hc
        have := mul_nonneg ht1.le (sub_nonneg.2 (not_lt.1 hc))
        linarith
      exact Q5p_eventually (z := zz) (w := ww) (Or.inl (Or.inl w0))
        (Or.inr (Or.inl (Or.inl z12))) (Or.inr (Or.inr (Or.inl (Or.inl l43))))
        (Or.inr (Or.inr (Or.inl (Or.inl w0)))) (Or.inr (Or.inr (Or.inr (Or.inl z12))))
    · -- Θ = 0
      have h23 : zz 3 = zz 2 := by linarith
      have hΘ0 : F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) = 0 := by
        rw [← eΘ]; exact h
      have key : F.S.kp * (ww 3 - ww 2) = (1 - F.S.tm) * (F.a11 * F.S.kp - F.a12 * (1 - F.S.sp) * D) := by
        rw [f3, f2]; linear_combination (-D) * hΘ0
      have pos : 0 < F.S.kp * (ww 3 - ww 2) := by
        rw [key]; exact mul_pos ht1 (sub_pos.2 hD3)
      have w23 : ww 2 < ww 3 := by
        have := (pos_iff_pos_of_mul_pos pos).1 hkp
        linarith
      exact Q5p_eventually (z := zz) (w := ww) (Or.inl (Or.inl w0))
        (Or.inr (Or.inl (Or.inl z12))) (Or.inr (Or.inl (Or.inr ⟨h23.symm, w23⟩)))
        (Or.inr (Or.inr (Or.inl (Or.inl w0)))) (Or.inr (Or.inr (Or.inr (Or.inl z12))))
    · -- Θ > 0
      have hlt : F.S.sm < F.S.tm := hcase.resolve_right h.ne'
      have l23 : zz 2 < zz 3 := by linarith
      exact Q5p_eventually (z := zz) (w := ww) (Or.inl (Or.inl w0))
        (Or.inr (Or.inl (Or.inl z12))) (Or.inr (Or.inl (Or.inl l23)))
        (Or.inr (Or.inr (Or.inl (Or.inl w0)))) (Or.inr (Or.inr (Or.inr (Or.inl z12))))

/-- The tilt parameter of `rimWpp`/`rimK1d`: `d+ < D` and `A12 (1-s+) D < A11 k+`
(`D < d+ A11/A12`; nonempty as `A12 < A11`). -/
theorem exists_tilt_D (hA : F.a12 = F.a22) :
    ∃ D, F.S.dp < D ∧ F.a12 * (1 - F.S.sp) * D < F.a11 * F.S.kp := by
  have hlt := F.a12_lt_a11_of_eq hA
  have hA0 : 0 < F.a12 := F.A12_pos
  have hdp := F.S.dp_pos
  have hsp' : 0 < 1 - F.S.sp := by linarith [F.S.sp_lt]
  have hlt' : F.S.dp < F.S.dp * F.a11 / F.a12 := by
    rw [lt_div_iff₀ hA0]; nlinarith
  obtain ⟨D, h1, h2, -, -⟩ := exists_Ioo_avoid hlt' 0 0
  refine ⟨D, h1, ?_⟩
  rw [lt_div_iff₀ hA0] at h2
  have h3 := F.S.dp_mul
  nlinarith [mul_lt_mul_of_pos_right h2 hsp']

/-- **Lemma W″** (§40.2, the referee's; holds for every `g`), at `A12 = A22`, `d+ = c-`,
`s- < t-`: view `u_W`, tilt `(-1, 0, D)` with `d+ < D < d+ A11/A12` (off two values, via
`exists_Ioo_avoid`), rim `(v, m2+, xa, m1-, m2-) = (0, 2, 3, 4, 6)`, rest `{xb, m1+}`; `Q5p_eventually`
(lex) after the three-way split on `Δ = g k+ d- - A12(1-s+)`: with `Z = z(xa)`, `z(m1-) = Z + (1-t-)Δ`,
`z(m2-) = Z + (1-s-)Δ`; `Δ > 0`: max `m2-`; `Δ < 0`: max `xa`; `Δ = 0`: `xa ≺ m1-` and the larger
of `m1-, m2-` by `w(m2-) - w(m1-) = A11 t- - A12 s- + g D (h- - k-)` (affine in `D`).  Replaces
Lemmas V, X and the corner `E'`. -/
theorem rimWpp (hA : F.a12 = F.a22) (hdc : F.S.dp = F.S.cm) (hst : F.S.sm < F.S.tm) :
    IsRupert (Finset.univ.image x) := by
  have hamd : F.S.am ≤ F.S.dp := by
    have htm := F.S.tm_pos; have hsm := F.S.sm_pos
    have h1 := F.S.am_mul; have h2 := F.S.cm_mul'; have h3 := F.S.bm_mul; have h4 := F.S.bm_pos
    have key : (F.S.am - F.S.cm) * (F.S.tm * F.S.sm) = F.S.bm * (F.S.sm - F.S.tm) := by
      have : F.S.am * F.S.tm = F.S.bm * (1 - F.S.tm) := by rw [h1, h3]
      linear_combination F.S.sm * this - F.S.tm * h2
    have : (F.S.am - F.S.cm) * (F.S.tm * F.S.sm) < 0 := by
      rw [key]; exact mul_neg_of_pos_of_neg h4 (sub_neg.2 hst)
    by_contra hc
    have := mul_pos (sub_pos.2 (not_le.1 (hdc ▸ hc))) (mul_pos htm hsm)
    linarith
  obtain ⟨D, hD, hD3⟩ := F.exists_tilt_D hA
  exact F.rimWpp_core hA hdc hamd (Or.inl hst) D hD hD3

end Frame09

section G2
/-! #### Group 2: ST tables of `rimK1a`/`rimK1b` (K1: `t- = s- = t`, `k- = h- = h`, `k+ t = h (1-s+)`; view `u_W`, tilt `±e_x`) -/
variable {t h sp kp tp hp : ℝ}

set_option maxHeartbeats 4000000 in
theorem rimK1a_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ (i + 1)).sub
          (quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i))
        ((quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ j).sub
          (quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1a_rest0 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) :
    ∀ i : ZMod 5,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ (i + 1)).sub
          (quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub (quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1a_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (R : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 5,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨1, 0, 0⟩
        ((quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ (i + 1)).sub
          (quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub (quint (⟨0, t, -h⟩ : C3) ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  have c1 := sub_pos.2 R
  have c2 := mul_pos htp hh
  have c3 := mul_pos hhp ht
  have c4 := mul_pos hhp hsp'
  have c5 := mul_pos hsp' (mul_pos hh htp')
  have c6 := mul_pos hsp' (mul_pos hhp ht')
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)



set_option maxHeartbeats 4000000 in
theorem rimK1b_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1b_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) :
    ∀ i : ZMod 5,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i))
        ((⟨0, t, -h⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1b_rest1 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (R : hp * (1 - sp) < kp * (1 - tp)) :
    ∀ i : ZMod 5,
      ST 1 ⟨0, 1 - sp, -kp⟩ ⟨-1, 0, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i))
        ((⟨tp, 0, hp⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ ⟨t, 0, -h⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  have c1 := sub_pos.2 R
  have c2 := mul_pos htp hh
  have c3 := mul_pos hhp ht
  have c4 := mul_pos hhp hsp'
  have c5 := mul_pos hsp' (mul_pos hh htp')
  have c6 := mul_pos hsp' (mul_pos hhp ht')
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)


end G2

/-! ### Group 2: Theorem K1 at the view `u_W` (`t- = s-`, `a- = d+`; then `k- = h-`, `c- = a- = d+`)

`Δ = F.K1Delta`.  View `u_W = (0, 1 - s+, -k+)` (parallel to `u2` on K1). -/

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- Shape facts on K1 used by `rimK1a`/`rimK1b`: `k- = h-` and `k+ t- = h-(1-s+)`, roof. -/
theorem k1_facts (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) :
    F.S.km = F.S.hm ∧ F.S.kp * F.S.tm = F.S.hm * (1 - F.S.sp) ∧
      F.S.hp * (1 - F.S.sp) < F.S.kp * (1 - F.S.tp) := by
  have htm1 := F.S.tm_lt
  have Km := F.Km_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [← hts] at Km
    have : (F.S.km - F.S.hm) * (1 - F.S.tm) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h (by linarith)
  · have h1 := F.S.am_mul; have h2 := F.S.dp_mul
    rw [← hdp] at h2
    rw [← h2, ← h1]; ring
  · have htp := F.S.tp_lt; have hsp1 := F.S.sp_lt
    have h1 := F.S.bp_mul; have h2 := F.S.dp_mul
    have : F.S.bp * (1 - F.S.tp) * (1 - F.S.sp) < F.S.dp * (1 - F.S.sp) * (1 - F.S.tp) := by
      have := mul_lt_mul_of_pos_right F.S.bp_lt_dp (mul_pos (sub_pos.2 htp) (sub_pos.2 hsp1))
      nlinarith
    rw [h1, h2] at this
    linarith

/-- **K1 (a)** (`Δ > 0`): `u_W`, tilt `e_x`, rim `(m2-, xb, m2+, xa, m1-) = (6, 5, 2, 3, 4)`, rest `{v, m1+}`;
`Q5p_eventually` (the doubles `xb` over `m2+` and `v` over `m2-` are decided by the tilt; `xb` is the
maximum for `β > 0`, `m1-` for `β = 0` where `w(m1-) - w(m2-) = (A11 - A12) t > 0`). -/
theorem rimK1a (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hΔ : 0 < F.K1Delta) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have hsp' : 0 < 1 - F.S.sp := by linarith
  have ht1 : 0 < 1 - F.S.tm := by linarith
  have hA22 : F.a12 ≤ F.a22 := F.A12_le_A22
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  have p6' : F.ptC 6 = ⟨0, F.S.tm, -F.S.hm⟩ := by rw [p6, ← hts, hkm]
  refine F.rupert_rim5p 6 5 2 3 4 ⟨0, F.S.tm, -F.S.hm⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨1, 0, 0⟩
    ⟨F.S.tm, 0, -F.S.hm⟩ p6' p5 p2 p3 p4 1 (Or.inl rfl) ⟨0, 1 - F.S.sp, -F.S.kp⟩ ⟨1, 0, 0⟩
    (Or.inr (Or.inl (by linarith))) ?_ ?_ ?_
  · exact rimK1a_cyc hsp hsp1 hkp htm htm1 hhm hkc
  · intro j' h6 h5 h2 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact rimK1a_rest0 hsp hsp1 hkp htm htm1 hhm hkc i
    · rw [p1]; exact rimK1a_rest1 hsp hsp1 hkp htm htm1 hhm hkc htp htp1 hhp R i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact absurd rfl h5
    · exact absurd rfl h6
  · set Pq : ZMod 5 → C3 := quint (⟨0, F.S.tm, -F.S.hm⟩ : C3) ⟨0, 1, 0⟩ ⟨0, F.S.sp, F.S.kp⟩
      ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨0, 1 - F.S.sp, -F.S.kp⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1, 0, 0⟩ with hww
    have e0 : zz 0 = F.a22 * (1 - F.S.sp) * F.S.tm + F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a22 * (1 - F.S.sp) := by
      simp only [hzz, hPq, GG, Gf, quint_1]; ring
    have e2 : zz 2 = F.a22 * (1 - F.S.sp) * F.S.sp - F.gg * F.S.kp * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * (1 - F.S.sp) := by
      simp only [hzz, hPq, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * (1 - F.S.sp) * F.S.tm + F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_4]; ring
    have f0 : ww 0 = F.a12 * F.S.tm := by
      simp only [hww, hPq, GG, Gf, quint_0]; ring
    have f4 : ww 4 = F.a11 * F.S.tm := by
      simp only [hww, hPq, GG, Gf, quint_4]; ring
    have eΔ : F.K1Delta = F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) := rfl
    have z21 : zz 2 < zz 1 := by
      rw [e1, e2]; nlinarith [mul_pos (lt_of_lt_of_le hA0 hA22) (mul_pos hsp' hsp'),
        mul_pos hg (mul_pos hkp hkp)]
    have z34 : zz 3 < zz 4 := by rw [e3, e4]; nlinarith
    have hΔ' : 0 < F.gg * F.S.hm * F.S.kp - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) := by
      rw [eΔ] at hΔ; nlinarith
    rcases hA22.eq_or_lt with hb | hb
    · have z10 : zz 1 < zz 0 := by
        rw [e1, e0, ← hb]; nlinarith
      exact Q5p_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inl z21))))
        (Or.inr (Or.inr (Or.inr (Or.inl z34)))) (Or.inl (Or.inl z21))
        (Or.inr (Or.inl (Or.inl z34))) (Or.inr (Or.inr (Or.inl (Or.inl z10))))
    · have z40 : zz 4 < zz 0 := by
        have : zz 0 - zz 4 = (F.a22 - F.a12) * ((1 - F.S.sp) * F.S.tm) := by rw [e0, e4]; ring
        have := mul_pos (sub_pos.2 hb) (mul_pos hsp' htm)
        linarith
      exact Q5p_eventually (z := zz) (w := ww) (Or.inr (Or.inr (Or.inl (Or.inl z21))))
        (Or.inr (Or.inr (Or.inr (Or.inl z34)))) (Or.inl (Or.inl z21))
        (Or.inr (Or.inl (Or.inl z34))) (Or.inr (Or.inl (Or.inl z40)))

/-- **K1 (b)** (`Δ < 0`): `u_W`, tilt `-e_x`, rim `(v, m2+, xb, xa, m1-) = (0, 2, 5, 3, 4)`, rest `{m2-, m1+}`;
`Q5p_eventually` (maximum `xb`; `xb ≻ xa` by `z` if `β > 0`, by `w` (`= α > 0`) if `β = 0`). -/
theorem rimK1b (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hΔ : F.K1Delta < 0) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have hsp' : 0 < 1 - F.S.sp := by linarith
  have ht1 : 0 < 1 - F.S.tm := by linarith
  have hA22 : F.a12 ≤ F.a22 := F.A12_le_A22
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  have p6' : F.ptC 6 = ⟨0, F.S.tm, -F.S.hm⟩ := by rw [p6, ← hts, hkm]
  refine F.rupert_rim5p 0 2 5 3 4 ⟨0, 0, 0⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩ ⟨1, 0, 0⟩
    ⟨F.S.tm, 0, -F.S.hm⟩ p0 p2 p5 p3 p4 1 (Or.inl rfl) ⟨0, 1 - F.S.sp, -F.S.kp⟩ ⟨-1, 0, 0⟩
    (Or.inr (Or.inl (by linarith))) ?_ ?_ ?_
  · exact rimK1b_cyc hsp hsp1 hkp htm htm1 hhm hkc
  · intro j' h0 h2 h5 h3 h4 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact rimK1b_rest1 hsp hsp1 hkp htm htm1 hhm hkc htp htp1 hhp R i
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd rfl h4
    · exact absurd rfl h5
    · rw [p6']; exact rimK1b_rest6 hsp hsp1 hkp htm htm1 hhm hkc i
  · set Pq : ZMod 5 → C3 := quint (⟨0, 0, 0⟩ : C3) ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩
      ⟨1, 0, 0⟩ ⟨F.S.tm, 0, -F.S.hm⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨0, 1 - F.S.sp, -F.S.kp⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨-1, 0, 0⟩ with hww
    have e0 : zz 0 = 0 := by
      simp only [hzz, hPq, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a22 * (1 - F.S.sp) * F.S.sp - F.gg * F.S.kp * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_1]; ring
    have e2 : zz 2 = F.a22 * (1 - F.S.sp) := by
      simp only [hzz, hPq, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * (1 - F.S.sp) := by
      simp only [hzz, hPq, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * (1 - F.S.sp) * F.S.tm + F.gg * F.S.hm * F.S.kp := by
      simp only [hzz, hPq, GG, Gf, quint_4]; ring
    have eΔ : F.K1Delta = F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) := rfl
    have z12 : zz 1 < zz 2 := by
      rw [e1, e2]; nlinarith [mul_pos (lt_of_lt_of_le hA0 hA22) (mul_pos hsp' hsp'),
        mul_pos hg (mul_pos hkp hkp)]
    have z04 : zz 0 < zz 4 := by
      rw [e0, e4]; nlinarith [mul_pos (mul_pos hA0 hsp') htm, mul_pos (mul_pos hg hhm) hkp]
    have z43 : zz 4 < zz 3 := by rw [e4, e3]; rw [eΔ] at hΔ; nlinarith
    exact Q5p_eventually (z := zz) (w := ww) (Or.inl (Or.inl z04))
      (Or.inr (Or.inl (Or.inl z12))) (Or.inr (Or.inr (Or.inl (Or.inl z43))))
      (Or.inr (Or.inr (Or.inl (Or.inl z04)))) (Or.inl (Or.inl z43))

/-- **K1 (d)** (`Δ = 0`, `A12 = A22`): as `rimWpp` with `s- = t-`: `u_W`, tilt `(-1, 0, D)`,
`d+ < D < d+ A11/A12` (off one value), rim `(v, m2+, xa, m1-, m2-) = (0, 2, 3, 4, 6)`, rest `{xb, m1+}`;
`z(xa) = z(m1-) = z(m2-) = Z`, `w(m1-) - w(xa) = (1-t)(A11 - A12 D/d+) > 0`,
`w(m2-) - w(m1-) = t (A11 - A12) > 0`; max `m2-`. -/
theorem rimK1d (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hA : F.a12 = F.a22)
    (hΔ : F.K1Delta = 0) : IsRupert (Finset.univ.image x) := by
  obtain ⟨D, hD, hD3⟩ := F.exists_tilt_D hA
  exact F.rimWpp_core hA (by rw [← hdp, F.S.cm_eq_am_of_eq hts]) hdp.le (Or.inr hΔ) D hD hD3

end Frame09

/-! #### Group 3: ST tables of K1 (c) (view `u3 = (1-t, 0, h)`, tilt `(-l, 1, 0)`, `kp t = h (1-sp)`) -/

section G3
variable {t h sp kp tp hp l : ℝ}

set_option hygiene false in
macro "k1c_pre" : tactic => `(tactic| (
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have hl' : 0 < l - 1 := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  have d1 := mul_pos hl' hh
  have d2 := mul_pos hh htp
  have d3 := mul_pos hhp ht'
  have d4 := mul_pos hh hhp
  have d5 := mul_pos hl' ht'
  have d6 := mul_pos hl' hkp
  have d7 := mul_pos hl' (mul_pos hh hsp)
  have c1 := mul_pos (mul_pos hhp hsp) ht'
  have c2 := mul_pos (mul_pos htp' hsp) hh
  have c3 := mul_pos (mul_pos hhp hsp') ht
  have c4 := mul_pos (mul_pos hh htp') hsp'
  have c5 := mul_pos (mul_pos hl' hh) hsp
  have c6 := mul_pos (mul_pos hl' ht') hkp))

set_option maxHeartbeats 4000000 in
theorem rimK1c_lt_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) < tp * h) (hl : 1 < l) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have hl' : 0 < l - 1 := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  have b1 := sub_pos.2 hab
  have b2 := mul_pos hl' hh
  have b3 := mul_pos hh htp
  have b4 := mul_pos hhp ht'
  have b5 := mul_pos hh hhp
  have b6 := mul_pos hl' ht'
  have b7 := mul_pos hl' hkp
  have b8 := mul_pos hl' (mul_pos hh hsp)
  have c1 := mul_pos (mul_pos hhp hsp) ht'
  have c2 := mul_pos (mul_pos htp' hsp) hh
  obtain ⟨z0, z1, z2, z3, z4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, z0, z1, z2, z3, z4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)
    | skip

set_option maxHeartbeats 4000000 in
theorem rimK1c_lt_rest4 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) < tp * h) (hl : 1 < l) :
    ∀ i : ZMod 5,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨t, 0, -h⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := sub_pos.2 hab
  obtain ⟨z0, z1, z2, z3, z4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, z0, z1, z2, z3, z4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1c_lt_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) < tp * h) (hl : 1 < l) :
    ∀ i : ZMod 5,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, t, -h⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := sub_pos.2 hab
  obtain ⟨z0, z1, z2, z3, z4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, z0, z1, z2, z3, z4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1c_gt_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : tp * h < hp * (1 - t)) (R : hp * (1 - sp) < kp * (1 - tp)) (hl : 1 < l) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := sub_pos.2 hab
  have r1 := mul_pos (sub_pos.2 hab) hsp'
  have r2 := mul_pos (sub_pos.2 R) ht'
  obtain ⟨z0, z1, z2, z3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, z0, z1, z2, z3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1c_gt_rest (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : tp * h < hp * (1 - t)) (R : hp * (1 - sp) < kp * (1 - tp)) (hl : 1 < l) (q : C3)
    (hq : q = ⟨0, 0, 0⟩ ∨ q = ⟨t, 0, -h⟩ ∨ q = ⟨0, t, -h⟩) :
    ∀ i : ZMod 4,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        (q.sub (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := sub_pos.2 hab
  have r1 := mul_pos (sub_pos.2 hab) hsp'
  have r2 := mul_pos (sub_pos.2 R) ht'
  obtain ⟨z0, z1, z2, z3⟩ := zmod4_add_one
  intro i
  rcases hq with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, z0, z1, z2, z3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)
set_option maxHeartbeats 4000000 in
theorem rimK1c_eq5_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hpos : 0 < l * h * sp - (1 - t) * kp) (hl : 1 < l) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have ht' : 0 < 1 - t := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have hl' : 0 < l - 1 := by linarith
  have a1 := mul_pos hsp' hkp
  have a2 := mul_pos hkp hh
  have a3 := mul_pos ht hkp
  have a4 := mul_pos ht hh
  have a5 := mul_pos hsp' hh
  have a6 := mul_pos ht' hkp
  have a7 := mul_pos ht' hh
  have a8 := mul_pos hsp' ht
  have a9 := mul_pos hsp hkp
  have b1 := hpos
  have b2 := mul_pos hl' hh
  have b3 := mul_pos hh htp
  have b4 := mul_pos hhp ht'
  have b5 := mul_pos hh hhp
  have b6 := mul_pos hl' ht'
  have b7 := mul_pos hl' hkp
  have b8 := mul_pos hl' (mul_pos hh hsp)
  have c1 := mul_pos (mul_pos hhp hsp) ht'
  have c2 := mul_pos (mul_pos htp' hsp) hh
  obtain ⟨z0, z1, z2, z3, z4⟩ := zmod5_add_one
  intro i j h1 h2
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, z0, z1, z2, z3, z4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)
    | skip

set_option maxHeartbeats 4000000 in
theorem rimK1c_eq5_rest4 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hpos : 0 < l * h * sp - (1 - t) * kp) (hl : 1 < l) :
    ∀ i : ZMod 5,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨t, 0, -h⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := hpos
  obtain ⟨z0, z1, z2, z3, z4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, z0, z1, z2, z3, z4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1c_eq5_rest6 (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hpos : 0 < l * h * sp - (1 - t) * kp) (hl : 1 < l) :
    ∀ i : ZMod 5,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((⟨0, t, -h⟩ : C3).sub (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := hpos
  obtain ⟨z0, z1, z2, z3, z4⟩ := zmod5_add_one
  intro i
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, z0, z1, z2, z3, z4, quint_0, quint_1, quint_2, quint_3, quint_4]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1c_eq4_cyc (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hneg : l * h * sp - (1 - t) * kp < 0) (R : hp * (1 - sp) < kp * (1 - tp)) (hl : 1 < l) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := sub_pos.2 hneg
  have r2 := mul_pos (sub_pos.2 R) ht'
  obtain ⟨z0, z1, z2, z3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, z0, z1, z2, z3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

set_option maxHeartbeats 4000000 in
theorem rimK1c_eq4_rest (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hneg : l * h * sp - (1 - t) * kp < 0) (R : hp * (1 - sp) < kp * (1 - tp)) (hl : 1 < l) (q : C3)
    (hq : q = ⟨0, 0, 0⟩ ∨ q = ⟨t, 0, -h⟩ ∨ q = ⟨0, t, -h⟩) :
    ∀ i : ZMod 4,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        (q.sub (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)) := by
  k1c_pre
  have e1 := sub_pos.2 hneg
  have r2 := mul_pos (sub_pos.2 R) ht'
  obtain ⟨z0, z1, z2, z3⟩ := zmod4_add_one
  intro i
  rcases hq with rfl | rfl | rfl <;>
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, z0, z1, z2, z3, quad_0, quad_1, quad_2, quad_3]
    first
    | (left; nlinarith)
    | (right; refine ⟨by nlinarith, by nlinarith⟩)

/-- The five-corner ST tables of K1 (c): rim `(v, m1+, xa, xb, m2+)`, rest `{m1-, m2-}`. -/
def K1c5ST (t h sp kp tp hp l : ℝ) : Prop :=
  (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))) ∧
  (∀ q : C3, (q = ⟨t, 0, -h⟩ ∨ q = ⟨0, t, -h⟩) → ∀ i : ZMod 5,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        (q.sub (quint (⟨0, 0, 0⟩ : C3) ⟨tp, 0, hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)))

/-- The four-corner ST tables of K1 (c): rim `(m1+, xa, xb, m2+)`, rest `{v, m1-, m2-}`. -/
def K1c4ST (t h sp kp tp hp l : ℝ) : Prop :=
  (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ j).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))) ∧
  (∀ q : C3, (q = ⟨0, 0, 0⟩ ∨ q = ⟨t, 0, -h⟩ ∨ q = ⟨0, t, -h⟩) → ∀ i : ZMod 4,
      ST 1 ⟨1 - t, 0, h⟩ ⟨-l, 1, 0⟩
        ((quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ (i + 1)).sub
          (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i))
        (q.sub (quad (⟨tp, 0, hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩ ⟨0, sp, kp⟩ i)))


theorem k1c_lt_ST (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) < tp * h) (hl : 1 < l) : K1c5ST t h sp kp tp hp l :=
  ⟨rimK1c_lt_cyc hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hl,
   fun q hq => by
     rcases hq with rfl | rfl
     · exact rimK1c_lt_rest4 hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hl
     · exact rimK1c_lt_rest6 hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hl⟩

theorem k1c_eq5_ST (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hpos : 0 < l * h * sp - (1 - t) * kp) (hl : 1 < l) : K1c5ST t h sp kp tp hp l :=
  ⟨rimK1c_eq5_cyc hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hpos hl,
   fun q hq => by
     rcases hq with rfl | rfl
     · exact rimK1c_eq5_rest4 hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hpos hl
     · exact rimK1c_eq5_rest6 hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hpos hl⟩

theorem k1c_gt_ST (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : tp * h < hp * (1 - t)) (R : hp * (1 - sp) < kp * (1 - tp)) (hl : 1 < l) : K1c4ST t h sp kp tp hp l :=
  ⟨rimK1c_gt_cyc hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab R hl,
   fun q hq => rimK1c_gt_rest hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab R hl q hq⟩

theorem k1c_eq4_ST (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp) (ht : 0 < t) (ht1 : t < 1)
    (hh : 0 < h) (hkc : kp * t = h * (1 - sp)) (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hab : hp * (1 - t) = tp * h) (hneg : l * h * sp - (1 - t) * kp < 0) (R : hp * (1 - sp) < kp * (1 - tp)) (hl : 1 < l) : K1c4ST t h sp kp tp hp l :=
  ⟨rimK1c_eq4_cyc hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hneg R hl,
   fun q hq => rimK1c_eq4_rest hsp hsp1 hkp ht ht1 hh hkc htp htp1 hhp hab hneg R hl q hq⟩

end G3

/-! ### Group 3: Theorem K1 (c), `Δ = 0`, `A12 < A22`, the edge view `u3 = xa - m1- = (1 - t, 0, h)`

Tilt `d = (-λ, 1, 0)`, `1 < λ < A22/A12`, off the finitely many bad values (`exists_Ioo_avoid`).
`z(xb) = z(m2+) = A12(1-t)` (a tie at order 0, broken by `w(xb) - w(m2+) = (A22 - λ A12)(1 - s+) > 0`),
`z(xa) = A11(1-t)`, `m1+ ≺ xa`, `v ≺ m2+`; the maximum is the larger of `xa, xb`. -/

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- Core of the five-corner rim of K1 (c): given the ST tables, the depths work for any tilt
`1 < l < A22/A12` (`z(m2+) = z(xb)` is a tie broken by `w`). -/
theorem k1c_core5 (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hΔ : F.K1Delta = 0)
    (l : ℝ) (hl1 : 1 < l) (hl2 : l * F.a12 < F.a22)
    (hST : K1c5ST F.S.tm F.S.hm F.S.sp F.S.kp F.S.tp F.S.hp l) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hkp := F.S.kp_pos
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt; have hhm := F.S.hm_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have hsp' : 0 < 1 - F.S.sp := by linarith
  have ht1 : 0 < 1 - F.S.tm := by linarith
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  have p6' : F.ptC 6 = ⟨0, F.S.tm, -F.S.hm⟩ := by rw [p6, ← hts, hkm]
  obtain ⟨hc, hr⟩ := hST
  refine F.rupert_rim5p 0 1 3 5 2 ⟨0, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩
    ⟨0, F.S.sp, F.S.kp⟩ p0 p1 p3 p5 p2 1 (Or.inl rfl) ⟨1 - F.S.tm, 0, F.S.hm⟩ ⟨-l, 1, 0⟩
    (Or.inl ht1.ne') hc ?_ ?_
  · intro j' h0 h1 h3 h5 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · rw [p4]; exact hr _ (Or.inl rfl) i
    · exact absurd rfl h5
    · rw [p6']; exact hr _ (Or.inr rfl) i
  · set Pq : ZMod 5 → C3 := quint (⟨0, 0, 0⟩ : C3) ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩
      ⟨0, F.S.sp, F.S.kp⟩ with hPq
    set zz : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨1 - F.S.tm, 0, F.S.hm⟩ with hzz
    set ww : ZMod 5 → ℝ := fun i => F.GG (Pq i) ⟨-l, 1, 0⟩ with hww
    have e0 : zz 0 = 0 := by simp only [hzz, hPq, GG, Gf, quint_0]; ring
    have e1 : zz 1 = F.a11 * F.S.tp * (1 - F.S.tm) + F.gg * F.S.hp * F.S.hm := by
      simp only [hzz, hPq, GG, Gf, quint_1]; ring
    have e2 : zz 2 = F.a11 * (1 - F.S.tm) := by simp only [hzz, hPq, GG, Gf, quint_2]; ring
    have e3 : zz 3 = F.a12 * (1 - F.S.tm) := by simp only [hzz, hPq, GG, Gf, quint_3]; ring
    have e4 : zz 4 = F.a12 * F.S.sp * (1 - F.S.tm) + F.gg * F.S.kp * F.S.hm := by
      simp only [hzz, hPq, GG, Gf, quint_4]; ring
    have f3 : ww 3 = F.a22 - l * F.a12 := by simp only [hww, hPq, GG, Gf, quint_3]; ring
    have f4 : ww 4 = (F.a22 - l * F.a12) * F.S.sp := by
      simp only [hww, hPq, GG, Gf, quint_4]; ring
    have hΔ' : F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) = 0 := hΔ
    have z43 : zz 4 = zz 3 := by rw [e3, e4]; linear_combination hΔ'
    have z04 : zz 0 < zz 4 := by rw [z43, e0, e3]; exact mul_pos hA0 ht1
    have w43 : ww 4 < ww 3 := by
      rw [f3, f4]; nlinarith [sub_pos.2 hl2]
    have z12 : zz 1 < zz 2 := by
      have h1 : F.S.kp * (zz 2 - zz 1) = (1 - F.S.tm) *
          (F.a11 * (F.S.kp * (1 - F.S.tp)) - F.a12 * (F.S.hp * (1 - F.S.sp))) := by
        rw [e2, e1]; linear_combination (-F.S.hp) * hΔ'
      have h2 : 0 < F.a11 * (F.S.kp * (1 - F.S.tp)) - F.a12 * (F.S.hp * (1 - F.S.sp)) := by
        have := sub_pos.2 R
        have h3 : 0 < F.S.kp * (1 - F.S.tp) := mul_pos hkp (sub_pos.2 F.S.tp_lt)
        nlinarith [mul_nonneg (sub_nonneg.2 hA11) h3.le, mul_pos hA0 this]
      have := mul_pos ht1 h2
      rw [← h1] at this
      have := (mul_pos_iff_of_pos_left hkp).1 this
      linarith
    exact Q5p_eventually (z := zz) (w := ww) (Or.inl (Or.inl z04))
      (Or.inr (Or.inl (Or.inl z12))) (Or.inr (Or.inr (Or.inl (Or.inr ⟨z43, w43⟩))))
      (Or.inr (Or.inr (Or.inl (Or.inl z04)))) (Or.inl (Or.inr ⟨z43, w43⟩))

/-- Core of the four-corner rim of K1 (c). -/
theorem k1c_core4 (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hΔ : F.K1Delta = 0)
    (l : ℝ) (hl1 : 1 < l) (hl2 : l * F.a12 < F.a22)
    (hST : K1c4ST F.S.tm F.S.hm F.S.sp F.S.kp F.S.tp F.S.hp l) :
    IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hkp := F.S.kp_pos
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt; have hhm := F.S.hm_pos
  have hg : 0 < F.gg := F.g_pos
  have hA0 : 0 < F.a12 := F.A12_pos
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have hsp' : 0 < 1 - F.S.sp := by linarith
  have ht1 : 0 < 1 - F.S.tm := by linarith
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  have p6' : F.ptC 6 = ⟨0, F.S.tm, -F.S.hm⟩ := by rw [p6, ← hts, hkm]
  obtain ⟨hc, hr⟩ := hST
  refine F.rupert_rim4 1 3 5 2 ⟨F.S.tp, 0, F.S.hp⟩ ⟨1, 0, 0⟩ ⟨0, 1, 0⟩
    ⟨0, F.S.sp, F.S.kp⟩ p1 p3 p5 p2 1 (Or.inl rfl) ⟨1 - F.S.tm, 0, F.S.hm⟩ ⟨-l, 1, 0⟩
    (Or.inl ht1.ne') hc ?_ ?_
  · intro j' h1 h3 h5 h2 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact hr _ (Or.inl rfl) i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3
    · rw [p4]; exact hr _ (Or.inr (Or.inl rfl)) i
    · exact absurd rfl h5
    · rw [p6']; exact hr _ (Or.inr (Or.inr rfl)) i
  · set Pq : ZMod 4 → C3 := quad (⟨F.S.tp, 0, F.S.hp⟩ : C3) ⟨1, 0, 0⟩ ⟨0, 1, 0⟩
      ⟨0, F.S.sp, F.S.kp⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨1 - F.S.tm, 0, F.S.hm⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.GG (Pq i) ⟨-l, 1, 0⟩ with hww
    have e0 : zz 0 = F.a11 * F.S.tp * (1 - F.S.tm) + F.gg * F.S.hp * F.S.hm := by
      simp only [hzz, hPq, GG, Gf, quad_0]; ring
    have e1 : zz 1 = F.a11 * (1 - F.S.tm) := by simp only [hzz, hPq, GG, Gf, quad_1]; ring
    have e2 : zz 2 = F.a12 * (1 - F.S.tm) := by simp only [hzz, hPq, GG, Gf, quad_2]; ring
    have e3 : zz 3 = F.a12 * F.S.sp * (1 - F.S.tm) + F.gg * F.S.kp * F.S.hm := by
      simp only [hzz, hPq, GG, Gf, quad_3]; ring
    have f2 : ww 2 = F.a22 - l * F.a12 := by simp only [hww, hPq, GG, Gf, quad_2]; ring
    have f3 : ww 3 = (F.a22 - l * F.a12) * F.S.sp := by
      simp only [hww, hPq, GG, Gf, quad_3]; ring
    have hΔ' : F.gg * F.S.kp * F.S.hm - F.a12 * (1 - F.S.sp) * (1 - F.S.tm) = 0 := hΔ
    have z32 : zz 3 = zz 2 := by rw [e2, e3]; linear_combination hΔ'
    have w32 : ww 3 < ww 2 := by
      rw [f2, f3]; nlinarith [sub_pos.2 hl2]
    have z01 : zz 0 < zz 1 := by
      have h1 : F.S.kp * (zz 1 - zz 0) = (1 - F.S.tm) *
          (F.a11 * (F.S.kp * (1 - F.S.tp)) - F.a12 * (F.S.hp * (1 - F.S.sp))) := by
        rw [e1, e0]; linear_combination (-F.S.hp) * hΔ'
      have h2 : 0 < F.a11 * (F.S.kp * (1 - F.S.tp)) - F.a12 * (F.S.hp * (1 - F.S.sp)) := by
        have := sub_pos.2 R
        have h3 : 0 < F.S.kp * (1 - F.S.tp) := mul_pos hkp (sub_pos.2 F.S.tp_lt)
        nlinarith [mul_nonneg (sub_nonneg.2 hA11) h3.le, mul_pos hA0 this]
      have := mul_pos ht1 h2
      rw [← h1] at this
      have := (mul_pos_iff_of_pos_left hkp).1 this
      linarith
    exact Q4_eventually (z := zz) (w := ww) (Or.inl (Or.inl z01))
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨z32, w32⟩))))

/-- Choice of the tilt `1 < l < A22/A12` avoiding one value. -/
theorem k1c_tilt (hA : F.a12 < F.a22) (b : ℝ) :
    ∃ l : ℝ, 1 < l ∧ l * F.a12 < F.a22 ∧ l ≠ b := by
  have hA0 : 0 < F.a12 := F.A12_pos
  have : (1 : ℝ) < F.a22 / F.a12 := by rw [lt_div_iff₀ hA0]; linarith
  obtain ⟨l, h1, h2, h3, -⟩ := exists_Ioo_avoid this b b
  exact ⟨l, h1, by rwa [lt_div_iff₀ hA0] at h2, h3⟩

theorem k1c_hab_lt (h : F.S.ap < F.S.bm) : F.S.hp * (1 - F.S.tm) < F.S.tp * F.S.hm := by
  have h1 := mul_lt_mul_of_pos_right h (mul_pos F.S.tp_pos (sub_pos.2 F.S.tm_lt))
  have e1 := F.S.ap_mul; have e2 := F.S.bm_mul
  have q1 : F.S.hp * (1 - F.S.tm) = F.S.ap * (F.S.tp * (1 - F.S.tm)) := by
    linear_combination (-(1 - F.S.tm)) * e1
  have q2 : F.S.tp * F.S.hm = F.S.bm * (F.S.tp * (1 - F.S.tm)) := by
    linear_combination (-F.S.tp) * e2
  rw [q1, q2]; exact h1

theorem k1c_hab_gt (h : F.S.bm < F.S.ap) : F.S.tp * F.S.hm < F.S.hp * (1 - F.S.tm) := by
  have h1 := mul_lt_mul_of_pos_right h (mul_pos F.S.tp_pos (sub_pos.2 F.S.tm_lt))
  have e1 := F.S.ap_mul; have e2 := F.S.bm_mul
  have q1 : F.S.hp * (1 - F.S.tm) = F.S.ap * (F.S.tp * (1 - F.S.tm)) := by
    linear_combination (-(1 - F.S.tm)) * e1
  have q2 : F.S.tp * F.S.hm = F.S.bm * (F.S.tp * (1 - F.S.tm)) := by
    linear_combination (-F.S.tp) * e2
  rw [q1, q2]; exact h1

theorem k1c_hab_eq (h : F.S.ap = F.S.bm) : F.S.hp * (1 - F.S.tm) = F.S.tp * F.S.hm := by
  have e1 := F.S.ap_mul; have e2 := F.S.bm_mul
  rw [h] at e1
  linear_combination (-(1 - F.S.tm)) * e1 + F.S.tp * e2

/-- **K1 (c), `a+ < b-`**: rim `(v, m1+, xa, xb, m2+) = (0, 1, 3, 5, 2)`, rest `{m1-, m2-}`;
`Q5p_eventually` (the pair `(m1+, m2+)` may tie in `z`; `w(m1+) - w(m2+)` is affine in `λ`, not
identically zero since `A12² ≠ A11 A22`: avoid its root). -/
theorem rimK1c_lt (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hA : F.a12 < F.a22)
    (hΔ : F.K1Delta = 0) (hab : F.S.ap < F.S.bm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hkp := F.S.kp_pos
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have hhp := F.S.hp_pos
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt; have hhm := F.S.hm_pos
  obtain ⟨l, hl1, hl2, -⟩ := F.k1c_tilt hA 0
  exact F.k1c_core5 hts hdp hΔ l hl1 hl2
    (k1c_lt_ST hsp hsp1 hkp htm htm1 hhm hkc htp htp1 hhp (F.k1c_hab_lt hab) hl1)

/-- **K1 (c), `a+ > b-`**: rim `(m1+, xa, xb, m2+) = (1, 3, 5, 2)`, rest `{v, m1-, m2-}`; `rupert_rim4`,
`Q4_eventually`. -/
theorem rimK1c_gt (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hA : F.a12 < F.a22)
    (hΔ : F.K1Delta = 0) (hab : F.S.bm < F.S.ap) : IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hkp := F.S.kp_pos
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have hhp := F.S.hp_pos
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt; have hhm := F.S.hm_pos
  obtain ⟨l, hl1, hl2, -⟩ := F.k1c_tilt hA 0
  exact F.k1c_core4 hts hdp hΔ l hl1 hl2
    (k1c_gt_ST hsp hsp1 hkp htm htm1 hhm hkc htp htp1 hhp (F.k1c_hab_gt hab) R hl1)

/-- **K1 (c), `a+ = b-`**: `m1+` is a double over the corner `v`; with `p = (h+/h)(λ h s+ - (1-t)k+)`
(`λ` chosen off the root) the rim is `(v, m1+, xa, xb, m2+)` if `p > 0` and `(m1+, xa, xb, m2+)` if
`p < 0`.  Proof: choose `λ`, split on the sign of `λ h s+ - (1-t) k+`, reuse the generic rim
lemmas of the two other cases (state them over reals with `ap`, `bm` as parameters if needed). -/
theorem rimK1c_eq (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) (hA : F.a12 < F.a22)
    (hΔ : F.K1Delta = 0) (hab : F.S.ap = F.S.bm) : IsRupert (Finset.univ.image x) := by
  obtain ⟨hkm, hkc, R⟩ := F.k1_facts hts hdp
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hkp := F.S.kp_pos
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have hhp := F.S.hp_pos
  have htm := F.S.tm_pos; have htm1 := F.S.tm_lt; have hhm := F.S.hm_pos
  have hab' := F.k1c_hab_eq hab
  obtain ⟨l, hl1, hl2, hlb⟩ := F.k1c_tilt hA ((1 - F.S.tm) * F.S.kp / (F.S.hm * F.S.sp))
  have hne : l * F.S.hm * F.S.sp - (1 - F.S.tm) * F.S.kp ≠ 0 := by
    intro h0
    apply hlb
    rw [eq_div_iff (mul_pos hhm hsp).ne']
    linarith
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact F.k1c_core4 hts hdp hΔ l hl1 hl2
      (k1c_eq4_ST hsp hsp1 hkp htm htm1 hhm hkc htp htp1 hhp hab' (by linarith) R hl1)
  · exact F.k1c_core5 hts hdp hΔ l hl1 hl2
      (k1c_eq5_ST hsp hsp1 hkp htm htm1 hhm hkc htp htp1 hhp hab' (by linarith) hl1)

end Frame09

/-! ### Group 4: Theorem K2 (`a- = b+ ∧ b+ = s+A2`): test `T1'` (the new one; `T2` is `rimT2_sector`) -/

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
/-- ST table (cycle) of `T1'` (bare reals; tilt `e_y`, `σ = -1`, rim `(m1-, xa, m1+, m2+, xb, m2-)`). -/
theorem t1pST_cyc {tm hm tp hp sp kp sm km : ℝ} (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp)
    (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hH : hp * tm = (1 - tp) * hm) (hE : tm * kp < hm) (hD : hm * (1 - sp) < tm * kp) (hts : tm < sm)
    :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ i))
        ((hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ j).sub
          (hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have q2 := sub_pos.2 hE
  have q3 := sub_pos.2 hts
  have q4 := sub_pos.2 hD
  have a16 := mul_pos hsm q4
  have a17 := mul_pos hsp q4
  have a18 := mul_pos htm q4
  have a1 := mul_pos htm hkp
  have a2 := mul_pos htm hkm
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos hsp hhm
  have a5 := mul_pos htm hhp
  have a6 := mul_pos htp hhm
  have a7 := mul_pos hsp q2
  have a8 := mul_pos hsm q2
  have a9 := mul_pos htm q2
  have a10 := mul_pos htm hsp
  have a11 := mul_pos htm hsm
  have a12 := mul_pos hsp' hhm
  have a13 := mul_pos hsm' hhm
  have a14 := mul_pos hkm htm'
  have a15 := mul_pos htp' hhm
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i j h1 h2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring1, by nlinarith⟩)
    | (right; refine ⟨by linear_combination hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (-1 : ℝ) * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (1 - sp) * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (sp - 1) * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination sp * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (-sp) * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (1 - sm) * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (sm - 1) * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination sm * hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (-sm) * hH, by nlinarith⟩)

set_option linter.unusedTactic false in
theorem t1pST_rest {tm hm tp hp sp kp sm km : ℝ} (hsp : 0 < sp) (hsp1 : sp < 1) (hkp : 0 < kp)
    (htm : 0 < tm) (htm1 : tm < 1) (hhm : 0 < hm) (hsm : 0 < sm) (hsm1 : sm < 1) (hkm : 0 < km)
    (htp : 0 < tp) (htp1 : tp < 1) (hhp : 0 < hp)
    (hH : hp * tm = (1 - tp) * hm) (hE : tm * kp < hm) (hD : hm * (1 - sp) < tm * kp)
    (hts : tm < sm) :
    ∀ i : ZMod 6,
      ST (-1) ⟨tm, 0, -hm⟩ ⟨0, 1, 0⟩
        ((hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ (i + 1)).sub
          (hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ i))
        ((⟨0, 0, 0⟩ : C3).sub
          (hex6 (⟨tm, 0, -hm⟩ : C3) ⟨1, 0, 0⟩ ⟨tp, 0, hp⟩ ⟨0, sp, kp⟩ ⟨0, 1, 0⟩ ⟨0, sm, -km⟩ i)) := by
  have hsp' : 0 < 1 - sp := by linarith
  have hsm' : 0 < 1 - sm := by linarith
  have htm' : 0 < 1 - tm := by linarith
  have htp' : 0 < 1 - tp := by linarith
  have q2 := sub_pos.2 hE
  have q3 := sub_pos.2 hts
  have a1 := mul_pos htm hkp
  have a2 := mul_pos htm hkm
  have a3 := mul_pos hsm hhm
  have a4 := mul_pos hsp hhm
  have a5 := mul_pos htm hhp
  have a6 := mul_pos htp hhm
  have a7 := mul_pos hsp q2
  have a10 := mul_pos htm hsp
  have a11 := mul_pos htm hsm
  have a12 := mul_pos hsp' hhm
  have a15 := mul_pos htp' hhm
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := zmod6_add_one
  intro i
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [ST, Dc, C3.sub, b0, b1, b2, b3, b4, b5, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5]
    first
    | (left; nlinarith)
    | (right; refine ⟨by ring1, by nlinarith⟩)
    | (right; refine ⟨by linear_combination hH, by nlinarith⟩)
    | (right; refine ⟨by linear_combination (-1 : ℝ) * hH, by nlinarith⟩)



namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **K2's `T1'`** (§40.4.2): view `u1 = m1- - v = (t-, 0, -h-)`, tilt `e_y`, the six-corner rim
`(m1-, m2-, xb, m2+, m1+, xa)` in the paper's ccw order, i.e. `(4, 3, 1, 2, 5, 6)` with `σ = -1`
(the reversed order, as `t1P` in `CaseC09Rims.lean` with `m1+` between `xa` and `m2+`), rest `{v}`
(`v = m1- - u1` is hidden, `m1+ = xa + h' u1` is a shown double); robust: `rupert_rim_rob` (k = 6)
with `robust_cycT1p`.  Depths: `z(m1-) = A11 t-² + g h-²`, `z(m2-) = A12 t- s- + g h- k-`,
`z(xb) = A12 t-`, `z(m2+) = A12 t- s+ - g h- k+`, `z(xa) = A11 t-`, `z(m1+) = z(xa) + h' ⟨u1,u1⟩_G < z(xa)`.
Hypothesis `hS` is `g h- k- > A12 t-(1 - s-)`; `hts` is `t- < s-`. -/
theorem rimK2T1p (H1 : F.S.am = F.S.bp) (H2 : F.S.bp = F.S.sp * F.S.A2) (hts : F.S.tm < F.S.sm)
    (hS : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km) :
    IsRupert (Finset.univ.image x) := by
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkp := F.S.kp_pos; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hhm := F.S.hm_pos; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt; have hkm := F.S.km_pos
  have hA : 0 < F.a12 := F.A12_pos
  have hA11 : F.a12 ≤ F.a11 := F.A12_le_A11
  have hg : 0 < F.gg := F.g_pos
  have hcm : 0 < F.S.cm := by unfold Shape09.cm; exact div_pos hkm hsm
  have hH : F.S.hp * F.S.tm = (1 - F.S.tp) * F.S.hm := by
    have e1 := F.S.bp_mul; have e2 := F.S.am_mul
    rw [← H1] at e1
    rw [← e1, ← e2]; ring
  have hmeq : F.S.hm = F.S.tm * (F.S.kp + F.S.sp * F.S.cm) := by
    have e2 := F.S.am_mul
    have h3 : F.S.bp = F.S.kp + F.S.sp * F.S.cm := by rw [H2, F.S.sp_A2]
    rw [← e2, H1, h3]; ring
  have hE : F.S.tm * F.S.kp < F.S.hm := by
    rw [hmeq]; nlinarith [mul_pos (mul_pos htm hsp) hcm]
  have hD : F.S.hm * (1 - F.S.sp) < F.S.tm * F.S.kp := by
    have e2 := F.S.am_mul; have e3 := F.S.dp_mul
    have hr := F.S.bp_lt_dp
    rw [← H1] at hr
    have : F.S.am * F.S.tm * (1 - F.S.sp) < F.S.dp * (1 - F.S.sp) * F.S.tm := by
      have := mul_lt_mul_of_pos_right hr (mul_pos htm (sub_pos.2 hsp1))
      nlinarith
    rw [e2, e3] at this; linarith
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := F.ptC_pts
  let c : ZMod 6 → Fin 7 := ![4, 3, 1, 2, 5, 6]
  have hc : ∀ i, F.ptC (c i) =
      hex6 (⟨F.S.tm, 0, -F.S.hm⟩ : C3) ⟨1, 0, 0⟩ ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, F.S.sp, F.S.kp⟩ ⟨0, 1, 0⟩
        ⟨0, F.S.sm, -F.S.km⟩ i := by
    intro i
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [c, hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, p4, p3, p1, p2, p5, p6]
  refine F.rupert_rim_rob (k := 6) (by norm_num) c (-1) (Or.inr rfl)
    ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 1, 0⟩ (Or.inl (ne_of_gt htm)) ?_ ?_ ?_
  · intro i j h1 h2
    simp only [hc]
    exact t1pST_cyc hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm htp htp1 hhp hH hE hD hts i j h1 h2
  · intro j' hj' i
    simp only [hc]
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p0]; exact t1pST_rest hsp hsp1 hkp htm htm1 hhm hsm hsm1 hkm htp htp1 hhp hH hE hD hts i
    · exact absurd rfl (hj' 2)
    · exact absurd rfl (hj' 3)
    · exact absurd rfl (hj' 1)
    · exact absurd rfl (hj' 0)
    · exact absurd rfl (hj' 4)
    · exact absurd rfl (hj' 5)
  · have hz : ∀ i, F.GG (F.ptC (c i)) ⟨F.S.tm, 0, -F.S.hm⟩ = ![
        F.a11 * F.S.tm * F.S.tm + F.gg * F.S.hm * F.S.hm, F.a11 * F.S.tm,
        F.a11 * F.S.tp * F.S.tm - F.gg * F.S.hp * F.S.hm,
        F.a12 * F.S.tm * F.S.sp - F.gg * F.S.hm * F.S.kp, F.a12 * F.S.tm,
        F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km] i := by
      intro i
      rw [hc]
      rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hex6_0, hex6_1, hex6_2, hex6_3, hex6_4, hex6_5, GG, Gf] <;> simp <;> ring
    have hz' : (fun i => F.GG (F.ptC (c i)) ⟨F.S.tm, 0, -F.S.hm⟩) = fun i : ZMod 6 => ![
        F.a11 * F.S.tm * F.S.tm + F.gg * F.S.hm * F.S.hm, F.a11 * F.S.tm,
        F.a11 * F.S.tp * F.S.tm - F.gg * F.S.hp * F.S.hm,
        F.a12 * F.S.tm * F.S.sp - F.gg * F.S.hm * F.S.kp, F.a12 * F.S.tm,
        F.a12 * F.S.tm * F.S.sm + F.gg * F.S.hm * F.S.km] i := funext hz
    rw [hz']
    have hz40 := t1_z4_lt_z0 (g := F.gg) hA hA11 htm htm1 hsm1 hts hhm F.Km_eq hS
    have m1 := mul_pos hA htm
    have m2 := mul_pos hg hhm
    have m3 := mul_pos m2 hkp
    have m4 := mul_pos m1 hsp
    have m5 := mul_pos (mul_pos hg hhp) hhm
    have m6 := mul_nonneg (mul_nonneg hA.le htm.le) (sub_nonneg.2 hA11)
    refine robust_cycT1p ?_ ?_ ?_ (Or.inr ?_)
    · nlinarith [mul_pos (mul_pos (by linarith : 0 < F.a11) htm) (sub_pos.2 htp1)]
    · nlinarith [mul_pos m1 (sub_pos.2 hsp1)]
    · nlinarith
    · nlinarith
end Frame09

/-! ### The case tree (proved from the pieces above) -/

namespace Frame09
variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- **Theorem K2** (§40.4): every shape on `a- = b+ ∧ b+ = s+A2` is Rupert (`T2 = rimT2_sector` or
`T1' = rimK2T1p`; the failures `g h- k- ≥ A12 s-(1-t-)` and `g h- k- ≤ A12 t-(1-s-)` contradict `t- < s-`). -/
theorem rupert_K2 (H1 : F.S.am = F.S.bp) (H2 : F.S.bp = F.S.sp * F.S.A2) :
    IsRupert (Finset.univ.image x) := by
  have hts := F.S.tm_lt_sm_of_K2 H1 H2
  have H4 := F.S.cm_lt_dp_of_K2 H1 H2
  have hA : 0 < F.a12 := F.A12_pos
  by_cases hS : F.a12 * F.S.tm * (1 - F.S.sm) < F.gg * F.S.hm * F.S.km
  · exact F.rimK2T1p H1 H2 hts hS
  · refine F.rimT2_sector H2 H4 ?_
    have h1 := not_lt.1 hS
    have hh := F.S.hm_pos; have hsm1 := F.S.sm_lt; have htm1 := F.S.tm_lt
    have hq : F.a12 * (F.S.sm * (1 - F.S.tm) - F.S.tm * (1 - F.S.sm)) > 0 := by
      have : F.S.sm * (1 - F.S.tm) - F.S.tm * (1 - F.S.sm) = F.S.sm - F.S.tm := by ring
      rw [this]; exact mul_pos hA (sub_pos.2 hts)
    nlinarith

/-- **Theorem K1** (§40.3): every frame shape on `t- = s- ∧ a- = d+` is Rupert at its metric. -/
theorem rupert_K1 (hts : F.S.tm = F.S.sm) (hdp : F.S.am = F.S.dp) :
    IsRupert (Finset.univ.image x) := by
  rcases lt_trichotomy F.K1Delta 0 with hΔ | hΔ | hΔ
  · exact F.rimK1b hts hdp hΔ
  · rcases F.A12_le_A22.lt_or_eq with hA | hA
    · rcases lt_trichotomy F.S.ap F.S.bm with hab | hab | hab
      · exact F.rimK1c_lt hts hdp hA hΔ hab
      · exact F.rimK1c_eq hts hdp hA hΔ hab
      · exact F.rimK1c_gt hts hdp hA hΔ hab
    · exact F.rimK1d hts hdp hA hΔ
  · exact F.rimK1a hts hdp hΔ

/-- **Theorem 09.6' (A12 = A22)**, off `K1`: `W` (`d+ > c-`), `T2'` (`d+ < c-`), and on `d+ = c-`:
`27.57` (`Q3456`) if `t- < s-`, `W″` if `s- < t-` (`t- = s-` would be `K1`). -/
theorem rupert_a12_eq_a22 (hx : Function.Injective x) (hA : F.a12 = F.a22)
    (hK1 : ¬ (F.S.tm = F.S.sm ∧ F.S.am = F.S.dp)) : IsRupert (Finset.univ.image x) := by
  rcases lt_trichotomy F.S.dp F.S.cm with h | h | h
  · exact F.rimT2p hA h
  · rcases lt_trichotomy F.S.tm F.S.sm with hts | hts | hts
    · have had : F.S.dp < F.S.am := by rw [h]; exact F.S.cm_lt_am hts
      exact F.rupert_of_Q3456 hx (F.S.q3456_of_lt hts had)
    · exact absurd ⟨hts, by rw [h, F.S.cm_eq_am_of_eq hts]⟩ hK1
    · exact F.rimWpp hA h hts
  · refine F.rimW h ?_
    have h0 : 0 < F.a12 := F.A12_pos
    have := F.S.sp_lt
    rw [← hA]; nlinarith

end Frame09

/-- **The special positions of type 09's acute case (c) are Rupert.**  Closes the type-09 branch of the skeleton:
(`exact hN.2 (CaseC09Special.isRupert hx hrest)`). -/
theorem CaseC09Special.isRupert {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (h : CaseC09Special x) : IsRupert (Finset.univ.image x) := by
  obtain ⟨F, hK1 | hA | hK2⟩ := h
  · exact F.rupert_K1 hK1.1 hK1.2
  · by_cases hK1 : F.S.tm = F.S.sm ∧ F.S.am = F.S.dp
    · exact F.rupert_K1 hK1.1 hK1.2
    · exact F.rupert_a12_eq_a22 hx hA hK1
  · exact F.rupert_K2 hK2.1 hK2.2

end Minimality.CaseC09
