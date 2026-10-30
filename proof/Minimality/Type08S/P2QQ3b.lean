module

public import Minimality.Type08S.P2QQ3a

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkQ / Q3b: W copies of the G3p part-C pieces (`crimA2`, `seg08`, `impQ_*`, `impK_T4`, `rupert_of_free_limit_rim`, ...)
on `Norm08w` (recipe of packages.md).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W

theorem det_nf08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    det3 (a - d) (b - d) (c - d) ≠ 0 := by
  have := N.hd.det_Qac_ne
  intro h; apply this
  simp only [det3_expand, PiLp.sub_apply] at h ⊢
  linarith

set_option maxHeartbeats 4000000 in
theorem seg08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) :
    let x := pts08 a a' b b' c c' d
    (∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 → x m ≠ x i + s • (x j - x i)) ∧
    ∃ i j l m : Fin 7, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0 := by
  intro x
  refine ⟨?_, 6, 0, 2, 4, by simpa [x, pts08] using det_nf08 N⟩
  have hd := N.hd
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have f1_0 : N.F.abc'.f a = 0 := N.F.abc'.hP
  have f1_1 : N.F.abc'.f a' < 0 := N.F.abc'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_2 : N.F.abc'.f b = 0 := N.F.abc'.hQ
  have f1_3 : N.F.abc'.f b' < 0 := N.F.abc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_4 : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f1_5 : N.F.abc'.f c' = 0 := N.F.abc'.hR
  have f1_6 : N.F.abc'.f d = 0 := hd.abc'
  have f2_0 : N.F.ab'c.f a = 0 := N.F.ab'c.hP
  have f2_1 : N.F.ab'c.f a' < 0 := N.F.ab'c.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_2 : N.F.ab'c.f b < 0 := N.F.ab'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_3 : N.F.ab'c.f b' = 0 := N.F.ab'c.hQ
  have f2_4 : N.F.ab'c.f c = 0 := N.F.ab'c.hR
  have f2_5 : N.F.ab'c.f c' < 0 := N.F.ab'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f2_6 : N.F.ab'c.f d = 0 := hd.ab'c
  have f3_0 : N.F.a'bc.f a < 0 := N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_1 : N.F.a'bc.f a' = 0 := N.F.a'bc.hP
  have f3_2 : N.F.a'bc.f b = 0 := N.F.a'bc.hQ
  have f3_3 : N.F.a'bc.f b' < 0 := N.F.a'bc.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_4 : N.F.a'bc.f c = 0 := N.F.a'bc.hR
  have f3_5 : N.F.a'bc.f c' < 0 := N.F.a'bc.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f3_6 : N.F.a'bc.f d = 0 := hd.a'bc
  have f4_0 : N.F.ab'c'.f a = 0 := N.F.ab'c'.hP
  have f4_1 : N.F.ab'c'.f a' < 0 := N.F.ab'c'.neg a' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_2 : N.F.ab'c'.f b < 0 := N.F.ab'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_3 : N.F.ab'c'.f b' = 0 := N.F.ab'c'.hQ
  have f4_4 : N.F.ab'c'.f c < 0 := N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f4_5 : N.F.ab'c'.f c' = 0 := N.F.ab'c'.hR
  have f4_6 : N.F.ab'c'.f d < 0 := hd.ab'c'
  have f5_0 : N.F.a'bc'.f a < 0 := N.F.a'bc'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_1 : N.F.a'bc'.f a' = 0 := N.F.a'bc'.hP
  have f5_2 : N.F.a'bc'.f b = 0 := N.F.a'bc'.hQ
  have f5_3 : N.F.a'bc'.f b' < 0 := N.F.a'bc'.neg b' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_4 : N.F.a'bc'.f c < 0 := N.F.a'bc'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f5_5 : N.F.a'bc'.f c' = 0 := N.F.a'bc'.hR
  have f5_6 : N.F.a'bc'.f d < 0 := hd.a'bc'
  have f6_0 : N.F.a'b'c.f a < 0 := N.F.a'b'c.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_1 : N.F.a'b'c.f a' = 0 := N.F.a'b'c.hP
  have f6_2 : N.F.a'b'c.f b < 0 := N.F.a'b'c.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_3 : N.F.a'b'c.f b' = 0 := N.F.a'b'c.hQ
  have f6_4 : N.F.a'b'c.f c = 0 := N.F.a'b'c.hR
  have f6_5 : N.F.a'b'c.f c' < 0 := N.F.a'b'c.neg c' (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f6_6 : N.F.a'b'c.f d < 0 := hd.a'b'c
  have f7_0 : N.F.a'b'c'.f a < 0 := N.F.a'b'c'.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_1 : N.F.a'b'c'.f a' = 0 := N.F.a'b'c'.hP
  have f7_2 : N.F.a'b'c'.f b < 0 := N.F.a'b'c'.neg b (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_3 : N.F.a'b'c'.f b' = 0 := N.F.a'b'c'.hQ
  have f7_4 : N.F.a'b'c'.f c < 0 := N.F.a'b'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  have f7_5 : N.F.a'b'c'.f c' = 0 := N.F.a'b'c'.hR
  have f7_6 : N.F.a'b'c'.f d < 0 := hd.a'b'c'
  refine noSeg_of_aff08 (![fun y => N.F.abc'.f y + N.F.ab'c.f y + N.F.ab'c'.f y, fun y => N.F.a'bc.f y + N.F.a'bc'.f y + N.F.a'b'c.f y + N.F.a'b'c'.f y, fun y => N.F.abc'.f y + N.F.a'bc.f y + N.F.a'bc'.f y, fun y => N.F.ab'c.f y + N.F.ab'c'.f y + N.F.a'b'c.f y + N.F.a'b'c'.f y, fun y => N.F.ab'c.f y + N.F.a'bc.f y + N.F.a'b'c.f y, fun y => N.F.abc'.f y + N.F.ab'c'.f y + N.F.a'bc'.f y + N.F.a'b'c'.f y, fun y => N.F.abc'.f y + N.F.ab'c.f y + N.F.a'bc.f y]) ?_ ?_
  · intro m y z s
    fin_cases m <;> simp [facet_aff08] <;> ring
  · intro m w hw
    fin_cases m <;> fin_cases w <;> first | exact absurd rfl hw | (simp only [x, pts08]; simp; linarith)


set_option maxHeartbeats 4000000 in
theorem crimA2 (θ : Fin 6 → ℝ) (hθ : Ineq08w θ) (h6 : 1 < θ 5) :
    CRim θ (fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) 4 1 (1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08w θ hθ.1 hθ.2.1 hθ.2.2
  have dA : 0 < -1 + (θ 5) := by linarith
  have dB : 0 < -1 + (θ 0) := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := polyAw (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) p0 p1 p2 p3 p4 p5 e1 e2 e3 dA dB ga gb
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  constructor
  · intro i j hi hj
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hi | exact absurd (by decide) hj | skip
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith
  · intro m i
    fin_cases m <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl
    all_goals
      norm_num [fc08, cdet, cp08]
      try linarith

theorem impQ_N2 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) (h6 : 1 < θ 5) (s j : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 2 s j).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 2 s j).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 2 s j).lab ∘ σ)) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := common08w θ hθ.1 hθ.2.1 hθ.2.2
  have hD2 : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  refine noRim_of_sep (w := wv08 E₁ E₂ E₃ (-(θ 3 / θ 2)) 0 1) ?_ h 1 ?_
  · rw [view2]; apply perp_diff08; simp [cp08]
  · intro l
    refine forall_lab2 s j (fun i => ⟪wv08 E₁ E₂ E₃ (-(θ 3 / θ 2)) 0 1, nfShape08 o E₁ E₂ E₃ θ i⟫ <
      ⟪wv08 E₁ E₂ E₃ (-(θ 3 / θ 2)) 0 1, nfShape08 o E₁ E₂ E₃ θ 1⟫) ?_ ?_ ?_ ?_ (σ l)
    all_goals
      simp only [inner_wv08]
      simp [cp08]
      have hq : θ 3 / θ 2 * θ 2 = θ 3 := div_mul_cancel₀ _ p2.ne'
      have hq0 : 0 < θ 3 / θ 2 := div_pos p3 p2
      nlinarith [mul_pos hD2 (show 0 < θ 5 - 1 by linarith), mul_pos hD2 hq0, mul_pos hD2 (show 0 < θ 5 by linarith)]

theorem impQ_T4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) (h0 : 1 < θ 0) (s j : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 2 s j).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 2 s j).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 2 s j).lab ∘ σ)) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := common08w θ hθ.1 hθ.2.1 hθ.2.2
  have hD2 : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  refine noRim_of_sep (w := wv08 E₁ E₂ E₃ 1 0 (-(θ 2 / θ 3))) ?_ h 5 ?_
  · rw [view2]; apply perp_diff08; simp [cp08]
  · intro l
    refine forall_lab2 s j (fun i => ⟪wv08 E₁ E₂ E₃ 1 0 (-(θ 2 / θ 3)), nfShape08 o E₁ E₂ E₃ θ i⟫ <
      ⟪wv08 E₁ E₂ E₃ 1 0 (-(θ 2 / θ 3)), nfShape08 o E₁ E₂ E₃ θ 5⟫) ?_ ?_ ?_ ?_ (σ l)
    all_goals
      simp only [inner_wv08]
      simp [cp08]
      have hq : θ 2 / θ 3 * θ 3 = θ 2 := div_mul_cancel₀ _ p3.ne'
      have hq0 : 0 < θ 2 / θ 3 := div_pos p2 p3
      nlinarith [mul_pos hD2 (show 0 < θ 0 - 1 by linarith), mul_pos hD2 hq0, mul_pos hD2 (show 0 < θ 0 by linarith)]

theorem impK_T4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) (h6 : θ 5 < 1) (s : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 0 s false).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 0 s false).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 0 s false).lab ∘ σ)) : False := by
  obtain ⟨p0, p1, p2, p3, p4, p5, -⟩ := common08w θ hθ.1 hθ.2.1 hθ.2.2
  have hD2 : 0 < det3 E₁ E₂ E₃ ^ 2 := by positivity
  refine noRim_of_sep (w := wv08 E₁ E₂ E₃ 0 (θ 5 - 1) (-(θ 4))) ?_ h 6 ?_
  · rw [view0]; apply perp_diff08; simp [cp08]; ring
  · intro l
    refine forall_lab0 s (fun i => ⟪wv08 E₁ E₂ E₃ 0 (θ 5 - 1) (-(θ 4)), nfShape08 o E₁ E₂ E₃ θ i⟫ <
      ⟪wv08 E₁ E₂ E₃ 0 (θ 5 - 1) (-(θ 4)), nfShape08 o E₁ E₂ E₃ θ 6⟫) ?_ ?_ ?_ ?_ (σ l)
    all_goals
      simp only [inner_wv08]
      simp [cp08]
      nlinarith [mul_pos hD2 (show 0 < 1 - θ 5 by linarith), mul_pos hD2 p4, mul_pos hD2 (mul_pos p4 p5),
        mul_pos hD2 (mul_pos p1 (show 0 < 1 - θ 5 by linarith)), mul_pos hD2 (mul_pos p4 p3)]

theorem nfN2_nws4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) (h6 : 1 < θ 5) (ε : ℝ) (hε : ε ≠ 0) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod 4)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ)
      (ε • (nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1))
      ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) ∘ σ)) :
    NWS4 (quad ⟪nfShape08 o E₁ E₂ E₃ θ 1, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 2, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 5, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 3, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫) := by
  have hc := crimA2 θ hθ h6
  have hκ : ε * det3 E₁ E₂ E₃ ≠ 0 := mul_ne_zero hε hE
  have hpos : 0 < (ε * det3 E₁ E₂ E₃) ^ 2 := by positivity
  have key := rim_nws4 (x := nfShape08 o E₁ E₂ E₃ θ) (fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i)
    (ε * det3 E₁ E₂ E₃) hκ ?_ σ h
  · simp only [inner_smul_right] at key
    have := nws4_quad_scale (inv_ne_zero hε) key
    simpa [← mul_assoc, inv_mul_cancel₀ hε] using this
  · intro i j hi hj
    rw [det3_view08]
    have := hc.1 i j hi hj
    have e : ε * det3 E₁ E₂ E₃ * (ε * (det3 E₁ E₂ E₃ * (fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 4 -
        fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 1))) =
        (ε * det3 E₁ E₂ E₃) ^ 2 * (1 * (fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 4 -
        fc08 θ ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) i)
        ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) (i + 1)) ((fun i : ZMod 4 => (![1, 2, 5, 3] : Fin 4 → Fin 7) i) j) 1)) := by ring
    rw [e]; exact mul_pos hpos this

theorem hq2_of_regN2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (h : RegN2 N.F) :
    N.F.ab'c'.f a' < N.F.ab'c'.f c := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  have hg := region_gamma6 N hE hθ hpts
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hfcn : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have h6 : 1 < θ 5 := by
    have h' : N.F.abc'.f a' < N.F.abc'.f c := h
    rw [hg] at h'; nlinarith
  have hpoly := q2polyw θ hθ.1 hθ.2.1 hθ.2.2 h6
  have hneg : N.F.ab'c'.f c < 0 := N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08w θ hθ.1 hθ.2.1 hθ.2.2
  have hfac := facet_prop08 N.F.ab'c' c a'
  have d1 : det3 (b' - a) (c' - a) (c - a) = det3 E₁ E₂ E₃ * fc08 θ 0 3 5 4 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 3 5 4; rw [← hpts] at this; exact this
  have d2 : det3 (b' - a) (c' - a) (a' - a) = det3 E₁ E₂ E₃ * fc08 θ 0 3 5 1 := by
    have := det3_nf08 o E₁ E₂ E₃ θ 0 3 5 1; rw [← hpts] at this; exact this
  rw [d1, d2] at hfac
  have hq := fc_q2 θ
  have hfac' : N.F.ab'c'.f a' * fc08 θ 0 3 5 4 = N.F.ab'c'.f c * fc08 θ 0 3 5 1 := by
    apply mul_left_cancel₀ hE; linear_combination hfac
  have h4 : 0 < fc08 θ 0 3 5 4 := by
    have := (facts08w θ hθ.1 hθ.2.1 hθ.2.2).2.2.2.2.2.2.2.2.2.2.2.1
    exact this
  have key : (N.F.ab'c'.f a' - N.F.ab'c'.f c) * fc08 θ 0 3 5 4 < 0 := by
    have : (N.F.ab'c'.f a' - N.F.ab'c'.f c) * fc08 θ 0 3 5 4 =
        N.F.ab'c'.f c * (fc08 θ 0 3 5 1 - fc08 θ 0 3 5 4) := by linear_combination hfac'
    rw [this]; exact mul_neg_of_neg_of_pos hneg (by linarith)
  by_contra hcon
  push_neg at hcon
  nlinarith
theorem nfN2_of_rim {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ}
    (hθ : Ineq08w θ) (h6 : 1 < θ 5) (s : Bool) {k' : ℕ} [NeZero k']
    (σ : ZMod k' → ZMod (test08 0 s false).k)
    (h : RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 0 s false).view (nfShape08 o E₁ E₂ E₃ θ))
      ((test08 0 s false).lab ∘ σ)) :
    NWS4 (quad ⟪nfShape08 o E₁ E₂ E₃ θ 1, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 2, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 5, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫
      ⟪nfShape08 o E₁ E₂ E₃ θ 3, nfShape08 o E₁ E₂ E₃ θ 4 - nfShape08 o E₁ E₂ E₃ θ 1⟫) := by
  cases s
  · exact nfN2_nws4 hE hθ h6 (-1) (by norm_num) σ (by rw [neg_one_smul]; exact h)
  · exact nfN2_nws4 hE hθ h6 1 one_ne_zero σ (by rw [one_smul]; exact h)


/-- **Free closings need no HDN hypothesis** (consolidation §1.5 (1); this is the core of G5a's
`slideN2a'`/`slideQ`, stated at a rim certificate of the limit): if the limit has a robust corner
rim of N2's `K_{a'}` or Q's `K_d` (polygon + robust depths, labels a cyclic subsequence), then the
shape is Rupert, with any HDNs and ties. -/
theorem rupert_of_free_limit_rim {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d)
    (hT : ¬ IsT a' b c d) (hT' : ¬ IsT' a b c' d)
    (t : Fin 3 × Bool × Bool) (ht : t ∉ SC08) {k' : ℕ} [NeZero k'] (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k)
    (hrim : RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
      ((test08 t.1 t.2.1 t.2.2).lab ∘ σ)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  have hFc := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := N.F.a'bc.neg a (by simp) haa' hab hac
  have hg6 := region_gamma6 N hE hθ hpts
  have hg0 := region_alpha1 N hE hθ hpts
  by_cases htie₁ : N.F.abc'.f a' = N.F.abc'.f c
  · exact absurd (N.hd.tieT_geom htie₁) hT
  by_cases htie₂ : N.F.a'bc.f c' = N.F.a'bc.f a
  · exact absurd (N.hd.tieT'_geom htie₂) hT'
  obtain ⟨i, s, j⟩ := t
  rw [hpts] at hrim
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases lt_or_gt_of_ne htie₁ with hfar | hfc
  · -- N2 region: `γ₆ > 1`
    have h6 : 1 < θ 5 := by
      rw [hg6] at hfar; nlinarith
    rcases hi with rfl | rfl | rfl
    · cases j
      · have hN := nfN2_of_rim hE hθ h6 s σ hrim
        rw [← hpts] at hN
        have hNx : NWS4 (quad ⟪a', c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫) := hN
        have hq₂ := hq2_of_regN2 N hfar
        obtain ⟨s', δ, hs0, hs1, hδ, hdmid⟩ := N.hd.middle_Qbc hfar
        have e : (insert d ({a', a, c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} :=
          (type08_set_perm a a' b b' c c' d).1
        rw [← e]
        exact isRupert_quad_edge_middle_x_formU (m := d) N.F.swap₁.perm₂₃ hfar hq₂
          ⟨s', δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ hNx
      · exact absurd (Or.inl ⟨rfl, rfl⟩) ht
    · exact absurd (Or.inr rfl) ht
    · exact (impQ_N2 hE hθ h6 s j σ hrim).elim
  · by_cases hfa : N.F.a'bc.f a < N.F.a'bc.f c'
    · exact close_caseQ N.F N.hd hfc hfa
    · have hfc' : N.F.a'bc.f c' < N.F.a'bc.f a := lt_of_le_of_ne (not_lt.mp hfa) htie₂
      have h6 : θ 5 < 1 := by
        rw [hg6] at hfc; nlinarith
      have h0 : 1 < θ 0 := by
        rw [hg0] at hfc'; nlinarith
      rcases hi with rfl | rfl | rfl
      · cases j
        · exact (impK_T4 hE hθ h6 s σ hrim).elim
        · exact absurd (Or.inl ⟨rfl, rfl⟩) ht
      · exact absurd (Or.inr rfl) ht
      · exact (impQ_T4 hE hθ h0 s j σ hrim).elim

theorem grp_view_ne {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (i : Fin 3) :
    (grp08 i).view (pts08 a a' b b' c c' d) ≠ 0 := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  fin_cases i <;> simp [grp08, ViewGroup.view, LabTest.quad, pts08, sub_eq_zero]
  · exact Ne.symm ha'c
  · exact hdb.symm
  · exact hdb.symm

theorem view0_test08 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (c0 : Fin 3 × Bool × Bool) :
    (test08 c0.1 c0.2.1 c0.2.2).view (pts08 a a' b b' c c' d) ≠ 0 := by
  obtain ⟨T, hT, h | h⟩ := test08_eq c0.1 c0.2.1 c0.2.2
  · rw [h, grp_tests_view _ T hT]; exact grp_view_ne N _
  · rw [h]; simp only [LabTest.neg, grp_tests_view _ T hT, neg_ne_zero]; exact grp_view_ne N _



end W
end Type08Sp
end Minimality
