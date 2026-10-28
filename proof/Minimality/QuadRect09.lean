module

public import Minimality.QuadTripleRect
public import Minimality.Type10RightPrism

@[expose] public section

/-!
# Theorem 09.Q: `QuadTripleRect` at the quadrilaterals of type 09 is Rupert

FEWER-FACES-PROOFS.md §39.5.  Plan (see `out/bottleneck/sp09/handoff_lean_Q.md`):

* Group A: `QuadTripleRect` (+ no three collinear, two quadrilaterals covering `V`) gives a
  *prism shape*: `V = {v, v+A, v+A+l e, v+αA+z1 e, v+B, v+B+l e, v+βB+z2 e}` with `A, B ⊥ e`,
  `0 < α, β < 1`, `l, z1, z2 > 0`.
* Group B: the prism shape in any position is the standard one (`e = ez`, `v = 0`).
* Group C: the standard shape is Rupert at the near-axis view `ez + ε d` by an explicit motion
  (certificates of `RightPrism.lean`).
* Group D: wiring `isRupert_of_quadTripleRect09`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Group C: the standard prism shape -/

/-- The standard shape: bottom triangle `0, a, b` at height `0`, the points over `a`, `b` at
height `lam`, and the two roof points `α a` at height `z1`, `β b` at height `z2`. -/
noncomputable def quadRectStd (a b : ℝ²) (lam α β z1 z2 : ℝ) : Finset ℝ³ := by
  classical
  exact {liftPt 0 0, liftPt a 0, liftPt a lam, liftPt (α • a) z1,
    liftPt b 0, liftPt b lam, liftPt (β • b) z2}

/-- The limit problem of §39.5 for the near-axis view `ez + ε liftPt dv 0`: the first-order motion
`(ω, τ)` (screen velocity `vel q z = proj_xy (ω × liftPt q z + τ) = t + ω₂ J q + z a`) satisfies
the strict inequalities at the five shadow vertices `0, a, a+lam e, b+lam e, b` of the pentagon
`(0, a, a+lam e, b+lam e, b)` (ccw) in the form of the certificates `cert_flat`, `cert_up`,
`cert_down` of `RightPrism.lean`; and `dv` points into the triangle at the roof edges:
`cross2 a dv < 0 < cross2 b dv`, `0 < cross2 (b - a) dv`. -/
def QuadRectMotion (a b : ℝ²) (lam : ℝ) (dv : ℝ²) (ω τ : ℝ³) : Prop :=
  let vel : ℝ² → ℝ → ℝ² := fun q z => proj_xy (cross ω (liftPt q z) + τ)
  cross2 a dv < 0 ∧ 0 < cross2 b dv ∧ 0 < cross2 (b - a) dv ∧
  -- vertex 0 (`cert_flat`, `qm = b`, `qp = a`)
  0 < cross2 a (vel 0 0) ∧ 0 < cross2 (0 - b) (vel 0 0) ∧
  -- vertex a at height 0 (`cert_up`, `qm = 0`, `d = lam`)
  0 < lam * cross2 (vel a 0) dv ∧ 0 < cross2 (a - 0) (vel a 0) ∧
  -- vertex a at height lam (`cert_down`, `qp = b`, `d = -lam`)
  0 < cross2 (b - a) (vel a lam) ∧ 0 < -(-lam * cross2 (vel a lam) dv) ∧
  -- vertex b at height lam (`cert_up`, `qm = a`, `d = -lam`)
  0 < -lam * cross2 (vel b lam) dv ∧ 0 < cross2 (b - a) (vel b lam) ∧
  -- vertex b at height 0 (`cert_down`, `qp = 0`, `d = lam`)
  0 < cross2 (0 - b) (vel b 0) ∧ 0 < -(lam * cross2 (vel b 0) dv)

/-- Coordinate form of the limit LP, once `dv` is fixed. -/
theorem quadRectMotion_coords (a0 a1 b0 b1 d0 d1 lam : ℝ) (hlam : 0 < lam)
    (h1 : a0 * d1 - a1 * d0 < 0) (h2 : 0 < b0 * d1 - b1 * d0)
    (h3 : 0 < (b0 - a0) * d1 - (b1 - a1) * d0)
    (hk : (b0 - a0) * d0 + (b1 - a1) * d1 ≠ 0) :
    ∃ o1 o2 o3 t0 t1 : ℝ,
      a1 * t0 < a0 * t1 ∧ b0 * t1 < b1 * t0 ∧
      0 < lam * ((-(o3 * a1) + t0) * d1 - (o3 * a0 + t1) * d0) ∧
      a1 * (-(o3 * a1) + t0) < a0 * (o3 * a0 + t1) ∧
      (b1 - a1) * (o2 * lam - o3 * a1 + t0) < (b0 - a0) * (o3 * a0 - o1 * lam + t1) ∧
      0 < lam * ((o2 * lam - o3 * a1 + t0) * d1 - (o3 * a0 - o1 * lam + t1) * d0) ∧
      lam * ((o2 * lam - o3 * b1 + t0) * d1 - (o3 * b0 - o1 * lam + t1) * d0) < 0 ∧
      (b1 - a1) * (o2 * lam - o3 * b1 + t0) < (b0 - a0) * (o3 * b0 - o1 * lam + t1) ∧
      b0 * (o3 * b0 + t1) < b1 * (-(o3 * b1) + t0) ∧
      lam * ((-(o3 * b1) + t0) * d1 - (o3 * b0 + t1) * d0) < 0 := by
  set k : ℝ := (b0 - a0) * d0 + (b1 - a1) * d1 with hkdef
  have hk2 : 0 < k ^ 2 := by positivity
  have hN : 0 < d0 ^ 2 + d1 ^ 2 := by
    by_contra hc
    have e0 : d0 = 0 := by nlinarith [sq_nonneg d0, sq_nonneg d1]
    have e1 : d1 = 0 := by nlinarith [sq_nonneg d0, sq_nonneg d1]
    rw [e0, e1] at h1; simp at h1
  set tc : ℝ := -k * ((a0 + b0) * d0 + (a1 + b1) * d1) / (2 * (d0 ^ 2 + d1 ^ 2)) with htcdef
  have htc : tc * (d0 ^ 2 + d1 ^ 2) = -k * ((a0 + b0) * d0 + (a1 + b1) * d1) / 2 := by
    rw [htcdef]; field_simp
  have hB4 : 0 < -(a0 * d1 - a1 * d0) := by linarith
  obtain ⟨t, ht⟩ := ((eventually_atTop_pos (tc * (a0 * d0 + a1 * d1)) _ hB4).and
    ((eventually_atTop_pos (-(tc * (b0 * d0 + b1 * d1))) _ h2).and
    ((eventually_atTop_pos (tc * (a0 * d0 + a1 * d1) + k * (a0 ^ 2 + a1 ^ 2)) _ hB4).and
    (eventually_atTop_pos (-(tc * (b0 * d0 + b1 * d1)) - k * (b0 ^ 2 + b1 ^ 2)) _ h2)))).exists
  obtain ⟨ht4, ht5, ht7, ht12⟩ := ht
  have hB8 : 0 < lam * ((b0 - a0) * d1 - (b1 - a1) * d0) := mul_pos hlam h3
  obtain ⟨μ, hμ⟩ := ((eventually_atTop_pos
    ((b0 - a0) * (k * a0 + (tc * d0 - t * d1)) - (b1 - a1) * (-k * a1 + (-tc * d1 - t * d0)))
      _ hB8).and (eventually_atTop_pos
    ((b0 - a0) * (k * b0 + (tc * d0 - t * d1)) - (b1 - a1) * (-k * b1 + (-tc * d1 - t * d0)))
      _ hB8)).exists
  obtain ⟨hμ8, hμ11⟩ := hμ
  refine ⟨-μ * d1, μ * d0, k, -tc * d1 - t * d0, tc * d0 - t * d1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have : (-(k * a1) + (-tc * d1 - t * d0)) * d1 - (k * a0 + (tc * d0 - t * d1)) * d0 = k ^ 2 / 2 := by
      rw [hkdef]; linear_combination (-1) * htc
    rw [this]; exact mul_pos hlam (by positivity)
  · linarith
  · linarith
  · have : (μ * d0 * lam - k * a1 + (-tc * d1 - t * d0)) * d1 - (k * a0 - -μ * d1 * lam + (tc * d0 - t * d1)) * d0 = k ^ 2 / 2 := by
      rw [hkdef]; linear_combination (-1) * htc
    rw [this]; exact mul_pos hlam (by positivity)
  · have : (μ * d0 * lam - k * b1 + (-tc * d1 - t * d0)) * d1 - (k * b0 - -μ * d1 * lam + (tc * d0 - t * d1)) * d0 = -(k ^ 2 / 2) := by
      rw [hkdef]; linear_combination (-1) * htc
    rw [this]; have := mul_pos hlam (show 0 < k ^ 2 / 2 by positivity); linarith
  · linarith
  · linarith
  · have : (-(k * b1) + (-tc * d1 - t * d0)) * d1 - (k * b0 + (tc * d0 - t * d1)) * d0 = -(k ^ 2 / 2) := by
      rw [hkdef]; linear_combination (-1) * htc
    rw [this]; have := mul_pos hlam (show 0 < k ^ 2 / 2 by positivity); linarith

/-- **C1** (the limit LP, pure real algebra): for `0 < cross2 a b`, `0 < lam` a direction `dv` and
a motion exist.  Paper: `dv = -(a+b)` perturbed so that `dv · (b - a) ≠ 0`; `ω₃ = ±1`,
`a_screen = μ dv`, `t = τ c + σ dv` with `c ⊥ dv`; `τ` between `-ω₃ c·Jb` and `-ω₃ c·Ja`,
`σ ≪ 0`, `μ ≫ 0`. -/
theorem exists_quadRectMotion (a b : ℝ²) (lam : ℝ) (hab : 0 < cross2 a b) (hlam : 0 < lam) :
    ∃ (dv : ℝ²) (ω τ : ℝ³), QuadRectMotion a b lam dv ω τ := by
  simp only [cross2] at hab
  obtain ⟨s0, hs1, hs2, hsk⟩ : ∃ s0 : ℝ, -1 < s0 ∧ s0 < 1 ∧
      (b 0 - a 0) * (-(a 0 + b 0) + s0 * (b 0 - a 0)) +
        (b 1 - a 1) * (-(a 1 + b 1) + s0 * (b 1 - a 1)) ≠ 0 := by
    by_cases hn : b 0 ^ 2 + b 1 ^ 2 - a 0 ^ 2 - a 1 ^ 2 = 0
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      have hp : 0 < (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 := by
        by_contra hc
        have e0 : b 0 - a 0 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1)]
        have e1 : b 1 - a 1 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1)]
        have : b 0 = a 0 := by linarith
        have : b 1 = a 1 := by linarith
        nlinarith
      intro h; nlinarith
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      intro h; apply hn; nlinarith
  obtain ⟨o1, o2, o3, t0, t1, hc⟩ := quadRectMotion_coords (a 0) (a 1) (b 0) (b 1)
    (-(a 0 + b 0) + s0 * (b 0 - a 0)) (-(a 1 + b 1) + s0 * (b 1 - a 1)) lam hlam
    (by nlinarith) (by nlinarith) (by nlinarith) hsk
  refine ⟨!₂[-(a 0 + b 0) + s0 * (b 0 - a 0), -(a 1 + b 1) + s0 * (b 1 - a 1)],
    !₂[o1, o2, o3], !₂[t0, t1, 0], ?_⟩
  simp [QuadRectMotion, cross2, cross, proj_xy, liftPt]
  obtain ⟨c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hc
  refine ⟨by nlinarith, by nlinarith, by nlinarith, c4, c5, by linarith, c7, c8, by linarith, by linarith, c11, c12, by linarith⟩

/-- **C2a**: the roof point `α a` at height `z1` is hidden at `ez + ε dv`: it lies on the edge `0a`
of the bottom triangle in projection, and `cross2 a dv < 0` pushes it strictly inside (first-order
branch of `tt`).  Variant of `cert_hidden_bottom` with `e1` replaced by its first-order test. -/
theorem cert_hidden_bottom_edge (V : Finset ℝ³) (ω τ : ℝ³) (a b dv : ℝ²) (α z1 : ℝ)
    (h0 : liftPt 0 0 ∈ V) (ha : liftPt a 0 ∈ V) (hb : liftPt b 0 ∈ V)
    (hab : 0 < cross2 a b) (hα0 : 0 < α) (hα1 : α < 1) (hz1 : 0 < z1) (hd : cross2 a dv < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt dv 0) ω τ (liftPt (α • a) z1) := by
  simp only [cross2] at hab hd
  have T0 := tt dv (a - 0) 0 (liftPt (b - 0) 0) (Or.inl (by
    rw [proj_xy_liftPt]; simpa [cross2] using hab))
  have T1 := tt dv (a - 0) 0 (liftPt (α • a) z1 - liftPt 0 0) (Or.inr ⟨by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]; simp [cross2]; ring, by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt, PiLp.sub_apply, liftPt_two, liftPt_two]
    simp [cross2]; nlinarith [mul_pos hα0 hab, mul_pos (sub_pos.2 hα1) hab]⟩)
  have T2 := tt dv (b - a) 0 (liftPt (α • a) z1 - liftPt a 0) (Or.inl (by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]; simp [cross2]; nlinarith [mul_pos hα0 hab, mul_pos (sub_pos.2 hα1) hab]))
  have T3 := tt dv (0 - b) 0 (liftPt (α • a) z1 - liftPt b 0) (Or.inl (by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]; simp [cross2]; nlinarith [mul_pos hα0 hab, mul_pos (sub_pos.2 hα1) hab]))
  filter_upwards [T0, T1, T2, T3] with ε t0 t1 t2 t3
  refine Or.inr ⟨_, h0, _, ha, _, hb, ?_, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self]; exact t0
  · rw [liftPt_sub_liftPt, sub_self]; exact t1
  · rw [liftPt_sub_liftPt, sub_self]; exact t2
  · rw [liftPt_sub_liftPt, sub_self]; exact t3

/-- **C2b**: the same for `β b` at height `z2` on the edge `b0` (`0 < cross2 b dv`). -/
theorem cert_hidden_bottom_edge' (V : Finset ℝ³) (ω τ : ℝ³) (a b dv : ℝ²) (β z2 : ℝ)
    (h0 : liftPt 0 0 ∈ V) (ha : liftPt a 0 ∈ V) (hb : liftPt b 0 ∈ V)
    (hab : 0 < cross2 a b) (hβ0 : 0 < β) (hβ1 : β < 1) (hz2 : 0 < z2) (hd : 0 < cross2 b dv) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt dv 0) ω τ (liftPt (β • b) z2) := by
  simp only [cross2] at hab hd
  have T0 := tt dv (a - 0) 0 (liftPt (b - 0) 0) (Or.inl (by
    rw [proj_xy_liftPt]; simpa [cross2] using hab))
  have T1 := tt dv (a - 0) 0 (liftPt (β • b) z2 - liftPt 0 0) (Or.inl (by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]; simp [cross2]; nlinarith [mul_pos hβ0 hab, mul_pos (sub_pos.2 hβ1) hab]))
  have T2 := tt dv (b - a) 0 (liftPt (β • b) z2 - liftPt a 0) (Or.inl (by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]; simp [cross2]; nlinarith [mul_pos hβ0 hab, mul_pos (sub_pos.2 hβ1) hab]))
  have T3 := tt dv (0 - b) 0 (liftPt (β • b) z2 - liftPt b 0) (Or.inr ⟨by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]; simp [cross2]; ring, by
    rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt, PiLp.sub_apply, liftPt_two, liftPt_two]
    simp [cross2]; nlinarith [mul_pos hβ0 hab, mul_pos (sub_pos.2 hβ1) hab]⟩)
  filter_upwards [T0, T1, T2, T3] with ε t0 t1 t2 t3
  refine Or.inr ⟨_, h0, _, ha, _, hb, ?_, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self]; exact t0
  · rw [liftPt_sub_liftPt, sub_self]; exact t1
  · rw [liftPt_sub_liftPt, sub_self]; exact t2
  · rw [liftPt_sub_liftPt, sub_self]; exact t3

/-- **C2**: the standard shape is Rupert, from a motion of the limit problem.  Seven
certificates (`cert_flat` at `0`; `cert_up`/`cert_down` at the four lateral corners;
`cert_hidden_bottom_edge`, `…'` at the roof points), `filter_upwards` and `isRupert_of_tiltCert`
at `w = ez + ε liftPt dv 0` (`w ≠ 0` from the third coordinate). -/
theorem isRupert_quadRectStd_of_motion (a b : ℝ²) (lam α β z1 z2 : ℝ) (hab : 0 < cross2 a b)
    (hlam : 0 < lam) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hz1 : 0 < z1)
    (hz2 : 0 < z2) {dv : ℝ²} {ω τ : ℝ³} (hM : QuadRectMotion a b lam dv ω τ) :
    IsRupert (quadRectStd a b lam α β z1 z2) := by
  classical
  obtain ⟨hd1, hd2, hd3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hM
  set V := quadRectStd a b lam α β z1 z2 with hV
  have m0 : liftPt 0 0 ∈ V := by simp [hV, quadRectStd]
  have ma : liftPt a 0 ∈ V := by simp [hV, quadRectStd]
  have mA : liftPt a lam ∈ V := by simp [hV, quadRectStd]
  have mr : liftPt (α • a) z1 ∈ V := by simp [hV, quadRectStd]
  have mb : liftPt b 0 ∈ V := by simp [hV, quadRectStd]
  have mB : liftPt b lam ∈ V := by simp [hV, quadRectStd]
  have ms : liftPt (β • b) z2 ∈ V := by simp [hV, quadRectStd]
  have mA' : liftPt a (0 + lam) ∈ V := by rw [zero_add]; exact mA
  have mB' : liftPt b (0 + lam) ∈ V := by rw [zero_add]; exact mB
  have ma' : liftPt a (lam + -lam) ∈ V := by rw [add_neg_cancel]; exact ma
  have mb' : liftPt b (lam + -lam) ∈ V := by rw [add_neg_cancel]; exact mb
  have k0 := cert_flat V dv ω τ (q := 0) (z := 0) mb ma (by simp only [cross2] at hab ⊢; simp; nlinarith)
    (by rw [sub_zero]; exact c4) c5
  have k1 := cert_up V dv ω τ (q := a) (qm := 0) (z := 0) (d := lam) m0 mA'
    (by have : cross2 (0 - a) dv = -cross2 a dv := by simp [cross2]; ring
        rw [this]; nlinarith) c6 c7
  have k2 := cert_down V dv ω τ (q := a) (qp := b) (z := lam) (d := -lam) ma' mB
    (by nlinarith) c8 c9
  have k3 := cert_up V dv ω τ (q := b) (qm := a) (z := lam) (d := -lam) mA mb'
    (by rw [show cross2 (a - b) dv = -cross2 (b - a) dv by simp [cross2]; ring]; nlinarith) c10 c11
  have k4 := cert_down V dv ω τ (q := b) (qp := 0) (z := 0) (d := lam) mB' m0
    (by have : cross2 (0 - b) dv = -cross2 b dv := by simp [cross2]; ring
        rw [this]; nlinarith) c12 c13
  have k5 := cert_hidden_bottom_edge V ω τ a b dv α z1 m0 ma mb hab hα0 hα1 hz1 hd1
  have k6 := cert_hidden_bottom_edge' V ω τ a b dv β z2 m0 ma mb hab hβ0 hβ1 hz2 hd2
  obtain ⟨ε, hε⟩ := (k0.and (k1.and (k2.and (k3.and (k4.and (k5.and k6)))))).exists
  obtain ⟨t0, t1, t2, t3, t4, t5, t6⟩ := hε
  refine isRupert_of_tiltCert V (ez + ε • liftPt dv 0) ?_ ω τ fun x hx => ?_
  · intro h0
    have := congrArg (· 2) h0
    simp [ez, liftPt] at this
  · simp only [hV, quadRectStd, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t0
    · exact t1
    · exact t2
    · exact t5
    · exact t4
    · exact t3
    · exact t6

theorem isRupert_quadRectStd (a b : ℝ²) (lam α β z1 z2 : ℝ) (hab : 0 < cross2 a b)
    (hlam : 0 < lam) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hz1 : 0 < z1)
    (hz2 : 0 < z2) : IsRupert (quadRectStd a b lam α β z1 z2) := by
  obtain ⟨dv, ω, τ, hM⟩ := exists_quadRectMotion a b lam hab hlam
  exact isRupert_quadRectStd_of_motion a b lam α β z1 z2 hab hlam hα0 hα1 hβ0 hβ1 hz1 hz2 hM

/-! ### Group B: the prism shape in any position -/

/-- The prism shape over `v` with bottom triangle `v, v+A, v+B ⊥ e`, lateral height `l e` and roof
points `v + αA + z1 e`, `v + βB + z2 e`. -/
noncomputable def prismShape (v A B e : ℝ³) (l α β z1 z2 : ℝ) : Finset ℝ³ := by
  classical
  exact {v, v + A, v + A + l • e, v + α • A + z1 • e, v + B, v + B + l • e, v + β • B + z2 • e}

theorem prismShape_swap (v A B e : ℝ³) (l α β z1 z2 : ℝ) :
    prismShape v A B e l α β z1 z2 = prismShape v B A e l β α z2 z1 := by
  classical
  unfold prismShape
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem isRupert_prismShape_pos (v A B e : ℝ³) (l α β z1 z2 : ℝ) (he : e ≠ 0)
    (hA : ⟪e, A⟫ = 0) (hB : ⟪e, B⟫ = 0) (hdet : 0 < det3 A B e)
    (hl : 0 < l) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hz1 : 0 < z1)
    (hz2 : 0 < z2) : IsRupert (prismShape v A B e l α β z1 z2) := by
  classical
  obtain ⟨R, hR, lam, hlam, hRe⟩ := exists_rotation_to_ez_pos e he
  set L := R.toEuclideanLin
  have hz : ∀ u, ⟪e, u⟫ = 0 → (L u) 2 = 0 := by
    intro u hu
    have : lam * (L u) 2 = ⟪e, u⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRe, inner_toEuclideanLin_SO3 hR,
        real_inner_comm]
    rw [hu] at this
    exact (mul_eq_zero.mp this).resolve_left hlam.ne'
  set a := proj_xy (L A)
  set b := proj_xy (L B)
  have hLA : L A = liftPt a 0 := by rw [← hz _ hA, liftPt_proj_xy]
  have hLB : L B = liftPt b 0 := by rw [← hz _ hB, liftPt_proj_xy]
  have hcr : lam * cross2 a b = det3 A B e := cross2_proj_rot hR hRe _ _
  have hab : 0 < cross2 a b := by
    rw [← hcr] at hdet; exact pos_of_mul_pos_right hdet hlam.le
  have hlift : ∀ (q : ℝ²) (s : ℝ), liftPt q 0 + s • (lam • ez) = liftPt q (s * lam) := by
    intro q s; ext i; fin_cases i <;> simp [liftPt, ez, mul_comm]
  have hlift2 : ∀ (c : ℝ) (q : ℝ²) (s : ℝ),
      c • liftPt q 0 + s • (lam • ez) = liftPt (c • q) (s * lam) := by
    intro c q s; ext i; fin_cases i <;> simp [liftPt, ez, mul_comm]
  apply isRupert_of_isRupert_image_rotation R hR
  apply isRupert_of_isRupert_image_add (-L v)
  have himg : (((prismShape v A B e l α β z1 z2).image L).image fun x => -L v + x) =
      quadRectStd a b (l * lam) α β (z1 * lam) (z2 * lam) := by
    unfold prismShape quadRectStd
    simp only [Finset.image_insert, Finset.image_singleton, map_add, map_smul, hRe]
    have e1 : -L v + L v = liftPt 0 0 := by ext i; fin_cases i <;> simp [liftPt]
    have e2 : -L v + (L v + L A) = liftPt a 0 := by rw [hLA]; abel
    have e3 : -L v + (L v + L A + l • (lam • ez)) = liftPt a (l * lam) := by
      rw [hLA, ← hlift]; abel
    have e4 : -L v + (L v + α • L A + z1 • (lam • ez)) = liftPt (α • a) (z1 * lam) := by
      rw [hLA, ← hlift2]; abel
    have e5 : -L v + (L v + L B) = liftPt b 0 := by rw [hLB]; abel
    have e6 : -L v + (L v + L B + l • (lam • ez)) = liftPt b (l * lam) := by
      rw [hLB, ← hlift]; abel
    have e7 : -L v + (L v + β • L B + z2 • (lam • ez)) = liftPt (β • b) (z2 * lam) := by
      rw [hLB, ← hlift2]; abel
    rw [e1, e2, e3, e4, e5, e6, e7]
  rw [himg]
  exact isRupert_quadRectStd a b _ α β _ _ hab (mul_pos hl hlam) hα0 hα1 hβ0 hβ1
    (mul_pos hz1 hlam) (mul_pos hz2 hlam)

/-- **B**: any prism shape (`e ≠ 0`, `A, B ⊥ e`, `A, B, e` independent, `0 < α, β < 1`, and
`l, z1, z2 > 0`) is Rupert. -/
theorem isRupert_prismShape (v A B e : ℝ³) (l α β z1 z2 : ℝ) (he : e ≠ 0)
    (hA : ⟪e, A⟫ = 0) (hB : ⟪e, B⟫ = 0) (hdet : det3 A B e ≠ 0)
    (hl : 0 < l) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hz1 : 0 < z1)
    (hz2 : 0 < z2) : IsRupert (prismShape v A B e l α β z1 z2) := by
  rcases lt_or_gt_of_ne hdet with h | h
  · rw [prismShape_swap]
    refine isRupert_prismShape_pos v B A e l β α z2 z1 he hB hA ?_ hl hβ0 hβ1 hα0 hα1 hz2 hz1
    rw [det3_swap]; linarith
  · exact isRupert_prismShape_pos v A B e l α β z1 z2 he hA hB h hl hα0 hα1 hβ0 hβ1 hz1 hz2

/-! ### Group A: `QuadTripleRect` forces a prism shape -/

theorem ker_eq_span_pair (L : ℝ³ →ₗ[ℝ] ℝ) (t : ℝ³) (ht : L t ≠ 0) (u e w : ℝ³)
    (hu : L u = 0) (he : L e = 0) (hw : L w = 0)
    (hind : ∀ s r : ℝ, s • u + r • e = 0 → s = 0 ∧ r = 0) :
    ∃ α ζ : ℝ, w = α • u + ζ • e := by
  have hsurj : Function.Surjective L := fun r => ⟨(r / L t) • t, by simp [map_smul, ht]⟩
  have hr : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  rw [hr, finrank_top, finrank_euclideanSpace_fin] at h1
  simp only [Module.finrank_self] at h1
  have hker : Module.finrank ℝ (LinearMap.ker L) = 2 := by omega
  have hli : LinearIndependent ℝ ![u, e] := by
    rw [LinearIndependent.pair_iff]; exact hind
  have hS := finrank_span_eq_card hli
  have hrange : Set.range ![u, e] = {u, e} := by simp [Matrix.range_cons, Set.pair_comm]
  rw [hrange] at hS
  simp at hS
  have hle : Submodule.span ℝ {u, e} ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hu
    · exact he
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hS, hker])
  have : w ∈ Submodule.span ℝ {u, e} := by rw [heq]; exact hw
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp this
  exact ⟨a, b, hab.symm⟩

theorem aff_lin (f : ℝ³ →ᵃ[ℝ] ℝ) (a b : ℝ³) : f.linear (a - b) = f a - f b := by
  have := f.linearMap_vsub a b
  simpa using this

/-- **A1** (linear algebra): the common direction of two distinct planes through `v`.  If `w` lies in
the direction spaces of both planes and `e ≠ 0` too, then `w ∥ e`.  (`f1.linear`, `f2.linear` are
independent: `f1` is nonconstant, `f2 y < 0 = f2 v` while `f1 y = f1 v` at some `y`.) -/
theorem eq_smul_of_ker_both (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) (v e w y z : ℝ³) (he : e ≠ 0)
    (hv1 : f1 v = 0) (hv2 : f2 v = 0) (he1 : f1 (v + e) = 0) (he2 : f2 (v + e) = 0)
    (hw1 : f1.linear w = 0) (hw2 : f2.linear w = 0)
    (hy1 : f1 y = 0) (hy2 : f2 y < 0) (hz1 : f1 z < 0) : ∃ c : ℝ, w = c • e := by
  have hLe1 : f1.linear e = 0 := by
    have := aff_lin f1 (v + e) v; rw [add_sub_cancel_left, he1, hv1] at this; simpa using this
  have hLe2 : f2.linear e = 0 := by
    have := aff_lin f2 (v + e) v; rw [add_sub_cancel_left, he2, hv2] at this; simpa using this
  have hLy2 : f2.linear (y - v) < 0 := by rw [aff_lin]; linarith
  obtain ⟨α, ζ, h⟩ := ker_eq_span_pair f1.linear (z - v) (by rw [aff_lin]; linarith) (y - v) e w
    (by rw [aff_lin]; linarith) hLe1 hw1 (by
      intro s r hsr
      have h2 := congrArg f2.linear hsr
      rw [map_add, map_smul, map_smul, hLe2, map_zero] at h2
      simp only [smul_eq_mul, mul_zero, add_zero] at h2
      have hs : s = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · linarith
      subst hs
      simp only [zero_smul, zero_add] at hsr
      exact ⟨rfl, (smul_eq_zero.mp hsr).resolve_right he⟩)
  have h2 := congrArg f2.linear h
  rw [hw2, map_add, map_smul, map_smul, hLe2] at h2
  simp only [smul_eq_mul, mul_zero, add_zero] at h2
  have hα : α = 0 := by
    rcases mul_eq_zero.mp h2.symm with h | h
    · exact h
    · linarith
  exact ⟨ζ, by rw [h, hα, zero_smul, zero_add]⟩

/-- **A2** (the faces): `Q1 = {v, p', p, r1}` with `p = p' + l e` and `r1 = v + α(p' - v) + ζ e`,
`0 < α < 1`, `ζ ≠ 0`.  Hypotheses are the data extracted from `QuadTripleRect` for the face `Q1`
(`f1` its functional, `f2` the functional of the other face, `p, p'` the two minimizers of `f2`,
`e ⊥ (p' - v)` since `⟪p', e⟫ = ⟪v, e⟫`). -/
theorem quadFace_coords {V Q1 : Finset ℝ³} {v p p' e : ℝ³} (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (hgen : NoThreeCollinear V) (hQV : Q1 ⊆ V) (hc : Q1.card = 4) (hvQ : v ∈ Q1)
    (hf1 : ∀ x ∈ Q1, f1 x = 0) (hf1' : ∃ z ∈ V, f1 z < 0) (hf2v : f2 v = 0)
    (hfar : ∀ x ∈ Q1, x ≠ v → f2 x < 0)
    (he : e ≠ 0) (he1 : f1 (v + e) = 0) (he2 : f2 (v + e) = 0) (hy : ∃ y, f1 y = 0 ∧ f2 y < 0)
    (hp : p ∈ Q1) (hp' : p' ∈ Q1) (hpm : ∀ x ∈ Q1, f2 p ≤ f2 x) (hpm' : ∀ x ∈ Q1, f2 p' ≤ f2 x)
    (hne : ⟪p, e⟫ ≠ ⟪p', e⟫) (hp'e : ⟪p' - v, e⟫ = 0) :
    ∃ (l α ζ : ℝ), p = p' + l • e ∧ 0 < α ∧ α < 1 ∧ ζ ≠ 0 ∧
      Q1 = {v, p', p, v + α • (p' - v) + ζ • e} := by
  classical
  obtain ⟨z, hzV, hz⟩ := hf1'
  have hf1v : f1 v = 0 := hf1 v hvQ
  have hLe1 : f1.linear e = 0 := by
    have := aff_lin f1 (v + e) v; rw [add_sub_cancel_left, he1, hf1v] at this; simpa using this
  have hLe2 : f2.linear e = 0 := by
    have := aff_lin f2 (v + e) v; rw [add_sub_cancel_left, he2, hf2v] at this; simpa using this
  obtain ⟨x0, hx0, hx0v⟩ : ∃ x ∈ Q1, x ≠ v := by
    by_contra h
    push Not at h
    have h1 : Q1 ⊆ {v} := fun x hx => by simpa using h x hx
    have := Finset.card_le_card h1
    simp at this; omega
  have hneg0 := hfar x0 hx0 hx0v
  have hp'v : p' ≠ v := by
    intro h; have := hpm' x0 hx0; rw [h, hf2v] at this; linarith
  have hpv : p ≠ v := by
    intro h; have := hpm x0 hx0; rw [h, hf2v] at this; linarith
  have hpp' : p ≠ p' := fun h => hne (by rw [h])
  have hfp' : f2 p' < 0 := hfar p' hp' hp'v
  have hfpp : f2 p = f2 p' := le_antisymm (hpm p' hp') (hpm' p hp)
  obtain ⟨l, hl⟩ := eq_smul_of_ker_both f1 f2 v e (p - p') p' z he hf1v hf2v he1 he2
    (by rw [aff_lin, hf1 p hp, hf1 p' hp']; simp) (by rw [aff_lin, hfpp]; simp)
    (hf1 p' hp') hfp' hz
  have hpl : p = p' + l • e := by rw [← hl]; abel
  have hl0 : l ≠ 0 := by
    intro h; apply hpp'; rw [hpl, h]; simp
  -- the fourth point
  have h3 : ({v, p', p} : Finset ℝ³).card = 3 :=
    Finset.card_eq_three.mpr ⟨v, p', p, hp'v.symm, hpv.symm, hpp'.symm, rfl⟩
  have hsub : ({v, p', p} : Finset ℝ³) ⊆ Q1 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcs : (Q1 \ {v, p', p}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, h3, hc]
  obtain ⟨r1, hr1⟩ := Finset.card_eq_one.mp hcs
  have hr1mem : r1 ∈ Q1 \ {v, p', p} := by rw [hr1]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hr1mem
  obtain ⟨hr1Q, hr1v, hr1p', hr1p⟩ := hr1mem
  have hQ1 : Q1 = {v, p', p, r1} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hx3 : x = v ∨ x = p' ∨ x = p
      · tauto
      · right; right; right
        have : x ∈ Q1 \ {v, p', p} := by
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨hx, hx3⟩
        rw [hr1] at this; simpa using this
    · rintro (rfl | rfl | rfl | rfl) <;> assumption
  -- coordinates of r1
  have hp'v0 : p' - v ≠ 0 := sub_ne_zero.mpr hp'v
  obtain ⟨α, ζ, hαζ⟩ := ker_eq_span_pair f1.linear (z - v) (by rw [aff_lin]; linarith) (p' - v) e
    (r1 - v) (by rw [aff_lin, hf1 p' hp', hf1v]; simp) hLe1
    (by rw [aff_lin, hf1 r1 hr1Q, hf1v]; simp) (by
      intro s r hsr
      have h2 := congrArg (fun w => ⟪p' - v, w⟫) hsr
      simp only [inner_add_right, inner_smul_right, hp'e, mul_zero, add_zero, inner_zero_right] at h2
      have hs : s = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (inner_self_eq_zero.mp h) hp'v0
      subst hs
      simp only [zero_smul, zero_add] at hsr
      exact ⟨rfl, (smul_eq_zero.mp hsr).resolve_right he⟩)
  have hr1eq : r1 = v + α • (p' - v) + ζ • e := by rw [add_assoc, ← hαζ]; abel
  have hf2r : f2 r1 = α * f2 p' := by
    have h2 := congrArg f2.linear hαζ
    rw [map_add, map_smul, map_smul, hLe2, aff_lin, aff_lin, hf2v] at h2
    simp only [smul_eq_mul, mul_zero, add_zero, sub_zero] at h2
    exact h2
  have hfr1 : f2 r1 < 0 := hfar r1 hr1Q hr1v
  have hα0 : 0 < α := by
    by_contra h; push Not at h; nlinarith
  have hα1 : α ≤ 1 := by
    by_contra h; push Not at h
    have := hpm' r1 hr1Q; nlinarith
  have hα1' : α ≠ 1 := by
    intro h
    have hpV := hQV hp; have hp'V := hQV hp'; have hrV := hQV hr1Q
    refine hgen p' hp'V p hpV r1 hrV hpp'.symm (Ne.symm hr1p') (Ne.symm hr1p) (ζ / l) ?_
    rw [hr1eq, h, hpl]
    simp only [one_smul, add_sub_cancel_left, smul_smul]
    rw [div_mul_cancel₀ _ hl0]
    abel
  have hζ : ζ ≠ 0 := by
    intro h
    have hpV := hQV hp'; have hvV := hQV hvQ; have hrV := hQV hr1Q
    refine hgen v hvV p' hpV r1 hrV hp'v.symm (Ne.symm hr1v) (Ne.symm hr1p') α ?_
    rw [hr1eq, h]; simp
  exact ⟨l, α, ζ, hpl, hα0, lt_of_le_of_ne hα1 hα1', hζ, by rw [hQ1, hr1eq]⟩

theorem face_ne_v {Q : Finset ℝ³} {v a : ℝ³} (fb : ℝ³ →ᵃ[ℝ] ℝ) (hc : Q.card = 4) (hvQ : v ∈ Q)
    (hfbv : fb v = 0) (hfar : ∀ x ∈ Q, x ≠ v → fb x < 0) (ham : ∀ x ∈ Q, fb a ≤ fb x) :
    (∃ x ∈ Q, x ≠ v) ∧ a ≠ v := by
  have hx : ∃ x ∈ Q, x ≠ v := by
    by_contra h
    push Not at h
    have h1 : Q ⊆ {v} := fun x hx => by simpa using h x hx
    have := Finset.card_le_card h1
    simp at this; omega
  obtain ⟨x0, hx0, hx0v⟩ := hx
  refine ⟨⟨x0, hx0, hx0v⟩, ?_⟩
  intro h; have := ham x0 hx0; rw [h, hfbv] at this; linarith [hfar x0 hx0 hx0v]

theorem minimizer_dir {V Q : Finset ℝ³} {v e a b : ℝ³} (fa fb : ℝ³ →ᵃ[ℝ] ℝ)
    (hc : Q.card = 4) (hvQ : v ∈ Q) (hfa : ∀ x ∈ Q, fa x = 0) (hfbv : fb v = 0)
    (hfar : ∀ x ∈ Q, x ≠ v → fb x < 0) (he : e ≠ 0) (hea : fa (v + e) = 0) (heb : fb (v + e) = 0)
    (hz : ∃ z ∈ V, fa z < 0) (ha : a ∈ Q) (hb : b ∈ Q) (ham : ∀ x ∈ Q, fb a ≤ fb x)
    (hbm : ∀ x ∈ Q, fb b ≤ fb x) : ∃ c : ℝ, b - a = c • e := by
  obtain ⟨z, -, hz⟩ := hz
  obtain ⟨-, hav⟩ := face_ne_v fb hc hvQ hfbv hfar ham
  exact eq_smul_of_ker_both fa fb v e (b - a) a z he (hfa v hvQ) hfbv hea heb
    (by rw [aff_lin, hfa a ha, hfa b hb]; simp)
    (by rw [aff_lin, le_antisymm (hbm a ha) (ham b hb)]; simp)
    (hfa a ha) (hfar a ha hav) hz

theorem minimizer_mem {V Q : Finset ℝ³} {v e a b w : ℝ³} (fa fb : ℝ³ →ᵃ[ℝ] ℝ)
    (hgen : NoThreeCollinear V) (hQV : Q ⊆ V)
    (hc : Q.card = 4) (hvQ : v ∈ Q) (hfa : ∀ x ∈ Q, fa x = 0) (hfbv : fb v = 0)
    (hfar : ∀ x ∈ Q, x ≠ v → fb x < 0) (he : e ≠ 0) (hea : fa (v + e) = 0) (heb : fb (v + e) = 0)
    (hz : ∃ z ∈ V, fa z < 0) (ha : a ∈ Q) (hb : b ∈ Q) (hw : w ∈ Q) (ham : ∀ x ∈ Q, fb a ≤ fb x)
    (hbm : ∀ x ∈ Q, fb b ≤ fb x) (hwm : ∀ x ∈ Q, fb w ≤ fb x) (hab : a ≠ b) : w = a ∨ w = b := by
  by_contra h
  push Not at h
  obtain ⟨c1, h1⟩ := minimizer_dir (V := V) fa fb hc hvQ hfa hfbv hfar he hea heb hz ha hw ham hwm
  obtain ⟨c2, h2⟩ := minimizer_dir (V := V) fa fb hc hvQ hfa hfbv hfar he hea heb hz ha hb ham hbm
  have hc2 : c2 ≠ 0 := by
    rintro rfl; apply hab; simp at h2; exact (sub_eq_zero.mp h2).symm
  refine hgen a (hQV ha) b (hQV hb) w (hQV hw) hab (Ne.symm h.1) (Ne.symm h.2) (c1 / c2) ?_
  rw [h1, h2, smul_smul, div_mul_cancel₀ _ hc2]

theorem det3_ne_planes (L1 L2 : ℝ³ →ₗ[ℝ] ℝ) (A B e : ℝ³) (he : e ≠ 0) (hA1 : L1 A = 0)
    (hB1 : L1 B ≠ 0) (he1 : L1 e = 0) (he2 : L2 e = 0) (hA2 : L2 A ≠ 0) : det3 A B e ≠ 0 := by
  intro h0
  have hc := congrArg L1 (det3_cramer A B e (cross e A))
  simp only [map_add, map_sub, map_smul, hA1, he1, h0, zero_smul, map_zero, smul_eq_mul,
    mul_zero, add_zero, zero_add] at hc
  have h3 : det3 A e (cross e A) * L1 B = 0 := by linarith
  have h4 : det3 A e (cross e A) = 0 := (mul_eq_zero.mp h3).resolve_right hB1
  have h5 : det3 e A (cross e A) = 0 := by rw [det3_swap, h4]; simp
  have h6 : det3 e A (cross e A) = ⟪cross e A, cross e A⟫ := by rw [det3, real_inner_comm]
  rw [h6, inner_self_eq_zero] at h5
  have h7 := eq_smul_of_cross_eq_zero he h5
  apply hA2
  rw [h7, map_smul, he2, smul_zero]

theorem prism_assemble {V Q1 Q2 : Finset ℝ³} {v a c e : ℝ³} {l α β z1 z2 : ℝ}
    (hU : Q1 ∪ Q2 = V) (hQ1 : Q1 = {v, a, a + l • e, v + α • (a - v) + z1 • e})
    (hQ2 : Q2 = {v, c, c + l • e, v + β • (c - v) + z2 • e}) :
    V = prismShape v (a - v) (c - v) e l α β z1 z2 := by
  classical
  rw [← hU, hQ1, hQ2]
  unfold prismShape
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, add_sub_cancel]
  tauto

set_option maxHeartbeats 1600000 in
/-- **A3**: `QuadTripleRect` at `Q1, Q2` with `Q1 ∩ Q2 = {v}`, `Q1 ∪ Q2 = V`, four points each and no
three collinear gives a prism shape with `⟪x - v, e⟫ ≥ 0`.  The symmetries used: swapping
`(p, q) ↔ (p', q')`, `e ↦ -e` (choose by the disjunction `∃ w ∈ Q1 …` / `∃ w ∈ Q2 …` and the side
`≤`/`≥`), `Q1 ↔ Q2`; `l = ⟪p - v, e⟫/|e|²`-type scalars are absorbed in `l`, `ζ`. -/
theorem prismShape_of_quadTripleRect {V Q1 Q2 : Finset ℝ³} {v : ℝ³}
    (hgen : NoThreeCollinear V) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hc1 : Q1.card = 4) (hc2 : Q2.card = 4) (hU : Q1 ∪ Q2 = V)
    (hQ : QuadTripleRect V Q1 Q2 v) :
    ∃ (A B e : ℝ³) (l α β z1 z2 : ℝ), e ≠ 0 ∧ ⟪e, A⟫ = 0 ∧ ⟪e, B⟫ = 0 ∧ det3 A B e ≠ 0 ∧
      0 < l ∧ 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < z1 ∧ 0 < z2 ∧
      V = prismShape v A B e l α β z1 z2 := by
  classical
  obtain ⟨f1, f2, hf1, hf1n, hf2, hf2n, e, he, he1, he2, p, hp, p', hp', q, hq, q', hq', hpm, hpm',
    hqm, hqm', hpq, hpq', hne, hD, hS⟩ := hQ
  have hvQ1 : v ∈ Q1 := by
    have : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
    exact (Finset.mem_inter.mp this).1
  have hvQ2 : v ∈ Q2 := by
    have : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
    exact (Finset.mem_inter.mp this).2
  have hf1v : f1 v = 0 := hf1 v hvQ1
  have hf2v : f2 v = 0 := hf2 v hvQ2
  have hmem : ∀ x ∈ Q1, x ∈ Q2 → x = v := fun x h1 h2 => by
    have : x ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this; simpa using this
  have hfar1 : ∀ x ∈ Q1, x ≠ v → f2 x < 0 := fun x hx hxv =>
    hf2n x (h1V hx) (fun h => hxv (hmem x hx h))
  have hfar2 : ∀ x ∈ Q2, x ≠ v → f1 x < 0 := fun x hx hxv =>
    hf1n x (h2V hx) (fun h => hxv (hmem x h hx))
  obtain ⟨⟨x1, hx1, hx1v⟩, -⟩ := face_ne_v (a := p) f2 hc1 hvQ1 hf2v hfar1 hpm
  obtain ⟨⟨x2, hx2, hx2v⟩, -⟩ := face_ne_v (a := q) f1 hc2 hvQ2 hf1v hfar2 hqm
  have hz1 : ∃ z ∈ V, f1 z < 0 := ⟨x2, h2V hx2, hfar2 x2 hx2 hx2v⟩
  have hz2 : ∃ z ∈ V, f2 z < 0 := ⟨x1, h1V hx1, hfar1 x1 hx1 hx1v⟩
  have hy1 : ∃ y, f1 y = 0 ∧ f2 y < 0 := ⟨x1, hf1 x1 hx1, hfar1 x1 hx1 hx1v⟩
  have hy2 : ∃ y, f2 y = 0 ∧ f1 y < 0 := ⟨x2, hf2 x2 hx2, hfar2 x2 hx2 hx2v⟩
  have hpp' : p ≠ p' := fun h => hne (by rw [h])
  have hqq' : q ≠ q' := fun h => hne (by rw [hpq, hpq', h])
  obtain ⟨a, b, c, d, ha, hb, hc, hd, ham, hbm, hcm, hdm, hac, hbd, hab, hav⟩ :
      ∃ a b c d, a ∈ Q1 ∧ b ∈ Q1 ∧ c ∈ Q2 ∧ d ∈ Q2 ∧ (∀ x ∈ Q1, f2 a ≤ f2 x) ∧
        (∀ x ∈ Q1, f2 b ≤ f2 x) ∧ (∀ x ∈ Q2, f1 c ≤ f1 x) ∧ (∀ x ∈ Q2, f1 d ≤ f1 x) ∧
        ⟪a, e⟫ = ⟪c, e⟫ ∧ ⟪b, e⟫ = ⟪d, e⟫ ∧ ⟪a, e⟫ ≠ ⟪b, e⟫ ∧ ⟪a - v, e⟫ = 0 := by
    rcases hD with ⟨w, hw, hwm, hwe⟩ | ⟨w, hw, hwm, hwe⟩
    · rcases minimizer_mem (V := V) f1 f2 hgen h1V hc1 hvQ1 hf1 hf2v hfar1 he he1 he2 hz1 hp hp' hw
        hpm hpm' hwm hpp' with h | h
      · rw [h] at hwe
        exact ⟨p, p', q, q', hp, hp', hq, hq', hpm, hpm', hqm, hqm', hpq, hpq', hne,
          by rw [inner_sub_left, hwe, sub_self]⟩
      · rw [h] at hwe
        exact ⟨p', p, q', q, hp', hp, hq', hq, hpm', hpm, hqm', hqm, hpq', hpq, hne.symm,
          by rw [inner_sub_left, hwe, sub_self]⟩
    · rcases minimizer_mem (V := V) f2 f1 hgen h2V hc2 hvQ2 hf2 hf1v hfar2 he he2 he1 hz2 hq hq' hw
        hqm hqm' hwm hqq' with h | h
      · rw [h] at hwe
        exact ⟨p, p', q, q', hp, hp', hq, hq', hpm, hpm', hqm, hqm', hpq, hpq', hne,
          by rw [inner_sub_left, hpq, hwe, sub_self]⟩
      · rw [h] at hwe
        exact ⟨p', p, q', q, hp', hp, hq', hq, hpm', hpm, hqm', hqm, hpq', hpq, hne.symm,
          by rw [inner_sub_left, hpq', hwe, sub_self]⟩
  have hav' : ⟪a, e⟫ = ⟪v, e⟫ := by rw [inner_sub_left] at hav; linarith
  have hcv' : ⟪c, e⟫ = ⟪v, e⟫ := by rw [← hac]; exact hav'
  obtain ⟨l, α, ζ, hbl, hα0, hα1, hζ, hQ1e⟩ := quadFace_coords (V := V) f1 f2 hgen h1V hc1 hvQ1 hf1
    hz1 hf2v hfar1 he he1 he2 hy1 hb ha hbm ham hab.symm hav
  obtain ⟨l', β, ζ', hdl, hβ0, hβ1, hζ', hQ2e⟩ := quadFace_coords (V := V) f2 f1 hgen h2V hc2 hvQ2
    hf2 hz2 hf1v hfar2 he he2 he1 hy2 hd hc hdm hcm (by rw [← hbd, ← hac]; exact hab.symm)
    (by rw [inner_sub_left, hcv', sub_self])
  have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr he
  have hee' : 0 < ⟪e, e⟫ := lt_of_le_of_ne real_inner_self_nonneg (Ne.symm hee)
  have h1 : ⟪b, e⟫ - ⟪a, e⟫ = l * ⟪e, e⟫ := by
    rw [hbl, inner_add_left, real_inner_smul_left]; ring
  have h1' : ⟪d, e⟫ - ⟪c, e⟫ = l' * ⟪e, e⟫ := by
    rw [hdl, inner_add_left, real_inner_smul_left]; ring
  have hll : l = l' := by
    apply mul_right_cancel₀ hee; rw [← h1, ← h1', hbd, hac]
  subst hll
  have hl0 : l ≠ 0 := by
    intro h; apply hab; rw [h, zero_mul] at h1; linarith
  have hr1 : ⟪v + α • (a - v) + ζ • e - v, e⟫ = ζ * ⟪e, e⟫ := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hav']; ring
  have hr2 : ⟪v + β • (c - v) + ζ' • e - v, e⟫ = ζ' * ⟪e, e⟫ := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hcv']; ring
  have hr1Q : v + α • (a - v) + ζ • e ∈ Q1 := by rw [hQ1e]; simp
  have hr2Q : v + β • (c - v) + ζ' • e ∈ Q2 := by rw [hQ2e]; simp
  -- the planes are independent
  have hav0 : a ≠ v := (face_ne_v f2 hc1 hvQ1 hf2v hfar1 ham).2
  have hcv0 : c ≠ v := (face_ne_v f1 hc2 hvQ2 hf1v hfar2 hcm).2
  have hLe1 : f1.linear e = 0 := by
    have := aff_lin f1 (v + e) v; rw [add_sub_cancel_left, he1, hf1v] at this; simpa using this
  have hLe2 : f2.linear e = 0 := by
    have := aff_lin f2 (v + e) v; rw [add_sub_cancel_left, he2, hf2v] at this; simpa using this
  have hA1 : f1.linear (a - v) = 0 := by rw [aff_lin, hf1 a ha, hf1v]; simp
  have hB1 : f1.linear (c - v) ≠ 0 := by
    rw [aff_lin, hf1v, sub_zero]; exact (hfar2 c hc hcv0).ne
  have hA2 : f2.linear (a - v) ≠ 0 := by
    rw [aff_lin, hf2v, sub_zero]; exact (hfar1 a ha hav0).ne
  have final : ∀ (e' : ℝ³) (l' z1 z2 : ℝ), e' ≠ 0 → f1.linear e' = 0 → f2.linear e' = 0 →
      ⟪e', a - v⟫ = 0 → ⟪e', c - v⟫ = 0 → 0 < l' → 0 < z1 → 0 < z2 →
      Q1 = {v, a, a + l' • e', v + α • (a - v) + z1 • e'} →
      Q2 = {v, c, c + l' • e', v + β • (c - v) + z2 • e'} →
      ∃ (A B e : ℝ³) (l α β z1 z2 : ℝ), e ≠ 0 ∧ ⟪e, A⟫ = 0 ∧ ⟪e, B⟫ = 0 ∧ det3 A B e ≠ 0 ∧
      0 < l ∧ 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 < z1 ∧ 0 < z2 ∧
      V = prismShape v A B e l α β z1 z2 := by
    intro e' l' z1 z2 he' h1' h2' hA hB hl' hz1' hz2' hQ1' hQ2'
    exact ⟨a - v, c - v, e', l', α, β, z1, z2, he', hA, hB,
      det3_ne_planes f1.linear f2.linear _ _ e' he' hA1 hB1 h1' h2' hA2, hl', hα0, hα1, hβ0, hβ1,
      hz1', hz2', prism_assemble hU hQ1' hQ2'⟩
  have hb1 : b = a + l • e := hbl
  have hd1 : d = c + l • e := hdl
  have hQ1' : Q1 = {v, a, a + l • e, v + α • (a - v) + ζ • e} := by rw [hQ1e, hbl]
  have hQ2' : Q2 = {v, c, c + l • e, v + β • (c - v) + ζ' • e} := by rw [hQ2e, hdl]
  have hbQ : b ∈ Q1 ∪ Q2 := Finset.mem_union_left _ hb
  have hr1Q' : v + α • (a - v) + ζ • e ∈ Q1 ∪ Q2 := Finset.mem_union_left _ hr1Q
  have hr2Q' : v + β • (c - v) + ζ' • e ∈ Q1 ∪ Q2 := Finset.mem_union_right _ hr2Q
  have hbv : ⟪b - v, e⟫ = l * ⟪e, e⟫ := by rw [inner_sub_left]; linarith
  rcases hS with hS | hS
  · have hl1 := hS b hbQ
    have hl2 := hS _ hr1Q'
    have hl3 := hS _ hr2Q'
    have hlp : 0 < l := by
      have : 0 ≤ l := by by_contra h; push Not at h; nlinarith
      exact lt_of_le_of_ne this (Ne.symm hl0)
    have hz1p : 0 < ζ := by
      have : 0 ≤ ζ := by
        by_contra h; push Not at h; rw [inner_sub_left] at hr1; nlinarith
      exact lt_of_le_of_ne this (Ne.symm hζ)
    have hz2p : 0 < ζ' := by
      have : 0 ≤ ζ' := by
        by_contra h; push Not at h; rw [inner_sub_left] at hr2; nlinarith
      exact lt_of_le_of_ne this (Ne.symm hζ')
    exact final e l ζ ζ' he hLe1 hLe2 (by rw [real_inner_comm]; exact hav)
      (by rw [real_inner_comm, inner_sub_left, hcv', sub_self]) hlp hz1p hz2p hQ1' hQ2'
  · have hl1 := hS b hbQ
    have hl2 := hS _ hr1Q'
    have hl3 := hS _ hr2Q'
    have hlp : l < 0 := by
      have : l ≤ 0 := by by_contra h; push Not at h; nlinarith
      exact lt_of_le_of_ne this hl0
    have hz1p : ζ < 0 := by
      have : ζ ≤ 0 := by
        by_contra h; push Not at h; rw [inner_sub_left] at hr1; nlinarith
      exact lt_of_le_of_ne this hζ
    have hz2p : ζ' < 0 := by
      have : ζ' ≤ 0 := by
        by_contra h; push Not at h; rw [inner_sub_left] at hr2; nlinarith
      exact lt_of_le_of_ne this hζ'
    refine final (-e) (-l) (-ζ) (-ζ') (neg_ne_zero.mpr he) (by rw [map_neg, hLe1, neg_zero])
      (by rw [map_neg, hLe2, neg_zero]) (by rw [inner_neg_left, real_inner_comm, hav, neg_zero])
      (by rw [inner_neg_left, real_inner_comm, inner_sub_left, hcv', sub_self, neg_zero])
      (by linarith) (by linarith) (by linarith) ?_ ?_
    · rw [neg_smul_neg, neg_smul_neg]; exact hQ1'
    · rw [neg_smul_neg, neg_smul_neg]; exact hQ2'

/-! ### Group D: the wiring -/

/-- **Theorem 09.Q** in the form of the skeleton: `QuadTripleRect` at the quadrilaterals `0134`,
`0256` (vertex `0`) of seven points in general position makes them Rupert.  (No face of type 09
besides the two quadrilaterals is used.) -/
theorem isRupert_of_quadTripleRect09 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hQ : QuadTripleRect (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
      (({0, 2, 5, 6} : Finset (Fin 7)).image x) (x 0)) :
    IsRupert (Finset.univ.image x) := by
  classical
  have h1V : ({0, 1, 3, 4} : Finset (Fin 7)).image x ⊆ Finset.univ.image x :=
    Finset.image_subset_image (Finset.subset_univ _)
  have h2V : ({0, 2, 5, 6} : Finset (Fin 7)).image x ⊆ Finset.univ.image x :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hint : ({0, 1, 3, 4} : Finset (Fin 7)).image x ∩ ({0, 2, 5, 6} : Finset (Fin 7)).image x
      = {x 0} := by
    rw [← Finset.image_inter _ _ hx, show ({0, 1, 3, 4} : Finset (Fin 7)) ∩ {0, 2, 5, 6} = {0} by
      decide, Finset.image_singleton]
  have hc1 : (({0, 1, 3, 4} : Finset (Fin 7)).image x).card = 4 := by
    rw [Finset.card_image_of_injective _ hx]; decide
  have hc2 : (({0, 2, 5, 6} : Finset (Fin 7)).image x).card = 4 := by
    rw [Finset.card_image_of_injective _ hx]; decide
  have hU : ({0, 1, 3, 4} : Finset (Fin 7)).image x ∪ ({0, 2, 5, 6} : Finset (Fin 7)).image x
      = Finset.univ.image x := by
    rw [← Finset.image_union, show ({0, 1, 3, 4} : Finset (Fin 7)) ∪ {0, 2, 5, 6} = Finset.univ by
      decide]
  obtain ⟨A, B, e, l, α, β, z1, z2, he, hA, hB, hdet, hl, hα0, hα1, hβ0, hβ1, hz1, hz2, hV⟩ :=
    prismShape_of_quadTripleRect hgen h1V h2V hint hc1 hc2 hU hQ
  rw [hV]
  exact isRupert_prismShape _ A B e l α β z1 z2 he hA hB hdet hl hα0 hα1 hβ0 hβ1 hz1 hz2

end Minimality

end
