module

public import Minimality.Type08S.P2PF0

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F, N2 `K_c` (view `c - a'`): the picture facts of `Norm08 + RegN2`.

In the canonical frame at `a'` (`c - a' = κ e3`, `b - a'` edge-on with `X_b = L > 0`, `Y_{c'} > 0`):
the screen quadrilateral `(x̄, f̄, r̄, ḡ) = (0, b̄, c̄', b̄')` is strictly convex at `r` and `g`, the F-middle
`d` is over the open chord (`0 < X_d < L`), and `a` is strictly inside the screen quadrilateral
(four strict inequalities).  NOTE (D5): `a` is NOT always inside the triangle `(x̄, f̄, ḡ)`
(true for ~5% of N2 samples); it lies in the triangle `(f̄, r̄, ḡ)` or on the diagonal `f̄ḡ` otherwise.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem inner_diff (x y z e : ℝ³) : ⟪x - y, e⟫ = ⟪x - z, e⟫ - ⟪y - z, e⟫ := by
  rw [← inner_sub_left]; congr 1; abel

/-- Screen cross product of two difference vectors, with origin `O`. -/
theorem cross_pts (hF : Fr e1 e2 e3) {u : ℝ³} {κ : ℝ} (hu : u = κ • e3) (O P Q R T : ℝ³) :
    det3 u (P - Q) (R - T) = κ * ((⟪P - O, e1⟫ - ⟪Q - O, e1⟫) * (⟪R - O, e2⟫ - ⟪T - O, e2⟫) -
      (⟪P - O, e2⟫ - ⟪Q - O, e2⟫) * (⟪R - O, e1⟫ - ⟪T - O, e1⟫)) := by
  rw [cross2_frame hF hu, inner_diff P Q O e1, inner_diff P Q O e2, inner_diff R T O e1,
    inner_diff R T O e2]

/-- The screen cross product as `D · (normal-form polynomial) / κ`. -/
theorem tgt_eq (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (hF : Fr e1 e2 e3) {κ : ℝ}
    {i0 j0 : Fin 7}
    (hu : nfShape08 o E₁ E₂ E₃ θ j0 - nfShape08 o E₁ E₂ E₃ θ i0 = κ • e3) (O : ℝ³)
    (i1 j1 i2 j2 : Fin 7) (Qp : ℝ)
    (hQe : ddet (fun k => cp08 θ j0 k - cp08 θ i0 k) (fun k => cp08 θ j1 k - cp08 θ i1 k)
      (fun k => cp08 θ j2 k - cp08 θ i2 k) = Qp) :
    κ * ((⟪nfShape08 o E₁ E₂ E₃ θ j1 - O, e1⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i1 - O, e1⟫) *
        (⟪nfShape08 o E₁ E₂ E₃ θ j2 - O, e2⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i2 - O, e2⟫) -
      (⟪nfShape08 o E₁ E₂ E₃ θ j1 - O, e2⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i1 - O, e2⟫) *
        (⟪nfShape08 o E₁ E₂ E₃ θ j2 - O, e1⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i2 - O, e1⟫)) =
      det3 E₁ E₂ E₃ * Qp := by
  rw [← cross_pts hF hu O, det3_nfd, hQe]

/-- Positivity of a screen cross product from a normal-form determinant. -/
theorem tgt_nf (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (hF : Fr e1 e2 e3) {κ : ℝ} (hk : κ ≠ 0)
    (hkD : 0 < κ * det3 E₁ E₂ E₃) {i0 j0 : Fin 7}
    (hu : nfShape08 o E₁ E₂ E₃ θ j0 - nfShape08 o E₁ E₂ E₃ θ i0 = κ • e3) (O : ℝ³)
    (i1 j1 i2 j2 : Fin 7) (Qp : ℝ)
    (hQe : ddet (fun k => cp08 θ j0 k - cp08 θ i0 k) (fun k => cp08 θ j1 k - cp08 θ i1 k)
      (fun k => cp08 θ j2 k - cp08 θ i2 k) = Qp) (hQ : 0 < Qp) :
    0 < (⟪nfShape08 o E₁ E₂ E₃ θ j1 - O, e1⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i1 - O, e1⟫) *
        (⟪nfShape08 o E₁ E₂ E₃ θ j2 - O, e2⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i2 - O, e2⟫) -
      (⟪nfShape08 o E₁ E₂ E₃ θ j1 - O, e2⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i1 - O, e2⟫) *
        (⟪nfShape08 o E₁ E₂ E₃ θ j2 - O, e1⟫ - ⟪nfShape08 o E₁ E₂ E₃ θ i2 - O, e1⟫) :=
  sign_transfer hk hkD (tgt_eq o E₁ E₂ E₃ θ hF hu O i1 j1 i2 j2 Qp hQe) hQ

/-- Picture numbers of the N2 closing `K_c` that are not class-(c) data (frame numbers). -/
def PicN2 (L Xr Yr Xg Yg Xd Xa Ya : ℝ) : Prop :=
  0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yg * Xr - Xg * Yr ∧ 0 < Xd ∧ Xd < L ∧
  0 < Ya ∧ 0 < (Xr - L) * Ya - Yr * (Xa - L) ∧
  0 < (Xg - Xr) * (Ya - Yr) - (Yg - Yr) * (Xa - Xr) ∧ 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)

set_option maxHeartbeats 4000000 in
theorem pic_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hce : c - a' = κ • e3) (hb2 : ⟪b - a', e2⟫ = 0)
    (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫) :
    PicN2 ⟪b - a', e1⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪d - a', e1⟫
      ⟪a - a', e1⟫ ⟪a - a', e2⟫ := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  have h6 := theta_N2 N hE hθ hpts hreg
  have hS : ∀ i, pts08 a a' b b' c c' d i = nfShape08 o E₁ E₂ E₃ θ i := fun i => by rw [hpts]
  have ha : a = nfShape08 o E₁ E₂ E₃ θ 0 := by simpa [pts08] using hS 0
  have ha' : a' = nfShape08 o E₁ E₂ E₃ θ 1 := by simpa [pts08] using hS 1
  have hb : b = nfShape08 o E₁ E₂ E₃ θ 2 := by simpa [pts08] using hS 2
  have hb' : b' = nfShape08 o E₁ E₂ E₃ θ 3 := by simpa [pts08] using hS 3
  have hc : c = nfShape08 o E₁ E₂ E₃ θ 4 := by simpa [pts08] using hS 4
  have hc' : c' = nfShape08 o E₁ E₂ E₃ θ 5 := by simpa [pts08] using hS 5
  have hd : d = nfShape08 o E₁ E₂ E₃ θ 6 := by simpa [pts08] using hS 6
  clear hpts hS
  subst ha ha' hb hb' hc hc' hd
  obtain ⟨p0, p1, p2, p3, p4, p5, e1', e2', e3', ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < -1 + θ 5 := by linarith
  have dB : 0 < -1 + θ 0 := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := polyA (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)
    p0 p1 p2 p3 p4 p5 e1' e2' e3' dA dB ga gb f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  have hu : (nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1) = κ • e3 := hce
  have hkD : 0 < κ * det3 E₁ E₂ E₃ := by
    have h1 := cross_pts hF hce ((nfShape08 d E₁ E₂ E₃ θ 1)) ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 1)) ((nfShape08 d E₁ E₂ E₃ θ 5)) ((nfShape08 d E₁ E₂ E₃ θ 1))
    have h2 := det3_nfd d E₁ E₂ E₃ θ 1 4 1 2 1 5
    have hq : ddet (fun k => cp08 θ 4 k - cp08 θ 1 k) (fun k => cp08 θ 2 k - cp08 θ 1 k)
        (fun k => cp08 θ 5 k - cp08 θ 1 k) = θ 0 * (θ 4 + θ 5 - 1) := by
      simp [ddet, cp08]; ring
    rw [hq] at h2
    simp only [sub_self, inner_zero_left, sub_zero, hb2] at h1
    refine kD_pos hκ (L := ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫) (Y := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 1), e2⟫) (P := θ 0 * (θ 4 + θ 5 - 1)) ?_ hL hr
      (by positivity)
    linear_combination h2 - h1
  have T1 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 5 3 5 2 _ (by simp [ddet, cp08]; ring) t3
  have T2 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 1 5 1 3 _ (by simp [ddet, cp08]; ring) t6
  have T3 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 1 2 1 0 _ (by simp [ddet, cp08]; ring) t2
  have T4 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 2 5 2 0 _ (by simp [ddet, cp08]; ring) t4
  have T5 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 5 3 5 0 _ (by simp [ddet, cp08]; ring) t7
  have T6 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 3 1 3 0 _ (by simp [ddet, cp08]; ring) t9
  simp only [sub_self, inner_zero_left, sub_zero, hb2] at T1 T2 T3 T4 T5 T6
  -- F-middle
  have hvec : (θ 4 + θ 5 - 1) • ((nfShape08 d E₁ E₂ E₃ θ 6) - (nfShape08 d E₁ E₂ E₃ θ 1)) = θ 4 • ((nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1)) + θ 5 • ((nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1)) := by
    simp only [nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    module
  have hc1 : ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ = 0 := by rw [hce, real_inner_smul_left, real_inner_comm]; rw [hF.n13]; ring
  have hXd : (θ 4 + θ 5 - 1) * ⟪(nfShape08 d E₁ E₂ E₃ θ 6) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ = θ 4 * ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ := by
    have := congrArg (fun v => ⟪v, e1⟫) hvec
    simp only [inner_add_left, real_inner_smul_left, hc1] at this
    linarith
  have hs : 0 < θ 4 + θ 5 - 1 := e3'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have : 0 < (θ 4 + θ 5 - 1) * ⟪(nfShape08 d E₁ E₂ E₃ θ 6) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ := by rw [hXd]; exact mul_pos p4 hL
    exact (pos_of_mul_pos_right this hs.le)
  · have h1 : 0 < (θ 4 + θ 5 - 1) * (⟪nfShape08 d E₁ E₂ E₃ θ 2 - nfShape08 d E₁ E₂ E₃ θ 1, e1⟫ -
        ⟪nfShape08 d E₁ E₂ E₃ θ 6 - nfShape08 d E₁ E₂ E₃ θ 1, e1⟫) := by
      nlinarith [mul_pos dA hL]
    exact sub_pos.mp (pos_of_mul_pos_right h1 hs.le)
  · have : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 1), e2⟫ := by linarith
    exact (pos_of_mul_pos_right this hL.le)
  · linarith
  · linarith
  · linarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.pic_N2
