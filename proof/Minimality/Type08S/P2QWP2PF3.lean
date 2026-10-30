module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QWSCl
public import Minimality.Type08S.P2QWP2PF0
public import Minimality.Type08S.P2QWP2PF1
public import Minimality.Type08S.P2QWP2PF2

@[expose] public section

set_option relaxedAutoImplicit true
set_option relaxedAutoImplicit true

/-!
# P-F, T4 `K_2` (`x' = b`, `x = d`, `f = c'`, `r = b'`, `g = c`, F-middle `a`, G-middle `a'`):
the picture facts of `Norm08w + RegT4`, and `ClsT4 b d c' b' c a a'` from the top-vertex class `TopP` alone.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W5

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
theorem pic_K2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫) :
    PicT4 ⟪c' - b, e1⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪a - b, e1⟫
      (⟪a' - b, e2⟫ / ⟪c - b, e2⟫) := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
  obtain ⟨h6, h1⟩ := theta_T4 N hE hθ hpts hreg
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
  have h66 : nfShape08 d E₁ E₂ E₃ θ 6 = d := rfl
  obtain ⟨p0, p1, p2, p3, p4, p5, e1', e2', e3', ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08w θ hθ.1 hθ.2.1 hθ.2.2
  have dA : 0 < 1 - θ 5 := by linarith
  have dB : 0 < -1 + θ 0 := by linarith
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := polyBw (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)
    p0 p1 p2 p3 p4 p5 e1' e2' e3' dA dB ga gb f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  have hu : nfShape08 d E₁ E₂ E₃ θ 6 - nfShape08 d E₁ E₂ E₃ θ 2 = κ • e3 := hxe
  have hkD : 0 < κ * det3 E₁ E₂ E₃ := by
    have h1 := cross_pts hF hxe ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 5)) ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 3)) ((nfShape08 d E₁ E₂ E₃ θ 2))
    have h2 := det3_nfd d E₁ E₂ E₃ θ 2 6 2 5 2 3
    have hq : ddet (fun k => cp08 θ 6 k - cp08 θ 2 k) (fun k => cp08 θ 5 k - cp08 θ 2 k)
        (fun k => cp08 θ 3 k - cp08 θ 2 k) = θ 0 * θ 3 := by
      simp [ddet, cp08]; try ring
    rw [hq, h66] at h2
    simp only [sub_self, inner_zero_left, sub_zero, hf2, zero_mul] at h1
    refine kD_pos hκ (L := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫) (Y := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (P := θ 0 * θ 3) ?_ hL hr
      (mul_pos p0 p3)
    linear_combination h2 - h1
  have T1 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 2)) 3 4 3 5 _ (by simp [ddet, cp08]; try ring) t3
  have T2 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 2)) 2 3 2 4 _ (by simp [ddet, cp08]; try ring) t6
  have T3 := tgt_eq d E₁ E₂ E₃ θ hF hu ((nfShape08 d E₁ E₂ E₃ θ 2)) 2 5 2 1 (θ 0 * θ 5) (by simp [ddet, cp08]; try ring)
  have T4 := tgt_eq d E₁ E₂ E₃ θ hF hu ((nfShape08 d E₁ E₂ E₃ θ 2)) 2 5 2 4 (θ 0) (by simp [ddet, cp08]; try ring)
  simp only [h66, sub_self, inner_zero_left, sub_zero, hf2, zero_mul] at T1 T2 T3 T4
  -- F-middle
  have hvec : θ 0 • ((nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2)) = ((nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2)) + (θ 0 + θ 1 - 1) • (d - (nfShape08 d E₁ E₂ E₃ θ 2)) := by
    simp only [nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    module
  have hb1 : ⟪d - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ = 0 := by
    rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n13]; ring
  have hXd : θ 0 * ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ = ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ := by
    have := congrArg (fun v => ⟪v, e1⟫) hvec
    simp only [inner_add_left, real_inner_smul_left, hb1] at this
    linarith
  -- G-middle
  have hLg : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := by
    refine sign_transfer hκ hkD (T := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (Q := θ 0) ?_ p0
    linear_combination T4
  have hYg : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := pos_of_mul_pos_right hLg hL.le
  have hYq : ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ = θ 5 * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := by
    have h0 : (κ * ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫) * (⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ - θ 5 * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) = 0 := by
      linear_combination T3 - θ 5 * T4
    have hne : κ * ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ ≠ 0 := mul_ne_zero hκ hL.ne'
    have := (mul_eq_zero.mp h0).resolve_left hne
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have : 0 < θ 0 * ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ := by rw [hXd]; exact hL
    exact pos_of_mul_pos_right this p0.le
  · by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos dB hL]
  · rw [hYq, mul_div_assoc, div_self hYg.ne', mul_one]
    linarith

theorem ClsT4_K2_of_top {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    (htop : TopP 0 ⟪c' - b, e1⟫ ⟪d - b, e3⟫ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e2⟫ ⟪b' - b, e3⟫
      ⟪c - b, e1⟫ ⟪c - b, e2⟫ ⟪c - b, e3⟫) : ClsT4 b d c' b' c a a' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pic_K2 N hreg hF hκ hxe hf2 hL hr
  exact ⟨e1, e2, e3, κ, hF, hκ, hxe, hf2, hL, hr, h1, h2, htop, h3, h4, h5⟩

end W5
end Type08Sp
end Minimality

