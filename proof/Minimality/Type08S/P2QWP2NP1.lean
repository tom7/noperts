module

public import Minimality.Type08S.P2QQ0c
public import Minimality.Type08S.P2QWSCl
public import Minimality.Type08S.P2QWP2PF0
public import Minimality.Type08S.P2QWP2PF1
public import Minimality.Type08S.P2QWP2PF2
public import Minimality.Type08S.P2QWP2PF3
public import Minimality.Type08S.P2PF4

@[expose] public section

set_option relaxedAutoImplicit true
set_option relaxedAutoImplicit true

/-!
# P3a instantiation data, N2 `K_c`: extra picture facts (`Y_g > 0`, `Y_d = 0`, `d` not on the line `c b`).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace W5

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
theorem extra_N2 {a a' b b' c c' d : ℝ³} (N : Norm08w a a' b b' c c' d) (hreg : RegN2 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hce : c - a' = κ • e3) (hb2 : ⟪b - a', e2⟫ = 0)
    (hL : 0 < ⟪b - a', e1⟫) (hr : 0 < ⟪c' - a', e2⟫) :
    0 < ⟪b' - a', e2⟫ ∧ ⟪d - a', e2⟫ = 0 ∧
      ⟪b - a', e1⟫ * (⟪d - a', e3⟫ - κ) - ⟪d - a', e1⟫ * (⟪b - a', e3⟫ - κ) ≠ 0 := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts, -⟩ := exists_nf08w N
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
    common08w θ hθ.1 hθ.2.1 hθ.2.2
  have dA : 0 < -1 + θ 5 := by linarith
  have dB : 0 < -1 + θ 0 := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
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
  have hs : 0 < θ 4 + θ 5 - 1 := e3'
  -- Y_g > 0
  have T1 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu ((nfShape08 d E₁ E₂ E₃ θ 1)) 1 2 1 3 (θ 2 * (θ 4 + θ 5 - 1))
    (by simp [ddet, cp08]; try ring) (mul_pos p2 hs)
  simp only [sub_self, inner_zero_left, sub_zero, hb2, zero_mul, mul_zero] at T1
  have hYg : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 1), e2⟫ := pos_of_mul_pos_right (by linarith) hL.le
  -- Y_d = 0
  have hvec : (θ 4 + θ 5 - 1) • (nfShape08 d E₁ E₂ E₃ θ 6 - (nfShape08 d E₁ E₂ E₃ θ 1)) = θ 4 • ((nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1)) + θ 5 • ((nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1)) := by
    simp only [nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    module
  have hc2 : ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1), e2⟫ = 0 := by rw [hce, real_inner_smul_left, real_inner_comm]; rw [hF.n23]; ring
  have hc1 : ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ = 0 := by rw [hce, real_inner_smul_left, real_inner_comm]; rw [hF.n13]; ring
  have hc3 : ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 1), e3⟫ = κ := by rw [hce, real_inner_smul_left, hF.n33]; ring
  have hYd : ⟪d - (nfShape08 d E₁ E₂ E₃ θ 1), e2⟫ = 0 := by
    have := congrArg (fun v => ⟪v, e2⟫) hvec
    simp only [inner_add_left, real_inner_smul_left, hb2, hc2, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hs.ne'
  refine ⟨hYg, hYd, ?_⟩
  -- d not on the line c b
  intro hD0
  have hdet := det3_pts hF ((nfShape08 d E₁ E₂ E₃ θ 1)) ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 4)) (nfShape08 d E₁ E₂ E₃ θ 6) ((nfShape08 d E₁ E₂ E₃ θ 4)) ((nfShape08 d E₁ E₂ E₃ θ 5)) ((nfShape08 d E₁ E₂ E₃ θ 4))
  have hn := det3_nfd d E₁ E₂ E₃ θ 4 2 4 6 4 5
  have hq : ddet (fun k => cp08 θ 2 k - cp08 θ 4 k) (fun k => cp08 θ 6 k - cp08 θ 4 k)
      (fun k => cp08 θ 5 k - cp08 θ 4 k) = - θ 0 := by
    simp [ddet, cp08]; try ring
  rw [hq, hdet] at hn
  have h66 : nfShape08 d E₁ E₂ E₃ θ 6 = d := rfl
  simp only [h66] at hn
  simp only [hb2, hc1, hc2, hc3, hYd, sub_zero, zero_sub, mul_zero, zero_mul, sub_self, add_zero] at hn
  have hz0 : ((⟪(nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1), e3⟫ - κ) *
      ⟪d - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - (nfShape08 d E₁ E₂ E₃ θ 1), e1⟫ *
      (⟪d - (nfShape08 d E₁ E₂ E₃ θ 1), e3⟫ - κ)) = 0 := by linarith
  rw [hz0, zero_mul, zero_add] at hn
  have : det3 E₁ E₂ E₃ * θ 0 = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hE h
  · exact p0.ne' h

end W5
end Type08Sp
end Minimality

