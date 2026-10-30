module

public import Minimality.Type08S.P2NP2

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a instantiation data, T4 `K_2`: extra picture facts.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 4000000 in
theorem extra_K2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hL : 0 < ⟪c' - b, e1⟫) (hr : 0 < ⟪b' - b, e2⟫)
    (hcg : 0 < ⟪c - b, e2⟫ * ⟪b' - b, e1⟫ - ⟪c - b, e1⟫ * ⟪b' - b, e2⟫)
    (hlam : ⟪a' - b, e2⟫ / ⟪c - b, e2⟫ < 1) :
    0 < ⟪c - b, e2⟫ ∧ ⟪a - b, e2⟫ = 0 ∧
      ⟪c' - b, e1⟫ * (⟪a - b, e3⟫ - κ) - ⟪a - b, e1⟫ * (⟪c' - b, e3⟫ - κ) ≠ 0 ∧
      0 < ⟪a' - b, e2⟫ ∧ ⟪a' - b, e2⟫ < ⟪c - b, e2⟫ ∧
      ⟪a' - b, e1⟫ * ⟪c - b, e2⟫ = ⟪a' - b, e2⟫ * ⟪c - b, e1⟫ ∧
      0 < κ * ((0 - ⟪c - b, e2⟫) * (⟪a' - b, e3⟫ - ⟪c - b, e3⟫) -
        (κ - ⟪c - b, e3⟫) * (⟪a' - b, e2⟫ - ⟪c - b, e2⟫)) := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
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
    common08 θ hθ
  have dA : 0 < 1 - θ 5 := by linarith
  have dB : 0 < -1 + θ 0 := by linarith
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
  -- Y_g > 0
  have T1 := tgt_eq (e1 := e1) (e2 := e2) (e3 := e3) d E₁ E₂ E₃ θ hF hu ((nfShape08 d E₁ E₂ E₃ θ 2)) 2 5 2 4 (θ 0)
    (by simp [ddet, cp08]; try ring)
  simp only [h66, sub_self, inner_zero_left, sub_zero, hf2, zero_mul, mul_zero] at T1
  have hLg : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := by
    refine sign_transfer hκ hkD (T := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (Q := θ 0) ?_ p0
    linear_combination T1
  have hYg : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := pos_of_mul_pos_right hLg hL.le
  -- Y_p = 0
  have hvec : θ 0 • ((nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2)) = ((nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2)) + (θ 0 + θ 1 - 1) • (d - (nfShape08 d E₁ E₂ E₃ θ 2)) := by
    simp only [nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    module
  have hd2 : ⟪d - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ = 0 := by rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n23]; ring
  have hd1 : ⟪d - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ = 0 := by rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n13]; ring
  have hd3 : ⟪d - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫ = κ := by rw [hxe, real_inner_smul_left, hF.n33]; ring
  have hYp : ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ = 0 := by
    have := congrArg (fun v => ⟪v, e2⟫) hvec
    simp only [inner_add_left, real_inner_smul_left, hd2, hf2, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left p0.ne'
  -- the G-middle
  have T3 := tgt_eq (e1 := e1) (e2 := e2) (e3 := e3) d E₁ E₂ E₃ θ hF hu ((nfShape08 d E₁ E₂ E₃ θ 2)) 2 5 2 1 (θ 0 * θ 5)
    (by simp [ddet, cp08]; try ring)
  simp only [h66, sub_self, inner_zero_left, sub_zero, hf2, zero_mul, mul_zero] at T3
  have hLq : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := by
    refine sign_transfer hκ hkD (T := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (Q := θ 0 * θ 5) ?_ (mul_pos p0 p5)
    linear_combination T3
  have hYq : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := pos_of_mul_pos_right hLq hL.le
  have hYlt : ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ < ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ := (div_lt_one hYg).mp hlam
  -- coplanarity of a', c, d, b
  have hcop3 := det3_pts hF ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 1)) ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 4)) ((nfShape08 d E₁ E₂ E₃ θ 2)) d ((nfShape08 d E₁ E₂ E₃ θ 2))
  have hcn := det3_nfd d E₁ E₂ E₃ θ 2 1 2 4 2 6
  have hq0 : ddet (fun k => cp08 θ 1 k - cp08 θ 2 k) (fun k => cp08 θ 4 k - cp08 θ 2 k)
      (fun k => cp08 θ 6 k - cp08 θ 2 k) = 0 := by
    simp [ddet, cp08]; try ring
  rw [hq0, h66] at hcn
  rw [hcop3] at hcn
  simp only [hd1, hd2, hd3, sub_self, inner_zero_left, sub_zero, zero_mul, mul_zero, add_zero,
    zero_add] at hcn
  have hcopQ : ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ = 0 := by
    have : κ * (⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hκ
  refine ⟨hYg, hYp, ?_, hYq, hYlt, ?_, ?_⟩
  · -- p = a not on the line x f
    intro hD0
    have hdet := det3_pts hF ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 5)) d ((nfShape08 d E₁ E₂ E₃ θ 0)) d ((nfShape08 d E₁ E₂ E₃ θ 3)) d
    have hn := det3_nfd d E₁ E₂ E₃ θ 6 5 6 0 6 3
    have hq : ddet (fun k => cp08 θ 5 k - cp08 θ 6 k) (fun k => cp08 θ 0 k - cp08 θ 6 k)
        (fun k => cp08 θ 3 k - cp08 θ 6 k) = - (θ 1 * θ 3) := by
      simp [ddet, cp08]; try ring
    rw [hq] at hn
    simp only [h66] at hn
    rw [hdet] at hn
    simp only [hd1, hd2, hd3, hf2, hYp, sub_zero, zero_sub, mul_zero, zero_mul, sub_self, add_zero] at hn
    have hz0 : ((⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫ - κ) * ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * (⟪(nfShape08 d E₁ E₂ E₃ θ 0) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫ - κ)) = 0 := by
      linarith
    rw [hz0, zero_mul, zero_add] at hn
    have : det3 E₁ E₂ E₃ * (θ 1 * θ 3) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hE h
    · exact (mul_pos p1 p3).ne' h
  · linarith [hcopQ]
  · -- the chord sign
    have hdet := det3_pts hF ((nfShape08 d E₁ E₂ E₃ θ 2)) d ((nfShape08 d E₁ E₂ E₃ θ 4)) ((nfShape08 d E₁ E₂ E₃ θ 1)) ((nfShape08 d E₁ E₂ E₃ θ 4)) ((nfShape08 d E₁ E₂ E₃ θ 3)) ((nfShape08 d E₁ E₂ E₃ θ 2))
    have hn := det3_nfd d E₁ E₂ E₃ θ 4 6 4 1 2 3
    have hq : ddet (fun k => cp08 θ 6 k - cp08 θ 4 k) (fun k => cp08 θ 1 k - cp08 θ 4 k)
        (fun k => cp08 θ 3 k - cp08 θ 2 k) = θ 2 * θ 4 := by
      simp [ddet, cp08]; try ring
    rw [hq] at hn
    simp only [h66] at hn
    rw [hdet] at hn
    simp only [hd1, hd2, hd3, sub_self, inner_zero_left, sub_zero] at hn
    have hpos : 0 < κ * (det3 E₁ E₂ E₃ * (θ 2 * θ 4)) := by
      rw [← mul_assoc]; exact mul_pos hkD (mul_pos p2 p4)
    rw [← hn] at hpos
    have hca := chord_alg (κ := κ) (Xg := ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫) (Yg := ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (zg := ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫)
      (Xq := ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫) (Yq := ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (zq := ⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫)
      (Xr := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫) (Yr := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) (zr := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫) hcopQ
    have h3 : 0 < (κ * (((0 - ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) * (⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫) -
        (κ - ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e3⟫) * (⟪(nfShape08 d E₁ E₂ E₃ θ 1) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫)))) *
        (⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - (nfShape08 d E₁ E₂ E₃ θ 2), e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - (nfShape08 d E₁ E₂ E₃ θ 2), e2⟫) := by
      have := mul_pos hYg hpos
      have hk := congrArg (fun x => κ * x) hca
      linarith [hk, this]
    exact (pos_iff_pos_of_mul_pos h3).mpr hcg

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.extra_K2
