module

public import Minimality.Type08S.P2NP1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a instantiation data, T4 `K_b` and `K_2`: extra picture facts
(`Y_g > 0`, `Y_p = 0`, `p` not on the line `x f`, `q` on the chord `x g` strictly between, chord sign).
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Algebra of the chord row: `Yg * Det = R3 * (Yg Xr - Xg Yr)` when `q` is on the screen line `0 g`. -/
theorem chord_alg {κ Xg Yg zg Xq Yq zq Xr Yr zr : ℝ} (hcop : Xq * Yg - Yq * Xg = 0) :
    Yg * ((((0 - Yg) * (zq - zg) - (κ - zg) * (Yq - Yg)) * Xr +
      ((κ - zg) * (Xq - Xg) - (0 - Xg) * (zq - zg)) * Yr +
      ((0 - Xg) * (Yq - Yg) - (0 - Yg) * (Xq - Xg)) * zr)) =
    ((0 - Yg) * (zq - zg) - (κ - zg) * (Yq - Yg)) * (Yg * Xr - Xg * Yr) := by
  linear_combination (Yr * (κ - zg) + Yg * zr) * hcop

set_option maxHeartbeats 4000000 in
theorem extra_Kb {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hreg : RegT4 N.F)
    (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0) (hxe : b - d = κ • e3) (hf2 : ⟪c - d, e2⟫ = 0)
    (hL : 0 < ⟪c - d, e1⟫) (hr : 0 < ⟪b' - d, e2⟫)
    (hcg : 0 < ⟪c' - d, e2⟫ * ⟪b' - d, e1⟫ - ⟪c' - d, e1⟫ * ⟪b' - d, e2⟫)
    (hlam : ⟪a - d, e2⟫ / ⟪c' - d, e2⟫ < 1) :
    0 < ⟪c' - d, e2⟫ ∧ ⟪a' - d, e2⟫ = 0 ∧
      ⟪c - d, e1⟫ * (⟪a' - d, e3⟫ - κ) - ⟪a' - d, e1⟫ * (⟪c - d, e3⟫ - κ) ≠ 0 ∧
      0 < ⟪a - d, e2⟫ ∧ ⟪a - d, e2⟫ < ⟪c' - d, e2⟫ ∧
      ⟪a - d, e1⟫ * ⟪c' - d, e2⟫ = ⟪a - d, e2⟫ * ⟪c' - d, e1⟫ ∧
      0 < κ * ((0 - ⟪c' - d, e2⟫) * (⟪a - d, e3⟫ - ⟪c' - d, e3⟫) -
        (κ - ⟪c' - d, e3⟫) * (⟪a - d, e2⟫ - ⟪c' - d, e2⟫)) := by
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
  have hu : nfShape08 d E₁ E₂ E₃ θ 2 - nfShape08 d E₁ E₂ E₃ θ 6 = κ • e3 := hxe
  have hkD : 0 < κ * det3 E₁ E₂ E₃ := by
    have h1 := cross_pts hF hxe d ((nfShape08 d E₁ E₂ E₃ θ 4)) d ((nfShape08 d E₁ E₂ E₃ θ 3)) d
    have h2 := det3_nfd d E₁ E₂ E₃ θ 6 2 6 4 6 3
    have hq : ddet (fun k => cp08 θ 2 k - cp08 θ 6 k) (fun k => cp08 θ 4 k - cp08 θ 6 k)
        (fun k => cp08 θ 3 k - cp08 θ 6 k) = θ 2 := by
      simp [ddet, cp08]; try ring
    rw [hq, h66] at h2
    simp only [sub_self, inner_zero_left, sub_zero, hf2, zero_mul] at h1
    refine kD_pos hκ (L := ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - d, e1⟫) (Y := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - d, e2⟫) (P := θ 2) ?_ hL hr p2
    linear_combination h2 - h1
  -- Y_g > 0
  have T1 := tgt_nf d E₁ E₂ E₃ θ hF hκ hkD hu d 6 4 6 5 (θ 0) (by simp [ddet, cp08]; try ring) p0
  simp only [h66, sub_self, inner_zero_left, sub_zero, hf2, zero_mul, mul_zero] at T1
  have hYg : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫ := pos_of_mul_pos_right (by linarith) hL.le
  -- Y_p = 0
  have hvec : nfShape08 d E₁ E₂ E₃ θ 1 - d = θ 4 • ((nfShape08 d E₁ E₂ E₃ θ 2) - d) + θ 5 • ((nfShape08 d E₁ E₂ E₃ θ 4) - d) := by
    simp only [nfShape08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    module
  have hb2 : ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - d, e2⟫ = 0 := by rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n23]; ring
  have hb1 : ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - d, e1⟫ = 0 := by rw [hxe, real_inner_smul_left, real_inner_comm]; rw [hF.n13]; ring
  have hb3 : ⟪(nfShape08 d E₁ E₂ E₃ θ 2) - d, e3⟫ = κ := by rw [hxe, real_inner_smul_left, hF.n33]; ring
  have hYp : ⟪nfShape08 d E₁ E₂ E₃ θ 1 - d, e2⟫ = 0 := by
    have := congrArg (fun v => ⟪v, e2⟫) hvec
    simp only [inner_add_left, real_inner_smul_left, hb2, hf2, mul_zero, add_zero] at this
    exact this
  -- the G-middle
  have T3 := tgt_eq d E₁ E₂ E₃ θ hF hu d 6 4 6 0 1 (by simp [ddet, cp08]; try ring)
  simp only [h66, sub_self, inner_zero_left, sub_zero, hf2, zero_mul, mul_zero] at T3
  have hLa : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - d, e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫ := by
    refine sign_transfer hκ hkD (T := ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - d, e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫) (Q := 1) ?_ one_pos
    linear_combination T3
  have hYq : 0 < ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫ := pos_of_mul_pos_right hLa hL.le
  have hYlt : ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫ < ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫ := by
    have := (div_lt_one hYg).mp hlam
    exact this
  -- coplanarity of a, c', b, d
  have hcop3 := det3_pts hF d ((nfShape08 d E₁ E₂ E₃ θ 0)) d ((nfShape08 d E₁ E₂ E₃ θ 5)) d ((nfShape08 d E₁ E₂ E₃ θ 2)) d
  have hcn := det3_nfd d E₁ E₂ E₃ θ 6 0 6 5 6 2
  have hq0 : ddet (fun k => cp08 θ 0 k - cp08 θ 6 k) (fun k => cp08 θ 5 k - cp08 θ 6 k)
      (fun k => cp08 θ 2 k - cp08 θ 6 k) = 0 := by
    simp [ddet, cp08]; try ring
  rw [hq0, h66] at hcn
  rw [hcop3] at hcn
  simp only [h66, sub_self, inner_zero_left, sub_zero, hb1, hb2, hb3, zero_mul, mul_zero, add_zero,
    zero_add, mul_zero] at hcn
  have hcopQ : ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e1⟫ = 0 := by
    have : κ * (⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e1⟫) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hκ
  refine ⟨hYg, hYp, ?_, hYq, hYlt, ?_, ?_⟩
  · -- p = a' not on the line x f
    intro hD0
    have hdet := det3_pts hF d (nfShape08 d E₁ E₂ E₃ θ 4) (nfShape08 d E₁ E₂ E₃ θ 2) (nfShape08 d E₁ E₂ E₃ θ 1) (nfShape08 d E₁ E₂ E₃ θ 2) (nfShape08 d E₁ E₂ E₃ θ 3) (nfShape08 d E₁ E₂ E₃ θ 2)
    have hn := det3_nfd d E₁ E₂ E₃ θ 2 4 2 1 2 3
    have hq : ddet (fun k => cp08 θ 4 k - cp08 θ 2 k) (fun k => cp08 θ 1 k - cp08 θ 2 k)
        (fun k => cp08 θ 3 k - cp08 θ 2 k) = - (θ 2 * (θ 4 + θ 5 - 1)) := by
      simp [ddet, cp08]; try ring
    rw [hq, hdet] at hn
    simp only [hb1, hb2, hb3, hf2, hYp, sub_zero, zero_sub, mul_zero, zero_mul, sub_self, add_zero] at hn
    have hz0 : ((⟪(nfShape08 d E₁ E₂ E₃ θ 4) - d, e3⟫ - κ) * ⟪nfShape08 d E₁ E₂ E₃ θ 1 - d, e1⟫ -
        ⟪(nfShape08 d E₁ E₂ E₃ θ 4) - d, e1⟫ * (⟪nfShape08 d E₁ E₂ E₃ θ 1 - d, e3⟫ - κ)) = 0 := by linarith
    rw [hz0, zero_mul, zero_add] at hn
    have : det3 E₁ E₂ E₃ * (θ 2 * (θ 4 + θ 5 - 1)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hE h
    · exact (mul_pos p2 e3').ne' h
  · linarith [hcopQ]
  · -- the chord sign
    have hdet := det3_pts hF d ((nfShape08 d E₁ E₂ E₃ θ 2)) ((nfShape08 d E₁ E₂ E₃ θ 5)) ((nfShape08 d E₁ E₂ E₃ θ 0)) ((nfShape08 d E₁ E₂ E₃ θ 5)) ((nfShape08 d E₁ E₂ E₃ θ 3)) d
    have hn := det3_nfd d E₁ E₂ E₃ θ 5 2 5 0 6 3
    have hq : ddet (fun k => cp08 θ 2 k - cp08 θ 5 k) (fun k => cp08 θ 0 k - cp08 θ 5 k)
        (fun k => cp08 θ 3 k - cp08 θ 6 k) = θ 3 * (θ 0 + θ 1 - 1) := by
      simp [ddet, cp08]; try ring
    rw [hq] at hn
    simp only [h66] at hn
    rw [hdet] at hn
    simp only [hb1, hb2, hb3, sub_self, inner_zero_left, sub_zero] at hn
    have hpos : 0 < κ * (det3 E₁ E₂ E₃ * (θ 3 * (θ 0 + θ 1 - 1))) := by
      rw [← mul_assoc]; exact mul_pos hkD (mul_pos p3 e1')
    rw [← hn] at hpos
    have hca := chord_alg (κ := κ) (Xg := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e1⟫) (Yg := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫) (zg := ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e3⟫)
      (Xq := ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e1⟫) (Yq := ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫) (zq := ⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e3⟫)
      (Xr := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - d, e1⟫) (Yr := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - d, e2⟫) (zr := ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - d, e3⟫) hcopQ
    have h3 : 0 < (κ * (((0 - ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫) * (⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e3⟫ -
          ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e3⟫) - (κ - ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e3⟫) *
          (⟪(nfShape08 d E₁ E₂ E₃ θ 0) - d, e2⟫ - ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫)))) *
        (⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e2⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - d, e1⟫ -
          ⟪(nfShape08 d E₁ E₂ E₃ θ 5) - d, e1⟫ * ⟪(nfShape08 d E₁ E₂ E₃ θ 3) - d, e2⟫) := by
      have := mul_pos hYg hpos
      have hk := congrArg (fun x => κ * x) hca
      linarith [hk, this]
    exact (pos_iff_pos_of_mul_pos h3).mpr hcg

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.extra_Kb
