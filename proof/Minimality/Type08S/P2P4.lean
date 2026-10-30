module

public import Minimality.Type08S.P2Defs

@[expose] public section

set_option relaxedAutoImplicit true

/-! # P4: `hq2_of_regN2` (proved).  Statement identical to `P2Pkg.hq2_of_regN2`. -/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 4000000 in
/-- culJ: `hq₂ ⟺ γ4β6(α1−1) + β1(α4−1)(γ6−1) > 0`, from the region inequalities and `γ6 > 1`. -/
theorem q2poly (θ : Fin 6 → ℝ) (hθ : ∀ k, 0 < ineq08 θ k) (h6 : 1 < θ 5) :
    0 < θ 3 * θ 4 * (θ 0 - 1) + θ 1 * (θ 2 - 1) * (θ 5 - 1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
  have dA : 0 < -1 + θ 5 := by linarith
  have dB : 0 < -1 + θ 0 := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
  nlinarith [mul_pos p3 p4, mul_pos (mul_pos p3 p4) dB, mul_pos p1 dA, mul_pos p2 p1,
    mul_pos (mul_pos p1 p2) dA, mul_pos p1 dA, mul_pos p0 dA, mul_pos p3 dA, mul_pos p4 dA]

theorem fc_q2 (θ : Fin 6 → ℝ) :
    fc08 θ 0 3 5 1 - fc08 θ 0 3 5 4 =
      θ 3 * θ 4 * (θ 0 - 1) + θ 1 * (θ 2 - 1) * (θ 5 - 1) := by
  simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem hq2_of_regN2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (h : RegN2 N.F) :
    N.F.ab'c'.f a' < N.F.ab'c'.f c := by
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
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
  have hpoly := q2poly θ hθ h6
  have hneg : N.F.ab'c'.f c < 0 := N.F.ab'c'.neg c (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08 θ hθ
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
    have := (facts08 θ hθ).2.2.2.2.2.2.2.2.2.2.2.1
    exact this
  have key : (N.F.ab'c'.f a' - N.F.ab'c'.f c) * fc08 θ 0 3 5 4 < 0 := by
    have : (N.F.ab'c'.f a' - N.F.ab'c'.f c) * fc08 θ 0 3 5 4 =
        N.F.ab'c'.f c * (fc08 θ 0 3 5 1 - fc08 θ 0 3 5 4) := by linear_combination hfac'
    rw [this]; exact mul_neg_of_neg_of_pos hneg (by linarith)
  by_contra hcon
  push_neg at hcon
  nlinarith

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.hq2_of_regN2
