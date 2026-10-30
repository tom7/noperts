module

public import Minimality.Type08S.P2TY1

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X2 / Y2: the cell `(+,−,−)`: rest point `c`, the depth pattern `QTop 6`, and `Rupert` from the frame data.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 3200000 in
theorem cell2_rest {σ t1 ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 : ℝ}
    (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α1) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4)) (hv : σ * v1 < 0)
    (hu : 0 < σ * (ha * t1 - w1)) (hu2 : -(σ * v1) * (1 - γ4) < α4 * (σ * (ha * t1 - w1))) :
    ∀ i : ZMod 6, LT σ t1 1 (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 i)
        (cell2Rim ν v1 ha w1 w3 C0 α1 α4 γ4 β1 β6 (i + 1)) (0, 0, C0) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := c2z6_add_one
  have hr : 0 < -(σ * v1) := by linarith
  have hB : 0 < α4 - α1 * (1 - γ4) := by nlinarith [mul_pos hα4 hβ1]
  have hF : 0 < α4 + γ4 - 1 := by
    rcases le_or_gt γ4 1 with h | h
    · nlinarith
    · linarith
  have k1 := mul_pos hr hha
  have k2 := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α1)
  have k3 := mul_pos (mul_pos hr hha) hα4
  have k4 := mul_pos (mul_pos hr hha) hγ4
  have k5 := mul_pos (mul_pos (mul_pos hr hha) hγ4) (by linarith : (0:ℝ) < α1)
  have k6 := mul_pos (mul_pos hr hha) (by linarith : (0:ℝ) < α1 - 1)
  have k7 := mul_pos (mul_pos (mul_pos hr hha) hγ4) (by linarith : (0:ℝ) < α1 - 1)
  have k8 := mul_pos (mul_pos hr hha) hB
  have k9 := mul_pos (mul_pos hr hha) hF
  have f1 := mul_pos hν hr
  have f8 := mul_pos (mul_pos hβ6 hν) hr
  have f9 := mul_pos (mul_pos hβ6 hν) (by linarith : 0 < α4 * (σ * (ha * t1 - w1)) - -(σ * v1) * (1 - γ4))
  intro i
  rcases c2z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [LT, ori, fo, cell2Rim, s0, s1, s2, s3, s4, s5, c2rim6_0, c2rim6_1, c2rim6_2, c2rim6_3,
      c2rim6_4, c2rim6_5]
     first
     | (left; linarith)
     | (right; refine ⟨by ring, by linarith⟩))

/-! ### The depth pattern -/

theorem lt_ev (zi zj δi δj : ℝ) (h : zi < zj) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), zi + s * δi < zj + s * δj :=
  ev_lt_cont (f := fun s => zi + s * δi) (g := fun s => zj + s * δj) (by fun_prop) (by fun_prop) (by simpa using h)

theorem ne_ev (zi zj δi δj : ℝ) (h : zi ≠ zj ∨ δi ≠ δj) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), zi + s * δi ≠ zj + s * δj := by
  rcases h with h | h
  · rcases lt_or_gt_of_ne h with h | h
    · filter_upwards [lt_ev zi zj δi δj h] with s hs using hs.ne
    · filter_upwards [lt_ev zj zi δj δi h] with s hs using hs.ne'
  · filter_upwards [pair_ev zi zj δi δj h] with s hs using hs.2.2

/-- Exactly one local maximum on the six-cycle `(A, B, W, Aa, R, P)`. -/
theorem qtop6_of {z0 z1 z2 z3 z4 z5 : ℝ} (h1 : z2 < z1) (h2 : z3 < z2 ∨ z3 < z4) (h3 : z4 < z5)
    (h4 : z1 < z0 ∨ z5 < z0) (n1 : z0 ≠ z1) (n2 : z0 ≠ z5) : QTop 6 (c2rim6 z0 z1 z2 z3 z4 z5) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := c2z6_add_one
  obtain ⟨m0, m1, m2, m3, m4, m5⟩ := c2z6_sub_one
  have common : ∀ p : ZMod 6, (p = 0 ∨ p = 1 ∨ p = 5) → ∀ i, i ≠ p → i ≠ 0 → i ≠ 1 → i ≠ 5 →
      c2rim6 z0 z1 z2 z3 z4 z5 i < c2rim6 z0 z1 z2 z3 z4 z5 (i - 1) ∨
      c2rim6 z0 z1 z2 z3 z4 z5 i < c2rim6 z0 z1 z2 z3 z4 z5 (i + 1) := by
    intro p _ i _ i0 i1 i5
    rcases c2z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl i0
    · exact absurd rfl i1
    · left; simp only [m2, c2rim6_1, c2rim6_2]; exact h1
    · simp only [m3, s3, c2rim6_2, c2rim6_3, c2rim6_4]; exact h2
    · right; simp only [s4, c2rim6_4, c2rim6_5]; exact h3
    · exact absurd rfl i5
  by_cases hb : z0 < z1
  · refine ⟨1, fun i hi => ?_⟩
    by_cases i0 : i = 0
    · subst i0; right; simp only [s0, c2rim6_0, c2rim6_1]; exact hb
    by_cases i5 : i = 5
    · subst i5; right; simp only [s5, c2rim6_5, c2rim6_0]
      rcases h4 with h | h
      · exact absurd h (not_lt.2 hb.le)
      · exact h
    exact common 1 (Or.inr (Or.inl rfl)) i hi i0 hi i5
  by_cases hp : z0 < z5
  · refine ⟨5, fun i hi => ?_⟩
    by_cases i0 : i = 0
    · subst i0; left; simp only [m0, c2rim6_0, c2rim6_5]; exact hp
    by_cases i1 : i = 1
    · subst i1; left; simp only [m1, c2rim6_0, c2rim6_1]
      rcases h4 with h | h
      · exact h
      · exact absurd h (not_lt.2 hp.le)
    exact common 5 (Or.inr (Or.inr rfl)) i hi i0 i1 hi
  · have b1 : z1 < z0 := lt_of_le_of_ne (not_lt.1 hb) (Ne.symm n1)
    have b5 : z5 < z0 := lt_of_le_of_ne (not_lt.1 hp) (Ne.symm n2)
    refine ⟨0, fun i hi => ?_⟩
    by_cases i1 : i = 1
    · subst i1; left; simp only [m1, c2rim6_0, c2rim6_1]; exact b1
    by_cases i5 : i = 5
    · subst i5; right; simp only [s5, c2rim6_5, c2rim6_0]; exact b5
    exact common 0 (Or.inl rfl) i hi hi i1 i5

theorem cell2_qtop_ev {A B W Aa R P δA δB δW δAa δR δP : ℝ}
    (h1 : W < B) (h2 : Aa < W ∨ Aa < R) (h3 : R < P) (h4 : B < A ∨ P < A)
    (n1 : A ≠ B ∨ δA ≠ δB) (n2 : A ≠ P ∨ δA ≠ δP) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), QTop 6 (c2rim6 (A + s * δA) (B + s * δB) (W + s * δW) (Aa + s * δAa)
      (R + s * δR) (P + s * δP)) := by
  have e2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), Aa + s * δAa < W + s * δW ∨ Aa + s * δAa < R + s * δR := by
    rcases h2 with h | h
    · filter_upwards [lt_ev _ _ δAa δW h] with s hs using Or.inl hs
    · filter_upwards [lt_ev _ _ δAa δR h] with s hs using Or.inr hs
  have e4 : ∀ᶠ s in 𝓝[>] (0 : ℝ), B + s * δB < A + s * δA ∨ P + s * δP < A + s * δA := by
    rcases h4 with h | h
    · filter_upwards [lt_ev _ _ δB δA h] with s hs using Or.inl hs
    · filter_upwards [lt_ev _ _ δP δA h] with s hs using Or.inr hs
  filter_upwards [lt_ev _ _ δW δB h1, e2, lt_ev _ _ δR δP h3, e4, ne_ev _ _ δA δB n1,
    ne_ev _ _ δA δP n2] with s a1 a2 a3 a4 a5 a6
  exact qtop6_of a1 a2 a3 a4 a5 a6

end Type08Sp
end Minimality
