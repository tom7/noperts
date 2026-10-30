module

public import Minimality.Type08S.P2Defs

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P-F infrastructure (plan2/pkB): frame cross products, determinants of normal-form differences,
sign transfer, and the region parameters `θ 5 > 1` / `θ 5 < 1 < θ 0`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Screen cross product of two vectors seen along `u = κ e3`. -/
theorem cross2_frame (hF : Fr e1 e2 e3) {u : ℝ³} {κ : ℝ} (hu : u = κ • e3) (p q : ℝ³) :
    det3 u p q = κ * (⟪p, e1⟫ * ⟪q, e2⟫ - ⟪p, e2⟫ * ⟪q, e1⟫) := by
  have h := det3_pc hF 0 0 κ ⟪p, e1⟫ ⟪p, e2⟫ ⟪p, e3⟫ ⟪q, e1⟫ ⟪q, e2⟫ ⟪q, e3⟫
  have e0 : u = pc e1 e2 e3 0 0 κ := by rw [hu, pc]; simp
  have ep : p = pc e1 e2 e3 ⟪p, e1⟫ ⟪p, e2⟫ ⟪p, e3⟫ := by rw [pc]; exact hF.expand p
  have eq' : q = pc e1 e2 e3 ⟪q, e1⟫ ⟪q, e2⟫ ⟪q, e3⟫ := by rw [pc]; exact hF.expand q
  have : det3 u p q = det3 (pc e1 e2 e3 0 0 κ) (pc e1 e2 e3 ⟪p, e1⟫ ⟪p, e2⟫ ⟪p, e3⟫)
      (pc e1 e2 e3 ⟪q, e1⟫ ⟪q, e2⟫ ⟪q, e3⟫) := by rw [← e0, ← ep, ← eq']
  rw [this, h]; ring

/-- Coordinates of a vector in a frame (difference form). -/
theorem frame_diff (E₁ E₂ E₃ o : ℝ³) (P Q : Fin 3 → ℝ) :
    (o + P 0 • E₁ + P 1 • E₂ + P 2 • E₃) - (o + Q 0 • E₁ + Q 1 • E₂ + Q 2 • E₃) =
      (P 0 - Q 0) • E₁ + (P 1 - Q 1) • E₂ + (P 2 - Q 2) • E₃ := by
  simp only [sub_smul]; abel

/-- 3x3 determinant of coordinate vectors. -/
def ddet (x y z : Fin 3 → ℝ) : ℝ :=
  (x 1 * y 2 - x 2 * y 1) * z 0 + (x 2 * y 0 - x 0 * y 2) * z 1 + (x 0 * y 1 - x 1 * y 0) * z 2

/-- `det3` of three frame-point differences. -/
theorem det3_nfd (o E₁ E₂ E₃ : ℝ³) (θ : Fin 6 → ℝ) (i1 j1 i2 j2 i3 j3 : Fin 7) :
    det3 (nfShape08 o E₁ E₂ E₃ θ j1 - nfShape08 o E₁ E₂ E₃ θ i1)
      (nfShape08 o E₁ E₂ E₃ θ j2 - nfShape08 o E₁ E₂ E₃ θ i2)
      (nfShape08 o E₁ E₂ E₃ θ j3 - nfShape08 o E₁ E₂ E₃ θ i3) =
    det3 E₁ E₂ E₃ * ddet (fun k => cp08 θ j1 k - cp08 θ i1 k) (fun k => cp08 θ j2 k - cp08 θ i2 k)
      (fun k => cp08 θ j3 k - cp08 θ i3 k) := by
  simp only [nf08_coord, frame_diff, det3_expand, ddet, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

theorem kD_pos {κ D P L Y : ℝ} (hk : κ ≠ 0) (h : κ * (L * Y) = D * P) (hL : 0 < L) (hY : 0 < Y)
    (hP : 0 < P) : 0 < κ * D := by
  have h1 : 0 < (κ * D) * P := by
    have : (κ * D) * P = κ * (κ * (L * Y)) := by rw [h]; ring
    rw [this]
    have : κ * (κ * (L * Y)) = κ ^ 2 * (L * Y) := by ring
    rw [this]; exact mul_pos (by positivity) (mul_pos hL hY)
  exact (pos_of_mul_pos_left h1 hP.le)

/-- Sign transfer: `κ T = D Q`, `κ D > 0`, `Q > 0` give `T > 0`. -/
theorem sign_transfer {κ D T Q : ℝ} (hk : κ ≠ 0) (hD : 0 < κ * D) (h : κ * T = D * Q)
    (hQ : 0 < Q) : 0 < T := by
  have h1 : 0 < κ ^ 2 * T := by
    have : κ ^ 2 * T = (κ * D) * Q := by rw [sq, mul_assoc, h]; ring
    rw [this]; exact mul_pos hD hQ
  exact (pos_of_mul_pos_right h1 (by positivity))

theorem sign_transfer_neg {κ D T Q : ℝ} (hk : κ ≠ 0) (hD : 0 < κ * D) (h : κ * T = D * Q)
    (hQ : Q < 0) : T < 0 := by
  have := sign_transfer (T := -T) (Q := -Q) hk hD (by linarith) (by linarith)
  linarith

/-- The region parameters: N2 has `γ₆ > 1`. -/
theorem theta_N2 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) (h : RegN2 N.F) : 1 < θ 5 := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hg := region_gamma6 N hE hθ hpts
  have hfc : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have h' : N.F.abc'.f a' < N.F.abc'.f c := h
  rw [hg] at h'; nlinarith

theorem theta_T4 {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) {o E₁ E₂ E₃ : ℝ³}
    {θ : Fin 6 → ℝ} (hE : det3 E₁ E₂ E₃ ≠ 0) (hθ : ∀ k, 0 < ineq08 θ k)
    (hpts : pts08 a a' b b' c c' d = nfShape08 o E₁ E₂ E₃ θ) (h : RegT4 N.F) :
    θ 5 < 1 ∧ 1 < θ 0 := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hg := region_gamma6 N hE hθ hpts
  have ha := region_alpha1 N hE hθ hpts
  have hfc : N.F.abc'.f c < 0 := N.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hfa : N.F.a'bc.f a < 0 :=
    N.F.a'bc.neg a (by simp) (by ne_tac) (by ne_tac) (by ne_tac)
  obtain ⟨h1, h2⟩ := h
  constructor
  · have h' : N.F.abc'.f c < N.F.abc'.f a' := h1
    rw [hg] at h'; nlinarith
  · have h' : N.F.a'bc.f c' < N.F.a'bc.f a := h2
    rw [ha] at h'; nlinarith

end Type08Sp
end Minimality
