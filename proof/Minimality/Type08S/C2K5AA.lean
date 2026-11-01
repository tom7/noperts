module

public import Minimality.Type08S.C2K5LP
public import Minimality.Type08S.P2QParEnd

@[expose] public section


/-!
# K5a / A: P0 for `ParEndK2` (K5-0), Par5 branch empty, CEf5 equations in W0 coordinates
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem p0_ext {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) {u v : ℝ³} (h1 : ⟪u, e1⟫ = ⟪v, e1⟫)
    (h2 : ⟪u, e2⟫ = ⟪v, e2⟫) (h3 : ⟪u, e3⟫ = ⟪v, e3⟫) : u = v := by
  rw [hF.expand u, hF.expand v, h1, h2, h3]

/-- an `e2`-orthogonal frame fact: if `e2 ⟂ p, q, r` with `det3 p q r ≠ 0` then false. -/
theorem p0_e2_not_perp {e2 p q r : ℝ³} (h22 : ⟪e2, e2⟫ = 1) (hdet : det3 p q r ≠ 0)
    (hp : ⟪p, e2⟫ = 0) (hq : ⟪q, e2⟫ = 0) (hr : ⟪r, e2⟫ = 0) : False := by
  have h := congrArg (fun v => ⟪v, e2⟫) (cramer p q r e2)
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hp, hq, hr] at h
  rw [real_inner_comm, h22] at h
  apply hdet; simpa using h

/-- Frame data of `ParEndK2` in `W0` coordinates (shared hypotheses). -/
theorem p0_k2_basic {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) {b b' c c' d a : ℝ³} {κ α1 α4 β1 γ4 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (hα1 : 0 < α1) (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0)
    (hYY : ⟪b' - b, e2⟫ = ⟪c - b, e2⟫) :
    ⟪b - d, e2⟫ = 0 ∧ ⟪a - d, e2⟫ = 0 ∧ γ4 = 1 := by
  have hq : b - d = -(κ • e3) := by rw [← hxe]; abel
  have hqe : ⟪b - d, e2⟫ = 0 := by
    rw [hq, inner_neg_left, inner_smul_left, real_inner_comm, hF.n23]; simp
  have hc'b : c' - b = α1 • (a - d) + (β1 - 1) • (b - d) := by rw [hc']; module
  have hpe : ⟪a - d, e2⟫ = 0 := by
    rw [hc'b] at hf2
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hqe] at hf2
    rcases mul_eq_zero.mp (by linarith : α1 * ⟪a - d, e2⟫ = 0) with h | h
    · exact absurd h hα1.ne'
    · exact h
  refine ⟨hqe, hpe, ?_⟩
  have hbc : b' - b - (c - b) = α4 • (a - d) + (γ4 - 1) • (c - d) := by rw [hb']; module
  have h0 : ⟪b' - b - (c - b), e2⟫ = 0 := by rw [inner_sub_left, hYY]; ring
  rw [hbc] at h0
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, hpe] at h0
  have hre : ⟪c - d, e2⟫ ≠ 0 := fun hr =>
    p0_e2_not_perp hF.n22 hdet hpe hqe hr
  have : (γ4 - 1) * ⟪c - d, e2⟫ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hre

/-- The `Par5` branch of `ParEndK2` is empty (frame form). -/
theorem p0_k2_par5_empty {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) {b b' c c' d a : ℝ³}
    {κ α1 α4 β1 γ4 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (hα4 : 0 < α4) (hβ1 : 0 < β1)
    (hxe : d - b = κ • e3) (hf2 : ⟪c' - b, e2⟫ = 0) (hL : 0 < ⟪c' - b, e1⟫)
    (hYY : ⟪b' - b, e2⟫ = ⟪c - b, e2⟫)
    (hcoll : Coll5 ⟪c' - b, e1⟫ κ ⟪c' - b, e3⟫ ⟪b' - b, e1⟫ ⟪b' - b, e3⟫ ⟪c - b, e1⟫
      ⟪c - b, e3⟫) : False := by
  have hq : b - d = -(κ • e3) := by rw [← hxe]; abel
  have hqe1 : ⟪b - d, e1⟫ = 0 := by
    rw [hq, inner_neg_left, inner_smul_left, real_inner_comm, hF.n13]; simp
  have hqe2 : ⟪b - d, e2⟫ = 0 := by
    rw [hq, inner_neg_left, inner_smul_left, real_inner_comm, hF.n23]; simp
  have hqe3 : ⟪b - d, e3⟫ = -κ := by
    rw [hq, inner_neg_left, inner_smul_left, real_inner_comm, hF.n33]; simp
  obtain ⟨hc1, hc2⟩ := hcoll
  set L := ⟪c' - b, e1⟫ with hLdef
  set Xr := ⟪b' - b, e1⟫
  set Xg := ⟪c - b, e1⟫
  have hid : L • (b' - c) = (Xr - Xg) • (c' - d) := by
    apply p0_ext hF
    · have : ⟪c' - d, e1⟫ = L + ⟪b - d, e1⟫ := by
        rw [hLdef, ← inner_add_left]; congr 1; abel
      have h2 : ⟪b' - c, e1⟫ = Xr - Xg := by
        simp only [Xr, Xg, ← inner_sub_left]; congr 1; abel
      simp only [inner_smul_left, RCLike.conj_to_real, this, h2, hqe1]; ring
    · have : ⟪c' - d, e2⟫ = ⟪c' - b, e2⟫ + ⟪b - d, e2⟫ := by
        rw [← inner_add_left]; congr 1; abel
      have h2 : ⟪b' - c, e2⟫ = 0 := by
        have : ⟪b' - c, e2⟫ = ⟪b' - b, e2⟫ - ⟪c - b, e2⟫ := by
          rw [← inner_sub_left]; congr 1; abel
        rw [this, hYY]; ring
      simp only [inner_smul_left, RCLike.conj_to_real, this, h2, hf2, hqe2]; ring
    · have : ⟪c' - d, e3⟫ = ⟪c' - b, e3⟫ + ⟪b - d, e3⟫ := by
        rw [← inner_add_left]; congr 1; abel
      have h2 : ⟪b' - c, e3⟫ = ⟪b' - b, e3⟫ - ⟪c - b, e3⟫ := by
        rw [← inner_sub_left]; congr 1; abel
      simp only [inner_smul_left, RCLike.conj_to_real, this, h2, hqe3]
      linear_combination hc1 - hc2
  have hlin : (L * α4 - (Xr - Xg) * α1) • (a - d) + (-((Xr - Xg) * β1)) • (b - d)
      + (L * (γ4 - 1)) • (c - d) = 0 := by
    have h := hid
    rw [hb', hc'] at h
    have h' : L • (d + α4 • (a - d) + γ4 • (c - d) - c) -
        (Xr - Xg) • (d + α1 • (a - d) + β1 • (b - d) - d) = 0 := by rw [h]; simp
    rw [← h']; module
  obtain ⟨-, ht, -⟩ := det3_indep hdet hlin
  have hXX : Xr - Xg = 0 := by
    rcases mul_eq_zero.mp (by linarith : (Xr - Xg) * β1 = 0) with h | h
    · exact h
    · exact absurd h hβ1.ne'
  obtain ⟨hs, -, -⟩ := det3_indep hdet hlin
  rw [hXX] at hs
  have : L * α4 = 0 := by linarith
  exact (mul_pos hL hα4).ne' this

end C2
end Type08Sp
end Minimality
