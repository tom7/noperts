module

public import Minimality.SilS0XC
public import Minimality.RimFromSigns
public import Minimality.Type24SAT.Facets24
public import Minimality.Type24
public import Minimality.TheoremP24
public import Minimality.DiagCross
public import Minimality.Q45Signs

@[expose] public section

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.TheoremP Minimality.RimFromSigns Minimality.T24.Q45

namespace Minimality.T24.Q45

/-!
# Q45 Rim Orientation, Kappa Signs, and Corner Middles (Task AC)

This module formalizes:
1. **AC1 (`rimOrient`)**: Frame-free rim orientation (Lemma S0).
   If vertex 1 is strictly inside the rim edge `x 2 -> x 6` with orientation `ρ`,
   then `ρ * Ω * ⟪F.N 5, u⟫ < 0`, where `Ω = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)`.
2. **AC2**: Plane-side determinant facts with `Ω`, rim `κ` rewrite lemmas,
   and signed relations `Ω * κ` for all six rims of section 2.3.
3. **AC3**: Corner middle decompositions and eventual filter bounds in `𝓝[>] 0`
   for B1, Bs1, B2 and their mirrors C1, Ct1, C2.
-/

-- =========================================================================
-- AC1: rimOrient (Lemma S0)
-- =========================================================================

/-- Non-degeneracy of the corner frame at vertex 1: `Ω ≠ 0` holds for every
Type 24 facet structure by Cauchy–Binet on the three cap faces `126, 016, 012`. -/
theorem omega_ne_zero {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) ≠ 0 := by
  have e := vol3_mul_inner (F.N 5) (F.N 1) (F.N 0) (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have z := fun (t : Fin 9) (i : Fin 7) (h : i ∈ s0x_S24 t) => F.zero t i h
  have s := fun (t : Fin 9) (a b : Fin 7) => F.inner_sub t a b
  rw [s 5 0 1, s 5 2 1, s 5 6 1, s 1 0 1, s 1 2 1, s 1 6 1, s 0 0 1, s 0 2 1, s 0 6 1] at e
  rw [z 5 1 (by decide), z 5 2 (by decide), z 5 6 (by decide),
      z 1 0 (by decide), z 1 1 (by decide), z 1 6 (by decide),
      z 0 0 (by decide), z 0 1 (by decide), z 0 2 (by decide)] at e
  have h1 := F.neg 5 0 (by decide)
  have h2 := F.neg 1 2 (by decide)
  have h3 := F.neg 0 6 (by decide)
  have h_vol : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [h_vol] at e
  intro h0
  rw [h0, mul_zero] at e
  have : (F.f 5 (x 0) - 0) * ((F.f 1 (x 2) - 0) * (F.f 0 (x 6) - 0)) = 0 := by linear_combination -e
  simp only [sub_zero] at this
  rcases mul_eq_zero.mp this with h | h
  · linarith
  rcases mul_eq_zero.mp h with h | h <;> linarith

/-- **AC1: Lemma S0 (rimOrient, frame-free)**.
If vertex 1 is strictly inside the rim edge `x 2 -> x 6` with orientation `ρ`,
then `ρ * Ω * ⟪F.N 5, u⟫ < 0`, where `Ω = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)`.
Proof: Cramer vector expansion of `u` in `(x 0 - x 1, x 2 - x 1, x 6 - x 1)`.
Because facet 5 (`126`) contains vertices 1, 2, 6, the inner products with `x 2 - x 1`
and `x 6 - x 1` vanish, leaving only `⟪F.N 5, x 0 - x 1⟫ = F.f 5 (x 0) < 0`. -/
theorem rimOrient {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (ρ : ℝ)
    (hin : 0 < ρ * det3 (x 6 - x 2) (x 1 - x 2) u) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * ⟪F.N 5, u⟫ < 0 := by
  have h2 : ⟪F.N 5, x 2 - x 1⟫ = 0 := by
    rw [F.inner_sub 5 2 1]
    have h1 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
    have h2 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
    rw [h1, h2, sub_self]
  have h6 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by
    rw [F.inner_sub 5 6 1]
    have h1 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
    have h6 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
    rw [h1, h6, sub_self]
  have h0_neg : ⟪F.N 5, x 0 - x 1⟫ < 0 := by
    rw [F.inner_sub 5 0 1]
    have h1 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
    have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    rw [h1, sub_zero]
    exact h0
  have hc := vol3_smul_cramer (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) u
  have h_inner := congr_arg (fun v => ⟪F.N 5, v⟫) hc
  rw [real_inner_smul_right] at h_inner
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right] at h_inner
  rw [h2, h6, mul_zero, mul_zero, add_zero, add_zero] at h_inner
  have h_vol_omega : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) =
      det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  have h_vol_edge : vol3 u (x 2 - x 1) (x 6 - x 1) =
      det3 (x 6 - x 2) (x 1 - x 2) u := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [h_vol_omega, h_vol_edge] at h_inner
  have h_prod : ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * ⟪F.N 5, u⟫ =
      (ρ * det3 (x 6 - x 2) (x 1 - x 2) u) * ⟪F.N 5, x 0 - x 1⟫ := by
    calc
      ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * ⟪F.N 5, u⟫ =
        ρ * (det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * ⟪F.N 5, u⟫) := by ring
      _ = ρ * (det3 (x 6 - x 2) (x 1 - x 2) u * ⟪F.N 5, x 0 - x 1⟫) := by rw [h_inner]
      _ = (ρ * det3 (x 6 - x 2) (x 1 - x 2) u) * ⟪F.N 5, x 0 - x 1⟫ := by ring
  rw [h_prod]
  exact mul_neg_of_pos_of_neg hin h0_neg

/-- In our negated frame `u = -u_doc` where `⟪F.N 5, u⟫ > 0`, `ρ * Ω < 0`. -/
theorem rho_mul_omega_neg_of_inner_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (ρ : ℝ)
    (hin : 0 < ρ * det3 (x 6 - x 2) (x 1 - x 2) u)
    (hN5 : 0 < ⟪F.N 5, u⟫) :
    ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := by
  have h := rimOrient F u ρ hin
  nlinarith

/-- In the doc's frame `u_doc` where `⟪F.N 5, u_doc⟫ < 0`, `0 < ρ * Ω`. -/
theorem rho_mul_omega_pos_of_inner_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (ρ : ℝ)
    (hin : 0 < ρ * det3 (x 6 - x 2) (x 1 - x 2) u)
    (hN5 : ⟪F.N 5, u⟫ < 0) :
    0 < ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  have h := rimOrient F u ρ hin
  nlinarith

-- =========================================================================
-- AC2: Kappa Signs as Plane-Side Facts with Ω and Rim Rewrite Lemmas
-- =========================================================================

/-- Algebraic decomposition of plane 026 screen determinant:
`det3 (x 0 - x 6) (x 2 - x 6) (x k - x 6) = (yk 0 + yk 1 + yk 2 - 1) * Ω`. -/
theorem det3_02k6_eq_sigma_sub_one_mul_omega (x : Fin 7 → ℝ³)
    (k : Fin 7) (yk : Fin 3 → ℝ)
    (hyk : x k - x 1 = yk 0 • (x 0 - x 1) + yk 1 • (x 2 - x 1) + yk 2 • (x 6 - x 1)) :
    det3 (x 0 - x 6) (x 2 - x 6) (x k - x 6) =
      (yk 0 + yk 1 + yk 2 - 1) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  have hk : x k - x 6 = yk 0 • (x 0 - x 1) + yk 1 • (x 2 - x 1) + (yk 2 - 1) • (x 6 - x 1) := by
    have h1 : x k - x 6 = (x k - x 1) - (x 6 - x 1) := by abel
    rw [h1, hyk]
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have h0 : x 0 - x 6 = (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have h2 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h0, h2, hk]
  rw [det3_comb (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) 1 0 (-1) 0 1 (-1) (yk 0) (yk 1) (yk 2 - 1)]
  have h_vol : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [h_vol]
  ring

/-- Plane-side fact for rim 6402: `0 < Ω * det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6)`.
Follows from `σ_4 = a4 + b4 + c4 > 1` (`type24_sigma_gt_one`). -/
theorem omega_mul_det3_0246_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6) := by
  have ⟨_, h4, _, _, _, _⟩ := type24_sigma_gt_one F p v y hxy hp hv0 hv1 hv2
  have hy4 : x 4 - x 1 = y 4 0 • (x 0 - x 1) + y 4 1 • (x 2 - x 1) + y 4 2 • (x 6 - x 1) := by
    have h := hxy 4
    rw [hp, Fin.sum_univ_three, hv0, hv1, hv2] at h
    exact sub_eq_of_eq_add' h
  have hdec := det3_02k6_eq_sigma_sub_one_mul_omega x 4 (y 4) hy4
  rw [Fin.sum_univ_three] at h4
  have h_om_ne := omega_ne_zero F
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  rw [hdec]
  calc
    0 < (y 4 0 + y 4 1 + y 4 2 - 1) * Ω ^ 2 := mul_pos (by linarith [h4]) h_om_sq
    _ = Ω * ((y 4 0 + y 4 1 + y 4 2 - 1) * Ω) := by ring

/-- Plane-side fact for rims 6302, 6032: `0 < Ω * det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6)`.
Follows from `σ_3 = a3 + b3 + c3 > 1` (`type24_sigma_gt_one`). -/
theorem omega_mul_det3_0236_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6) := by
  have ⟨h3, _, _, _, _, _⟩ := type24_sigma_gt_one F p v y hxy hp hv0 hv1 hv2
  have hy3 : x 3 - x 1 = y 3 0 • (x 0 - x 1) + y 3 1 • (x 2 - x 1) + y 3 2 • (x 6 - x 1) := by
    have h := hxy 3
    rw [hp, Fin.sum_univ_three, hv0, hv1, hv2] at h
    exact sub_eq_of_eq_add' h
  have hdec := det3_02k6_eq_sigma_sub_one_mul_omega x 3 (y 3) hy3
  rw [Fin.sum_univ_three] at h3
  have h_om_ne := omega_ne_zero F
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  rw [hdec]
  calc
    0 < (y 3 0 + y 3 1 + y 3 2 - 1) * Ω ^ 2 := mul_pos (by linarith [h3]) h_om_sq
    _ = Ω * ((y 3 0 + y 3 1 + y 3 2 - 1) * Ω) := by ring

/-- Plane-side fact for rim 6052: `0 < Ω * det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6)`.
Follows from `σ_5 = a5 + b5 + c5 > 1` (`type24_sigma_gt_one`). -/
theorem omega_mul_det3_0256_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6) := by
  have ⟨_, _, h5, _, _, _⟩ := type24_sigma_gt_one F p v y hxy hp hv0 hv1 hv2
  have hy5 : x 5 - x 1 = y 5 0 • (x 0 - x 1) + y 5 1 • (x 2 - x 1) + y 5 2 • (x 6 - x 1) := by
    have h := hxy 5
    rw [hp, Fin.sum_univ_three, hv0, hv1, hv2] at h
    exact sub_eq_of_eq_add' h
  have hdec := det3_02k6_eq_sigma_sub_one_mul_omega x 5 (y 5) hy5
  rw [Fin.sum_univ_three] at h5
  have h_om_ne := omega_ne_zero F
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  rw [hdec]
  calc
    0 < (y 5 0 + y 5 1 + y 5 2 - 1) * Ω ^ 2 := mul_pos (by linarith [h5]) h_om_sq
    _ = Ω * ((y 5 0 + y 5 1 + y 5 2 - 1) * Ω) := by ring

/-- General plane-side theorem along facet 7 (`236`): for any vertex `k ∉ facet 7`,
`det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6)` has the same sign relative to `Ω`
as `det3 (x 2 - x 6) (x 3 - x 6) (x 1 - x 6) = y3 0 * Ω`, which is strictly positive
since `0 < y3 0`. -/
theorem omega_mul_det3_23k6_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (k : Fin 7) (hk7 : k ∉ s0x_S24 7)
    (y3 : Fin 3 → ℝ)
    (hy3 : x 3 - x 1 = y3 0 • (x 0 - x 1) + y3 1 • (x 2 - x 1) + y3 2 • (x 6 - x 1))
    (ha3 : 0 < y3 0) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6) := by
  have h_om_ne := omega_ne_zero F
  have h2 : ⟪F.N 7, x 2 - x 6⟫ = 0 := by
    rw [F.inner_sub 7 2 6]
    have z2 : F.f 7 (x 2) = 0 := F.zero 7 2 (by decide)
    have z6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
    rw [z2, z6, sub_self]
  have h3 : ⟪F.N 7, x 3 - x 6⟫ = 0 := by
    rw [F.inner_sub 7 3 6]
    have z3 : F.f 7 (x 3) = 0 := F.zero 7 3 (by decide)
    have z6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
    rw [z3, z6, sub_self]
  have h1_neg : ⟪F.N 7, x 1 - x 6⟫ < 0 := by
    rw [F.inner_sub 7 1 6]
    have z6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
    have n1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
    rw [z6, sub_zero]; exact n1
  have hk_neg : ⟪F.N 7, x k - x 6⟫ < 0 := by
    rw [F.inner_sub 7 k 6]
    have z6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
    have nk : F.f 7 (x k) < 0 := F.neg 7 k hk7
    rw [z6, sub_zero]; exact nk
  have hc := vol3_smul_cramer (x 2 - x 6) (x 3 - x 6) (x 1 - x 6) (x k - x 6)
  have h_inner := congr_arg (fun v => ⟪F.N 7, v⟫) hc
  rw [real_inner_smul_right] at h_inner
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right] at h_inner
  rw [h2, h3, mul_zero, mul_zero, zero_add, zero_add] at h_inner
  have h_vol1 : vol3 (x 2 - x 6) (x 3 - x 6) (x 1 - x 6) = det3 (x 2 - x 6) (x 3 - x 6) (x 1 - x 6) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  have h_volk : vol3 (x 2 - x 6) (x 3 - x 6) (x k - x 6) = det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6) := by
    simp only [det3_expand, vol3, PiLp.sub_apply]; ring
  rw [h_vol1, h_volk] at h_inner
  have h231 : det3 (x 2 - x 6) (x 3 - x 6) (x 1 - x 6) = y3 0 * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    have h2' : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
      ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have h3' : x 3 - x 6 = y3 0 • (x 0 - x 1) + y3 1 • (x 2 - x 1) + (y3 2 - 1) • (x 6 - x 1) := by
      have h : x 3 - x 6 = (x 3 - x 1) - (x 6 - x 1) := by abel
      rw [h, hy3]
      ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have h1' : x 1 - x 6 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by
      ext i; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [h2', h3', h1']
    rw [det3_comb (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) 0 1 (-1) (y3 0) (y3 1) (y3 2 - 1) 0 0 (-1)]
    have h_v : vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) = det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
      simp only [det3_expand, vol3, PiLp.sub_apply]; ring
    rw [h_v]; ring
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have h_LHS : (Ω * det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6)) * ⟪F.N 7, x 1 - x 6⟫ < 0 := by
    calc
      (Ω * det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6)) * ⟪F.N 7, x 1 - x 6⟫ =
        Ω * (det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6) * ⟪F.N 7, x 1 - x 6⟫) := by ring
      _ = Ω * (det3 (x 2 - x 6) (x 3 - x 6) (x 1 - x 6) * ⟪F.N 7, x k - x 6⟫) := by rw [← h_inner]
      _ = (y3 0 * Ω ^ 2) * ⟪F.N 7, x k - x 6⟫ := by rw [h231]; ring
      _ < 0 := mul_neg_of_pos_of_neg (mul_pos ha3 h_om_sq) hk_neg
  have h_comm : ⟪F.N 7, x 1 - x 6⟫ * (Ω * det3 (x 2 - x 6) (x 3 - x 6) (x k - x 6)) < 0 := by linarith [h_LHS]
  exact pos_of_mul_neg_right h_comm (le_of_lt h1_neg)

/-- Plane-side fact for rim 6352: `0 < Ω * det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6)`.
Follows from `5 ∉ facet 236` and `a3 > 0`. -/
theorem omega_mul_det3_2356_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (ha3 : 0 < y 3 0) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6) := by
  have hy3 : x 3 - x 1 = y 3 0 • (x 0 - x 1) + y 3 1 • (x 2 - x 1) + y 3 2 • (x 6 - x 1) := by
    have h := hxy 3
    rw [hp, Fin.sum_univ_three, hv0, hv1, hv2] at h
    exact sub_eq_of_eq_add' h
  exact omega_mul_det3_23k6_pos F 5 (by decide) (y 3) hy3 ha3

/-- Plane-side fact for rim 6432: `0 < Ω * det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6)`.
Follows from `4 ∉ facet 236` and `a3 > 0`. -/
theorem omega_mul_det3_2346_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (ha3 : 0 < y 3 0) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) * det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6) := by
  have hy3 : x 3 - x 1 = y 3 0 • (x 0 - x 1) + y 3 1 • (x 2 - x 1) + y 3 2 • (x 6 - x 1) := by
    have h := hxy 3
    rw [hp, Fin.sum_univ_three, hv0, hv1, hv2] at h
    exact sub_eq_of_eq_add' h
  exact omega_mul_det3_23k6_pos F 4 (by decide) (y 3) hy3 ha3

-- -------------------------------------------------------------------------
-- Rim Kappa Rewrite Lemmas (DiagCross convention)
-- -------------------------------------------------------------------------

/-- Rewrite lemma for rim 6402:
`κ(6, 4, 0, 2) = - det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6)`.
Frame value: `-(a4 + b4 + c4 - 1) < 0`. -/
theorem kappa_rim6402 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 4) (x 0) (x 2) 2 - quad (x 6) (x 4) (x 0) (x 2) 0)
         (quad (x 6) (x 4) (x 0) (x 2) 3 - quad (x 6) (x 4) (x 0) (x 2) 1)
         (quad (x 6) (x 4) (x 0) (x 2) 0 - quad (x 6) (x 4) (x 0) (x 2) 1) =
      - det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6) := by
  change det3 (x 0 - x 6) (x 2 - x 4) (x 6 - x 4) = - det3 (x 0 - x 6) (x 2 - x 6) (x 4 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- Rewrite lemma for rim 6302:
`κ(6, 3, 0, 2) = - det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6)`.
Frame value: `-(a3 + b3 + c3 - 1) < 0`. -/
theorem kappa_rim6302 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 3) (x 0) (x 2) 2 - quad (x 6) (x 3) (x 0) (x 2) 0)
         (quad (x 6) (x 3) (x 0) (x 2) 3 - quad (x 6) (x 3) (x 0) (x 2) 1)
         (quad (x 6) (x 3) (x 0) (x 2) 0 - quad (x 6) (x 3) (x 0) (x 2) 1) =
      - det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6) := by
  change det3 (x 0 - x 6) (x 2 - x 3) (x 6 - x 3) = - det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- Rewrite lemma for rim 6352:
`κ(6, 3, 5, 2) = - det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6)`.
Frame value: `- a3 < 0`. -/
theorem kappa_rim6352 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 3) (x 5) (x 2) 2 - quad (x 6) (x 3) (x 5) (x 2) 0)
         (quad (x 6) (x 3) (x 5) (x 2) 3 - quad (x 6) (x 3) (x 5) (x 2) 1)
         (quad (x 6) (x 3) (x 5) (x 2) 0 - quad (x 6) (x 3) (x 5) (x 2) 1) =
      - det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6) := by
  change det3 (x 5 - x 6) (x 2 - x 3) (x 6 - x 3) = - det3 (x 2 - x 6) (x 3 - x 6) (x 5 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- Rewrite lemma for canonical rim 6052:
`κ(6, 0, 5, 2) = det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6)`.
Frame value: `+(a5 + b5 + c5 - 1) > 0`. -/
theorem kappa_rim6052_canonical (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 0) (x 5) (x 2) 2 - quad (x 6) (x 0) (x 5) (x 2) 0)
         (quad (x 6) (x 0) (x 5) (x 2) 3 - quad (x 6) (x 0) (x 5) (x 2) 1)
         (quad (x 6) (x 0) (x 5) (x 2) 0 - quad (x 6) (x 0) (x 5) (x 2) 1) =
      det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6) := by
  change det3 (x 5 - x 6) (x 2 - x 0) (x 6 - x 0) = det3 (x 0 - x 6) (x 2 - x 6) (x 5 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- Rewrite lemma for rim 6032:
`κ(6, 0, 3, 2) = det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6)`.
Frame value: `+(a3 + b3 + c3 - 1) > 0`. -/
theorem kappa_rim6032 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 0) (x 3) (x 2) 2 - quad (x 6) (x 0) (x 3) (x 2) 0)
         (quad (x 6) (x 0) (x 3) (x 2) 3 - quad (x 6) (x 0) (x 3) (x 2) 1)
         (quad (x 6) (x 0) (x 3) (x 2) 0 - quad (x 6) (x 0) (x 3) (x 2) 1) =
      det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6) := by
  change det3 (x 3 - x 6) (x 2 - x 0) (x 6 - x 0) = det3 (x 0 - x 6) (x 2 - x 6) (x 3 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- Rewrite lemma for rim 6432:
`κ(6, 4, 3, 2) = det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6)`.
Frame value: `+ a3 > 0`. -/
theorem kappa_rim6432 (x : Fin 7 → ℝ³) :
    det3 (quad (x 6) (x 4) (x 3) (x 2) 2 - quad (x 6) (x 4) (x 3) (x 2) 0)
         (quad (x 6) (x 4) (x 3) (x 2) 3 - quad (x 6) (x 4) (x 3) (x 2) 1)
         (quad (x 6) (x 4) (x 3) (x 2) 0 - quad (x 6) (x 4) (x 3) (x 2) 1) =
      det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6) := by
  change det3 (x 3 - x 6) (x 2 - x 4) (x 6 - x 4) = det3 (x 2 - x 6) (x 3 - x 6) (x 4 - x 6)
  simp only [det3_expand, PiLp.sub_apply]
  ring

-- -------------------------------------------------------------------------
-- Signed Products Ω * κ
-- -------------------------------------------------------------------------

theorem omega_mul_kappa_rim6402_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (quad (x 6) (x 4) (x 0) (x 2) 2 - quad (x 6) (x 4) (x 0) (x 2) 0)
           (quad (x 6) (x 4) (x 0) (x 2) 3 - quad (x 6) (x 4) (x 0) (x 2) 1)
           (quad (x 6) (x 4) (x 0) (x 2) 0 - quad (x 6) (x 4) (x 0) (x 2) 1) < 0 := by
  rw [kappa_rim6402]
  have h := omega_mul_det3_0246_pos F p v y hxy hp hv0 hv1 hv2
  linarith

theorem omega_mul_kappa_rim6302_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (quad (x 6) (x 3) (x 0) (x 2) 2 - quad (x 6) (x 3) (x 0) (x 2) 0)
           (quad (x 6) (x 3) (x 0) (x 2) 3 - quad (x 6) (x 3) (x 0) (x 2) 1)
           (quad (x 6) (x 3) (x 0) (x 2) 0 - quad (x 6) (x 3) (x 0) (x 2) 1) < 0 := by
  rw [kappa_rim6302]
  have h := omega_mul_det3_0236_pos F p v y hxy hp hv0 hv1 hv2
  linarith

theorem omega_mul_kappa_rim6352_neg {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (ha3 : 0 < y 3 0) :
    det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (quad (x 6) (x 3) (x 5) (x 2) 2 - quad (x 6) (x 3) (x 5) (x 2) 0)
           (quad (x 6) (x 3) (x 5) (x 2) 3 - quad (x 6) (x 3) (x 5) (x 2) 1)
           (quad (x 6) (x 3) (x 5) (x 2) 0 - quad (x 6) (x 3) (x 5) (x 2) 1) < 0 := by
  rw [kappa_rim6352]
  have h := omega_mul_det3_2356_pos F p v y hxy hp hv0 hv1 hv2 ha3
  linarith

theorem omega_mul_kappa_rim6052_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (quad (x 6) (x 0) (x 5) (x 2) 2 - quad (x 6) (x 0) (x 5) (x 2) 0)
           (quad (x 6) (x 0) (x 5) (x 2) 3 - quad (x 6) (x 0) (x 5) (x 2) 1)
           (quad (x 6) (x 0) (x 5) (x 2) 0 - quad (x 6) (x 0) (x 5) (x 2) 1) := by
  rw [kappa_rim6052_canonical]
  exact omega_mul_det3_0256_pos F p v y hxy hp hv0 hv1 hv2

theorem omega_mul_kappa_rim6032_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (quad (x 6) (x 0) (x 3) (x 2) 2 - quad (x 6) (x 0) (x 3) (x 2) 0)
           (quad (x 6) (x 0) (x 3) (x 2) 3 - quad (x 6) (x 0) (x 3) (x 2) 1)
           (quad (x 6) (x 0) (x 3) (x 2) 0 - quad (x 6) (x 0) (x 3) (x 2) 1) := by
  rw [kappa_rim6032]
  exact omega_mul_det3_0236_pos F p v y hxy hp hv0 hv1 hv2

theorem omega_mul_kappa_rim6432_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (p : ℝ³) (v : Fin 3 → ℝ³) (y : Fin 7 → Fin 3 → ℝ)
    (hxy : ∀ i, x i = p + ∑ e, y i e • v e) (hp : p = x 1)
    (hv0 : v 0 = x 0 - x 1) (hv1 : v 1 = x 2 - x 1) (hv2 : v 2 = x 6 - x 1)
    (ha3 : 0 < y 3 0) :
    0 < det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) *
      det3 (quad (x 6) (x 4) (x 3) (x 2) 2 - quad (x 6) (x 4) (x 3) (x 2) 0)
           (quad (x 6) (x 4) (x 3) (x 2) 3 - quad (x 6) (x 4) (x 3) (x 2) 1)
           (quad (x 6) (x 4) (x 3) (x 2) 0 - quad (x 6) (x 4) (x 3) (x 2) 1) := by
  rw [kappa_rim6432]
  exact omega_mul_det3_2346_pos F p v y hxy hp hv0 hv1 hv2 ha3

-- =========================================================================
-- AC3: Middles at the Corners (Item 4)
-- =========================================================================

-- View definitions in our negated frame (u = - u_doc)
def u_B1 (x : Fin 7 → ℝ³) (ε : ℝ) : ℝ³ := ε • (x 4 - x 0) - (x 5 - x 0)
def u_Bs1 (x : Fin 7 → ℝ³) (ε : ℝ) : ℝ³ := ε • (x 4 - x 0) - (x 5 - x 0)
def u_B2 (x : Fin 7 → ℝ³) (σ τ ε : ℝ) : ℝ³ := - (σ - 1) • (x 4 - x 0) - (τ + ε) • (x 5 - x 0)

def u_C1 (x : Fin 7 → ℝ³) (ε : ℝ) : ℝ³ := ε • (x 5 - x 0) - (x 4 - x 0)
def u_Ct1 (x : Fin 7 → ℝ³) (ε : ℝ) : ℝ³ := ε • (x 5 - x 0) - (x 4 - x 0)
def u_C2 (x : Fin 7 → ℝ³) (σ τ ε : ℝ) : ℝ³ := - (σ + ε) • (x 4 - x 0) - (τ - 1) • (x 5 - x 0)

-- -------------------------------------------------------------------------
-- Exact Algebraic Decompositions
-- -------------------------------------------------------------------------

-- B1 (chord 0 -> 4, middles x5 and x3)
theorem middle_B1_x5 (x : Fin 7 → ℝ³) (ε : ℝ) :
    x 5 = x 0 + ε • (x 4 - x 0) + (-1 : ℝ) • u_B1 x ε := by
  ext i
  simp only [u_B1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem middle_B1_x3 (x : Fin 7 → ℝ³) (s t ε : ℝ)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 0 + (s + ε * t) • (x 4 - x 0) + (-t) • u_B1 x ε := by
  ext i
  have hd := congr_arg (fun (v : ℝ³) => v i) hdecomp
  simp only [u_B1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  linear_combination hd

-- Bs1 (chord 0 -> 3, middles x4 and x5, s = 1)
theorem middle_Bs1_x4 (x : Fin 7 → ℝ³) (t ε : ℝ) (hden : 1 + ε * t ≠ 0)
    (hdecomp : x 3 - x 0 = (1 : ℝ) • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 4 = x 0 + (1 / (1 + ε * t)) • (x 3 - x 0) + (t / (1 + ε * t)) • u_Bs1 x ε := by
  ext i
  have hd := congr_arg (fun (v : ℝ³) => v i) hdecomp
  dsimp [u_Bs1]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  set D := 1 + ε * t
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  rw [hd]
  symm
  calc
    (x 0).ofLp i + 1 / D * (1 * e4 + t * e5) + t / D * (ε * e4 - e5)
      = (x 0).ofLp i + (1 * 1 + t * ε) / D * e4 + (1 * t - t * 1) / D * e5 := by ring
    _ = (x 0).ofLp i + D / D * e4 + 0 / D * e5 := by
        have h1 : 1 * 1 + t * ε = D := by dsimp [D]; ring
        have h2 : 1 * t - t * 1 = 0 := by ring
        rw [h1, h2]
    _ = (x 0).ofLp i + e4 := by
        rw [div_self hden, zero_div, zero_mul, add_zero, one_mul]
    _ = (x 4).ofLp i := by
        dsimp [e4]; ring

theorem middle_Bs1_x5 (x : Fin 7 → ℝ³) (t ε : ℝ) (hden : 1 + ε * t ≠ 0)
    (hdecomp : x 3 - x 0 = (1 : ℝ) • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 5 = x 0 + (ε / (1 + ε * t)) • (x 3 - x 0) + (-1 / (1 + ε * t)) • u_Bs1 x ε := by
  ext i
  have hd := congr_arg (fun (v : ℝ³) => v i) hdecomp
  dsimp [u_Bs1]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  set D := 1 + ε * t
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  rw [hd]
  symm
  calc
    (x 0).ofLp i + ε / D * (1 * e4 + t * e5) + (-1) / D * (ε * e4 - e5)
      = (x 0).ofLp i + (ε * 1 - 1 * ε) / D * e4 + (ε * t + 1) / D * e5 := by ring
    _ = (x 0).ofLp i + 0 / D * e4 + D / D * e5 := by
        have h1 : ε * 1 - 1 * ε = 0 := by ring
        have h2 : ε * t + 1 = D := by dsimp [D]; ring
        rw [h1, h2]
    _ = (x 0).ofLp i + e5 := by
        rw [zero_div, zero_mul, add_zero, div_self hden, one_mul]
    _ = (x 5).ofLp i := by
        dsimp [e5]; ring

-- B2 (chord 5 -> 3, middles x0 and x4, s > 1)
theorem middle_B2_x0 (x : Fin 7 → ℝ³) (s t ε : ℝ)
    (hden : s + t - 1 + s * ε ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 0 = x 5 + ((s - 1) / (s + t - 1 + s * ε)) • (x 3 - x 5) +
          (s / (s + t - 1 + s * ε)) • u_B2 x s t ε := by
  have h35 : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
    have h : x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) := by abel
    rw [h, hdecomp]
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h35]
  dsimp [u_B2]
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  set D := s + t - 1 + s * ε
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  symm
  calc
    (x 5).ofLp i + (s - 1) / D * (s * e4 + (t - 1) * e5) + s / D * (-(s - 1) * e4 - (t + ε) * e5)
      = (x 5).ofLp i + ((s - 1) * s - s * (s - 1)) / D * e4 +
        ((s - 1) * (t - 1) - s * (t + ε)) / D * e5 := by
        ring
    _ = (x 5).ofLp i + 0 / D * e4 + (-D) / D * e5 := by
        have h1 : (s - 1) * s - s * (s - 1) = 0 := by ring
        have h2 : (s - 1) * (t - 1) - s * (t + ε) = -D := by dsimp [D]; ring
        rw [h1, h2]
    _ = (x 5).ofLp i - e5 := by
        rw [zero_div, zero_mul, add_zero, neg_div_self hden]
        ring
    _ = (x 0).ofLp i := by
        dsimp [e5]
        ring

theorem middle_B2_x4 (x : Fin 7 → ℝ³) (s t ε : ℝ)
    (hden : s + t - 1 + s * ε ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 4 = x 5 + ((s + t - 1 + ε) / (s + t - 1 + s * ε)) • (x 3 - x 5) +
          ((s + t - 1) / (s + t - 1 + s * ε)) • u_B2 x s t ε := by
  have h35 : x 3 - x 5 = s • (x 4 - x 0) + (t - 1) • (x 5 - x 0) := by
    have h : x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) := by abel
    rw [h, hdecomp]
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h35]
  dsimp [u_B2]
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  set D := s + t - 1 + s * ε
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  symm
  calc
    (x 5).ofLp i + (s + t - 1 + ε) / D * (s * e4 + (t - 1) * e5) + (s + t - 1) / D * (-(s - 1) * e4 - (t + ε) * e5)
      = (x 5).ofLp i + ((s + t - 1 + ε) * s - (s + t - 1) * (s - 1)) / D * e4 +
        ((s + t - 1 + ε) * (t - 1) - (s + t - 1) * (t + ε)) / D * e5 := by
        ring
    _ = (x 5).ofLp i + D / D * e4 + (-D) / D * e5 := by
        have h1 : (s + t - 1 + ε) * s - (s + t - 1) * (s - 1) = D := by dsimp [D]; ring
        have h2 : (s + t - 1 + ε) * (t - 1) - (s + t - 1) * (t + ε) = -D := by dsimp [D]; ring
        rw [h1, h2]
    _ = (x 5).ofLp i + e4 - e5 := by
        rw [div_self hden, neg_div_self hden]
        ring
    _ = (x 4).ofLp i := by
        dsimp [e4, e5]
        ring

-- C1 (mirror of B1: chord 0 -> 5, middles x4 and x3)
theorem middle_C1_x4 (x : Fin 7 → ℝ³) (ε : ℝ) :
    x 4 = x 0 + ε • (x 5 - x 0) + (-1 : ℝ) • u_C1 x ε := by
  ext i
  simp only [u_C1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem middle_C1_x3 (x : Fin 7 → ℝ³) (s t ε : ℝ)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 3 = x 0 + (t + ε * s) • (x 5 - x 0) + (-s) • u_C1 x ε := by
  ext i
  have hd := congr_arg (fun (v : ℝ³) => v i) hdecomp
  simp only [u_C1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  linear_combination hd

-- Ct1 (mirror of Bs1: chord 0 -> 3, middles x5 and x4, t = 1)
theorem middle_Ct1_x5 (x : Fin 7 → ℝ³) (s ε : ℝ) (hden : 1 + ε * s ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + (1 : ℝ) • (x 5 - x 0)) :
    x 5 = x 0 + (1 / (1 + ε * s)) • (x 3 - x 0) + (s / (1 + ε * s)) • u_Ct1 x ε := by
  ext i
  have hd := congr_arg (fun (v : ℝ³) => v i) hdecomp
  dsimp [u_Ct1]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  set D := 1 + ε * s
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  rw [hd]
  symm
  calc
    (x 0).ofLp i + 1 / D * (s * e4 + 1 * e5) + s / D * (ε * e5 - e4)
      = (x 0).ofLp i + (1 * s - s * 1) / D * e4 + (1 * 1 + s * ε) / D * e5 := by ring
    _ = (x 0).ofLp i + 0 / D * e4 + D / D * e5 := by
        have h1 : 1 * s - s * 1 = 0 := by ring
        have h2 : 1 * 1 + s * ε = D := by dsimp [D]; ring
        rw [h1, h2]
    _ = (x 0).ofLp i + e5 := by
        rw [div_self hden, zero_div, zero_mul, add_zero, one_mul]
    _ = (x 5).ofLp i := by
        dsimp [e5]; ring

theorem middle_Ct1_x4 (x : Fin 7 → ℝ³) (s ε : ℝ) (hden : 1 + ε * s ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + (1 : ℝ) • (x 5 - x 0)) :
    x 4 = x 0 + (ε / (1 + ε * s)) • (x 3 - x 0) + (-1 / (1 + ε * s)) • u_Ct1 x ε := by
  ext i
  have hd := congr_arg (fun (v : ℝ³) => v i) hdecomp
  dsimp [u_Ct1]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  set D := 1 + ε * s
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  rw [hd]
  symm
  calc
    (x 0).ofLp i + ε / D * (s * e4 + 1 * e5) + (-1) / D * (ε * e5 - e4)
      = (x 0).ofLp i + (ε * s + 1) / D * e4 + (ε * 1 - 1 * ε) / D * e5 := by ring
    _ = (x 0).ofLp i + D / D * e4 + 0 / D * e5 := by
        have h1 : ε * s + 1 = D := by dsimp [D]; ring
        have h2 : ε * 1 - 1 * ε = 0 := by ring
        rw [h1, h2]
    _ = (x 0).ofLp i + e4 := by
        rw [zero_div, zero_mul, add_zero, div_self hden, one_mul]
    _ = (x 4).ofLp i := by
        dsimp [e4]; ring

-- C2 (mirror of B2: chord 4 -> 3, middles x0 and x5, t > 1)
theorem middle_C2_x0 (x : Fin 7 → ℝ³) (s t ε : ℝ)
    (hden : s + t - 1 + t * ε ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 0 = x 4 + ((t - 1) / (s + t - 1 + t * ε)) • (x 3 - x 4) +
          (t / (s + t - 1 + t * ε)) • u_C2 x s t ε := by
  have h34 : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
    have h : x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
    rw [h, hdecomp]
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h34]
  dsimp [u_C2]
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  set D := s + t - 1 + t * ε
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  symm
  calc
    (x 4).ofLp i + (t - 1) / D * ((s - 1) * e4 + t * e5) + t / D * (-(s + ε) * e4 - (t - 1) * e5)
      = (x 4).ofLp i + ((t - 1) * (s - 1) - t * (s + ε)) / D * e4 +
        ((t - 1) * t - t * (t - 1)) / D * e5 := by
        ring
    _ = (x 4).ofLp i + (-D) / D * e4 + 0 / D * e5 := by
        have h1 : (t - 1) * (s - 1) - t * (s + ε) = -D := by dsimp [D]; ring
        have h2 : (t - 1) * t - t * (t - 1) = 0 := by ring
        rw [h1, h2]
    _ = (x 4).ofLp i - e4 := by
        rw [zero_div, zero_mul, add_zero, neg_div_self hden]
        ring
    _ = (x 0).ofLp i := by
        dsimp [e4]
        ring

theorem middle_C2_x5 (x : Fin 7 → ℝ³) (s t ε : ℝ)
    (hden : s + t - 1 + t * ε ≠ 0)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    x 5 = x 4 + ((s + t - 1 + ε) / (s + t - 1 + t * ε)) • (x 3 - x 4) +
          ((s + t - 1) / (s + t - 1 + t * ε)) • u_C2 x s t ε := by
  have h34 : x 3 - x 4 = (s - 1) • (x 4 - x 0) + t • (x 5 - x 0) := by
    have h : x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) := by abel
    rw [h, hdecomp]
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h34]
  dsimp [u_C2]
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  set D := s + t - 1 + t * ε
  set e4 := (x 4).ofLp i - (x 0).ofLp i
  set e5 := (x 5).ofLp i - (x 0).ofLp i
  symm
  calc
    (x 4).ofLp i + (s + t - 1 + ε) / D * ((s - 1) * e4 + t * e5) + (s + t - 1) / D * (-(s + ε) * e4 - (t - 1) * e5)
      = (x 4).ofLp i + ((s + t - 1 + ε) * (s - 1) - (s + t - 1) * (s + ε)) / D * e4 +
        ((s + t - 1 + ε) * t - (s + t - 1) * (t - 1)) / D * e5 := by
        ring
    _ = (x 4).ofLp i + (-D) / D * e4 + D / D * e5 := by
        have h1 : (s + t - 1 + ε) * (s - 1) - (s + t - 1) * (s + ε) = -D := by dsimp [D]; ring
        have h2 : (s + t - 1 + ε) * t - (s + t - 1) * (t - 1) = D := by dsimp [D]; ring
        rw [h1, h2]
    _ = (x 4).ofLp i - e4 + e5 := by
        rw [div_self hden, neg_div_self hden]
        ring
    _ = (x 5).ofLp i := by
        dsimp [e4, e5]
        ring

-- -------------------------------------------------------------------------
-- Eventual Filter Bounds in 𝓝[>] 0
-- -------------------------------------------------------------------------

/-- Eventual chord and delta bounds for corner B1 (`s < 1, 0 < t`). -/
theorem eventually_B1_middle_bounds (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht : 0 < t) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε * t ∧ s + ε * t < 1) ∧
    (∀ᶠ _ in 𝓝[>] (0 : ℝ), (-1 : ℝ) < 0) ∧
    (∀ᶠ _ in 𝓝[>] (0 : ℝ), -t < 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have hc : ContinuousAt (fun ε : ℝ => ε) 0 := continuousAt_id
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
      (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) h1).filter_mono nhdsWithin_le_nhds
    exact h_pos.and h_lt
  · have hc : ContinuousAt (fun ε : ℝ => s + ε * t) 0 := by fun_prop
    have hval0 : 0 < s + (0 : ℝ) * t := by
      rw [zero_mul, add_zero]; exact hs0
    have hval1 : s + (0 : ℝ) * t < 1 := by
      rw [zero_mul, add_zero]; exact hs1
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε * t :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), s + ε * t < 1 :=
      (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval1).filter_mono nhdsWithin_le_nhds
    exact h_gt.and h_lt
  · exact eventually_mem_nhdsWithin.mono (fun _ _ => by norm_num)
  · exact eventually_mem_nhdsWithin.mono (fun _ _ => by linarith)

/-- Eventual chord and delta bounds for corner B2 (`1 < s, 0 < t`). -/
theorem eventually_B2_middle_bounds (s t : ℝ) (hs : 1 < s) (ht : 0 < t) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), s + t - 1 + s * ε ≠ 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s - 1) / (s + t - 1 + s * ε) ∧
                           (s - 1) / (s + t - 1 + s * ε) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s + t - 1 + ε) / (s + t - 1 + s * ε) ∧
                           (s + t - 1 + ε) / (s + t - 1 + s * ε) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s / (s + t - 1 + s * ε)) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s + t - 1) / (s + t - 1 + s * ε)) := by
  have hD0 : 0 < s + t - 1 + s * (0 : ℝ) := by
    rw [mul_zero, add_zero]; linarith
  have hcD : ContinuousAt (fun ε : ℝ => s + t - 1 + s * ε) 0 := by fun_prop
  have hD_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + t - 1 + s * ε :=
    (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hcD hD0).filter_mono nhdsWithin_le_nhds
  have h_ne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), s + t - 1 + s * ε ≠ 0 :=
    hD_pos.mono fun _ hd => hd.ne'
  have h_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  refine ⟨h_ne, ?_, ?_, ?_, ?_⟩
  · have hc0 : ContinuousAt (fun ε : ℝ => (s - 1) / (s + t - 1 + s * ε)) 0 := by
      exact ContinuousAt.div (by fun_prop) hcD (by linarith [hD0])
    have hval0 : 0 < (s - 1) / (s + t - 1 + s * (0 : ℝ)) := by
      rw [mul_zero, add_zero]; exact div_pos (by linarith) (by linarith)
    have hval1 : (s - 1) / (s + t - 1 + s * (0 : ℝ)) < 1 := by
      rw [mul_zero, add_zero]
      rw [div_lt_one (by linarith)]
      linarith
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s - 1) / (s + t - 1 + s * ε) :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc0 hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (s - 1) / (s + t - 1 + s * ε) < 1 :=
      (ContinuousAt.eventually_lt hc0 (continuousAt_const (x := 0)) hval1).filter_mono nhdsWithin_le_nhds
    exact h_gt.and h_lt
  · have hc4 : ContinuousAt (fun ε : ℝ => (s + t - 1 + ε) / (s + t - 1 + s * ε)) 0 := by
      exact ContinuousAt.div (by fun_prop) hcD (by linarith [hD0])
    have hval0 : 0 < (s + t - 1 + (0 : ℝ)) / (s + t - 1 + s * (0 : ℝ)) := by
      rw [add_zero, mul_zero, add_zero]
      rw [div_self (by linarith)]
      norm_num
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s + t - 1 + ε) / (s + t - 1 + s * ε) :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc4 hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (s + t - 1 + ε) / (s + t - 1 + s * ε) < 1 := by
      refine (hD_pos.and h_eps).mono fun ε ⟨hD, he⟩ => ?_
      rw [div_lt_one hD]
      have : (s - 1) * ε > 0 := mul_pos (by linarith) he
      linarith
    exact h_gt.and h_lt
  · exact hD_pos.mono fun _ hD => div_pos (by linarith) hD
  · exact hD_pos.mono fun _ hD => div_pos (by linarith) hD

/-- Eventual chord and delta bounds for corner C1 (`0 < s, 0 < t < 1`). -/
theorem eventually_C1_middle_bounds (s t : ℝ) (hs : 0 < s) (ht0 : 0 < t) (ht1 : t < 1) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t + ε * s ∧ t + ε * s < 1) ∧
    (∀ᶠ _ in 𝓝[>] (0 : ℝ), (-1 : ℝ) < 0) ∧
    (∀ᶠ _ in 𝓝[>] (0 : ℝ), -s < 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have hc : ContinuousAt (fun ε : ℝ => ε) 0 := continuousAt_id
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
      (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) h1).filter_mono nhdsWithin_le_nhds
    exact h_pos.and h_lt
  · have hc : ContinuousAt (fun ε : ℝ => t + ε * s) 0 := by fun_prop
    have hval0 : 0 < t + (0 : ℝ) * s := by
      rw [zero_mul, add_zero]; exact ht0
    have hval1 : t + (0 : ℝ) * s < 1 := by
      rw [zero_mul, add_zero]; exact ht1
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t + ε * s :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t + ε * s < 1 :=
      (ContinuousAt.eventually_lt hc (continuousAt_const (x := 0)) hval1).filter_mono nhdsWithin_le_nhds
    exact h_gt.and h_lt
  · exact eventually_mem_nhdsWithin.mono (fun _ _ => by norm_num)
  · exact eventually_mem_nhdsWithin.mono (fun _ _ => by linarith)

/-- Eventual chord and delta bounds for corner C2 (`0 < s, 1 < t`). -/
theorem eventually_C2_middle_bounds (s t : ℝ) (hs : 0 < s) (ht : 1 < t) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), s + t - 1 + t * ε ≠ 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (t - 1) / (s + t - 1 + t * ε) ∧
                           (t - 1) / (s + t - 1 + t * ε) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s + t - 1 + ε) / (s + t - 1 + t * ε) ∧
                           (s + t - 1 + ε) / (s + t - 1 + t * ε) < 1) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t / (s + t - 1 + t * ε)) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s + t - 1) / (s + t - 1 + t * ε)) := by
  have hD0 : 0 < s + t - 1 + t * (0 : ℝ) := by
    rw [mul_zero, add_zero]; linarith
  have hcD : ContinuousAt (fun ε : ℝ => s + t - 1 + t * ε) 0 := by fun_prop
  have hD_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + t - 1 + t * ε :=
    (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hcD hD0).filter_mono nhdsWithin_le_nhds
  have h_ne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), s + t - 1 + t * ε ≠ 0 :=
    hD_pos.mono fun _ hd => hd.ne'
  have h_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  refine ⟨h_ne, ?_, ?_, ?_, ?_⟩
  · have hc0 : ContinuousAt (fun ε : ℝ => (t - 1) / (s + t - 1 + t * ε)) 0 := by
      exact ContinuousAt.div (by fun_prop) hcD (by linarith [hD0])
    have hval0 : 0 < (t - 1) / (s + t - 1 + t * (0 : ℝ)) := by
      rw [mul_zero, add_zero]; exact div_pos (by linarith) (by linarith)
    have hval1 : (t - 1) / (s + t - 1 + t * (0 : ℝ)) < 1 := by
      rw [mul_zero, add_zero]
      rw [div_lt_one (by linarith)]
      linarith
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (t - 1) / (s + t - 1 + t * ε) :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc0 hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (t - 1) / (s + t - 1 + t * ε) < 1 :=
      (ContinuousAt.eventually_lt hc0 (continuousAt_const (x := 0)) hval1).filter_mono nhdsWithin_le_nhds
    exact h_gt.and h_lt
  · have hc5 : ContinuousAt (fun ε : ℝ => (s + t - 1 + ε) / (s + t - 1 + t * ε)) 0 := by
      exact ContinuousAt.div (by fun_prop) hcD (by linarith [hD0])
    have hval0 : 0 < (s + t - 1 + (0 : ℝ)) / (s + t - 1 + t * (0 : ℝ)) := by
      rw [add_zero, mul_zero, add_zero]
      rw [div_self (by linarith)]
      norm_num
    have h_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (s + t - 1 + ε) / (s + t - 1 + t * ε) :=
      (ContinuousAt.eventually_lt (continuousAt_const (x := 0)) hc5 hval0).filter_mono nhdsWithin_le_nhds
    have h_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (s + t - 1 + ε) / (s + t - 1 + t * ε) < 1 := by
      refine (hD_pos.and h_eps).mono fun ε ⟨hD, he⟩ => ?_
      rw [div_lt_one hD]
      have : (t - 1) * ε > 0 := mul_pos (by linarith) he
      linarith
    exact h_gt.and h_lt
  · exact hD_pos.mono fun _ hD => div_pos (by linarith) hD
  · exact hD_pos.mono fun _ hD => div_pos (by linarith) hD

end Minimality.T24.Q45
