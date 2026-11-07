module

public import Minimality.Type29KSAT.KDec
public import Minimality.Type29SAT.Nf

@[expose] public section

/-!
# L29T, T11: the atoms of the class clause of K2 in normal form coordinates

The class clause of the K2 core (off `Z1`) says: not all of the atoms
`KF1456 = det3 (x1 - x4) (x5 - x6) N_F`, `KF1546 = det3 (x1 - x5) (x4 - x6) N_F`, `B:34 = <N_B, x3 - x4>` vanish.
In the coordinates of a normal form they are `(t - 1) c`, `(1 - s) c` and `-(a0 + h0) m3 / a0` with `c, m3 <> 0`, so the clause
holds when `(s, t, a0 + h0)` is not `(1, 1, 0)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K.SAT

/-- **The three atoms of the class clause are not all zero** (for a facet family `F` of `y`). -/
def K2NZ {y : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 y) : Prop :=
  ¬ (det3 (y 1 - y 4) (y 5 - y 6) (F.N 5) = 0 ∧ det3 (y 1 - y 5) (y 4 - y 6) (F.N 5) = 0 ∧
    ⟪F.N 1, y 3 - y 4⟫ = 0)

/-- A vector `M` orthogonal to `E1`, `E2` and not to `E3` (with `E1, E2, E3` independent) has `det3 E1 E2 M <> 0`. -/
theorem det3_ne_of_perp (E1 E2 E3 M : ℝ³) (hD : det3 E1 E2 E3 ≠ 0) (h1 : ⟪M, E1⟫ = 0) (h2 : ⟪M, E2⟫ = 0)
    (h3 : ⟪M, E3⟫ ≠ 0) : det3 E1 E2 M ≠ 0 := by
  intro h
  have key : det3 E1 E2 M * det3 E1 E2 E3 =
      ⟪M, E3⟫ * ((E1 1 * E2 2 - E1 2 * E2 1) ^ 2 + (E1 2 * E2 0 - E1 0 * E2 2) ^ 2 +
        (E1 0 * E2 1 - E1 1 * E2 0) ^ 2) := by
    rw [inn3] at h1 h2 ⊢
    simp only [det3_expand]
    linear_combination
      ((E1 0 * E2 0 + E1 1 * E2 1 + E1 2 * E2 2) * (E2 0 * E3 0 + E2 1 * E3 1 + E2 2 * E3 2) -
        (E1 0 * E3 0 + E1 1 * E3 1 + E1 2 * E3 2) * (E2 0 * E2 0 + E2 1 * E2 1 + E2 2 * E2 2)) * h1 -
      ((E1 0 * E1 0 + E1 1 * E1 1 + E1 2 * E1 2) * (E2 0 * E3 0 + E2 1 * E3 1 + E2 2 * E3 2) -
        (E1 0 * E3 0 + E1 1 * E3 1 + E1 2 * E3 2) * (E1 0 * E2 0 + E1 1 * E2 1 + E1 2 * E2 2)) * h2
  rw [h, zero_mul] at key
  have hG : (E1 1 * E2 2 - E1 2 * E2 1) ^ 2 + (E1 2 * E2 0 - E1 0 * E2 2) ^ 2 +
      (E1 0 * E2 1 - E1 1 * E2 0) ^ 2 = 0 := by
    rcases mul_eq_zero.mp key.symm with h' | h'
    · exact absurd h' h3
    · exact h'
  have q0 := sq_nonneg (E1 1 * E2 2 - E1 2 * E2 1)
  have q1 := sq_nonneg (E1 2 * E2 0 - E1 0 * E2 2)
  have q2 := sq_nonneg (E1 0 * E2 1 - E1 1 * E2 0)
  have c0 : E1 1 * E2 2 - E1 2 * E2 1 = 0 := by nlinarith
  have c1 : E1 2 * E2 0 - E1 0 * E2 2 = 0 := by nlinarith
  have c2 : E1 0 * E2 1 - E1 1 * E2 0 = 0 := by nlinarith
  apply hD
  simp only [det3_expand, c0, c1, c2]; ring

variable {x : Fin 7 → ℝ³}

theorem k2_atom1 (N : NF29 x) (M : ℝ³) : det3 (x 1 - x 4) (x 5 - x 6) M = (N.t - 1) * det3 N.E₁ N.E₂ M := by
  simp only [det3_expand, N.x1, N.x4, N.x5, N.x6, nfP, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

theorem k2_atom2 (N : NF29 x) (M : ℝ³) : det3 (x 1 - x 5) (x 4 - x 6) M = (1 - N.s) * det3 N.E₁ N.E₂ M := by
  simp only [det3_expand, N.x1, N.x4, N.x5, N.x6, nfP, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

/-- **The class clause of K2 holds off `Z1`**: if `(s, t, a0 + h0) <> (1, 1, 0)`, the three atoms are not all zero. -/
theorem k2nz_of_nf (N : NF29 x) (F : S0xFac 9 s0x_S29 x)
    (hZ : ¬ (N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0)) : K2NZ F := by
  rintro ⟨hA, hB, hC⟩
  have e41 : x 4 - x 1 = N.E₁ := by rw [N.x4, N.x1]; simp only [nfP]; module
  have e51 : x 5 - x 1 = N.E₂ := by rw [N.x5, N.x1]; simp only [nfP]; module
  have e31 : x 3 - x 1 = -N.E₃ := by rw [N.x3, N.x1]; simp only [nfP]; module
  have e01 : x 0 - x 1 = N.a0 • N.E₁ + N.b0 • N.E₂ + (-N.h0) • N.E₃ := by
    rw [N.x0, N.x1]; simp only [nfP]; module
  have e34 : x 3 - x 4 = -N.E₃ - N.E₁ := by rw [N.x3, N.x4]; simp only [nfP]; module
  -- facet F = 1456
  have f1 : ⟪F.N 5, N.E₁⟫ = 0 := by
    have := F.inner_sub 5 4 1
    rw [e41, F.zero 5 4 (by decide), F.zero 5 1 (by decide)] at this
    simpa using this
  have f2 : ⟪F.N 5, N.E₂⟫ = 0 := by
    have := F.inner_sub 5 5 1
    rw [e51, F.zero 5 5 (by decide), F.zero 5 1 (by decide)] at this
    simpa using this
  have f3 : 0 < ⟪F.N 5, N.E₃⟫ := by
    have := F.inner_sub 5 3 1
    rw [e31, F.zero 5 1 (by decide), inner_neg_right] at this
    have h := F.neg 5 3 (by decide)
    linarith
  have hne := det3_ne_of_perp N.E₁ N.E₂ N.E₃ (F.N 5) N.hD f1 f2 f3.ne'
  have ht : N.t = 1 := by
    rw [k2_atom1 N] at hA
    rcases mul_eq_zero.mp hA with h | h
    · linarith
    · exact absurd h hne
  have hs : N.s = 1 := by
    rw [k2_atom2 N] at hB
    rcases mul_eq_zero.mp hB with h | h
    · linarith
    · exact absurd h hne
  -- facet B = 015
  have g2 : ⟪F.N 1, N.E₂⟫ = 0 := by
    have := F.inner_sub 1 5 1
    rw [e51, F.zero 1 5 (by decide), F.zero 1 1 (by decide)] at this
    simpa using this
  have g0 : N.a0 * ⟪F.N 1, N.E₁⟫ + N.b0 * ⟪F.N 1, N.E₂⟫ + (-N.h0) * ⟪F.N 1, N.E₃⟫ = 0 := by
    have := F.inner_sub 1 0 1
    rw [e01, F.zero 1 0 (by decide), F.zero 1 1 (by decide)] at this
    simpa [inner_add_right, real_inner_smul_right] using this
  have g3 : 0 < ⟪F.N 1, N.E₃⟫ := by
    have := F.inner_sub 1 3 1
    rw [e31, F.zero 1 1 (by decide), inner_neg_right] at this
    have h := F.neg 1 3 (by decide)
    linarith
  rw [e34, inner_sub_right, inner_neg_right] at hC
  rw [g2] at g0
  have hm : (N.a0 + N.h0) * ⟪F.N 1, N.E₃⟫ = 0 := by
    have ha := N.ha0
    have : N.a0 * ⟪F.N 1, N.E₁⟫ = N.h0 * ⟪F.N 1, N.E₃⟫ := by linarith
    have h1 : ⟪F.N 1, N.E₁⟫ = -⟪F.N 1, N.E₃⟫ := by linarith
    rw [h1] at this
    linarith
  have hh : N.a0 + N.h0 = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · exact absurd h g3.ne'
  exact hZ ⟨hs, ht, hh⟩

/-- The reflection preserves the property `K2NZ`. -/
theorem k2nz_mir {y : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 y) (h : K2NZ F) : K2NZ (mirFac F) := by
  rintro ⟨hA, hB, hC⟩
  apply h
  simp only [mirFac, ← mir_sub, mir_det3, mir_inner] at hA hB hC
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · exact hC

end Minimality.H29K.SAT
