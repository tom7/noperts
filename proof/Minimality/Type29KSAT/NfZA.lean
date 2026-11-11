module

public import Minimality.Type29KSAT.NfK2

@[expose] public section

/-!
# Type 29, class K2a on the stratum `Z1`: the atoms of the class in normal form coordinates

On `Z1 = {s = 1, t = 1, a0 + h0 = 0}` the three atoms `KF1456 = det3 (x1 - x4) (x5 - x6) N_F`,
`KF1546 = det3 (x1 - x5) (x4 - x6) N_F` and `B:34 = <N_B, x3 - x4>` vanish (`z1_atoms`).  The case hypothesis of the
case-A core is that the edge direction `x1 - x4` is not orthogonal to the plane of the facet `B = 015`;
this is the nonvanishing of one of the two inner products `<x1 - x4, x0 - x1>`, `<x1 - x4, x0 - x5>`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K.SAT

variable {x : Fin 7 → ℝ³}

/-- **The three atoms of the class vanish on `Z1`.** -/
theorem z1_atoms (N : NF29 x) (F : S0xFac 9 s0x_S29 x) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0) :
    det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0 ∧ det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0 ∧
      ⟪F.N 1, x 3 - x 4⟫ = 0 := by
  obtain ⟨hs, ht, hh⟩ := hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [k2_atom1 N, ht]; ring
  · rw [k2_atom2 N, hs]; ring
  · have e51 : x 5 - x 1 = N.E₂ := by rw [N.x5, N.x1]; simp only [nfP]; module
    have e31 : x 3 - x 1 = -N.E₃ := by rw [N.x3, N.x1]; simp only [nfP]; module
    have e01 : x 0 - x 1 = N.a0 • N.E₁ + N.b0 • N.E₂ + (-N.h0) • N.E₃ := by
      rw [N.x0, N.x1]; simp only [nfP]; module
    have e34 : x 3 - x 4 = -N.E₃ - N.E₁ := by rw [N.x3, N.x4]; simp only [nfP]; module
    have g2 : ⟪F.N 1, N.E₂⟫ = 0 := by
      have := F.inner_sub 1 5 1
      rw [e51, F.zero 1 5 (by decide), F.zero 1 1 (by decide)] at this
      simpa using this
    have g0 : N.a0 * ⟪F.N 1, N.E₁⟫ + N.b0 * ⟪F.N 1, N.E₂⟫ + (-N.h0) * ⟪F.N 1, N.E₃⟫ = 0 := by
      have := F.inner_sub 1 0 1
      rw [e01, F.zero 1 0 (by decide), F.zero 1 1 (by decide)] at this
      simpa [inner_add_right, real_inner_smul_right] using this
    rw [g2] at g0
    have ha := N.ha0
    have h1 : ⟪F.N 1, N.E₁⟫ = -⟪F.N 1, N.E₃⟫ := by
      have hh' : N.h0 = -N.a0 := by linarith
      rw [hh'] at g0
      have : N.a0 * (⟪F.N 1, N.E₁⟫ + ⟪F.N 1, N.E₃⟫) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h ha.ne
      · linarith
    rw [e34, inner_sub_right, inner_neg_right]
    linarith

/-- **The case hypothesis of case A**: the edge direction `x1 - x4` is not orthogonal to both `x0 - x1` and `x0 - x5`
(on `Z1` these two edges span the plane of the facet `B = 015`). -/
def CaseA (y : Fin 7 → ℝ³) : Prop := ⟪y 1 - y 4, y 0 - y 1⟫ ≠ 0 ∨ ⟪y 1 - y 4, y 0 - y 5⟫ ≠ 0

end Minimality.H29K.SAT
