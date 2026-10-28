module

public import Minimality.Type08TouchN2
public import Minimality.Type08TouchT4
public import Minimality.Type08
public import Minimality.Type08Codim
public import Minimality.Type08R0
public import Minimality.Type08Rd
public import Minimality.Type08Flat

@[expose] public section

set_option autoImplicit true

/-!
# GT, group A: the generic frame lemma `HFrame.rupert_coords`

`sector_final` (Type08Sector) with the view `u`, the tilt `w` (arbitrary frame coordinates) and the
open depth condition `Q` (any cycle length) abstracted.  Every GT core is an instance.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Lexicographic orientation test in frame coordinates, view `cu`, tilt `cw`. -/
def LexTest (σ : ℝ) (cu cw : V3) (P Q S : V3) : Prop :=
  0 < σ * tst cu P Q S ∨ (tst cu P Q S = 0 ∧ 0 < σ * tst cw P Q S)

/-- The linear depth functional with frame coordinates `c`. -/
noncomputable def lin (E M U : ℝ) (c P : V3) : ℝ := c.x / E * P.x + c.y / M * P.y + c.z / U * P.z

/-- The vector with frame coordinates `c`. -/
noncomputable def fv (vb g u0 N : ℝ³) (c : V3) : ℝ³ :=
  (c.x / ⟪hfE vb g u0, hfE vb g u0⟫) • hfE vb g u0 + (c.y / ⟪N, N⟫) • (-N) +
    (c.z / ⟪u0, u0⟫) • u0

end Type08Sp

namespace HFrame
open Type08Sp
variable {vb g u0 N : ℝ³} {fG : ℝ³ → ℝ} (Fr : HFrame vb g u0 N fG)
include Fr

theorem fv_tst (c : V3) (P Q S : ℝ³) :
    det3 (hfE vb g u0) (-N) u0 * det3 (Q - P) (S - P) (fv vb g u0 N c) =
      tst c (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) := by
  have h := Fr.tst_gen (fv vb g u0 N c) P Q S
  have h1 := Fr.hee
  have h2 := Fr.hNN
  have h3 := Fr.hu
  have ee : ⟪hfE vb g u0, fv vb g u0 N c⟫ = c.x := by
    have a1 : ⟪hfE vb g u0, N⟫ = 0 := by rw [real_inner_comm]; exact Fr.inner_N_e
    simp only [fv, inner_add_right, real_inner_smul_right, inner_neg_right, a1,
      Fr.inner_e_u]
    field_simp; ring
  have eN : ⟪-N, fv vb g u0 N c⟫ = c.y := by
    have a1 : ⟪N, hfE vb g u0⟫ = 0 := Fr.inner_N_e
    have a2 : ⟪N, u0⟫ = 0 := Fr.hNu
    simp only [fv, inner_add_right, real_inner_smul_right, inner_neg_right, inner_neg_left, a1, a2]
    field_simp; ring
  have eu : ⟪u0, fv vb g u0 N c⟫ = c.z := by
    have a1 : ⟪u0, hfE vb g u0⟫ = 0 := by rw [real_inner_comm]; exact Fr.inner_e_u
    have a2 : ⟪u0, N⟫ = 0 := by rw [real_inner_comm]; exact Fr.hNu
    simp only [fv, inner_add_right, real_inner_smul_right, inner_neg_right, a1, a2]
    field_simp; ring
  rw [ee, eN, eu] at h
  exact h.symm

theorem fv_depth (c : V3) : ∃ K : ℝ, ∀ P : ℝ³,
    ⟪P, fv vb g u0 N c⟫ =
      lin ⟪hfE vb g u0, hfE vb g u0⟫ ⟪N, N⟫ ⟪u0, u0⟫ c (hfΦ vb g u0 fG P) + K := by
  refine ⟨(c.x / ⟪hfE vb g u0, hfE vb g u0⟫) * ⟪vb, hfE vb g u0⟫ +
    (c.y / ⟪N, N⟫) * (-⟪vb, N⟫) + (c.z / ⟪u0, u0⟫) * ⟪g, u0⟫, fun P => ?_⟩
  have h2 : ⟪P - vb, N⟫ = fG P := by rw [real_inner_comm, ← Fr.hN, Fr.hv]; ring
  have e1 : ⟪P, hfE vb g u0⟫ = ⟪P - vb, hfE vb g u0⟫ + ⟪vb, hfE vb g u0⟫ := by
    rw [← inner_add_left]; congr 1; abel
  have e2 : ⟪P, -N⟫ = -fG P - ⟪vb, N⟫ := by
    rw [inner_neg_right, ← h2, inner_sub_left]; ring
  have e3 : ⟪P, u0⟫ = ⟪P - g, u0⟫ + ⟪g, u0⟫ := by
    rw [← inner_add_left]; congr 1; abel
  simp only [fv, lin, hfΦ, inner_add_right, real_inner_smul_right, e1, e2, e3, inner_neg_right]
  ring

/-- **Generic lexicographic tilt, frame form.** -/
theorem rupert_coords (V : Finset ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³)
    (hxV : ∀ i, x i ∈ V) (σ : ℝ) (cu cw : V3) (hcu : cu.x ≠ 0 ∨ cu.y ≠ 0 ∨ cu.z ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      LexTest σ cu cw (hfΦ vb g u0 fG (x i)) (hfΦ vb g u0 fG (x (i + 1))) (hfΦ vb g u0 fG (x j)))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      LexTest σ cu cw (hfΦ vb g u0 fG (x i)) (hfΦ vb g u0 fG (x (i + 1))) (hfΦ vb g u0 fG y))
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → Q z → Q (fun i => c * z i))
    (hQk : ∀ (z : ZMod k → ℝ) (K : ℝ), Q z → Q (fun i => z i + K))
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q fun i =>
      lin ⟪hfE vb g u0, hfE vb g u0⟫ ⟪N, N⟫ ⟪u0, u0⟫ cu (hfΦ vb g u0 fG (x i)) +
      s * lin ⟪hfE vb g u0, hfE vb g u0⟫ ⟪N, N⟫ ⟪u0, u0⟫ cw (hfΦ vb g u0 fG (x i))) :
    IsRupert V := by
  classical
  set E : ℝ := ⟪hfE vb g u0, hfE vb g u0⟫ with hE
  set M : ℝ := ⟪N, N⟫ with hM
  set U : ℝ := ⟪u0, u0⟫ with hU
  set D0 := det3 (hfE vb g u0) (-N) u0 with hD0
  have hD0ne : D0 ≠ 0 := Fr.D0_ne
  set t := σ * D0 with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hconv : ∀ P Q S : ℝ³,
      LexTest σ cu cw (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) →
      TiltSign (Q - P) (S - P) (ε • fv vb g u0 N cu) (ε • fv vb g u0 N cw) := by
    intro P Q S h
    have hu := Fr.fv_tst cu P Q S
    have hw := Fr.fv_tst cw P Q S
    rcases h with h | ⟨h0, h1⟩
    · left
      rw [det3_smul_right]
      refine sgn_pos t _ ?_
      calc 0 < σ * tst cu (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) := h
        _ = t * det3 (Q - P) (S - P) (fv vb g u0 N cu) := by rw [ht, ← hu]; ring
    · right
      have hd0 : det3 (Q - P) (S - P) (fv vb g u0 N cu) = 0 := by
        rw [h0] at hu
        rcases mul_eq_zero.mp hu with h | h
        · exact absurd h hD0ne
        · exact h
      refine ⟨by rw [det3_smul_right, hd0, mul_zero], ?_⟩
      rw [det3_smul_right]
      refine sgn_pos t _ ?_
      calc 0 < σ * tst cw (hfΦ vb g u0 fG P) (hfΦ vb g u0 fG Q) (hfΦ vb g u0 fG S) := h1
        _ = t * det3 (Q - P) (S - P) (fv vb g u0 N cw) := by rw [ht, ← hw]; ring
  have hu0 : ε • fv vb g u0 N cu ≠ 0 := by
    intro h0
    have h1 : fv vb g u0 N cu = 0 := by
      rcases hεs with h | h <;> rw [h] at h0 <;> simpa using h0
    have ee : ⟪hfE vb g u0, fv vb g u0 N cu⟫ = cu.x := by
      have a1 : ⟪hfE vb g u0, N⟫ = 0 := by rw [real_inner_comm]; exact Fr.inner_N_e
      have := Fr.hee; have := Fr.hNN; have := Fr.hu
      simp only [fv, inner_add_right, real_inner_smul_right, inner_neg_right, a1, Fr.inner_e_u]
      field_simp; ring
    have eN : ⟪-N, fv vb g u0 N cu⟫ = cu.y := by
      have a1 : ⟪N, hfE vb g u0⟫ = 0 := Fr.inner_N_e
      have a2 : ⟪N, u0⟫ = 0 := Fr.hNu
      have := Fr.hee; have := Fr.hNN; have := Fr.hu
      simp only [fv, inner_add_right, real_inner_smul_right, inner_neg_right, inner_neg_left, a1, a2]
      field_simp; ring
    have eu : ⟪u0, fv vb g u0 N cu⟫ = cu.z := by
      have a1 : ⟪u0, hfE vb g u0⟫ = 0 := by rw [real_inner_comm]; exact Fr.inner_e_u
      have a2 : ⟪u0, N⟫ = 0 := by rw [real_inner_comm]; exact Fr.hNu
      have := Fr.hee; have := Fr.hNN; have := Fr.hu
      simp only [fv, inner_add_right, real_inner_smul_right, inner_neg_right, a1, a2]
      field_simp; ring
    rw [h1] at ee eN eu
    simp only [inner_zero_right] at ee eN eu
    rcases hcu with h | h | h <;> exact h (by linarith)
  refine isRupert_of_tilted_unimodal' V (ε • fv vb g u0 N cu) (ε • fv vb g u0 N cw) hu0 hk x hxV
    (fun i j hi hj => hconv _ _ _ (hcyc i j hi hj))
    (fun y hy hyx i => hconv _ _ _ (hrest y hy hyx i))
    (fun z => Q (fun i => ε * z i)) ?_ ?_ ?_ ?_
  · have : {z : ZMod k → ℝ | Q (fun i => ε * z i)} =
        (fun z : ZMod k → ℝ => fun i => ε * z i) ⁻¹' {z | Q z} := rfl
    rw [this]
    exact hQo.preimage (by fun_prop)
  · intro z c hc hQ
    have := hQs _ c hc hQ
    convert this using 2 with i
    ring
  · obtain ⟨Ku, hKu⟩ := Fr.fv_depth cu
    obtain ⟨Kw, hKw⟩ := Fr.fv_depth cw
    filter_upwards [hQe] with s hs
    have := hQk _ (Ku + s * Kw) hs
    show Q (fun i => ε * ⟪x i, ε • fv vb g u0 N cu + s • (ε • fv vb g u0 N cw)⟫)
    convert this using 2 with i
    have h1 : ⟪x i, ε • fv vb g u0 N cu + s • (ε • fv vb g u0 N cw)⟫ =
        ε * (⟪x i, fv vb g u0 N cu⟫ + s * ⟪x i, fv vb g u0 N cw⟫) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right]
      ring
    rw [h1, ← mul_assoc, hεε, one_mul, hKu, hKw]
    ring
  · intro z hinj hQ
    have h1 : IsCyclicUnimodal (fun i => ε * z i) :=
      hQu _ (fun i j hij => hinj (by
        rcases hεs with h | h <;> rw [h] at hij <;> simpa using hij)) hQ
    have h2 := h1.affine_sign (by omega) hεs 0
    convert h2 using 2 with i
    simp only [add_zero]
    rw [← mul_assoc, hεε, one_mul]

end HFrame
end Minimality
