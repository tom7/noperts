module

public import Minimality.Type08S.P2Defs

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X (package 7, P1'a): coordinate-rim machinery
A rim given by frame coordinates `X : ZMod k → ℝ×ℝ×ℝ` (with `x = pt e1 e2 e3 o`), view `e3`, tilt
`t1 e1 + t2 e2`; lexicographic orientation tests `LT` and the depth pattern `QTop`
("every index except one has a strictly larger neighbour": exactly one local maximum).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- The point with frame coordinates `P`. -/
def pr (e1 e2 e3 o : ℝ³) (p : ℝ × ℝ × ℝ) : ℝ³ := pt e1 e2 e3 o p.1 p.2.1 p.2.2

/-- Zero-order orientation of the projections. -/
def ori (P Q S : ℝ × ℝ × ℝ) : ℝ :=
  (Q.1 - P.1) * (S.2.1 - P.2.1) - (S.1 - P.1) * (Q.2.1 - P.2.1)

/-- First-order (tilt) term. -/
def fo (t1 t2 : ℝ) (P Q S : ℝ × ℝ × ℝ) : ℝ :=
  ((Q.2.1 - P.2.1) * (S.2.2 - P.2.2) - (Q.2.2 - P.2.2) * (S.2.1 - P.2.1)) * t1 +
  ((Q.2.2 - P.2.2) * (S.1 - P.1) - (Q.1 - P.1) * (S.2.2 - P.2.2)) * t2

/-- Lexicographic orientation test. -/
def LT (σ t1 t2 : ℝ) (P Q S : ℝ × ℝ × ℝ) : Prop :=
  0 < σ * ori P Q S ∨ (ori P Q S = 0 ∧ 0 < σ * fo t1 t2 P Q S)

/-- Depth of `P` at the tilted view `e3 + s (t1 e1 + t2 e2)`, up to a constant. -/
def dep (t1 t2 s : ℝ) (P : ℝ × ℝ × ℝ) : ℝ := P.2.2 + s * (t1 * P.1 + t2 * P.2.1)

theorem pr_sub (hF : Fr e1 e2 e3) (o : ℝ³) (P Q : ℝ × ℝ × ℝ) :
    pr e1 e2 e3 o Q - pr e1 e2 e3 o P =
      pc e1 e2 e3 (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2) := by
  simp only [pr, pt, pc]; module

theorem e3_pc : pc e1 e2 e3 0 0 1 = e3 := by simp [pc]

theorem tilt_bridge (hF : Fr e1 e2 e3) (o : ℝ³) (σ t1 t2 : ℝ) (P Q S : ℝ × ℝ × ℝ) :
    LT σ t1 t2 P Q S ↔
      TiltSignS σ (pr e1 e2 e3 o Q - pr e1 e2 e3 o P) (pr e1 e2 e3 o S - pr e1 e2 e3 o P) e3
        (pc e1 e2 e3 t1 t2 0) := by
  rw [pr_sub hF, pr_sub hF]
  have h1 : det3 (pc e1 e2 e3 (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2))
      (pc e1 e2 e3 (S.1 - P.1) (S.2.1 - P.2.1) (S.2.2 - P.2.2)) e3 = ori P Q S := by
    have he : det3 (pc e1 e2 e3 (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2))
      (pc e1 e2 e3 (S.1 - P.1) (S.2.1 - P.2.1) (S.2.2 - P.2.2)) e3 = det3 (pc e1 e2 e3 (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2))
      (pc e1 e2 e3 (S.1 - P.1) (S.2.1 - P.2.1) (S.2.2 - P.2.2)) (pc e1 e2 e3 0 0 1) := by
      rw [e3_pc (e1 := e1) (e2 := e2) (e3 := e3)]
    rw [he, det3_pc hF]; simp only [ori]; ring
  have h2 : det3 (pc e1 e2 e3 (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2))
      (pc e1 e2 e3 (S.1 - P.1) (S.2.1 - P.2.1) (S.2.2 - P.2.2)) (pc e1 e2 e3 t1 t2 0) =
        fo t1 t2 P Q S := by
    rw [det3_pc hF]; simp only [fo]; ring
  simp only [TiltSignS, LT, h1, h2]

/-- The "exactly one local maximum" depth pattern. -/
def QTop (k : ℕ) [NeZero k] (z : ZMod k → ℝ) : Prop :=
  ∃ p : ZMod k, ∀ i, i ≠ p → z i < z (i - 1) ∨ z i < z (i + 1)

theorem QTop_open (k : ℕ) [NeZero k] : IsOpen {z : ZMod k → ℝ | QTop k z} := by
  have : {z : ZMod k → ℝ | QTop k z} =
      ⋃ p : ZMod k, ⋂ i : ZMod k, {z : ZMod k → ℝ | i ≠ p → z i < z (i - 1) ∨ z i < z (i + 1)} := by
    ext z; simp [QTop]
  rw [this]
  refine isOpen_iUnion fun p => isOpen_iInter_of_finite fun i => ?_
  by_cases h : i = p
  · simp [h]
  · have : {z : ZMod k → ℝ | i ≠ p → z i < z (i - 1) ∨ z i < z (i + 1)} =
        {z | z i < z (i - 1)} ∪ {z | z i < z (i + 1)} := by ext z; simp [h]
    rw [this]
    exact (isOpen_lt (continuous_apply i) (continuous_apply (i - 1))).union
      (isOpen_lt (continuous_apply i) (continuous_apply (i + 1)))

theorem QTop_smul {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {c : ℝ} (hc : 0 < c) (h : QTop k z) :
    QTop k (fun i => c * z i) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, fun i hi => ?_⟩
  rcases hp i hi with h | h
  · exact Or.inl (mul_lt_mul_of_pos_left h hc)
  · exact Or.inr (mul_lt_mul_of_pos_left h hc)

theorem QTop_shift {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (K : ℝ) (h : QTop k z) :
    QTop k (fun i => z i + K) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, fun i hi => ?_⟩
  rcases hp i hi with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem QTop_unimodal {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (h : QTop k z) : IsCyclicUnimodal z := by
  obtain ⟨p, hp⟩ := h
  exact isCyclicUnimodal_of_top hk hinj p hp

/-- **Coordinate rim ⇒ Rupert.**  `X` is the rim in frame coordinates (view `e3`, tilt `t1 e1 + t2 e2`),
every other point of `V` passes the lexicographic tests, and the tilted depths have exactly one local
maximum for small tilt. -/
theorem rupert_of_coordRim (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (X : ZMod k → ℝ × ℝ × ℝ) (hxV : ∀ i, pr e1 e2 e3 o (X i) ∈ V)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (t1 t2 : ℝ)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → LT σ t1 t2 (X i) (X (i + 1)) (X j))
    (hall : ∀ y ∈ V, ∃ P, y = pr e1 e2 e3 o P ∧
      ((∃ j, P = X j) ∨ ∀ i, LT σ t1 t2 (X i) (X (i + 1)) P))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), QTop k fun i => dep t1 t2 s (X i)) : IsRupert V := by
  have hu0 : e3 ≠ 0 := by
    intro h; have := hF.n33; rw [h] at this; simp at this
  refine isRupert_of_tilted_unimodal_σ V e3 (pc e1 e2 e3 t1 t2 0) hu0 hk
    (fun i => pr e1 e2 e3 o (X i)) hxV σ hσ ?_ ?_ (fun z => QTop k z) (QTop_open k)
    (fun z c hc => QTop_smul hc) ?_ (fun z hinj hQ => QTop_unimodal (by omega) hinj hQ)
  · intro i j hi hj
    exact (tilt_bridge hF o σ t1 t2 _ _ _).1 (hcyc i j hi hj)
  · intro y hy hyx i
    obtain ⟨P, rfl, hP⟩ := hall y hy
    rcases hP with ⟨j, rfl⟩ | hP
    · exact absurd rfl (hyx j)
    · exact (tilt_bridge hF o σ t1 t2 _ _ _).1 (hP i)
  · filter_upwards [hQe] with s hs
    have hd : ∀ i, ⟪pr e1 e2 e3 o (X i), e3 + s • pc e1 e2 e3 t1 t2 0⟫ =
        dep t1 t2 s (X i) + ⟪o, e3 + s • pc e1 e2 e3 t1 t2 0⟫ := by
      intro i
      have : pr e1 e2 e3 o (X i) = o + pc e1 e2 e3 (X i).1 (X i).2.1 (X i).2.2 := rfl
      rw [this, inner_add_left]
      have h2 : ⟪pc e1 e2 e3 (X i).1 (X i).2.1 (X i).2.2, e3 + s • pc e1 e2 e3 t1 t2 0⟫ =
          dep t1 t2 s (X i) := by
        have : e3 + s • pc e1 e2 e3 t1 t2 0 = pc e1 e2 e3 (s * t1) (s * t2) 1 := by
          simp only [pc]; module
        rw [this, inner_pc hF]; simp only [dep]; ring
      rw [h2]; ring
    have := QTop_shift (⟪o, e3 + s • pc e1 e2 e3 t1 t2 0⟫) hs
    simpa only [hd] using this


/-! ### `ZMod 6` bookkeeping -/

/-- A 6-cycle of values. -/
def six {α : Type*} (p₀ p₁ p₂ p₃ p₄ p₅ : α) : ZMod 6 → α := ![p₀, p₁, p₂, p₃, p₄, p₅]
theorem six_0 {α : Type*} {p₀ p₁ p₂ p₃ p₄ p₅ : α} : six p₀ p₁ p₂ p₃ p₄ p₅ 0 = p₀ := rfl
theorem six_1 {α : Type*} {p₀ p₁ p₂ p₃ p₄ p₅ : α} : six p₀ p₁ p₂ p₃ p₄ p₅ 1 = p₁ := rfl
theorem six_2 {α : Type*} {p₀ p₁ p₂ p₃ p₄ p₅ : α} : six p₀ p₁ p₂ p₃ p₄ p₅ 2 = p₂ := rfl
theorem six_3 {α : Type*} {p₀ p₁ p₂ p₃ p₄ p₅ : α} : six p₀ p₁ p₂ p₃ p₄ p₅ 3 = p₃ := rfl
theorem six_4 {α : Type*} {p₀ p₁ p₂ p₃ p₄ p₅ : α} : six p₀ p₁ p₂ p₃ p₄ p₅ 4 = p₄ := rfl
theorem six_5 {α : Type*} {p₀ p₁ p₂ p₃ p₄ p₅ : α} : six p₀ p₁ p₂ p₃ p₄ p₅ 5 = p₅ := rfl

theorem z6_cases (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide
theorem z6_add_one : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧
    (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := by decide
theorem z6_sub_one : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

end Type08Sp
end Minimality
