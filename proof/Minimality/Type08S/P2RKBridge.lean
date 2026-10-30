module

public import Minimality.Type08S.P2RKCore

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K, bridge: from the sign-normalised core tests to `TiltSign` tests in ℝ³ (orientation `σ = ±1`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace K

/-- Mirror `X ↦ σ X` of frame coordinates. -/
def unm (σ : ℝ) (P : P3) : P3 := (σ * P.1, P.2)

/-- The cycle in the order for which the `TiltSign` tests hold: `x` if `σ = 1`, reversed if `σ = -1`. -/
noncomputable def orient {α : Type*} (σ : ℝ) {k : ℕ} (f : ZMod k → α) : ZMod k → α := fun i => if σ = 1 then f i else f (-i)

theorem LT_unm {σ : ℝ} (hσ : σ * σ = 1) (t1 t2 : ℝ) (P Q S : P3) :
    LT σ t1 t2 (unm σ P) (unm σ Q) (unm σ S) ↔ LT 1 (σ * t1) t2 P Q S := by
  have h1 : ori (unm σ P) (unm σ Q) (unm σ S) = σ * ori P Q S := by simp only [ori, unm]; ring
  have h2 : fo t1 t2 (unm σ P) (unm σ Q) (unm σ S) = σ * fo (σ * t1) t2 P Q S := by
    simp only [fo, unm]
    linear_combination (-(((Q.2.1 - P.2.1) * (S.2.2 - P.2.2) - (Q.2.2 - P.2.2) * (S.2.1 - P.2.1)) * t1)) * hσ
  have h3 : ∀ x : ℝ, σ * (σ * x) = x := fun x => by linear_combination x * hσ
  simp only [LT, h1, h2, h3, one_mul, mul_eq_zero]
  have : σ ≠ 0 := fun h => by rw [h] at hσ; norm_num at hσ
  simp [this]

theorem ts_of_LT {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (o : ℝ³) {σ : ℝ} (hσ : σ * σ = 1) {ν : ℝ} (hν : 0 < ν)
    (t1 t2 t3 : ℝ) (P Q S : P3) (h : LT 1 (σ * t1) t2 P Q S) :
    TiltSignS σ (pr e1 e2 e3 o (unm σ Q) - pr e1 e2 e3 o (unm σ P))
      (pr e1 e2 e3 o (unm σ S) - pr e1 e2 e3 o (unm σ P)) (ν • e3) (pc e1 e2 e3 t1 t2 t3) := by
  rw [← LT_unm hσ] at h
  rw [pr_sub hF, pr_sub hF]
  have e0 : ν • e3 = pc e1 e2 e3 0 0 ν := by simp [pc]
  have d1 : det3 (pc e1 e2 e3 ((unm σ Q).1 - (unm σ P).1) ((unm σ Q).2.1 - (unm σ P).2.1) ((unm σ Q).2.2 - (unm σ P).2.2))
      (pc e1 e2 e3 ((unm σ S).1 - (unm σ P).1) ((unm σ S).2.1 - (unm σ P).2.1) ((unm σ S).2.2 - (unm σ P).2.2))
      (pc e1 e2 e3 0 0 ν) = ν * ori (unm σ P) (unm σ Q) (unm σ S) := by
    rw [det3_pc hF]; simp only [ori]; ring
  have d2 : det3 (pc e1 e2 e3 ((unm σ Q).1 - (unm σ P).1) ((unm σ Q).2.1 - (unm σ P).2.1) ((unm σ Q).2.2 - (unm σ P).2.2))
      (pc e1 e2 e3 ((unm σ S).1 - (unm σ P).1) ((unm σ S).2.1 - (unm σ P).2.1) ((unm σ S).2.2 - (unm σ P).2.2))
      (pc e1 e2 e3 t1 t2 t3) = fo t1 t2 (unm σ P) (unm σ Q) (unm σ S) + t3 * ori (unm σ P) (unm σ Q) (unm σ S) := by
    rw [det3_pc hF]; simp only [ori, fo]; ring
  simp only [TiltSignS, e0, d1, d2]
  rcases h with h | ⟨h0, h1⟩
  · left; nlinarith [mul_pos hν h]
  · right; refine ⟨by rw [h0]; ring, ?_⟩
    rw [h0]; linarith

theorem tilt_orient {k : ℕ} [NeZero k] (V : Finset ℝ³) (x : ZMod k → ℝ³) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (u₀ v : ℝ³)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSignS σ (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v) :
    (∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (orient σ x (i + 1) - orient σ x i) (orient σ x j - orient σ x i) u₀ v) ∧
    (∀ y ∈ V, (∀ j, y ≠ orient σ x j) → ∀ i, TiltSign (orient σ x (i + 1) - orient σ x i) (y - orient σ x i) u₀ v) := by
  rcases hσ with rfl | rfl
  · simp only [orient, if_true]
    exact ⟨fun i j hi hj => by simpa [TiltSignS, TiltSign] using hcyc i j hi hj,
      fun y hy hyx i => by simpa [TiltSignS, TiltSign] using hrest y hy hyx i⟩
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [orient, hne, if_false]
    have key : ∀ i : ZMod k, ∀ w : ℝ³, ∀ u : ℝ³,
        det3 (x (-(i + 1)) - x (-i)) (w - x (-i)) u =
          -det3 (x (-(i + 1) + 1) - x (-(i + 1))) (w - x (-(i + 1))) u := by
      intro i w u
      have e : -(i + 1) + 1 = -i := by ring
      rw [e, det3_rev_edge]
    refine ⟨?_, ?_⟩
    · intro i j hi hj
      have h1 : -j ≠ -(i + 1) := by intro h; apply hj; simpa using congrArg Neg.neg h
      have h2 : -j ≠ -(i + 1) + 1 := by
        intro h; apply hi
        have : -(i + 1) + 1 = -i := by ring
        rw [this] at h; simpa using congrArg Neg.neg h
      have t := hcyc (-(i + 1)) (-j) h1 h2
      simp only [TiltSignS, neg_one_mul, neg_pos] at t
      simp only [TiltSign]
      rw [key i (x (-j)) u₀, key i (x (-j)) v]
      rcases t with t | ⟨t0, t1⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [t0, neg_zero], by linarith⟩
    · intro y hy hyx i
      have t := hrest y hy (fun j h => hyx (-j) (by simpa using h)) (-(i + 1))
      simp only [TiltSignS, neg_one_mul, neg_pos] at t
      simp only [TiltSign]
      rw [key i y u₀, key i y v]
      rcases t with t | ⟨t0, t1⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [t0, neg_zero], by linarith⟩

/-- The two `TiltSign` fields of `LexCell` (rim tests and tests of the other points) for the cycle `x`. -/
def TiltTests (V : Finset ℝ³) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (u₀ v : ℝ³) : Prop :=
  (∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v) ∧
  (∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)

/-- Generic wrapper: core (σ-normalised) `LT` tests for a coordinate cycle `Pc` give `TiltTests` for the
`σ`-oriented cycle `x` of the mirrored points, base view `ν e3`, tilt `pc t1 t2 t3`. -/
theorem wrapK {k : ℕ} [NeZero k] {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (o : ℝ³) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {ν : ℝ} (hν : 0 < ν) (t1 t2 t3 : ℝ) (Pc : ZMod k → P3) (x : ZMod k → ℝ³)
    (hx : ∀ i, x i = pr e1 e2 e3 o (unm σ (Pc i))) (V : Finset ℝ³)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → LT 1 (σ * t1) t2 (Pc i) (Pc (i + 1)) (Pc j))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) →
      ∃ Q : P3, y = pr e1 e2 e3 o (unm σ Q) ∧ ∀ i, LT 1 (σ * t1) t2 (Pc i) (Pc (i + 1)) Q) :
    TiltTests V (orient σ x) (ν • e3) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine tilt_orient V x σ hσ _ _ ?_ ?_
  · intro i j hi hj
    rw [hx, hx, hx]
    exact ts_of_LT hF o hσ2 hν t1 t2 t3 _ _ _ (hcyc i j hi hj)
  · intro y hy hyx i
    obtain ⟨Q, rfl, hQ⟩ := hrest y hy hyx
    rw [hx, hx]
    exact ts_of_LT hF o hσ2 hν t1 t2 t3 _ _ _ (hQ i)

end K
end Type08Sp
end Minimality
