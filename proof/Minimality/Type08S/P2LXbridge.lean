module

public import Minimality.Type08S.SCn
public import Minimality.Type08S.SCs

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma LX (ii), bridge (package K): triangle certificates give the `hrest` tests of a tilted rim
A point `y ∈ V` (not on the rim `x : ZMod 5 → ℝ³`) that has a `TriCert` (strictly inside a triangle of points of `V`,
lexicographic tilt `(u, v)`) passes the `TiltSign` test against every rim edge, provided the rim itself is
lexicographically convex (`hcyc`).  Proof: at `u + εv` the edge functional `ℓ` is affine; a minimiser of `ℓ` over the
non-rim points cannot have a triangle certificate.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem tiltSign_of_ev {a b u v : ℝ³}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a b (u + ε • v)) : TiltSign a b u v := by
  simp only [det3_add_smul] at h
  set A := det3 a b u
  set B := det3 a b v
  by_contra hn
  unfold TiltSign at hn
  have hA : A ≤ 0 := not_lt.1 fun h' => hn (Or.inl h')
  rcases hA.lt_or_eq with hlt | heq
  · have h2 := eventually_pos_affine (A := -A) (B := -B) (Or.inl (neg_pos.2 hlt))
    obtain ⟨ε, h3, h4⟩ := (h.and h2).exists
    linarith
  · have hB : B ≤ 0 := not_lt.1 fun h' => hn (Or.inr ⟨heq, h'⟩)
    obtain ⟨ε, h3, h4⟩ := (h.and self_mem_nhdsWithin).exists
    have : (0 : ℝ) < ε := h4
    rw [heq] at h3
    nlinarith

theorem bary_id (e a b c y w x0 : ℝ³) :
    det3 (c - b) (y - b) w + det3 (a - c) (y - c) w + det3 (b - a) (y - a) w = det3 (b - a) (c - a) w ∧
    det3 (b - a) (c - a) w * det3 e (y - x0) w =
      det3 (c - b) (y - b) w * det3 e (a - x0) w + det3 (a - c) (y - c) w * det3 e (b - x0) w +
      det3 (b - a) (y - a) w * det3 e (c - x0) w := by
  constructor <;> (simp only [det3_expand, PiLp.sub_apply]; ring)

theorem plucker_id (e p q r w : ℝ³) :
    det3 p q w * det3 e r w = det3 e q w * det3 p r w - det3 e p w * det3 q r w := by
  simp only [det3_expand, PiLp.sub_apply]; ring


theorem hrest_of_tri (V : Finset ℝ³) (u v : ℝ³) (x : ZMod 5 → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u v)
    (hE : ∀ y ∈ V, (∀ j, y ≠ x j) → TriCert V u v y) :
    ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u v := by
  classical
  intro y0 hy0 hy0x i
  apply tiltSign_of_ev
  set E := V.filter (fun y => ∀ j, y ≠ x j) with hEdef
  have hy0E : y0 ∈ E := by simp [hEdef, hy0, hy0x]
  have hc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (i + 1) - x i) (x j - x i) (u + ε • v) := by
    rw [Filter.eventually_all]
    intro j
    by_cases h1 : j ≠ i
    · by_cases h2 : j ≠ i + 1
      · filter_upwards [(hcyc i j h1 h2).eventually] with ε hε _ _ using hε
      · exact Filter.Eventually.of_forall fun ε h h' => (h2 h').elim
    · exact Filter.Eventually.of_forall fun ε h _ => (h1 h).elim
  have ht : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ E, ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V,
      0 < det3 (b - a) (c - a) (u + ε • v) ∧ 0 < det3 (b - a) (y - a) (u + ε • v) ∧
      0 < det3 (c - b) (y - b) (u + ε • v) ∧ 0 < det3 (a - c) (y - c) (u + ε • v) := by
    rw [Filter.eventually_all_finset]
    intro y hy
    have hyV : y ∈ V := (Finset.mem_filter.1 hy).1
    have hyx : ∀ j, y ≠ x j := (Finset.mem_filter.1 hy).2
    obtain ⟨a, ha, b, hb, c, hc', h0, h1, h2, h3⟩ := hE y hyV hyx
    filter_upwards [h0.eventually, h1.eventually, h2.eventually, h3.eventually] with ε e0 e1 e2 e3
    exact ⟨a, ha, b, hb, c, hc', e0, e1, e2, e3⟩
  filter_upwards [hc, ht] with ε hc ht
  set w := u + ε • v with hw
  set ℓ : ℝ³ → ℝ := fun p => det3 (x (i + 1) - x i) (p - x i) w with hℓ
  have hrim : ∀ j, 0 ≤ ℓ (x j) := by
    intro j
    by_cases h1 : j = i
    · subst h1; simp only [hℓ, sub_self]; simp [det3_expand]
    · by_cases h2 : j = i + 1
      · subst h2; simp only [hℓ, det3_expand, PiLp.sub_apply]; apply le_of_eq; ring
      · exact (hc j h1 h2).le
  have hz : 0 < ℓ (x (i + 2)) := by
    refine hc (i + 2) ?_ ?_
    · have : ∀ i : ZMod 5, i + 2 ≠ i := by decide
      exact this i
    · have : ∀ i : ZMod 5, i + 2 ≠ i + 1 := by decide
      exact this i
  obtain ⟨m, hmE, hmin⟩ := Finset.exists_min_image E ℓ ⟨y0, hy0E⟩
  have hmpos : 0 < ℓ m := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨a, ha, b, hb, c, hc', hA, hb1, hb2, hb3⟩ := ht m hmE
    obtain ⟨hs, hid⟩ := bary_id (x (i + 1) - x i) a b c m w (x i)
    have hlow : ∀ p ∈ V, ℓ m ≤ ℓ p := by
      intro p hp
      by_cases hpE : p ∈ E
      · exact hmin p hpE
      · have : ∃ j, p = x j := by
          by_contra hno
          push_neg at hno
          exact hpE (by simp [hEdef, hp, fun j => (hno j)])
        obtain ⟨j, rfl⟩ := this
        exact le_trans hneg (hrim j)
    have la := hlow a ha
    have lb := hlow b hb
    have lc := hlow c hc'
    set α := det3 (c - b) (m - b) w
    set β := det3 (a - c) (m - c) w
    set γ := det3 (b - a) (m - a) w
    set A := det3 (b - a) (c - a) w
    have h1 : α * (ℓ a - ℓ m) = 0 ∧ β * (ℓ b - ℓ m) = 0 ∧ γ * (ℓ c - ℓ m) = 0 := by
      have p1 : 0 ≤ α * (ℓ a - ℓ m) := mul_nonneg hb2.le (by linarith)
      have p2 : 0 ≤ β * (ℓ b - ℓ m) := mul_nonneg hb3.le (by linarith)
      have p3 : 0 ≤ γ * (ℓ c - ℓ m) := mul_nonneg hb1.le (by linarith)
      have hsum : α * (ℓ a - ℓ m) + β * (ℓ b - ℓ m) + γ * (ℓ c - ℓ m) = 0 := by
        have : A * ℓ m = α * ℓ a + β * ℓ b + γ * ℓ c := hid
        nlinarith
      refine ⟨by linarith, by linarith, by linarith⟩
    obtain ⟨k1, k2, k3⟩ := h1
    have ea : ℓ a = ℓ m := by
      rcases mul_eq_zero.1 k1 with h | h
      · exact absurd h hb2.ne'
      · linarith
    have eb : ℓ b = ℓ m := by
      rcases mul_eq_zero.1 k2 with h | h
      · exact absurd h hb3.ne'
      · linarith
    have ec : ℓ c = ℓ m := by
      rcases mul_eq_zero.1 k3 with h | h
      · exact absurd h hb1.ne'
      · linarith
    -- non-collinearity
    have pl := plucker_id (x (i + 1) - x i) (b - a) (c - a) (x (i + 2) - x i) w
    have d1 : det3 (x (i + 1) - x i) (b - a) w = 0 := by
      have : det3 (x (i + 1) - x i) (b - a) w = ℓ b - ℓ a := by
        simp only [hℓ, det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
    have d2 : det3 (x (i + 1) - x i) (c - a) w = 0 := by
      have : det3 (x (i + 1) - x i) (c - a) w = ℓ c - ℓ a := by
        simp only [hℓ, det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
    rw [d1, d2] at pl
    have : A * ℓ (x (i + 2)) = 0 := by simpa [hℓ] using pl
    exact absurd this (mul_pos hA hz).ne'
  exact lt_of_lt_of_le hmpos (hmin y0 hy0E)

end Type08Sp
end Minimality
