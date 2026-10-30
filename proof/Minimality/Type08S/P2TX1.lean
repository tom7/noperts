module

public import Minimality.Type08S.P2TDefs

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / X1: pure real lemmas for `cellXba_rupert` (4-cycle `QTop` for a tilted robust quad, tilt avoidance).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem z4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

theorem z4_rel : ∀ i p : ZMod 4, p = i - 1 ∨ p = i + 1 ∨ p = i + 2 ∨ p = i := by decide

theorem quad4_0 {α : Type*} {w0 w1 w2 w3 : α} : quad w0 w1 w2 w3 0 = w0 := rfl
theorem quad4_1 {α : Type*} {w0 w1 w2 w3 : α} : quad w0 w1 w2 w3 1 = w1 := rfl
theorem quad4_2 {α : Type*} {w0 w1 w2 w3 : α} : quad w0 w1 w2 w3 2 = w2 := rfl
theorem quad4_3 {α : Type*} {w0 w1 w2 w3 : α} : quad w0 w1 w2 w3 3 = w3 := rfl

theorem zn4 : (∀ i : ZMod 4, i + 1 ≠ i) ∧ (∀ i : ZMod 4, i + 2 ≠ i) ∧ (∀ i : ZMod 4, i + 3 ≠ i) ∧
    (∀ i : ZMod 4, i + 1 ≠ i + 2) ∧ (∀ i : ZMod 4, i + 1 ≠ i + 3) ∧ (∀ i : ZMod 4, i + 2 ≠ i + 3) ∧
    (∀ i : ZMod 4, i + 3 = i - 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Cyclic form: distinct values with no two-peak pattern have exactly one local maximum. -/
theorem qtop4_gen (z : ZMod 4 → ℝ) (hne : ∀ i j : ZMod 4, i ≠ j → z i ≠ z j)
    (pk : ∀ i : ZMod 4, ¬ (z (i + 1) < z i ∧ z (i + 1) < z (i + 2) ∧ z (i + 3) < z i ∧
      z (i + 3) < z (i + 2))) : QTop 4 z := by
  obtain ⟨n1, n2, n3, n12, n13, n23, e3⟩ := zn4
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ z ⟨0, Finset.mem_univ _⟩
  have hp' : ∀ j, z j ≤ z p := fun j => hp j (Finset.mem_univ _)
  refine ⟨p, fun i hi => ?_⟩
  rcases z4_rel i p with h | h | h | h
  · left; rw [← h]; exact lt_of_le_of_ne (hp' i) (hne _ _ hi)
  · right; rw [← h]; exact lt_of_le_of_ne (hp' i) (hne _ _ hi)
  · by_contra hc
    push Not at hc
    obtain ⟨c1, c2⟩ := hc
    rw [← e3 i] at c1
    refine pk i ⟨lt_of_le_of_ne c2 (hne _ _ (n1 i)), ?_, lt_of_le_of_ne c1 (hne _ _ (n3 i)), ?_⟩
    · have hh := hp' i
      rw [h] at hh
      exact lt_of_le_of_ne (le_trans c2 hh) (hne _ _ (n12 i))
    · have hh := hp' i
      rw [h] at hh
      exact lt_of_le_of_ne (le_trans c1 hh) (hne _ _ (n23 i).symm)
  · exact absurd h.symm hi

theorem qtop4_det {w0 w1 w2 w3 : ℝ} (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h03 : w0 ≠ w3)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (pk1 : ¬ (w1 < w0 ∧ w1 < w2 ∧ w3 < w0 ∧ w3 < w2))
    (pk2 : ¬ (w0 < w1 ∧ w0 < w3 ∧ w2 < w1 ∧ w2 < w3)) :
    QTop 4 (quad w0 w1 w2 w3) := by
  refine qtop4_gen _ ?_ ?_
  · intro i j hij
    rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hij
      | (simp only [quad4_0, quad4_1, quad4_2, quad4_3]; first | assumption | exact Ne.symm ‹_›)
  · intro i
    rcases z4_cases i with rfl | rfl | rfl | rfl
    · have : (0 : ZMod 4) + 1 = 1 := by decide
      have h2 : (0 : ZMod 4) + 2 = 2 := by decide
      have h3 : (0 : ZMod 4) + 3 = 3 := by decide
      simpa [this, h2, h3, quad4_0, quad4_1, quad4_2, quad4_3] using pk1
    · have : (1 : ZMod 4) + 1 = 2 := by decide
      have h2 : (1 : ZMod 4) + 2 = 3 := by decide
      have h3 : (1 : ZMod 4) + 3 = 0 := by decide
      simp only [this, h2, h3, quad4_0, quad4_1, quad4_2, quad4_3]
      exact fun ⟨a, b, c, d⟩ => pk2 ⟨c, d, a, b⟩
    · have : (2 : ZMod 4) + 1 = 3 := by decide
      have h2 : (2 : ZMod 4) + 2 = 0 := by decide
      have h3 : (2 : ZMod 4) + 3 = 1 := by decide
      simp only [this, h2, h3, quad4_0, quad4_1, quad4_2, quad4_3]
      exact fun ⟨a, b, c, d⟩ => pk1 ⟨d, c, b, a⟩
    · have : (3 : ZMod 4) + 1 = 0 := by decide
      have h2 : (3 : ZMod 4) + 2 = 1 := by decide
      have h3 : (3 : ZMod 4) + 3 = 2 := by decide
      simp only [this, h2, h3, quad4_0, quad4_1, quad4_2, quad4_3]
      exact fun ⟨a, b, c, d⟩ => pk2 ⟨b, a, d, c⟩

theorem pair_ev (zi zj δi δj : ℝ) (hδ : δi ≠ δj) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), (zi < zj → zi + s * δi < zj + s * δj) ∧
      (zj < zi → zj + s * δj < zi + s * δi) ∧ zi + s * δi ≠ zj + s * δj := by
  rcases lt_trichotomy zi zj with h | h | h
  · filter_upwards [ev_lt_cont (f := fun s => zi + s * δi) (g := fun s => zj + s * δj)
      (by fun_prop) (by fun_prop) (by simpa using h)] with s hs
    exact ⟨fun _ => hs, fun h' => absurd h' (not_lt.2 h.le), hs.ne⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine ⟨fun h' => absurd h h'.ne, fun h' => absurd h h'.ne', fun e => hδ ?_⟩
    have hs' : (0 : ℝ) < s := hs
    rw [h] at e
    exact mul_left_cancel₀ hs'.ne' (by linarith)
  · filter_upwards [ev_lt_cont (f := fun s => zj + s * δj) (g := fun s => zi + s * δi)
      (by fun_prop) (by fun_prop) (by simpa using h)] with s hs
    exact ⟨fun h' => absurd h' (not_lt.2 h.le), fun _ => hs, hs.ne'⟩

/-- A robust 4-cycle `(z0, z1, z2, z3)` (`¬ Sep z0 z2 z1 z3`) with pairwise distinct first-order terms is
eventually (in the tilt) a strict cycle with exactly one local maximum. -/
theorem qtop4_ev {z0 z1 z2 z3 δ0 δ1 δ2 δ3 : ℝ} (hrob : ¬ Sep z0 z2 z1 z3)
    (h01 : δ0 ≠ δ1) (h02 : δ0 ≠ δ2) (h03 : δ0 ≠ δ3) (h12 : δ1 ≠ δ2) (h13 : δ1 ≠ δ3) (h23 : δ2 ≠ δ3) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), QTop 4 (quad (z0 + s * δ0) (z1 + s * δ1) (z2 + s * δ2) (z3 + s * δ3)) := by
  filter_upwards [pair_ev z0 z1 δ0 δ1 h01, pair_ev z0 z2 δ0 δ2 h02, pair_ev z0 z3 δ0 δ3 h03,
    pair_ev z1 z2 δ1 δ2 h12, pair_ev z1 z3 δ1 δ3 h13, pair_ev z2 z3 δ2 δ3 h23] with s
    ⟨a01, b01, n01⟩ ⟨a02, b02, n02⟩ ⟨a03, b03, n03⟩ ⟨a12, b12, n12⟩ ⟨a13, b13, n13⟩ ⟨a23, b23, n23⟩
  refine qtop4_det n01 n02 n03 n12 n13 n23 ?_ ?_
  · rintro ⟨p1, p2, p3, p4⟩
    apply hrob
    left
    simp only [max_le_iff, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> by_contra hc <;> push Not at hc
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
  · rintro ⟨p1, p2, p3, p4⟩
    apply hrob
    right
    simp only [max_le_iff, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> by_contra hc <;> push Not at hc
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]
    · first | linarith [a01 hc] | linarith [b01 hc] | linarith [a02 hc] | linarith [b02 hc] | linarith [a03 hc] | linarith [b03 hc] | linarith [a12 hc] | linarith [b12 hc] | linarith [a13 hc] | linarith [b13 hc] | linarith [a23 hc] | linarith [b23 hc]

end Type08Sp
end Minimality
