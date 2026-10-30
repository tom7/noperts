module

public import Minimality.Type08S.P2LXbridge
public import Minimality.Type08S.P2LXbase

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma LX (ii), rim machinery (package K)
`rupert_of_rim5`: a pentagon given by frame coordinates, view `e3`, tilt `t1 e1 + t2 e2` (orientation sign `+1`):
the lexicographic convexity tests `hcyc`, a triangle certificate (`TriCert`) for every other vertex, and the
tilted depths having eventually a unique local maximum or a unique local minimum  ==>  Rupert.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Exactly one local maximum, or exactly one local minimum. -/
def QOr (k : ℕ) [NeZero k] (z : ZMod k → ℝ) : Prop := QTop k z ∨ QTop k fun i => -z i

theorem QOr_open (k : ℕ) [NeZero k] : IsOpen {z : ZMod k → ℝ | QOr k z} := by
  have h2 : IsOpen {z : ZMod k → ℝ | QTop k fun i => -z i} :=
    (QTop_open k).preimage (by fun_prop : Continuous fun (z : ZMod k → ℝ) i => -z i)
  exact (QTop_open k).union h2

theorem QOr_smul {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {c : ℝ} (hc : 0 < c) (h : QOr k z) :
    QOr k fun i => c * z i := by
  rcases h with h | h
  · exact Or.inl (QTop_smul hc h)
  · right
    have := QTop_smul hc h
    simpa [mul_neg] using this

theorem QOr_shift {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (K : ℝ) (h : QOr k z) :
    QOr k fun i => z i + K := by
  rcases h with h | h
  · exact Or.inl (QTop_shift K h)
  · right
    have := QTop_shift (-K) h
    simpa [neg_add, add_comm] using this

theorem QOr_unimodal {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (h : QOr k z) : IsCyclicUnimodal z := by
  rcases h with h | h
  · exact QTop_unimodal hk hinj h
  · have h1 := QTop_unimodal hk (fun a b e => hinj (neg_injective e)) h
    have := IsCyclicUnimodal.neg' hk h1
    simpa using this

/-- **Coordinate pentagon ⇒ Rupert** (triangle-certificate form). -/
theorem rupert_of_rim5 (hF : Fr e1 e2 e3) (o : ℝ³) (V : Finset ℝ³)
    (X : ZMod 5 → ℝ × ℝ × ℝ) (hxV : ∀ i, pr e1 e2 e3 o (X i) ∈ V) (t1 t2 : ℝ)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → LT 1 t1 t2 (X i) (X (i + 1)) (X j))
    (hE : ∀ y ∈ V, (∀ j, y ≠ pr e1 e2 e3 o (X j)) →
      TriCert V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 t1 t2 0) y)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), QOr 5 fun i => dep t1 t2 s (X i)) : IsRupert V := by
  have hu0 : e3 ≠ 0 := by
    intro h; have := hF.n33; rw [h] at this; simp at this
  have hcyc' : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TiltSign (pr e1 e2 e3 o (X (i + 1)) - pr e1 e2 e3 o (X i)) (pr e1 e2 e3 o (X j) - pr e1 e2 e3 o (X i))
        (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 t1 t2 0) := by
    intro i j hi hj
    have := (tilt_bridge hF o 1 t1 t2 _ _ _).1 (hcyc i j hi hj)
    rw [e3_pc]
    simpa [TiltSignS, TiltSign] using this
  have hrest := hrest_of_tri V (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 t1 t2 0) (fun i => pr e1 e2 e3 o (X i)) hxV
    hcyc' hE
  refine isRupert_of_tilted_unimodal_σ V e3 (pc e1 e2 e3 t1 t2 0) hu0 (k := 5) (by norm_num)
    (fun i => pr e1 e2 e3 o (X i)) hxV 1 (Or.inl rfl) ?_ ?_ (fun z => QOr 5 z) (QOr_open 5)
    (fun z c hc => QOr_smul hc) ?_ (fun z hinj hQ => QOr_unimodal (by omega) hinj hQ)
  · intro i j hi hj
    exact (tilt_bridge hF o 1 t1 t2 _ _ _).1 (hcyc i j hi hj)
  · intro y hy hyx i
    have := hrest y hy hyx i
    rw [e3_pc] at this
    have h2 : TiltSignS 1 (pr e1 e2 e3 o (X (i + 1)) - pr e1 e2 e3 o (X i)) (y - pr e1 e2 e3 o (X i)) e3
        (pc e1 e2 e3 t1 t2 0) := by
      simpa [TiltSignS, TiltSign] using this
    exact h2
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
    have := QOr_shift (⟪o, e3 + s • pc e1 e2 e3 t1 t2 0⟫) hs
    simpa only [hd] using this

end Type08Sp
end Minimality
