module

public import SmallRupert.Oct9Gale

@[expose] public section

/-!
# Weak quad edges (LEMMAS.md §9.6: Lemmas 9.10, 9.11, Corollary 9.0)

When `f = 0`, the edge views chosen in §9.5 are *weak* quad edges: the face
`x' y' p'` at the antipodal edge contains the view direction `u = y - x`.
This file proves Lemma 9.11 for such an edge: it gives a passage unless it is
touching or its lateral edge `p y'` is parallel to the normal of the two
parallel faces.

Tools: Lemma 8.0 / Corollary 8.0′ with either orientation of the shadow
(`isRupert_of_tilted_unimodal_σ`, by reversing the cycle), the unimodality of
the two 5-cycles of Lemma 9.11, and a four-vector identity for the tilt tests.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- `TiltSign` for the orientation `σ` (`σ = 1`: counterclockwise). -/
def TiltSignS (σ : ℝ) (a b u₀ v : ℝ³) : Prop :=
  0 < σ * det3 a b u₀ ∨ (det3 a b u₀ = 0 ∧ 0 < σ * det3 a b v)

theorem det3_rev_edge (A B W u : ℝ³) :
    det3 (A - B) (W - B) u = -det3 (B - A) (W - A) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem IsCyclicUnimodal.of_neg {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (h : IsCyclicUnimodal fun i => z (-i)) : IsCyclicUnimodal z := by
  classical
  obtain ⟨hinj, hcard⟩ := h
  refine ⟨fun i j hij => ?_, ?_⟩
  · have := @hinj (-i) (-j) (by simp only [neg_neg]; exact hij)
    simpa using this
  · rw [← hcard]
    refine Finset.card_bij (fun i _ => -i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      refine ⟨?_, ?_⟩
      · have e : -(-i - 1) = i + 1 := by ring
        rw [e, neg_neg]; exact hi.2
      · have e : -(-i + 1) = i - 1 := by ring
        rw [e, neg_neg]; exact hi.1
    · intro i _ j _ hij; simpa using hij
    · intro j hj
      refine ⟨-j, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨?_, ?_⟩
      · have e : -j - 1 = -(j + 1) := by ring
        rw [e]; exact hj.2
      · have e : -j + 1 = -(j - 1) := by ring
        rw [e]; exact hj.1

/-- **Corollary 8.0′ in either orientation** (with eventual `Q`). -/
theorem isRupert_of_tilted_unimodal_σ (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSignS σ (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → Q z → Q (fun i => c * z i))
    (hQe : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q fun i => ⟪x i, u₀ + ε • v⟫)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) : IsRupert V := by
  rcases hσ with rfl | rfl
  · refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk x hxV ?_ ?_ Q hQo hQs hQe hQu
    · intro i j hi hj; simpa [TiltSignS, TiltSign] using hcyc i j hi hj
    · intro y hy hyx i; simpa [TiltSignS, TiltSign] using hrest y hy hyx i
  · have key : ∀ i : ZMod k, ∀ w : ℝ³, ∀ u : ℝ³,
        det3 (x (-(i + 1)) - x (-i)) (w - x (-i)) u =
          -det3 (x (-(i + 1) + 1) - x (-(i + 1))) (w - x (-(i + 1))) u := by
      intro i w u
      have e : -(i + 1) + 1 = -i := by ring
      rw [e, det3_rev_edge]
    refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk (fun i => x (-i)) (fun i => hxV _) ?_ ?_
      (fun z => Q fun i => z (-i)) ?_ ?_ ?_ ?_
    · intro i j hi hj
      have h1 : -j ≠ -(i + 1) := by intro h; apply hj; simpa using congrArg Neg.neg h
      have h2 : -j ≠ -(i + 1) + 1 := by
        intro h; apply hi
        have : -(i + 1) + 1 = -i := by ring
        rw [this] at h; simpa using congrArg Neg.neg h
      have t := hcyc (-(i + 1)) (-j) h1 h2
      simp only [TiltSignS, neg_one_mul, neg_pos] at t
      simp only [TiltSign]
      rw [show i + 1 = i + 1 from rfl, key i (x (-j)) u₀, key i (x (-j)) v]
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
    · have hc : Continuous fun z : ZMod k → ℝ => fun i => z (-i) := by fun_prop
      exact hQo.preimage hc
    · intro z c hc hz; exact hQs _ c hc hz
    · simpa using hQe
    · intro z hz hQ
      have hinj : Function.Injective fun i => z (-i) := fun i j hij => by
        simpa using hz hij
      exact IsCyclicUnimodal.of_neg (hQu _ hinj hQ)

end SmallRupert

end
