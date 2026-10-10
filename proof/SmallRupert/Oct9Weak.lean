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

theorem isCyclicUnimodal_of_unique {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hinj : Function.Injective z) (m : ZMod k) (hm : z (m - 1) < z m ∧ z (m + 1) < z m)
    (ho : ∀ i, i ≠ m → ¬(z (i - 1) < z i ∧ z (i + 1) < z i)) : IsCyclicUnimodal z := by
  classical
  refine ⟨hinj, Finset.card_eq_one.mpr ⟨m, ?_⟩⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi; by_contra hne; exact ho i hne hi
  · rintro rfl; exact hm

theorem zmod5_table (i : ZMod 5) :
    (i = 0 ∧ i - 1 = 4 ∧ i + 1 = 1) ∨ (i = 1 ∧ i - 1 = 0 ∧ i + 1 = 2) ∨
    (i = 2 ∧ i - 1 = 1 ∧ i + 1 = 3) ∨ (i = 3 ∧ i - 1 = 2 ∧ i + 1 = 4) ∨
    (i = 4 ∧ i - 1 = 3 ∧ i + 1 = 0) := by
  revert i; decide

/-- The 5-cycle `(x, p, y', x', p')` of Lemma 9.11 (`b < c`, `e < d`, `a < max(b, e)`). -/
def Q5a (z : ZMod 5 → ℝ) : Prop := z 1 < z 2 ∧ z 4 < z 3 ∧ (z 0 < z 1 ∨ z 0 < z 4)

/-- The 5-cycle `(x, y, p, y', p')` of Lemma 9.11 (the tie with `ω < t₂`). -/
def Q5b (z : ZMod 5 → ℝ) : Prop := z 0 < z 1 ∧ z 2 < z 1 ∧ z 3 < z 2 ∧ z 4 < z 3

theorem isOpen_Q5a : IsOpen {z : ZMod 5 → ℝ | Q5a z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q5a, Set.setOf_and, Set.setOf_or]
  exact (hlt 1 2).inter ((hlt 4 3).inter ((hlt 0 1).union (hlt 0 4)))

theorem isOpen_Q5b : IsOpen {z : ZMod 5 → ℝ | Q5b z} := by
  have hlt : ∀ i j : ZMod 5, IsOpen {z : ZMod 5 → ℝ | z i < z j} := fun i j =>
    isOpen_lt (continuous_apply i) (continuous_apply j)
  simp only [Q5b, Set.setOf_and]
  exact (hlt 0 1).inter ((hlt 2 1).inter ((hlt 3 2).inter (hlt 4 3)))

theorem Q5a.mul {z : ZMod 5 → ℝ} (h : Q5a z) {c : ℝ} (hc : 0 < c) : Q5a fun i => c * z i := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp only; nlinarith, by simp only; nlinarith, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl (by simp only; nlinarith)
  · exact Or.inr (by simp only; nlinarith)

theorem Q5b.mul {z : ZMod 5 → ℝ} (h : Q5b z) {c : ℝ} (hc : 0 < c) : Q5b fun i => c * z i := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simp only; nlinarith, by simp only; nlinarith, by simp only; nlinarith,
    by simp only; nlinarith⟩

theorem Q5a.unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5a z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3⟩ := h
  have h23 : z 2 ≠ z 3 := hinj.ne (by decide)
  rcases lt_or_gt_of_ne h23 with h23 | h23
  · refine isCyclicUnimodal_of_unique hinj 3 ⟨by rw [show (3 - 1 : ZMod 5) = 2 from by decide]; exact h23, by rw [show (3 + 1 : ZMod 5) = 4 from by decide]; exact h2⟩ ?_
    intro i hi hc
    rcases zmod5_table i with ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ |
      ⟨rfl, e1, e2⟩ <;> rw [e1, e2] at hc
    · rcases h3 with h3 | h3 <;> linarith [hc.1, hc.2]
    · linarith [hc.2]
    · linarith [hc.2]
    · exact hi rfl
    · linarith [hc.1]
  · refine isCyclicUnimodal_of_unique hinj 2 ⟨by rw [show (2 - 1 : ZMod 5) = 1 from by decide]; exact h1, by rw [show (2 + 1 : ZMod 5) = 3 from by decide]; exact h23⟩ ?_
    intro i hi hc
    rcases zmod5_table i with ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ |
      ⟨rfl, e1, e2⟩ <;> rw [e1, e2] at hc
    · rcases h3 with h3 | h3 <;> linarith [hc.1, hc.2]
    · linarith [hc.2]
    · exact hi rfl
    · linarith [hc.1]
    · linarith [hc.1]

theorem Q5b.unimodal {z : ZMod 5 → ℝ} (hinj : Function.Injective z) (h : Q5b z) :
    IsCyclicUnimodal z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine isCyclicUnimodal_of_unique hinj 1 ⟨by rw [show (1 - 1 : ZMod 5) = 0 from by decide]; exact h1, by rw [show (1 + 1 : ZMod 5) = 2 from by decide]; exact h2⟩ ?_
  intro i hi hc
  rcases zmod5_table i with ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ | ⟨rfl, e1, e2⟩ |
    ⟨rfl, e1, e2⟩ <;> rw [e1, e2] at hc
  · linarith [hc.2]
  · exact hi rfl
  · linarith [hc.1]
  · linarith [hc.1]
  · linarith [hc.1]

/-- **The four-vector identity** behind the tilt tests in a face: if `e`, `w`
and `u` are coplanar and `⟪N, e⟫ = 0`, then
`⟪N, u⟫ * det3 e w v = ⟪N, w⟫ * det3 e u v`. -/
theorem det3_four (N e w u v : ℝ³) :
    ⟪N, u⟫ * det3 e w v = ⟪N, w⟫ * det3 e u v + det3 e w u * ⟪N, v⟫ - det3 w u v * ⟪N, e⟫ := by
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]; ring

end SmallRupert

end
