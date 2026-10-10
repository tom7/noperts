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

/-- `det3_pos_of_combo` with an orientation factor `σ`. -/
theorem det3_pos_of_combo_σ {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³} {σ : ℝ}
    (hr : 0 < σ * det3 (Q - P) (r - P) u) (hgr : α * f₁ r + β * f₂ r < 0)
    (hgw : α * f₁ w + β * f₂ w < 0) : 0 < σ * det3 (Q - P) (w - P) u := by
  set N := α • N₁ + β • N₂
  have hg : ∀ z, ⟪N, z - P⟫ = α * f₁ z + β * f₂ z := by
    intro z
    simp only [N, inner_add_left, real_inner_smul_left, ← h₁, ← h₂, h1P, h2P, sub_zero]
  have hNe : ⟪N, Q - P⟫ = 0 := by rw [hg, h1Q, h2Q]; ring
  have hNu : ⟪N, u⟫ = 0 := by
    simp only [N, inner_add_left, real_inner_smul_left]; linarith
  have key := det3_mul_inner_eq (w := w - P) (w' := r - P) hNe hNu
  rw [hg, hg] at key
  have key' : (σ * det3 (Q - P) (w - P) u) * (α * f₁ r + β * f₂ r) =
      (σ * det3 (Q - P) (r - P) u) * (α * f₁ w + β * f₂ w) := by
    rw [mul_assoc, key]; ring
  nlinarith

/-- A facet `G` through `P`, `Q`, `R` containing the view direction `u`. -/
theorem vert_face_pos_σ {V : Finset ℝ³} {P Q R : ℝ³} (G : FacetFn V P Q R) {u : ℝ³}
    (hu : ⟪G.N, u⟫ = 0) {σ : ℝ} {r w : ℝ³}
    (hr : r ∈ V) (hrP : r ≠ P) (hrQ : r ≠ Q) (hrR : r ≠ R) (hw : w ∈ V) (hwP : w ≠ P)
    (hwQ : w ≠ Q) (hwR : w ≠ R) (href : 0 < σ * det3 (Q - P) (r - P) u) :
    0 < σ * det3 (Q - P) (w - P) u :=
  det3_pos_of_combo_σ G.hN G.hN G.hP G.hQ G.hP G.hQ (α := 1) (β := 0) (by rw [hu]; ring) href
    (by have := G.neg r hr hrP hrQ hrR; linarith) (by have := G.neg w hw hwP hwQ hwR; linarith)

/-- A far edge `PQ` between a lower facet `x Q P` and an upper facet `x' Q P`. -/
theorem far_edge_pos_σ {V : Finset ℝ³} {x x' y P Q : ℝ³} (G : FacetFn V x Q P)
    (H : FacetFn V x' Q P) (hx : x ∈ V) (hx' : x' ∈ V) (hxx' : x ≠ x') (hxP : x ≠ P)
    (hxQ : x ≠ Q) (hx'P : x' ≠ P) (hx'Q : x' ≠ Q) (hGy : G.f y < 0) (hq : H.f x < H.f y)
    {σ : ℝ} {r w : ℝ³} (hr : r ∈ V) (hrP : r ≠ P) (hrQ : r ≠ Q) (hw : w ∈ V) (hwP : w ≠ P)
    (hwQ : w ≠ Q) (href : 0 < σ * det3 (Q - P) (r - P) (y - x)) :
    0 < σ * det3 (Q - P) (w - P) (y - x) := by
  have key : ∀ z ∈ V, z ≠ P → z ≠ Q →
      (H.f y - H.f x) * G.f z + (-(G.f y - G.f x)) * H.f z < 0 := by
    intro z hz hzP hzQ
    have hα : 0 < H.f y - H.f x := by linarith
    have hβ : 0 < -(G.f y - G.f x) := by rw [G.hP]; linarith
    by_cases hzx : z = x
    · subst hzx; rw [G.hP]; nlinarith [H.neg z hz hxx' hzQ hzP]
    by_cases hzx' : z = x'
    · subst hzx'; rw [H.hP]; nlinarith [G.neg z hz (Ne.symm hxx') hzQ hzP]
    nlinarith [G.neg z hz hzx hzQ hzP, H.neg z hz hzx' hzQ hzP]
  refine det3_pos_of_combo_σ G.hN H.hN G.hR G.hQ H.hR H.hQ ?_ href (key r hr hrP hrQ)
    (key w hw hwP hwQ)
  rw [← G.hN, ← H.hN]; ring

/-- The determinant tests at the edge view of a *weak* quad edge `x → y`
(the face `x' y' p'` contains `u = y - x`), with orientation `σ`. -/
theorem weak_edge_tests {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hT : F.a'b'c'.f x = F.a'b'c'.f y) {σ : ℝ}
    (hor : 0 < σ * det3 (p - y) (p' - y) (y - x)) :
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y → w ≠ p → w ≠ x →
      0 < σ * det3 (p - y) (w - y) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p → w ≠ y' →
      0 < σ * det3 (y' - p) (w - p) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y' → w ≠ p' → w ≠ x' →
      0 < σ * det3 (p' - y') (w - y') (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p' → w ≠ y → w ≠ x →
      0 < σ * det3 (y - p') (w - p') (y - x)) := by
  set V : Finset ℝ³ := {x, x', y, y', p, p'}
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have hBu : ⟪F.abc.N, y - x⟫ = 0 := by rw [← F.abc.hN, F.abc.hP, F.abc.hQ]; ring
  have hB'u : ⟪F.abc'.N, y - x⟫ = 0 := by rw [← F.abc'.hN, F.abc'.hP, F.abc'.hQ]; ring
  have hTu : ⟪F.a'b'c'.N, y - x⟫ = 0 := by rw [← F.a'b'c'.hN, hT]; ring
  have E1 : ∀ w ∈ V, w ≠ y → w ≠ p → w ≠ x → 0 < σ * det3 (p - y) (w - y) (y - x) :=
    fun w hw hwy hwp hwx => vert_face_pos_σ F.abc.p12.p23 hBu mp' (Ne.symm hyp')
      (Ne.symm hpp') (Ne.symm hxp') hw hwy hwp hwx hor
  have E2 : ∀ w ∈ V, w ≠ p → w ≠ y' → 0 < σ * det3 (y' - p) (w - p) (y - x) :=
    fun w hw hwp hwy' => far_edge_pos_σ F.ab'c F.a'b'c mx mx' hxx' hxp hxy' hx'p hx'y'
      (F.ab'c.neg y my (Ne.symm hxy) hyy' hyp) hq₁ my hyp hyy' hw hwp hwy'
      (by rw [det3_cyc y p y']; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy'))
  have E3 : ∀ w ∈ V, w ≠ y' → w ≠ p' → w ≠ x' → 0 < σ * det3 (p' - y') (w - y') (y - x) :=
    fun w hw hwy' hwp' hwx' => vert_face_pos_σ F.a'b'c'.p12.p23 hTu mp (Ne.symm hy'p) hpp'
      (Ne.symm hx'p) hw hwy' hwp' hwx'
      (by rw [det3_cyc p y' p']; exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p'))
  have E4 : ∀ w ∈ V, w ≠ p' → w ≠ y → w ≠ x → 0 < σ * det3 (y - p') (w - p') (y - x) :=
    fun w hw hwp' hwy hwx => vert_face_pos_σ F.abc'.p23.p12.p23 hB'u mp hpp' (Ne.symm hyp)
      (Ne.symm hxp) hw hwp' hwy hwx (by rw [← det3_cyc p' y p]; exact hor)
  exact ⟨E1, E2, E3, E4⟩

end SmallRupert

end
