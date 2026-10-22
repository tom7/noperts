module

public import Minimality.RimCert

@[expose] public section

/-!
# Rim certificates from the crossing tests (`FEWER-FACES-PROOFS.md` §18.2)

The certificate forms (`RimCertPts`, `RimCert`; no horizontal double normal) of the crossing
tests used by the tier proofs of type 21: Theorem 8.9 and Proposition 8.8 at views given by
determinant tests (`rimCertPts_of_edgeView_robust`, `rimCertPts_of_vertexView_robust`,
`rimCertPts_of_edgeView_uniform_robust`), the quad lift of Lemma 9.3 with ties
(`rimCert_quad_edge_lift_tie`), and Corollary 14.1 with the uniform tilt and ties
(`rimCert_edgePair_uniform_robust`).

`CertV K L E`: a rim certificate of `K` at a segment view `w − v` with `E v w` (an edge of the
type) or at a view satisfying `L` (the named vertex crossings of the type).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **A certificate at a named view**: a rim certificate (3, 4 or 5 corners) of `K` at the view
along a segment `w − v` of `K` with `E v w` (the edges of the type), or at a view satisfying `L`. -/
def CertV (K : Finset ℝ³) (L : ℝ³ → Prop) (E : ℝ³ → ℝ³ → Prop) : Prop :=
  ∃ u, (L u ∨ ∃ v ∈ K, ∃ w ∈ K, v ≠ w ∧ E v w ∧ u = w - v) ∧ RimCert K u

theorem CertV.seg {K : Finset ℝ³} {L : ℝ³ → Prop} {E : ℝ³ → ℝ³ → Prop} {v w : ℝ³} (hv : v ∈ K)
    (hw : w ∈ K) (hvw : v ≠ w) (hE : E v w) (h : RimCert K (w - v)) : CertV K L E :=
  ⟨w - v, Or.inr ⟨v, hv, w, hw, hvw, hE, rfl⟩, h⟩

theorem CertV.line {K : Finset ℝ³} {L : ℝ³ → Prop} {E : ℝ³ → ℝ³ → Prop} {u : ℝ³} (hL : L u)
    (h : RimCert K u) : CertV K L E :=
  ⟨u, Or.inl hL, h⟩

theorem CertV.mono {K : Finset ℝ³} {L L' : ℝ³ → Prop} {E : ℝ³ → ℝ³ → Prop} (h : CertV K L E)
    (hL : ∀ u, L u → L' u) : CertV K L' E := by
  obtain ⟨u, hu, hc⟩ := h
  exact ⟨u, hu.imp_left (hL u), hc⟩

/-- Changing the edge predicate. -/
theorem CertV.monoE {K : Finset ℝ³} {L : ℝ³ → Prop} {E E' : ℝ³ → ℝ³ → Prop} (h : CertV K L E)
    (hE : ∀ v w, E v w → E' v w) : CertV K L E' := by
  obtain ⟨u, hu, hc⟩ := h
  refine ⟨u, hu.imp_right ?_, hc⟩
  rintro ⟨v, hv, w, hw, hvw, he, rfl⟩
  exact ⟨v, hv, w, hw, hvw, hE v w he, rfl⟩

/-- A rim certificate at the reversed segment view. -/
theorem CertV.seg' {K : Finset ℝ³} {L : ℝ³ → Prop} {E : ℝ³ → ℝ³ → Prop} {v w : ℝ³} (hv : v ∈ K)
    (hw : w ∈ K) (hvw : v ≠ w) (hE : E w v) (h : RimCert K (v - w)) : CertV K L E :=
  CertV.seg hw hv (Ne.symm hvw) hE h

/-- A rim certificate at `±(w − v)`. -/
theorem CertV.seg_sigma {K : Finset ℝ³} {L : ℝ³ → Prop} {E : ℝ³ → ℝ³ → Prop} {v w : ℝ³} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hv : v ∈ K) (hw : w ∈ K) (hvw : v ≠ w) (hE : E v w ∧ E w v)
    (h : RimCert K (σ • (w - v))) : CertV K L E := by
  rcases hσ with rfl | rfl
  · rw [one_smul] at h; exact CertV.seg hv hw hvw hE.1 h
  · rw [neg_one_smul, neg_sub] at h; exact CertV.seg hw hv (Ne.symm hvw) hE.2 h

/-! ### Theorem 8.9 and Proposition 8.8 at views given by determinant tests -/

/-- **`isRupert_of_edgeView_robust` in certificate form.** -/
theorem rimCertPts_of_edgeView_robust (V M : Finset ℝ³) (u₀ : ℝ³) (_hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (_hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (_hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (_hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ≠ w → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫))
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) :
    RimCertPts V u₀ x := by
  classical
  refine rimCertPts_of_class V u₀ hk x hxV hcyc (fun z hz => ?_) hz
  by_cases hc : ∃ j, z = x j
  · obtain ⟨j, rfl⟩ := hc
    exact Or.inl (class_corner j)
  push Not at hc
  by_cases hzw : z = w
  · exact Or.inl (class_double i₀ (-h) (by rw [hzw, hw]; module))
  by_cases hzM : z ∈ M
  · left
    obtain ⟨c, s, δ, hc', hs0, hs1, -, hm⟩ := hM z hzM
    obtain ⟨t, ht⟩ : ∃ t : ℝ, c = x i₀ + t • u₀ := by
      rcases hc' with rfl | ⟨rfl, -⟩
      · exact ⟨0, by simp⟩
      · exact ⟨-h, by rw [hw]; module⟩
    rcases hm with hm | hm
    · exact class_middle i₀ (i₀ + 1) t 0 s δ hs0.le hs1.le (by rw [hm, ht]; module)
    · exact class_middle (i₀ - 1) i₀ 0 t s δ hs0.le hs1.le (by rw [hm, ht]; module)
  · exact Or.inr (hrest z hz hzM hzw hc)

/-- **`isRupert_of_vertexView_robust` in certificate form.** -/
theorem rimCertPts_of_vertexView_robust (V M : Finset ℝ³) (u₀ : ℝ³) (_hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (_hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : RimCertPts V u₀ x := by
  classical
  refine rimCertPts_of_class V u₀ hk x hxV hcyc (fun z hz => ?_) hz
  by_cases hc : ∃ j, z = x j
  · obtain ⟨j, rfl⟩ := hc
    exact Or.inl (class_corner j)
  push Not at hc
  by_cases hzM : z ∈ M
  · obtain ⟨i, s, δ, hs0, hs1, -, hm⟩ := hM z hzM
    exact Or.inl ⟨i, i + 1, s, δ, hs0.le, hs1.le, hm⟩
  · exact Or.inr (hrest z hz hzM hc)

/-- **`isRupert_of_edgeView_uniform_robust` in certificate form.** -/
theorem rimCertPts_of_edgeView_uniform_robust (V M D W : Finset ℝ³) (u₀ : ℝ³) (_hu₀ : u₀ ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (_hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ∉ D → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫)) (_hxW : ∀ i, x i ∈ W)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀) : RimCertPts V u₀ x := by
  classical
  refine rimCertPts_of_class V u₀ hk x hxV hcyc (fun z hz => ?_) hz
  by_cases hc : ∃ j, z = x j
  · obtain ⟨j, rfl⟩ := hc
    exact Or.inl (class_corner j)
  push Not at hc
  by_cases hzM : z ∈ M
  · obtain ⟨i, s, δ, hs0, hs1, -, hm⟩ := hM z hzM
    exact Or.inl ⟨i, i + 1, s, δ, hs0.le, hs1.le, hm⟩
  by_cases hzD : z ∈ D
  · obtain ⟨i, h, -, hy⟩ := hD z hzD
    exact Or.inl (class_double i (-h) (by rw [hy]; module))
  · exact Or.inr (hrest z hz hzM hzD hc)

/-- A 4-corner certificate is a rim certificate. -/
theorem RimCertPts.rimCert4 {V : Finset ℝ³} {u : ℝ³} {y : ZMod 4 → ℝ³} (h : RimCertPts V u y) :
    RimCert V u := h.rimCert (by norm_num)

theorem RimCertPts.rimCert3 {V : Finset ℝ³} {u : ℝ³} {y : ZMod 3 → ℝ³} (h : RimCertPts V u y) :
    RimCert V u := h.rimCert (by norm_num)

theorem RimCertPts.rimCert5 {V : Finset ℝ³} {u : ℝ³} {y : ZMod 5 → ℝ³} (h : RimCertPts V u y) :
    RimCert V u := h.rimCert (by norm_num)

/-! ### The quad lift and the uniform edge pair -/

/-- **Lemma 9.3 with ties, oriented core, certificate form**. -/
theorem rimCertPts_quad_edge_lift_core_tie {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (M : Finset ℝ³) (hMm : M ⊆ {m}) (hmid : m ∈ M → QuadMiddle x y p p' m)
    (hhid : m ∉ M → QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    (NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) ∧
        RimCertPts (insert m {x, x', y, y', p, p'}) (y - x) (quad y p y' p')) ∨
      (NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) ∧
        RimCertPts (insert m {x, x', y, y', p, p'}) (y - x) (quad x p y' p')) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd'
  obtain ⟨hmx, hmx', hmy, hmy', hmp, hmp'⟩ := hmO
  set V : Finset ℝ³ := insert m {x, x', y, y', p, p'} with hV
  have mx : x ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mx' : x' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my : y ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp : p ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have mp' : p' ∈ ({x, x', y, y', p, p'} : Finset ℝ³) := by simp
  have hmemV : ∀ z ∈ V, z = m ∨ z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  have hnotM : ∀ z, z ≠ m → z ∉ M := fun z hz hzM => hz (mem_singleton.mp (hMm hzM))
  have hu : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  -- the middle, for either choice of `v`
  have hEM : ∀ v w : ℝ³, ∀ hh : ℝ, ((v = y ∧ w = x ∧ hh = 1) ∨ (v = x ∧ w = y ∧ hh = -1)) →
      ∀ m' ∈ M, EdgeMiddle (y - x) v w p p' hh m' := by
    intro v w hh hvw m' hm'
    have hm'm : m' = m := mem_singleton.mp (hMm hm')
    subst hm'm
    obtain ⟨s, δ, hs0, hs1, hδ, hδ', hm⟩ := hmid hm'
    rcases hvw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases hm with hm | hm
      · exact ⟨v, s, δ, Or.inl rfl, hs0, hs1, hδ, Or.inl hm⟩
      · refine ⟨v, 1 - s, δ, Or.inl rfl, by linarith, by linarith, hδ, Or.inr ?_⟩
        rw [hm]; module
    · rcases hm with hm | hm
      · refine ⟨v, s, δ + 1 - s, Or.inl rfl, hs0, hs1, hδ', Or.inl ?_⟩
        rw [hm]; module
      · refine ⟨v, 1 - s, δ + 1 - s, Or.inl rfl, by linarith, by linarith, hδ', Or.inr ?_⟩
        rw [hm]; module
  -- the hidden point passes the edge tests
  have hH : m ∉ M → 0 < det3 (p - y) (m - y) (y - x) ∧ 0 < det3 (y' - p) (m - p) (y - x) ∧
      0 < det3 (p' - y') (m - y') (y - x) ∧ 0 < det3 (y - p') (m - p') (y - x) := by
    intro hmM
    obtain ⟨h1, h2, h3, h4⟩ := hhid hmM
    exact ⟨pos_of_mul_pos_pos (by rwa [mul_comm] at h1) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h2) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h3) hor,
      pos_of_mul_pos_pos (by rwa [mul_comm] at h4) hor⟩
  by_cases hN : NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫)
  · -- `K_y` is unimodal
    refine Or.inl ⟨hN, rimCertPts_of_edgeView_robust V M (y - x) hu (k := 4) (by norm_num)
      (quad y p y' p') 0 x 1 (by simp [V]) (by simp only [quad_0, one_smul]; abel) one_ne_zero ?_
      ?_ ?_ ?_ ?_ ?_⟩
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3]
      exacts [hnotM y (Ne.symm hmy), hnotM p (Ne.symm hmp), hnotM y' (Ne.symm hmy'),
        hnotM p' (Ne.symm hmp')]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 y my hyp hyy'
      · exact E3 y my hyy' hyp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · rw [h] at hzM ⊢
        obtain ⟨t1, t2, t3, t4⟩ := hH hzM
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        exacts [t1, t2, t3, t4]
      · exact absurd h hzw
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h h0
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact hN.isRobustUnimodal
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM y x 1 (Or.inl ⟨rfl, rfl, rfl⟩)
  · -- `K_x` is unimodal (the closing by `x` of Lemma 9.3)
    have hS₁ := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) (y - x) := by
      rw [← det3_cyc x y' p']; exact E3 x mx hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) (y - x) := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) (y - x) := by
      rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    have hN' := nws4_closing_x_tie hS₁ hS₂ hS₃ hS₄ (quad_edge_lower F hS₁ hS₂ hS₃ hS₄) hN hgood
      htouch
    refine Or.inr ⟨hN', rimCertPts_of_edgeView_robust V M (y - x) hu (k := 4) (by norm_num)
      (quad x p y' p') 0 y (-1) (by simp [V])
      (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add]; abel) (by norm_num) ?_ ?_ ?_ ?_
      ?_ ?_⟩
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [quad_0, quad_1, quad_2, quad_3]
      exacts [hnotM x (Ne.symm hmx), hnotM p (Ne.symm hmp), hnotM y' (Ne.symm hmy'),
        hnotM p' (Ne.symm hmp')]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 x mx hxp hxy'
      · exact E3 x mx hxy' hxp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzM hzw hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hmemV z hz with h | h | h | h | h | h | h
      · rw [h] at hzM ⊢
        obtain ⟨t1, t2, t3, t4⟩ := hH hzM
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact t1
        · exact t2
        · exact t3
        · rw [det3_shift_p']; exact t4
      · exact absurd h h0
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h hzw
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · rw [quad_inner]; exact hN'.isRobustUnimodal
    · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
      exact hEM x y (-1) (Or.inr ⟨rfl, rfl, rfl⟩)

theorem rimCert_quad_edge_lift_core_tie {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (M : Finset ℝ³) (hMm : M ⊆ {m}) (hmid : m ∈ M → QuadMiddle x y p p' m)
    (hhid : m ∉ M → QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    RimCert (insert m {x, x', y, y', p, p'}) (y - x) := by
  rcases rimCertPts_quad_edge_lift_core_tie F hq₁ hq₂ hor hgood M hMm hmid hhid hmO htouch with
    ⟨-, h⟩ | ⟨-, h⟩
  exacts [h.rimCert4, h.rimCert4]

/-- **Lemma 2 of §12 with ties, labelled certificate form**: the rim at the view along `x y` is
`(y, q, y', q')` (`K_y`, without weak saddle) or `(x, q, y', q')` (`K_x`), with `{q, q'} = {p, p'}`
in the counterclockwise order. -/
theorem rimCertPts_quad_edge_lift_tie {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hm : QuadMiddle x y p p' m ∨ QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    ∃ q q' : ℝ³, ((q = p ∧ q' = p') ∨ (q = p' ∧ q' = p)) ∧
      ((NWS4 (quad ⟪y, y - x⟫ ⟪q, y - x⟫ ⟪y', y - x⟫ ⟪q', y - x⟫) ∧
          RimCertPts (insert m {x, x', y, y', p, p'}) (y - x) (quad y q y' q')) ∨
        (NWS4 (quad ⟪x, y - x⟫ ⟪q, y - x⟫ ⟪y', y - x⟫ ⟪q', y - x⟫) ∧
          RimCertPts (insert m {x, x', y, y', p, p'}) (y - x) (quad x q y' q'))) := by
  classical
  -- the set `M` of middles
  obtain ⟨M, hMm, hmid, hhid⟩ : ∃ M : Finset ℝ³, M ⊆ {m} ∧ (m ∈ M → QuadMiddle x y p p' m) ∧
      (m ∉ M → QuadHidden x y y' p p' m) := by
    rcases hm with h | h
    · exact ⟨{m}, subset_rfl, fun _ => h, fun h' => absurd (mem_singleton_self m) h'⟩
    · exact ⟨∅, empty_subset _, fun h' => absurd h' (notMem_empty m), fun _ => h⟩
  have e : (insert m {x, x', y, y', p', p} : Finset ℝ³) = insert m {x, x', y, y', p, p'} := by
    rw [Finset.pair_comm p' p]
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have := rimCertPts_quad_edge_lift_core_tie F.swap₃ hq₂ hq₁ (by rw [det3_swap12]; linarith)
      (by rwa [min_comm]) M hMm (fun h => (hmid h).swap) (fun h => (hhid h).swap)
      ⟨hmO.1, hmO.2.1, hmO.2.2.1, hmO.2.2.2.1, hmO.2.2.2.2.2, hmO.2.2.2.2.1⟩
      (fun h => htouch ⟨h.2, h.1⟩)
    rw [e] at this
    exact ⟨p', p, Or.inr ⟨rfl, rfl⟩, this⟩
  · exact ⟨p, p', Or.inl ⟨rfl, rfl⟩,
      rimCertPts_quad_edge_lift_core_tie F hq₁ hq₂ hpos hgood M hMm hmid hhid hmO htouch⟩

/-- **Lemma 2 of §12 with ties, certificate form** (`isRupert_quad_edge_lift_tie` without the
horizontal double normal): a rim certificate at the view along `x y`. -/
theorem rimCert_quad_edge_lift_tie {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hm : QuadMiddle x y p p' m ∨ QuadHidden x y y' p p' m)
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫)) :
    RimCert (insert m {x, x', y, y', p, p'}) (y - x) := by
  obtain ⟨q, q', -, h | h⟩ := rimCertPts_quad_edge_lift_tie F hq₁ hq₂ hgood hm hmO htouch
  exacts [h.2.rimCert4, h.2.rimCert4]

/-- **`isRupert_quad_uniform_nws` in certificate form.** -/
theorem rimCert_quad_uniform_nws (V M : Finset ℝ³) {u y o a b c : ℝ³} {h : ℝ} (hh : h ≠ 0)
    (ho : o = y - h • u) (hu : u ≠ 0) (hyV : y ∈ V) (haV : a ∈ V) (hbV : b ∈ V)
    (hcV : c ∈ V) (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ o → z ≠ y → z ≠ a → z ≠ c → z ≠ b → EdgeHidden u y a c b z)
    (hN : NWS4 (quad ⟪y, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hM : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad y a c b i + s • (quad y a c b (i + 1) - quad y a c b i) + δ • u) :
    RimCert V u := by
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the corners are not the other axle end
  have hoy : y ≠ o := by
    intro e
    have h2 : y - h • u = y := by rw [ho] at e; exact e.symm
    have : h • u = 0 := by
      calc h • u = y - (y - h • u) := by abel
        _ = 0 := by rw [h2, sub_self]
    exact (smul_ne_zero hh hu) this
  have hoa : a ≠ o := by
    intro e
    have : det3 (a - y) (c - y) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  have hoc : c ≠ o := by
    intro e
    have : det3 (b - c) (y - c) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  have hob : b ≠ o := by
    intro e
    have : det3 (y - b) (a - b) u = 0 := by
      rw [e, ho]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    linarith
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine (rimCertPts_of_edgeView_uniform_robust V M {o} (V.erase o) u hu (k := 4) (by norm_num)
    (quad y a c b) ?_ ?_ ?_ ?_ ?_ ?_ hM ?_).rimCert4
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, haV, hcV, hbV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, haM, hcM, hbM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [q₁, by rw [i2]; exact q₄, q₂, by rw [i4]; exact q₁, q₃, by rw [i6]; exact q₂, q₄,
      by rw [i8]; exact q₃]
  · intro z hz hzM hzD hzx i
    have hzo : z ≠ o := fun e => hzD (by rw [e]; exact mem_singleton_self o)
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzo (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]; exact hN.isRobustUnimodal
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, mem_erase]
    exacts [⟨hoy, hyV⟩, ⟨hoa, haV⟩, ⟨hoc, hcV⟩, ⟨hob, hbV⟩]
  · intro z hz
    rw [mem_singleton.mp hz]
    exact ⟨0, h, hh, by rw [quad_0]; exact ho⟩

/-- **Corollary 14.1 with the uniform tilt and ties, certificate form**
(`isRupert_edgePair_uniform_robust` without the horizontal double normal). -/
theorem rimCert_edgePair_uniform_robust {v w a b c : ℝ³} (V M : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hvM : v ∉ M) (hwM : w ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z ∉ M → z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨
      EdgeHidden (w - v) v a c b z)
    (hM₁ : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad v a c b i + s • (quad v a c b (i + 1) - quad v a c b i) + δ • (w - v))
    (hM₂ : ∀ m ∈ M, ∃ i : ZMod 4, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = quad w a c b i + s • (quad w a c b (i + 1) - quad w a c b i) + δ • (w - v)) :
    RimCert V (w - v) := by
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at q₁; simp only [det3, inner_zero_right, lt_irrefl] at q₁
  rcases edgePair_nws q₁ q₂ q₃ q₄ hE h3 with hN | hN
  · -- `K_v`
    refine rimCert_quad_uniform_nws V M (y := v) (o := w) (h := -1) (by norm_num)
      (by rw [neg_one_smul, sub_neg_eq_add]; abel) hu hvV haV hbV hcV hvM haM hbM hcM q₁ q₂
      q₃ q₄ ?_ hN hM₁
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz hzM with e | e | e | e | e | hid
    · exact absurd e h2
    · exact absurd e h1
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact hid
  · -- `K_w`
    refine rimCert_quad_uniform_nws V M (y := w) (o := v) (h := 1) one_ne_zero
      (by rw [one_smul]; abel) hu hwV haV hbV hcV hwM haM hbM hcM
      (by rw [det3_vw_both]; exact q₁) q₂ (by rw [det3_vw_right]; exact q₃)
      (by rw [det3_vw_left]; exact q₄) ?_ hN hM₂
    intro z hz hzM h1 h2 h3 h4 h5
    rcases hV z hz hzM with e | e | e | e | e | hid
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact hid.shift

/-! ### The vertex crossing of Theorem 13.7 -/

theorem quad_mul_sigma (σ z₀ z₁ z₂ z₃ : ℝ) :
    quad (σ * z₀) (σ * z₁) (σ * z₂) (σ * z₃) = fun i => σ * quad z₀ z₁ z₂ z₃ i := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

/-- **The vertex crossing at `a'`, labelled certificate form**: the triangle rim `a' b b'` if
`a` is on the inner side of `b b'`, the quadrilateral `a' b a b'` if its depths are robustly
unimodal, as point certificates (`RimCertPts`) at `σ u`. -/
theorem rimCertPts_axisTest_core_gen {a a' b b' u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < σ * det3 (b - a') (b' - a') u) (hΓ : 0 < σ * det3 (b - a') (a - a') u)
    (hB : 0 < σ * det3 (a - a') (b' - a') u)
    (htri : ¬ (⟪a', u⟫ = ⟪b, u⟫ ∧ ⟪b, u⟫ = ⟪b', u⟫))
    (V : Finset ℝ³) (ha : a ∈ V) (ha' : a' ∈ V) (hb : b ∈ V) (hb' : b' ∈ V)
    (hV : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v) :
    (0 < σ * det3 (b' - b) (a - b) u → RimCertPts V (σ • u) (tri a' b b')) ∧
    (σ * det3 (b' - b) (a - b) u < 0 →
      IsRobustUnimodal (quad ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫) →
        RimCertPts V (σ • u) (quad a' b a b')) := by
  classical
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσσ
  have hu0 : u ≠ 0 := by rintro rfl; simp [det3] at hT
  have hw0 : σ • u ≠ 0 := smul_ne_zero hσ0 hu0
  have hdw : ∀ x y, det3 x y (σ • u) = σ * det3 x y u := fun x y => by
    simp only [det3, real_inner_smul_right]
  have hiw : ∀ x, ⟪x, σ • u⟫ = σ * ⟪x, u⟫ := fun x => real_inner_smul_right _ _ _
  have i1 : det3 (b' - b) (a' - b) u = det3 (b - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (a' - b') (b - b') u = det3 (b - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i3 : det3 (a' - b') (a - b') u = det3 (a - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (a - b) (a' - b) u = det3 (b - a') (a - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i5 : det3 (a - b) (b' - b) u = -det3 (b' - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b' - a) (a' - a) u = det3 (a - a') (b' - a') u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i7 : det3 (b' - a) (b - a) u = -det3 (b' - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  -- the corners are not middles
  have nmid : ∀ y, ApexMid a' b b' u y → y ≠ a ∧ y ≠ a' ∧ y ≠ b ∧ y ≠ b' := by
    intro y hy
    have hsT : ∀ s : ℝ, 0 < s → s < 1 → 0 < s * (σ * det3 (b - a') (b' - a') u) ∧
        0 < (1 - s) * (σ * det3 (b - a') (b' - a') u) :=
      fun s h0 h1 => ⟨mul_pos h0 hT, mul_pos (by linarith) hT⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> rw [e] at hy <;>
      rcases apexMid_sides hy with ⟨h1, s, hs0, hs1, h2⟩ | ⟨h1, s, hs0, hs1, h2⟩ <;>
      (try simp only [sub_self, det3_zero_mid, det3_zero_left', det3_self_left] at h1 h2) <;>
      obtain ⟨t1, t2⟩ := hsT s hs0 hs1 <;>
      first
        | nlinarith [congrArg (σ * ·) h1, congrArg (σ * ·) h2]
        | nlinarith [congrArg (σ * ·) h2]
  set M := V.filter (ApexMid a' b b' u) with hM
  refine ⟨fun hα => ?_, fun hα hsep => ?_⟩
  · -- the rim is the triangle `a' b b'`
    obtain ⟨b0, b1, b2⟩ := zmod3_add_one
    refine (rimCertPts_of_vertexView_robust V M (σ • u) hw0 (k := 3) le_rfl (tri a' b b') ?_ ?_
      ?_ ?_ ?_ ?_)
    · intro i; rcases zmod3_cases i with rfl | rfl | rfl
      exacts [ha', hb, hb']
    · intro i hi
      obtain ⟨-, hmid⟩ := mem_filter.mp hi
      rcases zmod3_cases i with rfl | rfl | rfl
      exacts [(nmid _ hmid).2.1 rfl, (nmid _ hmid).2.2.1 rfl, (nmid _ hmid).2.2.2 rfl]
    · intro i j hi hj
      rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw, i1, i2]
      exacts [hT, hT, hT]
    · intro y hy hyM hyx i
      have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2
      simp only [tri_0, tri_1, tri_2] at h0 h1 h2
      rcases hV y hy with e | e | e | e | hext
      · rw [e]
        rcases zmod3_cases i with rfl | rfl | rfl <;>
          simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw, i3]
        exacts [hΓ, hα, hB]
      · exact absurd e h0
      · exact absurd e h1
      · exact absurd e h2
      · rcases hext with ⟨w₁, w₂, w₃, w₄, μ, p1, p2, p3, p4, hsum, rfl⟩ | hmid
        · rcases zmod3_cases i with rfl | rfl | rfl <;>
            simp only [b0, b1, b2, tri_0, tri_1, tri_2, hdw] <;>
            rw [det3_hidden _ _ _ _ _ _ _ hsum] <;>
            simp only [sub_self, det3_zero_mid, det3_self_left, i1, i2, i3]
          · nlinarith [mul_pos p1 hΓ, mul_pos p4 hT]
          · nlinarith [mul_pos p1 hα, mul_pos p2 hT]
          · nlinarith [mul_pos p1 hB, mul_pos p3 hT]
        · exact absurd (mem_filter.mpr ⟨hy, hmid⟩) hyM
    · rw [tri_inner]
      simp only [hiw]
      exact tri_robust_smul hσ0 htri
    · intro m hm
      obtain ⟨-, hmid⟩ := mem_filter.mp hm
      rcases hmid with ⟨s, δ, hs0, hs1, hδ, rfl⟩ | ⟨s, δ, hs0, hs1, hδ, rfl⟩
      · exact ⟨0, s, σ * δ, hs0, hs1, mul_ne_zero hσ0 hδ, by
          simp only [b0, tri_0, tri_1]; exact mid_view hσσ⟩
      · exact ⟨2, 1 - s, σ * δ, by linarith, by linarith, mul_ne_zero hσ0 hδ, by
          simp only [b2, tri_0, tri_2]; exact mid_view' hσσ⟩
  · -- the rim is the quadrilateral `a' b a b'`
    obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
    have hα' : 0 < σ * -det3 (b' - b) (a - b) u := by linarith
    refine (rimCertPts_of_vertexView_robust V M (σ • u) hw0 (k := 4) (by norm_num)
      (quad a' b a b') ?_ ?_ ?_ ?_ ?_ ?_)
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [ha', hb, ha, hb']
    · intro i hi
      obtain ⟨-, hmid⟩ := mem_filter.mp hi
      rcases zmod4_cases i with rfl | rfl | rfl | rfl
      exacts [(nmid _ hmid).2.1 rfl, (nmid _ hmid).2.2.1 rfl, (nmid _ hmid).1 rfl,
        (nmid _ hmid).2.2.2 rfl]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hdw, i2, i3, i4, i5, i6, i7]
      exacts [hΓ, hT, hα', hΓ, hB, hα', hT, hB]
    · intro y hy hyM hyx i
      have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2; have h3 := hyx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      rcases hV y hy with e | e | e | e | hext
      · exact absurd e h2
      · exact absurd e h0
      · exact absurd e h1
      · exact absurd e h3
      · rcases hext with ⟨w₁, w₂, w₃, w₄, μ, p1, p2, p3, p4, hsum, rfl⟩ | hmid
        · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
            simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3, hdw] <;>
            rw [det3_hidden _ _ _ _ _ _ _ hsum] <;>
            simp only [sub_self, det3_zero_mid, det3_self_left, i2, i3, i4, i5, i6, i7]
          · nlinarith [mul_pos p1 hΓ, mul_pos p4 hT]
          · nlinarith [mul_pos p2 hΓ, mul_pos p4 hα']
          · nlinarith [mul_pos p2 hB, mul_pos p3 hα']
          · nlinarith [mul_pos p1 hB, mul_pos p3 hT]
        · exact absurd (mem_filter.mpr ⟨hy, hmid⟩) hyM
    · rw [quad_inner]
      simp only [hiw]
      rw [quad_mul_sigma]; exact hsep.sigma hσ
    · intro m hm
      obtain ⟨-, hmid⟩ := mem_filter.mp hm
      rcases hmid with ⟨s, δ, hs0, hs1, hδ, rfl⟩ | ⟨s, δ, hs0, hs1, hδ, rfl⟩
      · exact ⟨0, s, σ * δ, hs0, hs1, mul_ne_zero hσ0 hδ, by
          simp only [a0, quad_0, quad_1]; exact mid_view hσσ⟩
      · exact ⟨3, 1 - s, σ * δ, by linarith, by linarith, mul_ne_zero hσ0 hδ, by
          simp only [a3, quad_0, quad_3]; exact mid_view' hσσ⟩

/-- **The vertex crossing at `a'`, certificate form** (`isRupert_axisTest_core_robust` without the
horizontal double normal, with the robustness of the quadrilateral as a hypothesis): the
triangle rim `a' b b'` if `a` is on the inner side of `b b'`, the quadrilateral `a' b a b'` if
its depths are robustly unimodal; the certificate is at `σ u`. -/
theorem rimCert_axisTest_core_gen {a a' b b' u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < σ * det3 (b - a') (b' - a') u) (hΓ : 0 < σ * det3 (b - a') (a - a') u)
    (hB : 0 < σ * det3 (a - a') (b' - a') u)
    (htri : ¬ (⟪a', u⟫ = ⟪b, u⟫ ∧ ⟪b, u⟫ = ⟪b', u⟫))
    (V : Finset ℝ³) (ha : a ∈ V) (ha' : a' ∈ V) (hb : b ∈ V) (hb' : b' ∈ V)
    (hV : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v) :
    (0 < σ * det3 (b' - b) (a - b) u → RimCert V (σ • u)) ∧
    (σ * det3 (b' - b) (a - b) u < 0 →
      IsRobustUnimodal (quad ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫) → RimCert V (σ • u)) := by
  obtain ⟨K1, K2⟩ := rimCertPts_axisTest_core_gen hσ hT hΓ hB htri V ha ha' hb hb' hV
  exact ⟨fun h => (K1 h).rimCert3, fun h hr => (K2 h hr).rimCert4⟩

/-- **`isRupert_axisTest_core_robust` in certificate form** (the ties of `QuadTie`). -/
theorem rimCert_axisTest_core_robust {a a' b b' u : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hT : 0 < σ * det3 (b - a') (b' - a') u) (hΓ : 0 < σ * det3 (b - a') (a - a') u)
    (hB : 0 < σ * det3 (a - a') (b' - a') u)
    (hz : QuadTie ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫)
    (V : Finset ℝ³) (ha : a ∈ V) (ha' : a' ∈ V) (hb : b ∈ V) (hb' : b' ∈ V)
    (hV : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v) :
    (0 < σ * det3 (b' - b) (a - b) u → RimCert V (σ • u)) ∧
    (σ * det3 (b' - b) (a - b) u < 0 → ¬ DepthSep a' a b b' u → RimCert V (σ • u)) := by
  obtain ⟨K1, K2⟩ := rimCert_axisTest_core_gen hσ hT hΓ hB hz.2.1 V ha ha' hb hb' hV
  exact ⟨K1, fun hα hsep => K2 hα
    (isRobustUnimodal_quad hz (fun h => hsep (Or.inr h)) (fun h => hsep (Or.inl h)))⟩

/-- **One test of Theorem 13.7, labelled certificate form**: the point certificate of the
quadrilateral `a' b a b'` or the triangle `a' b b'` at `±u₁`, or the rim
is the quadrilateral `a' b a b'` with depths that are not robustly unimodal, and the projections
of `[a', a]` and `[b, b']`, and those of `[a', a]` and `[c, c']`, meet along `u₁`. -/
theorem rimCertPts_axisTest_gen {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (hfar₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (hfar₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (hP : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (htri : ¬ (⟪a', axisView G.l G.m a a' b c⟫ = ⟪b, axisView G.l G.m a a' b c⟫ ∧
      ⟪b, axisView G.l G.m a a' b c⟫ = ⟪b', axisView G.l G.m a a' b c⟫))
    (V : Finset ℝ³) (hO : ({a, a', b, b', c, c'} : Finset ℝ³) ⊆ V)
    (hV : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a a' b b' (axisView G.l G.m a a' b c) v) :
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (RimCertPts V (σ • axisView G.l G.m a a' b c) (quad a' b a b') ∨
        RimCertPts V (σ • axisView G.l G.m a a' b c) (tri a' b b'))) ∨
      (SegMeet a' a b b' (axisView G.l G.m a a' b c) ∧
        SegMeet a' a c c' (axisView G.l G.m a a' b c) ∧
        ¬ IsRobustUnimodal (quad ⟪a', axisView G.l G.m a a' b c⟫ ⟪b, axisView G.l G.m a a' b c⟫
          ⟪a, axisView G.l G.m a a' b c⟫ ⟪b', axisView G.l G.m a a' b c⟫)) := by
  obtain ⟨σ, s, δ, s', δ', hσ, hs0, hs1, hδ, hc, hs0', hs1', hδ', hc', hT, hΓ, hB⟩ :=
    axis_test_facts F G hfar₁ hfar₂
  set u := axisView G.l G.m a a' b c
  have hV' : ∀ v ∈ V, v = a ∨ v = a' ∨ v = b ∨ v = b' ∨ AxisExtra a a' b b' u v := by
    intro v hv
    rcases hV v hv with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, δ, hs0, hs1, hδ, h.trans hc⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨s', δ', hs0', hs1', hδ', h.trans hc'⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have mem : ∀ x ∈ ({a, a', b, b', c, c'} : Finset ℝ³), x ∈ V := fun x hx => hO hx
  obtain ⟨K1, K2⟩ := rimCertPts_axisTest_core_gen hσ hT hΓ hB htri V (mem a (by simp))
    (mem a' (by simp)) (mem b (by simp)) (mem b' (by simp)) hV'
  have hσα : σ * det3 (b' - b) (a - b) u ≠ 0 :=
    mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hP
  rcases lt_or_gt_of_ne hσα with hα | hα
  · by_cases hR : IsRobustUnimodal (quad ⟪a', u⟫ ⟪b, u⟫ ⟪a, u⟫ ⟪b', u⟫)
    · exact Or.inl ⟨σ, hσ, Or.inl (K2 hα hR)⟩
    · obtain ⟨m1, m2⟩ := axisTest_meets hσ hs0 hs1 hc hs0' hs1' hc' hT hΓ hB hα
      exact Or.inr ⟨m1, m2, hR⟩
  · exact Or.inl ⟨σ, hσ, Or.inr (K1 hα)⟩

/-- **One test of Theorem 13.7, certificate form** (`isRupert_axisTest_robust` without the
horizontal double normal, with any robustness criterion): the certificate at `±u₁`, or the rim
is the quadrilateral `a' b a b'` with depths that are not robustly unimodal, and the projections
of `[a', a]` and `[b, b']`, and those of `[a', a]` and `[c, c']`, meet along `u₁`. -/
theorem rimCert_axisTest_gen {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (hfar₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (hfar₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (hP : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (htri : ¬ (⟪a', axisView G.l G.m a a' b c⟫ = ⟪b, axisView G.l G.m a a' b c⟫ ∧
      ⟪b, axisView G.l G.m a a' b c⟫ = ⟪b', axisView G.l G.m a a' b c⟫))
    (V : Finset ℝ³) (hO : ({a, a', b, b', c, c'} : Finset ℝ³) ⊆ V)
    (hV : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a a' b b' (axisView G.l G.m a a' b c) v) :
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ RimCert V (σ • axisView G.l G.m a a' b c)) ∨
      (SegMeet a' a b b' (axisView G.l G.m a a' b c) ∧
        SegMeet a' a c c' (axisView G.l G.m a a' b c) ∧
        ¬ IsRobustUnimodal (quad ⟪a', axisView G.l G.m a a' b c⟫ ⟪b, axisView G.l G.m a a' b c⟫
          ⟪a, axisView G.l G.m a a' b c⟫ ⟪b', axisView G.l G.m a a' b c⟫)) :=
  (rimCertPts_axisTest_gen F G hfar₁ hfar₂ hP htri V hO hV).imp_left fun ⟨σ, hσ, h⟩ =>
    ⟨σ, hσ, h.elim (·.rimCert4) (·.rimCert3)⟩

/-- **`isRupert_axisTest_robust` in certificate form** (the ties of `QuadTie`). -/
theorem rimCert_axisTest_robust {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c')
    (hfar₁ : |galeD G.l G.m a b| < |galeD G.l G.m a c|)
    (hfar₂ : |galeD G.l G.m a b'| < |galeD G.l G.m a c'|)
    (hP : det3 (b' - b) (a - b) (axisView G.l G.m a a' b c) ≠ 0)
    (hz : QuadTie ⟪a', axisView G.l G.m a a' b c⟫ ⟪b, axisView G.l G.m a a' b c⟫
      ⟪a, axisView G.l G.m a a' b c⟫ ⟪b', axisView G.l G.m a a' b c⟫)
    (V : Finset ℝ³) (hO : ({a, a', b, b', c, c'} : Finset ℝ³) ⊆ V)
    (hV : ∀ v ∈ V, v ∈ ({a, a', b, b', c, c'} : Finset ℝ³) ∨
      AxisExtra a a' b b' (axisView G.l G.m a a' b c) v) :
    (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ RimCert V (σ • axisView G.l G.m a a' b c)) ∨
      (SegMeet a' a b b' (axisView G.l G.m a a' b c) ∧
        SegMeet a' a c c' (axisView G.l G.m a a' b c) ∧
        DepthSep a' a b b' (axisView G.l G.m a a' b c)) := by
  rcases rimCert_axisTest_gen F G hfar₁ hfar₂ hP hz.2.1 V hO hV with h | ⟨m1, m2, hR⟩
  · exact Or.inl h
  · refine Or.inr ⟨m1, m2, ?_⟩
    by_contra hsep
    exact hR (isRobustUnimodal_quad hz (fun h => hsep (Or.inr h)) (fun h => hsep (Or.inl h)))


/-! ### Weak separations with one tie -/

/-- At most one tied pair among four values. -/
def OneTie4 (z : Fin 4 → ℝ) : Prop :=
  ∀ i j i' j' : Fin 4, i ≠ j → i' ≠ j' → z i = z j → z i' = z j' →
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i')

/-- No two points of `V` at one depth along `w`. -/
def NoTieAt (V : Finset ℝ³) (w : ℝ³) : Prop := ∀ s ∈ V, ∀ t ∈ V, s ≠ t → ⟪s, w⟫ ≠ ⟪t, w⟫

/-- **A 4-cycle with at most one tie that is not robustly unimodal has weakly separated
diagonals**: `QuadTie` fails only at a level edge inside a run, which is a weak separation. -/
theorem weakSep_of_not_robust {z₀ z₁ z₂ z₃ : ℝ} (hone : OneTie4 ![z₀, z₁, z₂, z₃])
    (h : ¬ IsRobustUnimodal (quad z₀ z₁ z₂ z₃)) :
    max z₁ z₃ ≤ min z₀ z₂ ∨ max z₀ z₂ ≤ min z₁ z₃ := by
  by_contra hc
  push Not at hc
  obtain ⟨hcA, hcB⟩ := hc
  have two : ∀ i j i' j' : Fin 4, i ≠ j → i' ≠ j' → ¬ ((i = i' ∧ j = j') ∨ (i = j' ∧ j = i')) →
      ![z₀, z₁, z₂, z₃] i = ![z₀, z₁, z₂, z₃] j →
      ![z₀, z₁, z₂, z₃] i' = ![z₀, z₁, z₂, z₃] j' → False :=
    fun i j i' j' h1 h2 h3 e1 e2 => h3 (hone i j i' j' h1 h2 e1 e2)
  have nA : ¬ (max z₁ z₃ ≤ min z₀ z₂) := not_le.mpr hcA
  have nB : ¬ (max z₀ z₂ ≤ min z₁ z₃) := not_le.mpr hcB
  apply h
  refine isRobustUnimodal_quad ⟨fun ⟨e1, e2⟩ => two 0 1 1 2 (by decide) (by decide) (by decide)
      e1 e2, fun ⟨e1, e2⟩ => two 0 1 1 3 (by decide) (by decide) (by decide) e1 e2,
    fun ⟨e1, e2⟩ => two 0 2 2 3 (by decide) (by decide) (by decide) e1 e2,
    fun ⟨e1, e2⟩ => two 1 2 2 3 (by decide) (by decide) (by decide) e1 e2,
    fun ⟨p1, p2, p3⟩ => nA (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nB (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nB (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nA (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nA (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nB (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nB (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith))),
    fun ⟨p1, p2, p3⟩ => nA (max_le (le_min (by linarith) (by linarith))
      (le_min (by linarith) (by linarith)))⟩
    (fun h' => lt_asymm h' hcA) (fun h' => lt_asymm h' hcB)

/-- With distinct values, a weak separation is strict. -/
theorem lt_of_le_of_nodup4 {z₀ z₁ z₂ z₃ : ℝ} (hd : [z₀, z₁, z₂, z₃].Nodup)
    (h : max z₁ z₃ ≤ min z₀ z₂) : max z₁ z₃ < min z₀ z₂ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hd
  refine lt_of_le_of_ne h fun e => ?_
  rcases max_choice z₁ z₃ with m | m <;> rcases min_choice z₀ z₂ with n | n <;> rw [m, n] at e
  exacts [h01 e.symm, h12 e, h03 e.symm, h23 e.symm]

/-- At most one tie at `u` among four distinct points of `V`. -/
theorem OneTieAt.oneTie4 {V : Finset ℝ³} {u : ℝ³} (h : OneTieAt V u) {p₀ p₁ p₂ p₃ : ℝ³}
    (h₀ : p₀ ∈ V) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V) (hd : [p₀, p₁, p₂, p₃].Nodup) :
    OneTie4 ![⟪p₀, u⟫, ⟪p₁, u⟫, ⟪p₂, u⟫, ⟪p₃, u⟫] := by
  have hp : ∀ k : Fin 4, ![p₀, p₁, p₂, p₃] k ∈ V := by
    intro k; fin_cases k <;> assumption
  have hinj : Function.Injective ![p₀, p₁, p₂, p₃] := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hd
    obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hd
    intro i j e
    fin_cases i <;> fin_cases j <;> simp_all
  intro i j i' j' hij hij' e1 e2
  have e : ∀ k : Fin 4, ![⟪p₀, u⟫, ⟪p₁, u⟫, ⟪p₂, u⟫, ⟪p₃, u⟫] k = ⟪![p₀, p₁, p₂, p₃] k, u⟫ := by
    intro k; fin_cases k <;> rfl
  rw [e, e] at e1 e2
  rcases h _ (hp i) _ (hp j) _ (hp i') _ (hp j') (hinj.ne hij) (hinj.ne hij') e1 e2 with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hinj h1, hinj h2⟩
  · exact Or.inr ⟨hinj h1, hinj h2⟩

/-- No tie at `u` among four distinct points: their depths are distinct. -/
theorem NoTieAt.nodup4 {V : Finset ℝ³} {u : ℝ³} (h : NoTieAt V u) {p₀ p₁ p₂ p₃ : ℝ³}
    (h₀ : p₀ ∈ V) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V) (hd : [p₀, p₁, p₂, p₃].Nodup) :
    [⟪p₀, u⟫, ⟪p₁, u⟫, ⟪p₂, u⟫, ⟪p₃, u⟫].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd ⊢
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hd
  exact ⟨⟨h _ h₀ _ h₁ h01, h _ h₀ _ h₂ h02, h _ h₀ _ h₃ h03⟩, ⟨h _ h₁ _ h₂ h12, h _ h₁ _ h₃ h13⟩,
    h _ h₂ _ h₃ h23, not_false⟩

/-- With no tie at `u`, a weak separation of two pairs is strict. -/
theorem lt_of_le_of_noTie {V : Finset ℝ³} {u : ℝ³} (h : NoTieAt V u) {p q r s : ℝ³}
    (hp : p ∈ V) (hq : q ∈ V) (hr : r ∈ V) (hs : s ∈ V) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hle : max ⟪p, u⟫ ⟪q, u⟫ ≤ min ⟪r, u⟫ ⟪s, u⟫) :
    max ⟪p, u⟫ ⟪q, u⟫ < min ⟪r, u⟫ ⟪s, u⟫ := by
  refine lt_of_le_of_ne hle fun e => ?_
  rcases max_choice ⟪p, u⟫ ⟪q, u⟫ with m | m <;> rcases min_choice ⟪r, u⟫ ⟪s, u⟫ with n | n <;>
    rw [m, n] at e
  exacts [h _ hp _ hr hpr e, h _ hp _ hs hps e, h _ hq _ hr hqr e, h _ hq _ hs hqs e]

end Minimality

end
