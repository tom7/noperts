module

public import Minimality.Type21Lift

@[expose] public section

/-!
# Type 21: Theorem 5 of §9, the Gale route (`FEWER-FACES-PROOFS.md` §9), conditional

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`.

* **Step 1–2 of Theorem 9.9, as crossed pairs** (any octahedron) — `gale_crossed`: with
  normalized Gale data (`κ_A, κ_B, κ_C > 0`) and `W = C` admissible
  (`det (g_c, f) > 0`, `det (g_c', f) > 0` for `f = g_a + g_b + g_c`), the crossed pair
  `{b → a, a' → b'}` or `{a → b, b' → a'}` consists of quad edges that are not bad
  (`GoodQuad`: the two facet inequalities and not bad; Lemma 9.6 `facet_lt_of_dep`, and
  `not_bad_of_dep`).  `gale_edge`: the same for Gale data of any signs (no planar
  equator), normalized by `galeHat`; `W = C` admissible (`GaleAdm`) gives a good quad edge
  along `a b` if `κ_A κ_B > 0` and along `a b'` if `κ_A κ_B < 0`.
* **Theorem 5 of §9** — `isRupert_type21_gale` (for `K − 2`) and `isRupert_type21` (for
  `K − 2` or `K − 6`, through `σ2`, `IsCap21.O2`): if some admissible `W` of `K − 2` or of
  `K − 6` has a crossed pair containing a K-quad edge (the Gale-sign form: `W = {1,6}` with
  `ε03 ≠ ε45`, `W = {4,5}` with `ε03 ≠ ε16`, `W = {0,3}` with `ε16 ≠ ε45`) or a TT edge at
  which the cap is hidden (`HiddenAt`, at `04`, `01`, `14`; at `04` this never happens,
  `IsCap21.not_hidden_04`), then `K` is Rupert (`Type21Gale`).  Lemma 3 (`Type21Lift.lean`) handles the K-quad edges, Lemma 2 (a)
  (`isRupert_type21_hidden`) the TT edges.  Special positions excluded: planar equators
  (`κ ≠ 0`, inside `Type21Gale`), `GenPosTie` (no parallel segments, at most one tie at each edge view:
  no touching) and `NoHDNEdges`.  Coverage (that some admissible pair always qualifies) is
  open: about 11% of shapes fail the hypothesis.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **A good quad edge** `x → y` of an octahedron: `x'` is hidden at the view along `x y`
(the two facet inequalities at the faces through `x'` and `y'`) and the edge is not bad. -/
def GoodQuad {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p') : Prop :=
  F.a'b'c.f x < F.a'b'c.f y ∧ F.a'b'c'.f x < F.a'b'c'.f y ∧
    ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫

theorem GoodQuad.swap₃ {x x' y y' p p' : ℝ³} {F : OctFacets x x' y y' p p'} (h : GoodQuad F) :
    GoodQuad F.swap₃ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, h1, by rwa [min_comm]⟩

/-! ### The crossed pairs of Theorem 9.9 -/

/-- **Theorem 9.9, Steps 1–2, for `U = A`** (normalized labels, `W = C` admissible,
`[c a] > 0`): `b → a` and `a' → b'` are quad edges (Lemma 9.6) and not bad. -/
theorem gale_crossed_pos {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hfc : 0 < galeF G.l G.m a b c c) (hfc' : 0 < galeF G.l G.m a b c c')
    (hU : 0 < galeD G.l G.m c a) :
    GoodQuad F.perm₁₂.swap₃ ∧ GoodQuad F.swap₁.swap₂.swap₃ := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨c1, c2, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂
    (self c) hκc.ne'
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁ (hl.galeD hm c').perm₂₃.perm₁₂.swap₁
    (self c') (by rw [anti]; linarith)
  obtain ⟨a1, a2, a3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
  obtain ⟨b1, b2, b3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁
    (self b') (by rw [anti]; linarith)
  have hca' : 0 < galeD G.l G.m c a' := pos_of_mul_pos_pos c1 hU
  have hcb : galeD G.l G.m c b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at c3) hU
  have hcb' : galeD G.l G.m c b' < 0 := neg_of_mul_pos_neg (by linarith) hcb
  have hc'a : 0 < galeD G.l G.m c' a := by
    have e : galeD G.l G.m a c * galeD G.l G.m a c' = galeD G.l G.m c a * galeD G.l G.m c' a := by
      rw [anti c a, anti c' a]; ring
    exact pos_of_mul_pos_pos (e ▸ a2) hU
  have hc'a' : 0 < galeD G.l G.m c' a' := pos_of_mul_pos_pos d1 hc'a
  have hc'b : galeD G.l G.m c' b < 0 := neg_of_mul_neg_pos (by rwa [mul_comm] at d3) hc'a
  have hc'b' : galeD G.l G.m c' b' < 0 := neg_of_mul_pos_neg (by linarith) hc'b
  have hac : galeD G.l G.m a c < 0 := by rw [anti]; linarith
  have hab : 0 < galeD G.l G.m a b := pos_of_mul_neg_neg (by linarith) hac
  have hab' : 0 < galeD G.l G.m a b' := pos_of_mul_pos_pos a1 hab
  have hb'c : 0 < galeD G.l G.m b' c := by rw [anti]; linarith
  have hb'a : galeD G.l G.m b' a < 0 := neg_of_mul_neg_pos b3 hb'c
  have hb'a' : galeD G.l G.m b' a' < 0 := neg_of_mul_pos_neg b1 hb'a
  have hb'c' : 0 < galeD G.l G.m b' c' := by rw [anti]; linarith
  have sc := galeD_sum hl hm c
  have sc' := galeD_sum hl hm c'
  rw [galeF_eq] at hfc hfc'
  rw [self] at sc hfc
  rw [self] at sc'
  have hcc' := anti c c'
  have hndb := (F.perm₁₂.swap₃).nodup
  have hnda := (F.swap₁.swap₂.swap₃).nodup
  have hq₁ := facet_lt_of_dep (hl.galeD hm c).perm₁₂.swap₃ (F.perm₁₂.swap₃).a'b'c (by simp)
    (by simp) hndb (self c) (by nlinarith)
  have hq₂ := facet_lt_of_dep (hl.galeD hm c').perm₁₂ (F.perm₁₂.swap₃).a'b'c' (by simp)
    (by simp) (F.perm₁₂).nodup (self c') (by nlinarith)
  have hr₁ := facet_lt_of_dep (hl.galeD hm c).swap₁.swap₂.swap₃ (F.swap₁.swap₂.swap₃).a'b'c
    (by simp) (by simp) hnda (self c) (by nlinarith)
  have hr₂ := facet_lt_of_dep (hl.galeD hm c').swap₁.swap₂ (F.swap₁.swap₂.swap₃).a'b'c'
    (by simp) (by simp) (F.swap₁.swap₂).nodup (self c') (by nlinarith)
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  have hnba : a ≠ b := hnd.1.2.1
  have hnab' : a' ≠ b' := hnd.2.1.2.1
  have hgood₁ := not_bad_of_dep (hl.galeD hm b').perm₁₂.swap₃ (Ne.symm hnba) (self b')
    (by rw [anti]; linarith) (by rw [anti b b']; linarith) hb'a'.le hb'c'.le hb'c.le
  have hgood₂ := not_bad_of_dep (L := fun t => galeD G.l G.m t a)
    (hl.galeD' hm a).swap₁.swap₂.swap₃ hnab' (self a) (by rw [anti]; linarith)
    (by rw [anti a a', anti a b']; linarith) (by rw [anti]; linarith) hc'a.le hU.le
  exact ⟨⟨hq₁, hq₂, hgood₁⟩, ⟨hr₁, hr₂, hgood₂⟩⟩

/-- **Theorem 9.9, Steps 1–2** (normalized labels `κ_A, κ_B, κ_C > 0`, `W = C` admissible):
the crossed pair `{b → a, a' → b'}` or `{a → b, b' → a'}` consists of good quad edges. -/
theorem gale_crossed {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hfc : 0 < galeF G.l G.m a b c c) (hfc' : 0 < galeF G.l G.m a b c c') :
    (GoodQuad F.perm₁₂ ∧ GoodQuad F.swap₁.swap₂) ∨
      (GoodQuad F ∧ GoodQuad F.perm₁₂.swap₁.swap₂) := by
  obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
    (galeD_self _ _ c) hκc.ne'
  rcases lt_or_gt_of_ne (show galeD G.l G.m c a ≠ 0 by intro h0; rw [h0, zero_mul] at c3; linarith)
    with hU | hU
  · have hb : 0 < galeD G.l G.m c b := pos_of_mul_neg_neg (by rwa [mul_comm] at c3) hU
    obtain ⟨⟨p1, p2, p3⟩, ⟨q1, q2, q3⟩⟩ := gale_crossed_pos F.perm₁₂ G.perm₁₂ hκb hκa hκc
      (by rw [galeF_perm₁₂]; exact hfc) (by rw [galeF_perm₁₂]; exact hfc') hb
    rw [min_comm] at p3 q3
    exact Or.inr ⟨⟨p2, p1, p3⟩, ⟨q2, q1, q3⟩⟩
  · obtain ⟨⟨p1, p2, p3⟩, ⟨q1, q2, q3⟩⟩ := gale_crossed_pos F G hκa hκb hκc hfc hfc' hU
    rw [min_comm] at p3 q3
    exact Or.inl ⟨⟨p2, p1, p3⟩, ⟨q2, q1, q3⟩⟩

/-! ### Gale data of any signs -/

/-- The normalized representative of a pair: `x` if `κ = det (g_x, g_x') > 0`, else `x'`. -/
noncomputable def galeHat (κ : ℝ) (x x' : ℝ³) : ℝ³ := if 0 < κ then x else x'

/-- **The pair `W = {w, w'}` is admissible** (Step 1 of Theorem 9.9): `det (g_w, f) > 0`
and `det (g_w', f) > 0` for `f` the sum of the Gale vectors of the normalized
representatives `â, b̂, ĉ` (`galeHat`). -/
def GaleAdm {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (w w' : ℝ³) : Prop :=
  0 < galeF G.l G.m (galeHat (galeD G.l G.m a a') a a') (galeHat (galeD G.l G.m b b') b b')
      (galeHat (galeD G.l G.m c c') c c') w ∧
    0 < galeF G.l G.m (galeHat (galeD G.l G.m a a') a a') (galeHat (galeD G.l G.m b b') b b')
      (galeHat (galeD G.l G.m c c') c c') w'

theorem GaleAdm.perm₂₃ {a a' b b' c c' w w' : ℝ³} {G : GaleData a a' b b' c c'}
    (h : GaleAdm G w w') : GaleAdm G.perm₂₃ w w' := by
  obtain ⟨h1, h2⟩ := h
  rw [← galeF_perm₂₃] at h1 h2
  exact ⟨h1, h2⟩

theorem GaleAdm.perm₁₂₃ {a a' b b' c c' w w' : ℝ³} {G : GaleData a a' b b' c c'}
    (h : GaleAdm G w w') : GaleAdm G.perm₁₂.perm₂₃ w w' := by
  obtain ⟨h1, h2⟩ := h
  rw [← galeF_perm₁₂, ← galeF_perm₂₃] at h1 h2
  exact ⟨h1, h2⟩

/-- **Steps 1–2 of Theorem 9.9 for Gale data of any signs** (no planar equator): if
`W = C` is admissible, the edge between the pairs `A`, `B` of the crossed pair through `a`
(`a b` if `κ_A κ_B > 0`, `a b'` if `κ_A κ_B < 0`) is a good quad edge in one direction. -/
theorem gale_edge {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : galeD G.l G.m a a' ≠ 0)
    (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0) (hadm : GaleAdm G c c') :
    (0 < galeD G.l G.m a a' * galeD G.l G.m b b' → GoodQuad F ∨ GoodQuad F.perm₁₂) ∧
    (galeD G.l G.m a a' * galeD G.l G.m b b' < 0 →
      GoodQuad F.swap₂ ∨ GoodQuad F.swap₂.perm₁₂) := by
  have anti := galeD_anti G.l G.m
  obtain ⟨hA, hC⟩ := hadm
  simp only [galeHat] at hA hC
  rcases lt_or_gt_of_ne hκa with ha | ha <;> rcases lt_or_gt_of_ne hκb with hb | hb <;>
    rcases lt_or_gt_of_ne hκc with hc | hc <;>
    simp only [ha, hb, hc, lt_asymm ha, lt_asymm hb, lt_asymm hc, ↓reduceIte] at hA hC
  · -- `(−, −, −)`
    have ka : 0 < galeD G.l G.m a' a := by rw [anti]; linarith
    have kb : 0 < galeD G.l G.m b' b := by rw [anti]; linarith
    have kc : 0 < galeD G.l G.m c' c := by rw [anti]; linarith
    refine ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr (mul_pos_of_neg_of_neg ha hb).le)⟩
    rcases gale_crossed F.swap₁.swap₂.swap₃ G.swap₁.swap₂.swap₃ ka kb kc hC hA with
      ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
    · exact Or.inr ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
  · -- `(−, −, +)`
    have ka : 0 < galeD G.l G.m a' a := by rw [anti]; linarith
    have kb : 0 < galeD G.l G.m b' b := by rw [anti]; linarith
    refine ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr (mul_pos_of_neg_of_neg ha hb).le)⟩
    rcases gale_crossed F.swap₁.swap₂ G.swap₁.swap₂ ka kb hc hA hC with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  · -- `(−, +, −)`
    have ka : 0 < galeD G.l G.m a' a := by rw [anti]; linarith
    have kc : 0 < galeD G.l G.m c' c := by rw [anti]; linarith
    refine ⟨fun h => absurd h (not_lt.mpr (mul_neg_of_neg_of_pos ha hb).le), fun _ => ?_⟩
    rcases gale_crossed F.swap₁.swap₃ G.swap₁.swap₃ ka hb kc hC hA with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
    · exact Or.inr ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
  · -- `(−, +, +)`
    have ka : 0 < galeD G.l G.m a' a := by rw [anti]; linarith
    refine ⟨fun h => absurd h (not_lt.mpr (mul_neg_of_neg_of_pos ha hb).le), fun _ => ?_⟩
    rcases gale_crossed F.swap₁ G.swap₁ ka hb hc hA hC with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  · -- `(+, −, −)`
    have kb : 0 < galeD G.l G.m b' b := by rw [anti]; linarith
    have kc : 0 < galeD G.l G.m c' c := by rw [anti]; linarith
    refine ⟨fun h => absurd h (not_lt.mpr (mul_neg_of_pos_of_neg ha hb).le), fun _ => ?_⟩
    rcases gale_crossed F.swap₂.swap₃ G.swap₂.swap₃ ha kb kc hC hA with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
    · exact Or.inl ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
  · -- `(+, −, +)`
    have kb : 0 < galeD G.l G.m b' b := by rw [anti]; linarith
    refine ⟨fun h => absurd h (not_lt.mpr (mul_neg_of_pos_of_neg ha hb).le), fun _ => ?_⟩
    rcases gale_crossed F.swap₂ G.swap₂ ha kb hc hA hC with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
    · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
  · -- `(+, +, −)`
    have kc : 0 < galeD G.l G.m c' c := by rw [anti]; linarith
    refine ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr (mul_pos ha hb).le)⟩
    rcases gale_crossed F.swap₃ G.swap₃ ha hb kc hC hA with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
    · exact Or.inl ⟨h.2.1, h.1, by rw [min_comm]; exact h.2.2⟩
  · -- `(+, +, +)`
    refine ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr (mul_pos ha hb).le)⟩
    rcases gale_crossed F G ha hb hc hA hC with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
    · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩

/-! ### Theorem 5 -/

/-- **The hypothesis of Theorem 5 of §9** for an octahedron labelled as `O6` (pairs
`(0, 3)`, `(4, 5)`, `(1, 6)`) with Gale data `G` and the cap `d`: no planar equator
(`κ ≠ 0`), and some admissible `W` (`GaleAdm`) whose crossed pair contains a K-quad edge
(`W = {1,6}`: `ε03 ≠ ε45`; `W = {4,5}`: `ε03 ≠ ε16`; `W = {0,3}`: `ε16 ≠ ε45`) or, in the
non-quad pair `{04, 35}`, `{01, 36}` or `{14, 56}`, the TT edge `04`, `01` or `14` at
whose view the cap is hidden (`HiddenAt`). -/
def Type21Gale {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (d : ℝ³) : Prop :=
  galeD G.l G.m a a' ≠ 0 ∧ galeD G.l G.m b b' ≠ 0 ∧ galeD G.l G.m c c' ≠ 0 ∧
  ((GaleAdm G c c' ∧ (galeD G.l G.m a a' * galeD G.l G.m b b' < 0 ∨
      HiddenAt {a, a', b, b', c, c'} (b - a) d)) ∨
    (GaleAdm G b b' ∧ (galeD G.l G.m a a' * galeD G.l G.m c c' < 0 ∨
      HiddenAt {a, a', b, b', c, c'} (c - a) d)) ∨
    (GaleAdm G a a' ∧ (galeD G.l G.m b b' * galeD G.l G.m c c' < 0 ∨
      HiddenAt {a, a', b, b', c, c'} (c - b) d)))

/-- Lemma 2 (a) for a good quad edge of a relabelled octahedron. -/
theorem isRupert_goodQuad_hidden {x x' y y' p p' m : ℝ³} {O : Finset ℝ³}
    (F : OctFacets x x' y y' p p') (hG : GoodQuad F) (hset : ({x, x', y, y', p, p'} : Finset ℝ³) = O)
    (hH : HiddenAt O (y - x) m) (hmO : m ∉ O) (hgen : GenPosTie (insert m O))
    (hnd : NoHDNEdges (insert m O)) : IsRupert (insert m O) := by
  subst hset
  obtain ⟨h1, h2, h3⟩ := hG
  refine isRupert_type21_hidden F h1 h2 h3 hH ?_ hgen hnd
  simp only [mem_insert, mem_singleton, not_or] at hmO
  exact hmO

theorem HiddenAt.rev {O : Finset ℝ³} {x y m : ℝ³} (h : HiddenAt O (y - x) m) :
    HiddenAt O (x - y) m := by
  have := h.neg; rwa [neg_sub] at this

/-- Theorem 5 of §9 for `K − 2`, the pair `W = C = {1, 6}`: the crossed pair `{05, 34}`
(K-quad edges, Lemma 3) or `{04, 35}` (the TT edge `04` with the cap hidden, Lemma 2 (a)). -/
theorem isRupert_type21_WC {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hκa : galeD G.l G.m a a' ≠ 0) (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hadm : GaleAdm G c c')
    (h : galeD G.l G.m a a' * galeD G.l G.m b b' < 0 ∨ HiddenAt {a, a', b, b', c, c'} (b - a) d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hdO : d ∉ ({a, a', b, b', c, c'} : Finset ℝ³) := by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hda, hda', hdb, hdb', hdc, hdc'⟩
  have set6 : ∀ x₁ x₂ x₃ x₄ x₅ x₆ : ℝ³, ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³) =
      {a, a', b, b', c, c'} → ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³) = {a, a', b, b', c, c'} :=
    fun _ _ _ _ _ _ h => h
  obtain ⟨hpos, hneg⟩ := gale_edge F G hκa hκb hκc hadm
  rcases lt_or_gt_of_ne (mul_ne_zero hκa hκb) with hn | hp
  · rcases hneg hn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact isRupert_type21_05 F hd h1 h2 h3 hgen hnd
    · exact isRupert_type21_50 F hd h1 h2 h3 hgen hnd
  · rcases h with h | hH
    · exact absurd h (not_lt.mpr hp.le)
    rcases hpos hp with hG | hG
    · exact isRupert_goodQuad_hidden F hG rfl hH hdO hgen hnd
    · exact isRupert_goodQuad_hidden F.perm₁₂ hG
        (set6 _ _ _ _ _ _ (by
          ext z; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h | h | h | h) <;> simp [h]))
        hH.rev hdO hgen hnd

/-- Theorem 5 of §9 for `K − 2`, the pair `W = B = {4, 5}`: the crossed pair `{06, 13}`
(Lemma 3 at `06`) or `{01, 36}` (the TT edge `01` with the cap hidden). -/
theorem isRupert_type21_WB {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hκa : galeD G.l G.m a a' ≠ 0) (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hadm : GaleAdm G b b')
    (h : galeD G.l G.m a a' * galeD G.l G.m c c' < 0 ∨ HiddenAt {a, a', b, b', c, c'} (c - a) d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hdO : d ∉ ({a, a', b, b', c, c'} : Finset ℝ³) := by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hda, hda', hdb, hdb', hdc, hdc'⟩
  have set6 : ∀ x₁ x₂ x₃ x₄ x₅ x₆ : ℝ³, ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³) =
      {a, a', b, b', c, c'} → ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³) = {a, a', b, b', c, c'} :=
    fun _ _ _ _ _ _ h => h
  obtain ⟨hpos, hneg⟩ := gale_edge F.perm₂₃ G.perm₂₃ hκa hκc hκb hadm.perm₂₃
  rcases lt_or_gt_of_ne (mul_ne_zero hκa hκc) with hn | hp
  · rcases hneg hn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact isRupert_type21_06 F hd h1 h2 h3 hgen hnd
    · exact isRupert_type21_60 F hd h1 h2 h3 hgen hnd
  · rcases h with h | hH
    · exact absurd h (not_lt.mpr hp.le)
    rcases hpos hp with hG | hG
    · exact isRupert_goodQuad_hidden F.perm₂₃ hG
        (set6 _ _ _ _ _ _ (by
          ext z; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h | h | h | h) <;> simp [h]))
        hH hdO hgen hnd
    · exact isRupert_goodQuad_hidden F.perm₂₃.perm₁₂ hG
        (set6 _ _ _ _ _ _ (by
          ext z; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h | h | h | h) <;> simp [h]))
        hH.rev hdO hgen hnd

/-- Theorem 5 of §9 for `K − 2`, the pair `W = A = {0, 3}`: the crossed pair `{46, 15}`
(Lemma 3 at `46`) or `{14, 56}` (the TT edge `14` with the cap hidden). -/
theorem isRupert_type21_WA {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hκa : galeD G.l G.m a a' ≠ 0) (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hadm : GaleAdm G a a')
    (h : galeD G.l G.m b b' * galeD G.l G.m c c' < 0 ∨ HiddenAt {a, a', b, b', c, c'} (c - b) d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hdO : d ∉ ({a, a', b, b', c, c'} : Finset ℝ³) := by
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hda, hda', hdb, hdb', hdc, hdc'⟩
  have set6 : ∀ x₁ x₂ x₃ x₄ x₅ x₆ : ℝ³, ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³) =
      {a, a', b, b', c, c'} → ({x₁, x₂, x₃, x₄, x₅, x₆} : Finset ℝ³) = {a, a', b, b', c, c'} :=
    fun _ _ _ _ _ _ h => h
  obtain ⟨hpos, hneg⟩ := gale_edge F.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃ hκb hκc hκa hadm.perm₁₂₃
  rcases lt_or_gt_of_ne (mul_ne_zero hκb hκc) with hn | hp
  · rcases hneg hn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact isRupert_type21_46 F hd h1 h2 h3 hgen hnd
    · exact isRupert_type21_64 F hd h1 h2 h3 hgen hnd
  · rcases h with h | hH
    · exact absurd h (not_lt.mpr hp.le)
    rcases hpos hp with hG | hG
    · exact isRupert_goodQuad_hidden F.perm₁₂.perm₂₃ hG
        (set6 _ _ _ _ _ _ (by
          ext z; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h | h | h | h) <;> simp [h]))
        hH hdO hgen hnd
    · exact isRupert_goodQuad_hidden F.perm₁₂.perm₂₃.perm₁₂ hG
        (set6 _ _ _ _ _ _ (by
          ext z; simp only [mem_insert, mem_singleton]
          constructor <;> rintro (h | h | h | h | h | h) <;> simp [h]))
        hH.rev hdO hgen hnd

/-- **Theorem 5 of §9 for `K − 2`.**  Let `K = O6 ∪ {2}` be of type 21 (`IsCap21`), in
general position (`GenPosTie`) without horizontal double normals at the views along its
segments (`NoHDNEdges`).  If the Gale data of `O6` satisfy the hypothesis of Theorem 5
(`Type21Gale`), then `K` has an edge crossing whose reduced polygon is unimodal with strict
depths, and `K` is Rupert. -/
theorem isRupert_type21_gale {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c')
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hC : Type21Gale G d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨hκa, hκb, hκc, hW⟩ := hC
  rcases hW with ⟨hadm, h⟩ | ⟨hadm, h⟩ | ⟨hadm, h⟩
  · exact isRupert_type21_WC F hd G hgen hnd hκa hκb hκc hadm h
  · exact isRupert_type21_WB F hd G hgen hnd hκa hκb hκc hadm h
  · exact isRupert_type21_WA F hd G hgen hnd hκa hκb hκc hadm h

/-- **Theorem 5 of §9 (type 21, the proved part of the Gale route).**  Let `K` be of type 21:
the octahedron `O6 = K − 2` (`F`, opposite pairs `(0, 3)`, `(4, 5)`, `(1, 6)`) with the cap
`2` (`IsCap21`), in general position (`GenPosTie`) and without horizontal double normals at
the views along its segments (`NoHDNEdges`).  Suppose the Gale data of `K − 2`, or those of
`K − 6` (labelled by `σ2` as `5, 4, 3, 0, 1, 2`, cap `6`), satisfy the hypothesis of
Theorem 5 (`Type21Gale`: no planar equator, and an admissible `W` whose crossed pair
contains a K-quad edge, or a TT edge at which the cap is hidden).  Then `K` is Rupert.
That the hypothesis always holds is not proved (about 89% of random shapes satisfy it). -/
theorem isRupert_type21 {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hnd : NoHDNEdges (insert d ({a, a', b, b', c, c'} : Finset ℝ³)))
    (hC : (∃ G : GaleData a a' b b' c c', Type21Gale G d) ∨
      (∃ G : GaleData b' b a' a c d, Type21Gale G c')) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases hC with ⟨G, h⟩ | ⟨G, h⟩
  · exact isRupert_type21_gale F hd G hgen hnd h
  · rw [← type21_set_O2] at hgen hnd ⊢
    exact isRupert_type21_gale hd.O2 hd.sigma2 G hgen hnd h

end Minimality

end
