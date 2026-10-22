module

public import Minimality.Type21Entry

@[expose] public section

/-!
# Type 21, the other Gale classes: tools (`FEWER-FACES-PROOFS.md` §16 addendum)

* **Steps 1–2 of Theorem 9.9 in Gale form** — `step1_gale`, `arc_step1`: for an octahedron
  with normalized Gale data (`κ_A, κ_B, κ_C > 0`) and `f = g_a + g_b + g_c ≠ 0`, some pair `W`
  is admissible (Lemma 9.8, `arc_lemma`), and the two edges of its Step-1 pair are quad edges
  and E-good (`EGoodQuad`), in the orientation given by the sign of `[w u]` (Lemma 16.16).
* **The Gale data of `K − 6`** — `type21_galeO2`: from the dependencies `{1 ·}` and `{0 ·}`
  (Lemma 16.2) a `GaleData` of `O2 = K − 6`, with its values at the six vertices.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

/-- `x → y` is a quad edge in Gale form (Lemma 16.1 (i)), the third pair being `p, p'`. -/
def GaleQuad (l m : ℝ³ → ℝ) (x y p p' : ℝ³) : Prop :=
  galeD l m p x * (galeD l m p x + galeD l m p y) < 0 ∧
  galeD l m p' x * (galeD l m p' x + galeD l m p' y) < 0

/-- **Step 1 of Theorem 9.9 in Gale form** (`κ_A, κ_B, κ_C > 0`, `W = C` admissible,
`[c a] > 0`): `b → a` and `a' → b'` are quad edges. -/
theorem step1_gale_pos {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hfc : 0 < galeF G.l G.m a b c c) (hfc' : 0 < galeF G.l G.m a b c c')
    (hU : 0 < galeD G.l G.m c a) :
    EGoodQuad G.l G.m b b' a c c' ∧ EGoodQuad G.l G.m a' a b' c c' := by
  have hl := G.hl; have hm := G.hm
  have anti := galeD_anti G.l G.m
  have self := galeD_self G.l G.m
  obtain ⟨c1, c2, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (hl.galeD hm c).perm₂₃.perm₁₂
    (self c) hκc.ne'
  obtain ⟨d1, d2, d3⟩ := pole_signs F.perm₂₃.perm₁₂.swap₁ (hl.galeD hm c').perm₂₃.perm₁₂.swap₁
    (self c') (by rw [anti]; linarith)
  obtain ⟨a1, a2, a3⟩ := pole_signs F (hl.galeD hm a) (self a) hκa.ne'
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
  have sc := galeD_sum hl hm c
  have sc' := galeD_sum hl hm c'
  rw [galeF_eq] at hfc hfc'
  rw [self] at sc hfc
  rw [self] at sc'
  have hcc' := anti c c'
  obtain ⟨b1, b2, b3⟩ := pole_signs F.perm₁₂.swap₁ (hl.galeD hm b').perm₁₂.swap₁
    (self b') (by rw [anti]; linarith)
  have hac : galeD G.l G.m a c < 0 := by rw [anti]; linarith
  have hab : 0 < galeD G.l G.m a b := pos_of_mul_neg_neg (by linarith) hac
  have hab' : 0 < galeD G.l G.m a b' := pos_of_mul_pos_pos a1 hab
  have hb'c : 0 < galeD G.l G.m b' c := by rw [anti]; linarith
  have hb'a : galeD G.l G.m b' a < 0 := neg_of_mul_neg_pos b3 hb'c
  refine ⟨⟨by nlinarith, by nlinarith, ?_⟩, ⟨by nlinarith, by nlinarith, ?_⟩⟩
  · rw [anti b b']; nlinarith
  · exact mul_pos hκa hab'

/-- **Step 1 of Theorem 9.9 in Gale form**, both signs of `[c a]`. -/
theorem step1_gale {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hfc : 0 < galeF G.l G.m a b c c) (hfc' : 0 < galeF G.l G.m a b c c') :
    (0 < galeD G.l G.m c a → EGoodQuad G.l G.m b b' a c c' ∧ EGoodQuad G.l G.m a' a b' c c') ∧
    (galeD G.l G.m c a < 0 → EGoodQuad G.l G.m a a' b c c' ∧ EGoodQuad G.l G.m b' b a' c c') := by
  refine ⟨step1_gale_pos F G hκa hκb hκc hfc hfc', fun hU => ?_⟩
  obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
    (galeD_self _ _ _) hκc.ne'
  have hb : 0 < galeD G.l G.m c b := pos_of_mul_neg_neg (by rwa [mul_comm] at c3) hU
  exact step1_gale_pos F.perm₁₂ G.perm₁₂ hκb hκa hκc (by rw [galeF_perm₁₂]; exact hfc)
    (by rw [galeF_perm₁₂]; exact hfc') hb

/-- **Lemma 9.8 with Step 1, Gale form**: for normalized Gale data and `f ≠ 0`, some pair `W` is
admissible, and its Step-1 pair consists of quad edges (orientation by the sign of `[w u]`). -/
theorem arc_step1 {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c')
    (hf : ¬(G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0)) :
    ((0 < galeD G.l G.m c a → EGoodQuad G.l G.m b b' a c c' ∧ EGoodQuad G.l G.m a' a b' c c') ∧
      (galeD G.l G.m c a < 0 → EGoodQuad G.l G.m a a' b c c' ∧
        EGoodQuad G.l G.m b' b a' c c')) ∨
    ((0 < galeD G.l G.m b a → EGoodQuad G.l G.m c c' a b b' ∧ EGoodQuad G.l G.m a' a c' b b') ∧
      (galeD G.l G.m b a < 0 → EGoodQuad G.l G.m a a' c b b' ∧
        EGoodQuad G.l G.m c' c a' b b')) ∨
    ((0 < galeD G.l G.m a b → EGoodQuad G.l G.m c c' b a a' ∧ EGoodQuad G.l G.m b' b c' a a') ∧
      (galeD G.l G.m a b < 0 → EGoodQuad G.l G.m b b' c a a' ∧
        EGoodQuad G.l G.m c' c b' a a')) := by
  rcases arc_lemma F G hκa.ne' hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `W = A`
    right; right
    exact step1_gale F.perm₁₂.perm₂₃ G.perm₁₂.perm₂₃ hκb hκc hκa
      (by simpa [GaleData.perm₁₂, GaleData.perm₂₃, galeF] using
        (by simp only [galeF] at h1 ⊢; linarith : 0 < galeF G.l G.m b c a a))
      (by simpa [GaleData.perm₁₂, GaleData.perm₂₃, galeF] using
        (by simp only [galeF] at h2 ⊢; linarith : 0 < galeF G.l G.m b c a a'))
  · -- `W = B`
    right; left
    exact step1_gale F.perm₂₃ G.perm₂₃ hκa hκc hκb
      (by simpa [GaleData.perm₂₃, galeF_perm₂₃] using h1)
      (by simpa [GaleData.perm₂₃, galeF_perm₂₃] using h2)
  · left
    exact step1_gale F G hκa hκb hκc h1 h2

/-- **The Gale data of `K − 6`** (Lemma 16.2): with `r = β + τ [1 6]`, the dependencies `{1 ·}`
(`l`) and `{0 ·}` (`m`) of `O2 = K − 6` (labels `5, 4, 3, 0, 1, 2`) are independent, so they are
Gale data of `O2`; their values at the six vertices. -/
theorem type21_galeO2 {a a' b b' c c' d : ℝ³} {F : OctFacets a a' b b' c c'}
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') {α β τ : ℝ}
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a) (hr : β + τ * galeD G.l G.m c c' ≠ 0)
    (hca : galeD G.l G.m c a ≠ 0) :
    ∃ G2 : GaleData b' b a' a c d,
      G2.l b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c b' ∧
      G2.l b = β * galeD G.l G.m c b ∧ G2.l a' = β * galeD G.l G.m c a' ∧
      G2.l a = (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a ∧ G2.l c = 0 ∧
      G2.l d = galeD G.l G.m c c' ∧
      G2.m b' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' ∧
      G2.m b = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b +
        τ * galeD G.l G.m c b * galeD G.l G.m c' a ∧
      G2.m a' = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a a' +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a ∧
      G2.m a = 0 ∧ G2.m c = (β + τ * galeD G.l G.m c c') * galeD G.l G.m a c ∧
      G2.m d = galeD G.l G.m a c' := by
  obtain ⟨L1, hL1, l2, l1, l5, l4, l3, l0⟩ := type21_depO2_c hd G hco hα ht
  obtain ⟨L0, hL0, m0, m3, m5, m4, m1, m2⟩ := type21_depO2_a hd G hco hα ht
  have hac : galeD G.l G.m a c ≠ 0 := by
    rw [galeD_anti]; exact neg_ne_zero.mpr hca
  refine ⟨⟨L1, L0, hL1.perm₁₂.perm₂₃.swap₃, hL0.perm₁₂.swap₂, fun x y h1 h2 h3 h4 h5 h6 => ?_⟩,
    l5, l4, l3, l0, l1, l2, m5, m4, m3, m0, m1, m2⟩
  rw [l1, m1] at h5
  rw [l0, m0] at h4
  have hy : y = 0 := by
    have : y * ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a c) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero hr hac)
  have hx : x = 0 := by
    have : x * ((β + τ * galeD G.l G.m c c') * galeD G.l G.m c a) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero hr hca)
  exact ⟨hx, hy⟩

end Minimality

end
