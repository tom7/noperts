module

public import Minimality.Type08S.P2QDefs

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
namespace Minimality

/-- `pole_signs` without the nondegeneracy hypothesis: either `L` vanishes at all six, or strict signs. -/
theorem pole_signs_v {t t' e e' g g' : ℝ³} (F : OctFacets t t' e e' g g') {L : ℝ³ → ℝ}
    (hL : IsDep t t' e e' g g' L) (h0 : L t = 0) :
    (L t' = 0 ∧ L e = 0 ∧ L e' = 0 ∧ L g = 0 ∧ L g' = 0) ∨
    (0 < L e * L e' ∧ 0 < L g * L g' ∧ L e * L g < 0) := by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, hte, hte', htg, htg'⟩, ⟨ht'e, ht'e', ht'g, ht'g'⟩, ⟨hee', heg, heg'⟩,
    ⟨he'g, he'g'⟩, hgg', -⟩ := hnd
  have r1 := hL.apply F.a'bc.hN
  rw [F.a'bc.hP, F.a'bc.hQ, F.a'bc.hR, h0] at r1
  have r2 := hL.apply F.a'bc'.hN
  rw [F.a'bc'.hP, F.a'bc'.hQ, F.a'bc'.hR, h0] at r2
  have r3 := hL.apply F.a'b'c.hN
  rw [F.a'b'c.hP, F.a'b'c.hQ, F.a'b'c.hR, h0] at r3
  have r4 := hL.apply F.a'b'c'.hN
  rw [F.a'b'c'.hP, F.a'b'c'.hQ, F.a'b'c'.hR, h0] at r4
  have n1e' := F.a'bc.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g
  have n1g' := F.a'bc.neg g' (by simp) (Ne.symm ht'g') (Ne.symm heg') (Ne.symm hgg')
  have n2e' := F.a'bc'.neg e' (by simp) (Ne.symm ht'e') (Ne.symm hee') he'g'
  have n2g := F.a'bc'.neg g (by simp) (Ne.symm ht'g) (Ne.symm heg) hgg'
  have n3e := F.a'b'c.neg e (by simp) (Ne.symm ht'e) hee' heg
  have n3g' := F.a'b'c.neg g' (by simp) (Ne.symm ht'g') (Ne.symm he'g') (Ne.symm hgg')
  have n4e := F.a'b'c'.neg e (by simp) (Ne.symm ht'e) hee' heg'
  have n4g := F.a'b'c'.neg g (by simp) (Ne.symm ht'g) (Ne.symm he'g) hgg'
  obtain ⟨s1, z1⟩ := pair_sign (L₁ := L e') (L₂ := L g') (by linarith) n1e' n1g'
  obtain ⟨s2, z2⟩ := pair_sign (L₁ := L e') (L₂ := L g) (by linarith) n2e' n2g
  obtain ⟨s3, z3⟩ := pair_sign (L₁ := L e) (L₂ := L g') (by linarith) n3e n3g'
  obtain ⟨s4, z4⟩ := pair_sign (L₁ := L e) (L₂ := L g) (by linarith) n4e n4g
  have hs := hL.sum
  rw [h0] at hs
  by_cases he' : L e' = 0
  · left
    have a1 := z1.mp he'; have a2 := z2.mp he'; have a4 := z4.mpr a2
    refine ⟨by linarith, a4, he', a2, a1⟩
  right
  have hg' : L g' ≠ 0 := fun h' => he' (z1.mpr h')
  have hg : L g ≠ 0 := fun h' => he' (z2.mpr h')
  have he : L e ≠ 0 := fun h' => hg (z4.mp h')
  have q1 : L e' * L g' < 0 := lt_of_le_of_ne s1 (mul_ne_zero he' hg')
  have q2 : L e' * L g < 0 := lt_of_le_of_ne s2 (mul_ne_zero he' hg)
  have q3 : L e * L g' < 0 := lt_of_le_of_ne s3 (mul_ne_zero he hg')
  have q4 : L e * L g < 0 := lt_of_le_of_ne s4 (mul_ne_zero he hg)
  refine ⟨?_, ?_, q4⟩
  · have := mul_pos_of_neg_of_neg q4 q2
    have hgg : 0 < L g * L g := mul_self_pos.mpr hg
    nlinarith
  · have := mul_pos_of_neg_of_neg q4 q3
    have hee : 0 < L e * L e := mul_self_pos.mpr he
    nlinarith

/-- Pole signs at the first pair, for every Gale datum: `[a b][a c] < 0`. -/
theorem pole_first {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (G : GaleData a a' b b' c c') :
    galeD G.l G.m a b * galeD G.l G.m a c < 0 := by
  have hl := G.hl; have hm := G.hm
  have ind := G.indep
  -- `l` and `m` are not identically zero on the six points
  have vz : ∀ L : ℝ³ → ℝ, IsDep a a' b b' c c' L → L a = 0 → ¬ (L a' = 0 ∧ L b = 0 ∧ L b' = 0 ∧ L c = 0 ∧ L c' = 0) →
      0 < L b * L b' ∧ 0 < L c * L c' ∧ L b * L c < 0 := by
    intro L hL h0 hnz
    rcases pole_signs_v F hL h0 with h | h
    · exact absurd ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩ hnz
    · exact h
  have hLa := hl.galeD hm a
  have h0 : galeD G.l G.m a a = 0 := galeD_self _ _ a
  rcases pole_signs_v F hLa h0 with h | h
  · exfalso
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [galeD] at h1 h2 h3 h4 h5
    have hz := ind (-G.m a) (G.l a) (by ring) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    obtain ⟨e1, e2⟩ := hz
    have la : G.l a = 0 := e2
    have ma : G.m a = 0 := by linarith
    -- l and m are nontrivial
    have lnz : ¬ (G.l a' = 0 ∧ G.l b = 0 ∧ G.l b' = 0 ∧ G.l c = 0 ∧ G.l c' = 0) := by
      rintro ⟨x1, x2, x3, x4, x5⟩
      have := ind 1 0 (by simp [la]) (by simp [x1]) (by simp [x2]) (by simp [x3]) (by simp [x4]) (by simp [x5])
      simp at this
    have mnz : ¬ (G.m a' = 0 ∧ G.m b = 0 ∧ G.m b' = 0 ∧ G.m c = 0 ∧ G.m c' = 0) := by
      rintro ⟨x1, x2, x3, x4, x5⟩
      have := ind 0 1 (by simp [ma]) (by simp [x1]) (by simp [x2]) (by simp [x3]) (by simp [x4]) (by simp [x5])
      simp at this
    have pl := vz G.l hl la lnz
    have pm := vz G.m hm ma mnz
    have lb : G.l b ≠ 0 := fun h => by have := pl.1; rw [h] at this; simp at this
    have mb : G.m b ≠ 0 := fun h => by have := pm.1; rw [h] at this; simp at this
    have hc := hl.comb hm (G.m b) (-G.l b)
    have hc0 : (G.m b * G.l a + -G.l b * G.m a) = 0 := by rw [la, ma]; ring
    rcases pole_signs_v F hc hc0 with h | h
    · have hb : G.m b * G.l b + -G.l b * G.m b = 0 := by ring
      -- all six vanish: use indep with (m b, -l b)
      obtain ⟨y1, y2, y3, y4, y5⟩ := h
      have := ind (G.m b) (-G.l b) (by linarith) (by linarith) hb (by linarith) (by linarith) (by linarith)
      exact mb this.1
    · have : 0 < (G.m b * G.l b + -G.l b * G.m b) * (G.m b * G.l b' + -G.l b * G.m b') := h.1
      have hb : G.m b * G.l b + -G.l b * G.m b = 0 := by ring
      rw [hb] at this; simp at this
  · have := h.2.2
    simpa [galeD] using this

end Minimality
