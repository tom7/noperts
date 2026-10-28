module

public import Minimality.Type08S.Defs08

@[expose] public section

set_option autoImplicit true

/-!
# Group G1: the labelling refinement (`Type08Gen` only in the labelling Lemma 6 uses)

Paper: nothing new (§29 table: "the other five labellings are not exceptions").  Lean template:
`isRupert_type08_slide_gale`, `isRupert_type08_flat` (`Type08Codim.lean`, `Type08Flat.lean`).
Size: S-M (the first theorem is a copy of `isRupert_type08_slide_gale` with the six
`g_i` taken from `GenSel`; the second is the same for `isRupert_type08_flat`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The sign data of one labelling of Lemma 6, `(p,p'), (q,q')` and the third pair's `r`. -/
def LabSign (D : ℝ³ → ℝ³ → ℝ) (σ : ℝ) (p p' q q' r : ℝ³) : Prop :=
  0 < σ * D p p' ∧ 0 < σ * D q q' ∧ σ * D q r < 0

/-- `Type08Gen` in exactly the labellings that the Gale signs select (as `type08_lemma6`). -/
def GenSel {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (d : ℝ³) : Prop :=
  ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
    (LabSign (galeD G.l G.m) σ a a' b b' c → Type08Gen a a' b b' c c' d) ∧
    (LabSign (galeD G.l G.m) σ b b' a a' c → Type08Gen b b' a a' c c' d) ∧
    (LabSign (galeD G.l G.m) σ a a' c c' b → Type08Gen a a' c c' b b' d) ∧
    (LabSign (galeD G.l G.m) σ c c' a a' b → Type08Gen c c' a a' b b' d) ∧
    (LabSign (galeD G.l G.m) σ b b' c c' a → Type08Gen b b' c c' a a' d) ∧
    (LabSign (galeD G.l G.m) σ c c' b b' a → Type08Gen c c' b b' a a' d)

theorem GenSel.of_all {a a' b b' c c' d : ℝ³} (G : GaleData a a' b b' c c')
    (h : Type08GenAll a a' b b' c c' d) : GenSel G d := fun _ _ =>
  ⟨fun _ => h.1, fun _ => h.2.1, fun _ => h.2.2.1, fun _ => h.2.2.2.1, fun _ => h.2.2.2.2.1,
    fun _ => h.2.2.2.2.2⟩

/-- **Theorem 10.1′, Gale form, labelling-in-use version** (planar equators excluded). -/
theorem isRupert_type08_slide_gale_sel {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d) (G : GaleData a a' b b' c c') (hκa : galeD G.l G.m a a' ≠ 0)
    (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0)
    (hgen : GenSel G d) : IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have h := F.isOctahedron
  obtain ⟨-, -, hA⟩ := pole_signs F (G.hl.galeD G.hm a) (galeD_self _ _ a) hκa
  obtain ⟨-, -, hB⟩ := pole_signs F.perm₁₂ (G.hl.galeD G.hm b).perm₁₂ (galeD_self _ _ b) hκb
  obtain ⟨-, -, hC⟩ := pole_signs F.perm₂₃.perm₁₂ (G.hl.galeD G.hm c).perm₂₃.perm₁₂
    (galeD_self _ _ c) hκc
  obtain ⟨σ, hσ, hcases⟩ := type08_lemma6 hκa hκb hκc hA hB hC
  obtain ⟨G', hG'⟩ : ∃ G' : GaleData a a' b b' c c',
      ∀ s t, galeD G'.l G'.m s t = σ * galeD G.l G.m s t := by
    rcases hσ with rfl | rfl
    · exact ⟨G, fun s t => (one_mul _).symm⟩
    · exact ⟨G.mirror, fun s t => by rw [G.galeD_mirror]; ring⟩
  have hne : ∀ s t, galeD G.l G.m s t ≠ 0 → galeD G'.l G'.m s t ≠ 0 := by
    intro s t hst; rw [hG']; rcases hσ with rfl | rfl <;> simpa using hst
  have hpos : ∀ s t, 0 < σ * galeD G.l G.m s t → 0 < galeD G'.l G'.m s t := by
    intro s t h; rwa [hG']
  have hneg : ∀ s t, σ * galeD G.l G.m s t < 0 → galeD G'.l G'.m s t < 0 := by
    intro s t h; rwa [hG']
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen σ hσ
  have e := type08_set_perm a a' b b' c c' d
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact isRupert_type08_slide_normalized h F hd G' (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκc)
      (hneg _ _ h3) (g1 ⟨h1, h2, h3⟩)
  · rw [← e.2.1]
    exact isRupert_type08_slide_normalized h.perm₁₂ F.perm₁₂ hd.perm₁₂ G'.perm₁₂ (hpos _ _ h1)
      (hpos _ _ h2) (hne _ _ hκc) (hneg _ _ h3) (g2 ⟨h1, h2, h3⟩)
  · rw [← e.2.2.1]
    exact isRupert_type08_slide_normalized h.perm₂₃ F.perm₂₃ hd.perm₂₃ G'.perm₂₃ (hpos _ _ h1)
      (hpos _ _ h2) (hne _ _ hκb) (hneg _ _ h3) (g3 ⟨h1, h2, h3⟩)
  · rw [← e.2.2.2.1]
    exact isRupert_type08_slide_normalized h.perm₂₃.perm₁₂ F.perm₂₃.perm₁₂ hd.perm₂₃.perm₁₂
      G'.perm₂₃.perm₁₂ (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκb) (hneg _ _ h3) (g4 ⟨h1, h2, h3⟩)
  · rw [← e.2.2.2.2.1]
    exact isRupert_type08_slide_normalized h.perm₁₂.perm₂₃ F.perm₁₂.perm₂₃ hd.perm₁₂.perm₂₃
      G'.perm₁₂.perm₂₃ (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκa) (hneg _ _ h3) (g5 ⟨h1, h2, h3⟩)
  · rw [← e.2.2.2.2.2]
    exact isRupert_type08_slide_normalized h.perm₁₂.perm₂₃.perm₁₂ F.perm₁₂.perm₂₃.perm₁₂
      hd.perm₁₂.perm₂₃.perm₁₂ G'.perm₁₂.perm₂₃.perm₁₂ (hpos _ _ h1) (hpos _ _ h2) (hne _ _ hκa)
      (hneg _ _ h3) (g6 ⟨h1, h2, h3⟩)

/-- Weak sign condition for a pair of equators at the Gale sign `σ`: both `≥ 0` and at least one
`> 0`.  (D7: `isRupert_type08_flat` uses, at a planar equator `κ_p = 0`, both orders `(p,q)` and
`(q,p)` of the labelling with `σκ_q > 0`, so the condition must be symmetric; the earlier
`0 ≤ σκ_p ∧ 0 < σκ_q` version in the second clause of each pair demanded `0 < σκ_p` too.) -/
def WS (x y : ℝ) : Prop := 0 ≤ x ∧ 0 ≤ y ∧ (0 < x ∨ 0 < y)

/-- `Type08Gen` in the labellings used by `isRupert_type08_flat` (and, at no planar equator,
by `type08_lemma6`). -/
def GenSelFlat {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (d : ℝ³) : Prop :=
  ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
    (WS (σ * galeD G.l G.m a a') (σ * galeD G.l G.m b b') → Type08Gen a a' b b' c c' d) ∧
    (WS (σ * galeD G.l G.m b b') (σ * galeD G.l G.m a a') → Type08Gen b b' a a' c c' d) ∧
    (WS (σ * galeD G.l G.m a a') (σ * galeD G.l G.m c c') → Type08Gen a a' c c' b b' d) ∧
    (WS (σ * galeD G.l G.m c c') (σ * galeD G.l G.m a a') → Type08Gen c c' a a' b b' d) ∧
    (WS (σ * galeD G.l G.m b b') (σ * galeD G.l G.m c c') → Type08Gen b b' c c' a a' d) ∧
    (WS (σ * galeD G.l G.m c c') (σ * galeD G.l G.m b b') → Type08Gen c c' b b' a a' d)

theorem GenSelFlat.of_all {a a' b b' c c' d : ℝ³} (G : GaleData a a' b b' c c')
    (h : Type08GenAll a a' b b' c c' d) : GenSelFlat G d := fun _ _ =>
  ⟨fun _ => h.1, fun _ => h.2.1, fun _ => h.2.2.1, fun _ => h.2.2.2.1, fun _ => h.2.2.2.2.1,
    fun _ => h.2.2.2.2.2⟩

theorem isRupert_type08_flat_sel {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap F d)
    (hflat : ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (c - a) (a' - a) (c' - a) = 0) ∧
      ¬ (det3 (c - b) (b' - b) (c' - b) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0) ∧
      ¬ (det3 (c - a) (a' - a) (c' - a) = 0 ∧ det3 (b - a) (a' - a) (b' - a) = 0))
    (G : GaleData a a' b b' c c') (hgen : GenSelFlat G d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  obtain ⟨hf1, hf2, hf3⟩ := hflat
  have pA : galeD G.l G.m a a' = 0 → det3 (c - b) (b' - b) (c' - b) = 0 := G.planar_of_kappa
  have pB : galeD G.l G.m b b' = 0 → det3 (c - a) (a' - a) (c' - a) = 0 :=
    G.perm₁₂.planar_of_kappa
  have pC : galeD G.l G.m c c' = 0 → det3 (b - a) (a' - a) (b' - a) = 0 :=
    G.perm₂₃.perm₁₂.planar_of_kappa
  have e := type08_set_perm a a' b b' c c' d
  -- mirror the Gale vectors so that a given `κ` is positive; remember the sign
  have mirror : ∀ (s t : ℝ³), galeD G.l G.m s t ≠ 0 → ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ G' : GaleData a a' b b' c c', (∀ x y, galeD G'.l G'.m x y = σ * galeD G.l G.m x y) ∧
        0 < galeD G'.l G'.m s t := by
    intro s t hst
    rcases lt_or_gt_of_ne hst with hn | hp
    · exact ⟨-1, Or.inr rfl, G.mirror, fun x y => by rw [G.galeD_mirror]; ring,
        by rw [G.galeD_mirror]; linarith⟩
    · exact ⟨1, Or.inl rfl, G, fun x y => (one_mul _).symm, hp⟩
  by_cases ha : galeD G.l G.m a a' = 0
  · have hb : galeD G.l G.m b b' ≠ 0 := fun h => hf1 ⟨pA ha, pB h⟩
    have hc : galeD G.l G.m c c' ≠ 0 := fun h => hf2 ⟨pA ha, pC h⟩
    obtain ⟨σ, hσ, G', hG', hb'⟩ := mirror b b' hb
    have ha' : galeD G'.l G'.m a a' = 0 := by rw [hG', ha]; ring
    have hc' : galeD G'.l G'.m c c' ≠ 0 := by
      rw [hG']; rcases hσ with rfl | rfl <;> simpa using hc
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen σ hσ
    have w1 : WS (σ * galeD G.l G.m a a') (σ * galeD G.l G.m b b') := by
      rw [← hG', ← hG']; exact ⟨ha'.symm.le, hb'.le, Or.inr hb'⟩
    have w2 : WS (σ * galeD G.l G.m b b') (σ * galeD G.l G.m a a') := by
      rw [← hG', ← hG']; exact ⟨hb'.le, ha'.symm.le, Or.inl hb'⟩
    obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G'.hl.galeD G'.hm c).perm₂₃.perm₁₂
      (galeD_self _ _ c) hc'
    rcases lt_or_ge (galeD G'.l G'.m b c) 0 with hU | hU
    · exact isRupert_type08_flatA F hd G' ha' hb' hc' hU (g1 w1)
    · have hU' : galeD G'.l G'.m a c < 0 := by
        rw [galeD_anti _ _ a c, galeD_anti _ _ b c] at c3; nlinarith
      rw [← e.2.1]
      exact isRupert_type08_flatB F.perm₁₂ hd.perm₁₂ G'.perm₁₂ hb' ha' hc' hU' (g2 w2)
  · by_cases hb : galeD G.l G.m b b' = 0
    · have hc : galeD G.l G.m c c' ≠ 0 := fun h => hf3 ⟨pB hb, pC h⟩
      obtain ⟨σ, hσ, G', hG', ha'⟩ := mirror a a' ha
      have hb' : galeD G'.l G'.m b b' = 0 := by rw [hG', hb]; ring
      have hc' : galeD G'.l G'.m c c' ≠ 0 := by
        rw [hG']; rcases hσ with rfl | rfl <;> simpa using hc
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen σ hσ
      have w1 : WS (σ * galeD G.l G.m a a') (σ * galeD G.l G.m b b') := by
        rw [← hG', ← hG']; exact ⟨ha'.le, hb'.symm.le, Or.inl ha'⟩
      have w2 : WS (σ * galeD G.l G.m b b') (σ * galeD G.l G.m a a') := by
        rw [← hG', ← hG']; exact ⟨hb'.symm.le, ha'.le, Or.inr ha'⟩
      obtain ⟨-, -, c3⟩ := pole_signs F.perm₂₃.perm₁₂ (G'.hl.galeD G'.hm c).perm₂₃.perm₁₂
        (galeD_self _ _ c) hc'
      rcases lt_or_ge (galeD G'.l G'.m a c) 0 with hU | hU
      · rw [← e.2.1]
        exact isRupert_type08_flatA F.perm₁₂ hd.perm₁₂ G'.perm₁₂ hb' ha' hc' hU (g2 w2)
      · have hU' : galeD G'.l G'.m b c < 0 := by
          rw [galeD_anti _ _ a c, galeD_anti _ _ b c] at c3; nlinarith
        exact isRupert_type08_flatB F hd G' ha' hb' hc' hU' (g1 w1)
    · by_cases hc : galeD G.l G.m c c' = 0
      · obtain ⟨σ, hσ, G', hG', ha'⟩ := mirror a a' ha
        have hb' : galeD G'.l G'.m b b' ≠ 0 := by
          rw [hG']; rcases hσ with rfl | rfl <;> simpa using hb
        have hc' : galeD G'.l G'.m c c' = 0 := by rw [hG', hc]; ring
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen σ hσ
        have w3 : WS (σ * galeD G.l G.m a a') (σ * galeD G.l G.m c c') := by
          rw [← hG', ← hG']; exact ⟨ha'.le, hc'.symm.le, Or.inl ha'⟩
        have w4 : WS (σ * galeD G.l G.m c c') (σ * galeD G.l G.m a a') := by
          rw [← hG', ← hG']; exact ⟨hc'.symm.le, ha'.le, Or.inr ha'⟩
        obtain ⟨-, -, b3⟩ := pole_signs F.perm₁₂ (G'.hl.galeD G'.hm b).perm₁₂
          (galeD_self _ _ b) hb'
        rcases lt_or_ge (galeD G'.l G'.m a b) 0 with hU | hU
        · rw [← e.2.2.2.1]
          exact isRupert_type08_flatA F.perm₂₃.perm₁₂ hd.perm₂₃.perm₁₂ G'.perm₂₃.perm₁₂ hc' ha'
            hb' hU (g4 w4)
        · have hU' : galeD G'.l G'.m c b < 0 := by
            rw [galeD_anti _ _ a b, galeD_anti _ _ c b] at b3; nlinarith
          rw [← e.2.2.1]
          exact isRupert_type08_flatB F.perm₂₃ hd.perm₂₃ G'.perm₂₃ ha' hc' hb' hU' (g3 w3)
      · refine isRupert_type08_slide_gale_sel F hd G ha hb hc ?_
        intro σ hσ
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgen σ hσ
        have ws : ∀ x y : ℝ, 0 < x → 0 < y → WS x y := fun x y hx hy =>
          ⟨hx.le, hy.le, Or.inl hx⟩
        exact ⟨fun h => g1 (ws _ _ h.1 h.2.1), fun h => g2 (ws _ _ h.1 h.2.1),
          fun h => g3 (ws _ _ h.1 h.2.1), fun h => g4 (ws _ _ h.1 h.2.1),
          fun h => g5 (ws _ _ h.1 h.2.1), fun h => g6 (ws _ _ h.1 h.2.1)⟩

end Type08Sp
end Minimality
