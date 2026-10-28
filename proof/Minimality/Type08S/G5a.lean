module

public import Minimality.Type08S.G4p

@[expose] public section

set_option autoImplicit true

/-!
# G5a: `slideN2a'` (and `slideQ`) as form U

`slideQ` is not needed at all in case Q (`G4p.lean`, `close_caseQ`).  For `slideN2a'` (the rim
`K_x = x p y' p'` of case N2, realized on both face circles `x y p` and `x y p'`): if `K_x` has no weak
saddle at `u = y - x` then the tilt `v = (x - p) + (x - p')` hides `y` and `m` (the zero tests are
`det3 (p - x) (y - x) v = det3 (x - p') (y - p') v = ρ`, `det3 (p - x) (m - x) v = (1 + δ - s) ρ`) and
`isRupert_of_tilted_unimodal_σ` with `NWS4` gives Rupert with ANY horizontal double normal.
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem sgn_mul {σ ρ X : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : 0 < σ * ρ) (hX : 0 < ρ * X) :
    0 < σ * X := by
  rcases hσ with rfl | rfl <;> nlinarith

theorem x_tilt_dets (x y p p' : ℝ³) (s δ : ℝ) (m : ℝ³)
    (hm : m = y + s • (p - y) + δ • (y - x)) :
    det3 (p - x) (y - x) ((x - p) + (x - p')) = det3 (p - y) (p' - y) (y - x) ∧
    det3 (x - p') (y - p') ((x - p) + (x - p')) = det3 (p - y) (p' - y) (y - x) ∧
    det3 (p - x) (m - x) ((x - p) + (x - p')) = (1 + δ - s) * det3 (p - y) (p' - y) (y - x) ∧
    det3 (p - x) (y - x) (y - x) = 0 ∧ det3 (x - p') (y - p') (y - x) = 0 ∧
    det3 (p - x) (m - x) (y - x) = 0 := by
  subst hm
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 1000000 in
/-- **K_x of case N2 as form U** (no `NoBadNormal`). -/
theorem isRupert_quad_edge_middle_x_formU {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = y + s • (p - y) + δ • (y - x))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (hN' : NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫)) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests_or F hq₁ hq₂
  set ρ := det3 (p - y) (p' - y) (y - x) with hρ_def
  have hρ : ρ ≠ 0 := quad_orient_ne F
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
  set u := y - x with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨s, δ, hs0, hs1, hδ, hm⟩ := hmid
  -- the tests at `u` of the rims `v p y' p'` (`v = y` or `v = x`)
  have hcyc : ∀ v, (v = y ∨ v = x) → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quad v p y' p' (i + 1) - quad v p y' p' i)
        (quad v p y' p' j - quad v p y' p' i) u := by
    intro v hv i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;>
    rcases hv with rfl | rfl
    · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
    · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
    · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    · exact E2 v my hyp hyy'
    · exact E2 v mx hxp hxy'
    · exact E3 v my hyy' hyp'
    · exact E3 v mx hxy' hxp'
    · exact E3 p mp (Ne.symm hy'p) hpp'
    · exact E3 p mp (Ne.symm hy'p) hpp'
    · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
    · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
    · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
  -- `x'` is strictly inside both rims
  have hx'in : ∀ v, (v = y ∨ v = x) → ∀ i : ZMod 4,
      0 < ρ * det3 (quad v p y' p' (i + 1) - quad v p y' p' i) (x' - quad v p y' p' i) u := by
    intro v hv i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;>
      rcases hv with rfl | rfl
    · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
    · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
    · exact E2 x' mx' hx'p hx'y'
    · exact E2 x' mx' hx'p hx'y'
    · exact E3 x' mx' hx'y' hx'p'
    · exact E3 x' mx' hx'y' hx'p'
    · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
    · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
  have hinjq : ∀ v, (v = y ∨ v = x) → Function.Injective (quad v p y' p') := by
    intro v hv
    rcases hv with rfl | rfl
    · exact quad_injective hyp hyy' hyp' (Ne.symm hy'p) hpp' hy'p'
    · exact quad_injective hxp hxy' hxp' (Ne.symm hy'p) hpp' hy'p'
  have hxVq : ∀ v, (v = y ∨ v = x) → ∀ i, quad v p y' p' i ∈ V := by
    intro v hv i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    · rcases hv with rfl | rfl <;> simp [V, quad_0]
    all_goals simp [V, quad_1, quad_2, quad_3]
  -- the points off the rim `v p y' p'` and off `{w, m}`: only `x'` (and `m` if kept)
  have hrestV : ∀ v w, ((v = y ∧ w = x) ∨ (v = x ∧ w = y)) → ∀ z ∈ V, z ≠ m → z ≠ w →
      (∀ j, z ≠ quad v p y' p' j) → z = x' := by
    intro v w hvw z hz hzm hzw hzx
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
    simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
    rcases hmemV z hz with h | h | h | h | h | h | h
    · exact absurd h hzm
    · rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd h hzw, absurd h h0]
    · exact h
    · rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd h h0, absurd h hzw]
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h3
  -- `m − x` in the face `x y p`
  have hmx' : m - x = (1 + δ - s) • u + s • (p - x) := by rw [hm]; simp only [u]; module
  obtain ⟨σ, hσ, hσρ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * ρ := by
    rcases lt_or_gt_of_ne hρ with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have hs : ∀ X, 0 < ρ * X → 0 < σ * X := fun X h => sgn_mul hσ hσρ h
  obtain ⟨T1, T2, T3, Z1, Z2, Z3⟩ := x_tilt_dets x y p p' s δ m hm
  rw [← hρ_def] at T1 T2 T3
  refine isRupert_of_tilted_unimodal_σ V u ((x - p) + (x - p')) hu (by norm_num) (quad x p y' p')
    (hxVq x (Or.inr rfl)) σ hσ ?_ ?_ NWS4 isOpen_NWS4 (fun z c hc hz => hz.mul hc.ne') ?_
    (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)
  · intro i j hi hj
    exact Or.inl (hs _ (hcyc x (Or.inr rfl) i j hi hj))
  · intro z hz hzx i
    by_cases hzm : z = m
    · rw [hzm]
      have e1 : 0 < 1 + δ - s := by linarith
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
      · exact TiltSignS.zero hσρ Z3 T3 e1
      · left
        have e2 : det3 (y' - p) (m - p) u = (1 - s) * det3 (y' - p) (y - p) u := by
          rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        apply hs; rw [e2]; have := E2 y my hyp hyy'; nlinarith
      · left
        have e3 : det3 (p' - y') (m - y') u =
            (1 - s) * det3 (p' - y') (y - y') u + s * det3 (p' - y') (p - y') u := by
          rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        apply hs; rw [e3]; have := E3 y my hyy' hyp'; have := E3 p mp (Ne.symm hy'p) hpp'; nlinarith
      · left
        have e4 : det3 (x - p') (m - p') u = s * det3 (y - p') (p - p') u := by
          rw [hm]; simp only [u, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        apply hs; rw [e4]; have := E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp); nlinarith
    · by_cases hzy : z = y
      · rw [hzy]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact TiltSignS.zero hσρ Z1 (by rw [T1, one_mul]) one_pos
        · exact Or.inl (hs _ (E2 y my hyp hyy'))
        · exact Or.inl (hs _ (E3 y my hyy' hyp'))
        · exact TiltSignS.zero hσρ Z2 (by rw [T2, one_mul]) one_pos
      · have hzx' : z = x' := hrestV x y (Or.inr ⟨rfl, rfl⟩) z hz hzm hzy hzx
        rw [hzx']; exact Or.inl (hs _ (hx'in x (Or.inr rfl) i))
  · have := eventually_NWS4_slide (e := (x - p) + (x - p')) hN'
    filter_upwards [this] with ε hε
    convert hε using 1
    funext i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [quad_0, quad_1, quad_2, quad_3]


/-- `isRupert_quad_edge_middle_slide` without `hsx` (the `K_x` closing by form U). -/
theorem isRupert_quad_edge_middle_slideA {x x' y y' p p' m : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (hmid : ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < δ ∧ m = y + s • (p - y) + δ • (y - x))
    (hmO : m ≠ x ∧ m ≠ x' ∧ m ≠ y ∧ m ≠ y' ∧ m ≠ p ∧ m ≠ p')
    (htouch : ¬ (⟪p, y - x⟫ = ⟪y', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫))
    (hsy : NoBadNormal (quad y p y' p') (y - x) (p - y) ∨
      (UniOrSep (quint y m p y' p') (y - x) ∧
        NoBadNormal (quint y m p y' p') (y - x) (p' - y))) :
    IsRupert (insert m {x, x', y, y', p, p'}) := by
  rcases hsy with hsy | ⟨hu5, hs5⟩
  swap
  · exact isRupert_quad_edge_middle_five F hq₁ hq₂ hmid hmO hu5 hs5
  by_cases hN : NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫)
  · exact isRupert_quad_edge_middle_sel F hq₁ hq₂ hmid hmO (Or.inl ⟨hN, hsy⟩)
  · exact isRupert_quad_edge_middle_x_formU F hq₁ hq₂ hmid hmO
      (nws4_closing_oct F hq₁ hq₂ hN hgood htouch)

/-- `Type08Gen` without the fields `levelQ`, `slideQ`, `slideN2a'` (not needed, `Type08Sp.close_caseQ`). -/
structure Type08GenNoQA (a a' b b' c c' d : ℝ³) : Prop where
  tieTT' : ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∧ ∃ r : ℝ, c' - a = r • (b - d))
  routeT : (∃ r : ℝ, c - a' = r • (b - d)) → RouteT a a' b b' c c' d
  routeT' : (∃ r : ℝ, c' - a = r • (b - d)) → RouteT' a a' b b' c c' d
  touchN2 : (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫) →
    Touch30N2 a a' b b' c c' d
  touchT4 : (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫) →
    Touch30T4 a a' b b' c c' d
  touchTie : (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫) →
    ¬ ((∃ r : ℝ, c - a' = r • (b - d)) ∨ ∃ r : ℝ, c' - a = r • (b - d))
  slideN2c : NoBadNormal (quad c b c' b') (c - a') (b - c) ∨
    (UniOrSep (quint c d b c' b') (c - a') ∧
      NoBadNormal (quint c d b c' b') (c - a') (b' - c)) ∨
    RdCond c d b c' b' a'
  slideT4b : NoBadNormal (quad b c' b' c) (b - d) (c - d) ∨
    (UniOrSep (quint b c' b' c a') (b - d) ∧
      NoBadNormal (quint b c' b' c a') (b - d) (a - d)) ∨
    RdCond b a' c b' c' d
  slideT4d : NoBadNormal (quad d c' b' c) (b - d) (a - d) ∨
    ((UniOrSep (quint d a c' b' c) (b - d) ∨
        (det3 (d - b) (c' - d) (b' - c) = 0 ∧
          ¬ NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) ∧
          ∀ i, ⟪quint d a c' b' c i, b - d⟫ ≠ ⟪quint d a c' b' c (i + 1), b - d⟫)) ∧
      NoBadNormal (quint d a c' b' c) (b - d) (c - d))
  flatN2 : det3 (c - b) (b' - b) (c' - b) = 0 →
      ¬ (⟪b, c - a'⟫ = ⟪b', c - a'⟫ ∧ ⟪c, c - a'⟫ = ⟪c', c - a'⟫)
  flatT4 : det3 (c - b) (b' - b) (c' - b) = 0 →
      ¬ (⟪b, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c, b - d⟫ = ⟪c', b - d⟫)

set_option maxHeartbeats 1000000 in
/-- `isRupert_type08_slide_core` (Type08Codim.lean) verbatim, with the case-Q branch replaced by
`Type08Sp.close_caseQ` (form U), `slideN2a'` by form U, `hgen` without `levelQ`, `slideQ`, `slideN2a'`. -/
theorem isRupert_type08_core_noQA {a a' b b' c c' d : ℝ³}
    (F : OctFacets a a' b b' c c') (hd : IsCap F d)
    (hN2 : F.abc'.f a' < F.abc'.f c → F.ab'c'.f a' < F.ab'c'.f c ∧
      ¬ max ⟪c, c - a'⟫ ⟪c', c - a'⟫ ≤ min ⟪b, c - a'⟫ ⟪b', c - a'⟫)
    (hT4 : F.abc'.f c < F.abc'.f a' → F.a'bc.f c' < F.a'bc.f a →
      ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hT_far : F.abc'.f a' = F.abc'.f c → F.a'bc.f c' < F.a'bc.f a)
    (hT'_far : F.a'bc.f c' = F.a'bc.f a → F.abc'.f a' ≠ F.abc'.f c → F.abc'.f c < F.abc'.f a')
    (hTgood : F.abc'.f a' = F.abc'.f c ∨ F.a'bc.f c' = F.a'bc.f a →
      ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (hsideN2 : 0 ≤ det3 (b - c) (c' - c) (b' - c) * det3 (b - c) (c' - c) (a' - c))
    (hsideT4 : det3 (c - b) (b' - b) (a' - b) * det3 (c - b) (b' - b) (c' - b) ≤ 0)
    (hgen : Type08GenNoQA a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  have hnd7 : [d, a, a', b, b', c, c'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
      ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', not_false⟩
  have hFc := F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
  have hFa := F.a'bc.neg a (by simp) haa' hab hac
  -- the coordinates in the frame `d; a, c, b`
  obtain ⟨hα, hβ, hαβ, hb'⟩ := hd.Qac_coords'
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  have hE := hd.det_Qac_ne
  by_cases htie₁ : F.abc'.f a' = F.abc'.f c
  · -- the tie `T` (Lemma X): `β₂ = 1`, and the far end of `Q_ab` is `c'`
    have hfc' := hT_far htie₁
    have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
    have hβ₂eq : F.abc'.f a' / F.abc'.f c = 1 := by rw [htie₁, div_self hFc.ne]
    have ha'1 := ha'
    rw [hβ₂eq, one_smul] at ha'1
    have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂eq.le
    exact isRupert_routeT hb' hc' ha'1 hnd7 hE hα hβ hαβ hα₁1 hβ₁ hα₂ hκ (hTgood (Or.inl htie₁))
      (fun ht => hgen.touchTie ht (Or.inl (hd.tieT_geom htie₁)))
      (hgen.routeT (hd.tieT_geom htie₁))
  by_cases htie₂ : F.a'bc.f c' = F.a'bc.f a
  · -- the tie `T'` (Lemma X): `α₁ = 1`, and the far end of `Q_bc` is `c`
    have hfc := hT'_far htie₂ htie₁
    have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
    have hα₁eq : F.a'bc.f c' / F.a'bc.f a = 1 := by rw [htie₂, div_self hFa.ne]
    have hc'1 := hc'
    rw [hα₁eq, one_smul] at hc'1
    exact isRupert_routeT' hb' hc'1 ha' hnd7 hE hα hβ hαβ hβ₁ hα₂ hβ₂ hβ₂1 hαβ₂
      (hTgood (Or.inr htie₂)) (fun ht => hgen.touchTie ht (Or.inr (hd.tieT'_geom htie₂)))
      (hgen.routeT' (hd.tieT'_geom htie₂))
  rcases lt_or_gt_of_ne htie₁ with hfar | hfc
  · -- case N2: the quad edge `a' → c` of `O`, with the cap `d` a middle of `Q_bc`
    obtain ⟨hq₂, hgood⟩ := hN2 hfar
    by_cases ht : (⟪b, c - a'⟫ = ⟪c', c - a'⟫ ∧ ⟪b', c - a'⟫ = ⟪c', c - a'⟫)
    · -- the far triple tie (Propositions 29.3, 30.4)
      exact isRupert_touchN2 F hd hfar hq₂ hgood ht (hgen.touchN2 ht)
    obtain ⟨s, δ, hs0, hs1, hδ, hdmid⟩ := hd.middle_Qbc hfar
    have e : (insert d ({a', a, c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} :=
      (type08_set_perm a a' b b' c c' d).1
    rw [← e]
    rcases hgen.slideN2c with hs | hs | hR
    · exact isRupert_quad_edge_middle_slideA (m := d) F.swap₁.perm₂₃ hfar hq₂ hgood
        ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ ht (Or.inl hs)
    · exact isRupert_quad_edge_middle_slideA (m := d) F.swap₁.perm₂₃ hfar hq₂ hgood
        ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ ht (Or.inr hs)
    · -- `R_d` (A.10): if `K_{a'}` has no weak saddle, slide it; otherwise Lemma R0 and the
      -- two-peaked five-corner rim along `a'b'c`
      by_cases hNx : NWS4 (quad ⟪a', c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫)
      · exact isRupert_quad_edge_middle_x_formU (m := d) F.swap₁.perm₂₃ hfar hq₂
          ⟨s, δ, hs0, hs1, hδ, hdmid⟩ ⟨hda', hda, hdc, hdc', hdb, hdb'⟩ hNx
      have hNy : NWS4 (quad ⟪c, c - a'⟫ ⟪b, c - a'⟫ ⟪c', c - a'⟫ ⟪b', c - a'⟫) := by
        by_contra hN
        exact hNx (nws4_closing_oct F.swap₁.perm₂₃ hfar hq₂ hN hgood ht)
      exact isRupert_quad_edge_middle_rdCond F.swap₁.perm₂₃ hfar hq₂ ⟨s, δ, hs0, hs1, hδ, hdmid⟩
        ⟨F.abc'.f, F.abc'.N, F.abc'.hN, hd.abc', F.abc'.hQ, F.abc'.hR,
          F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc',
          F.abc'.neg b' (by simp) (Ne.symm hab') (Ne.symm hbb') hb'c'⟩
        hsideN2 hNy hNx hR
  · have hβ₂1 : F.abc'.f a' / F.abc'.f c < 1 := (div_lt_one_of_neg hFc).mpr hfc
    by_cases hfa : F.a'bc.f a < F.a'bc.f c'
    · -- case Q: the far ends are `a` and `c`
      have hα₁1 : F.a'bc.f c' / F.a'bc.f a < 1 := (div_lt_one_of_neg hFa).mpr hfa
      exact Type08Sp.close_caseQ F hd hfc hfa
    · -- case T4: the far ends are `c'` and `c`
      have hfc' : F.a'bc.f c' < F.a'bc.f a := lt_of_le_of_ne (not_lt.mp hfa) htie₂
      have hα₁1 : 1 < F.a'bc.f c' / F.a'bc.f a := (one_lt_div_of_neg hFa).mpr hfc'
      have hκ := t4_kappa_pos hd hb' hc' ha' hα hβ₁ hα₂ hβ₂1.le
      have hgood := hT4 hfc hfc'
      by_cases ht : (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)
      · -- the far triple tie (Propositions 29.3, 30.4)
        exact isRupert_touchT4 F hd hfc hfc' hgood ht (hgen.touchT4 ht)
      have hsd := t4d_slide_of_par hb' hc' hdb hd.det_Qac_ne hα hα₁1 hβ₁ hgood hgen.slideT4d
      rcases hgen.slideT4b with hs | hs | hR
      · exact isRupert_t4_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1
          hαβ₂ hκ hgood ht (Or.inl hs) hsd
      · exact isRupert_t4_slide hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂ hβ₂1
          hαβ₂ hκ hgood ht (Or.inr hs) hsd
      · -- `R_d` (A.10): if `K_d` has no weak saddle, slide it; otherwise Lemma R0 and the
        -- two-peaked five-corner rim along `Q_ab`
        by_cases hNd : NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
        · rcases hsd with hs | ⟨hu5, hs5⟩
          · exact isRupert_t4_sel hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂
              hβ₂1 hαβ₂ hκ (Or.inr ⟨hNd, hs⟩)
          · exact isRupert_t4d_five hb' hc' ha' hnd7 hd.det_Qac_ne hα hβ hαβ hα₁1 hβ₁ hα₂ hβ₂
              hβ₂1 hκ hu5 hs5
        have hNb : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) := by
          by_contra hN
          exact hNd (t4_closing hb' hc' ha' hdb hd.det_Qac_ne hα hβ (by linarith) hβ₁ hκ hgood
            ht hN)
        exact isRupert_t4b_rdCond hb' hc' ha' hdb hd.det_Qac_ne hα hβ hα₁1 hβ₁ hβ₂ hβ₂1 hαβ₂ hκ
          ⟨F.a'b'c.f, F.a'b'c.N, F.a'b'c.hN, F.a'b'c.hP, F.a'b'c.hR, F.a'b'c.hQ,
            F.a'b'c.neg b (by simp) (Ne.symm ha'b) hbb' hbc,
            F.a'b'c.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hb'c') (Ne.symm hcc')⟩
          hsideT4 hNb hNd hR



theorem isRupert_type08_noQA_normalized {a a' b b' c c' d : ℝ³} (h : IsOctahedron a a' b b' c c')
    (F : OctFacets a a' b b' c c') (hd : IsCap F d) (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : 0 < galeD G.l G.m b b')
    (hκc : galeD G.l G.m c c' ≠ 0) (hU : galeD G.l G.m b c < 0)
    (hgen : Type08GenNoQA a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨-, -, -, -, -, -, -, ha'b, ha'b', -, -, -, -, hac, hac'⟩ :=
    type08_signs F G hκa hκb hκc hU
  have hsides := type08_rd_sides h G hκa ha'b ha'b' hac hac'
  exact isRupert_type08_core_noQA F hd (fun hfar => type08_lemma7 F G hκa hκb hκc hU hfar)
    (fun _ _ => type08_t4_not_bad h F hd G hκa hκb hκc hU hd.t4_opp)
    (type08_T_far F G hκb hκc hU) (type08_T'_far F G hκb hκc hU)
    (fun _ => type08_t4_not_bad h F hd G hκa hκb hκc hU hd.t4_opp) hsides.1.le hsides.2.le hgen

namespace Type08Sp

/-- Shorthand for the common hypotheses of a single-field closure (as in `G5_Slides.lean`; G5b should
import this file instead of redefining). -/
def Single08 (a a' b b' c c' d : ℝ³) (f : F08) : Prop :=
  ¬ IsT a' b c d ∧ ¬ IsT' a b c' d ∧ ¬ FP a a' b b' c c' d f ∧
    ∀ g, g ≠ f → FP a a' b b' c c' d g

theorem noQA_of_FP {a a' b b' c c' d : ℝ³}
    (h : ∀ f, f ≠ .levelQ → f ≠ .slideQ → f ≠ .slideN2a' → FP a a' b b' c c' d f) :
    Type08GenNoQA a a' b b' c c' d :=
  ⟨h .tieTT (by simp) (by simp) (by simp), h .routeT (by simp) (by simp) (by simp),
   h .routeT' (by simp) (by simp) (by simp), h .touchN2 (by simp) (by simp) (by simp),
   h .touchT4 (by simp) (by simp) (by simp), h .touchTie (by simp) (by simp) (by simp),
   h .slideN2c (by simp) (by simp) (by simp), h .slideT4b (by simp) (by simp) (by simp),
   h .slideT4d (by simp) (by simp) (by simp), h .flatN2 (by simp) (by simp) (by simp),
   h .flatT4 (by simp) (by simp) (by simp)⟩

/-- **G5a, `slideQ`**: case Q needs no slide field (`close_caseQ`); `hT`, `hT'`, the failure of
`slideQ` and the field `slideN2a'` are not used. -/
theorem close_slideQ {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : Single08 a a' b b' c c' d .slideQ) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  isRupert_type08_noQ_normalized N.F.isOctahedron N.F N.hd N.G N.hκa N.hκb N.hκc N.hU
    (noQ_of_FP fun f h1 h2 => h.2.2.2 f h2)

/-- **G5a, `slideN2a'`**: the closing `K_{a'}` of case N2 is realized on both circles, so form U
(`isRupert_quad_edge_middle_x_formU`) applies with any horizontal double normal; `slideQ` and
`levelQ` are not used either (here they are true, but case Q is handled by `close_caseQ`). -/
theorem close_slideN2a' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    (h : Single08 a a' b b' c c' d .slideN2a') :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) :=
  isRupert_type08_noQA_normalized N.F.isOctahedron N.F N.hd N.G N.hκa N.hκb N.hκc N.hU
    (noQA_of_FP fun f h1 h2 h3 => h.2.2.2 f h3)

end Type08Sp

end Minimality
