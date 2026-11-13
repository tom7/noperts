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

namespace Type08Sp

end Type08Sp

end Minimality
