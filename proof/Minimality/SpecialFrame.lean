module

public import Minimality.TriTie
public import Minimality.ParallelFacets
public import Minimality.EdgeChord
public import Minimality.TriFacetsChord

@[expose] public section

/-!
# Frames for the special value of Lemma T′ (`FEWER-FACES-PROOFS.md` §23, §24)

At the special value of the types 05, 10, 13, 17, 19, 23, 27 the common view has a
triangle shadow with three edge-on faces, and one corner carries a vertical edge.
Theorem 23.18 reads Lemma T′ at each corner. This file has the frame and coordinate
lemmas for those readings:

- `isRupert_triShadow2_gen_tilt`: Lemma T over an edge (two vertices over the apex)
  with a general mixed tilt and the modes of `isRupert_triShadow2_gen`, so that the far
  ends may tie while points on the far side are hidden by the tilt ratio;
- `edge_core_gen_chord`, `isRupert_edge_coords_mode_chord`: Lemma T′ over an edge with
  the far ends tied, when the far end of the first face is its strict top (or bottom),
  with points on the far side;
- `vertex_core_parc`, `isRupert_vertex_coords_parc`: Lemma T′ at a vertex with a vertical
  edge over a far corner (the Extension of §7 in the mixed sectors where the vertical
  edge's other end is hidden), points on the far side on the side that the tilt hides.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, general mixed tilt, the tie allowed.** As `isRupert_triShadow2_tilt` with the modes of `isRupert_triShadow2_gen` in place of `s z_B < s z_A`. -/
theorem isRupert_triShadow2_gen_tilt (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hap : s * dz 0 < s * cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) a b z (-s * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 (cz m) ∨ y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (a = 0 → b = 0 → y = oblPt O r1 r2 (ca 0) 0 (cz 0) ∨ y = oblPt O r1 r2 0 (cb 0) (dz 0)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0))
    (hmode : s * dz n < s * cz m ∨ (∀ l, l < m → s * cz l < s * cz (l + 1)) ∨
      (∀ j, j < n → s * dz (j + 1) < s * dz j)) : IsRupert V := by
  have hNZ : NeZero (m + n + 2) := ⟨by omega⟩
  have hval : ∀ v : ℕ, v < m + n + 2 → ((v : ZMod (m + n + 2))).val = v := fun v hv => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv]
  set x : ZMod (m + n + 2) → ℝ³ := fun i => triPt2 O r1 r2 m n ca cz cb dz i.val with hx
  have hxC1 : ∀ v, v ≤ m → x (v : ZMod (m + n + 2)) = oblPt O r1 r2 (ca v) 0 (cz v) := by
    intro v hv; simp only [hx, hval v (by omega), triPt2, hv, ite_true]
  have hxC2 : ∀ l, l ≤ n → x ((m + n + 1 - l : ℕ) : ZMod (m + n + 2)) =
      oblPt O r1 r2 0 (cb l) (dz l) := by
    intro l hl
    simp only [hx, hval (m + n + 1 - l) (by omega), triPt2,
      show ¬ m + n + 1 - l ≤ m by omega, ite_false]
    rw [show m + n + 1 - (m + n + 1 - l) = l by omega]
  have hdepth : ∀ i : ZMod (m + n + 2), ⟪x i, ez⟫ = triZ2 m n cz dz i.val := by
    intro i; simp only [hx, triPt2, triZ2]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  -- monotonicity of the chains
  have mono : ∀ (f : ℕ → ℝ) (k : ℕ), (∀ l, l < k → f l < f (l + 1)) →
      ∀ i j, i < j → j ≤ k → f i < f j := by
    intro f k hf i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (hf j (by omega))
      · subst h; exact hf i (by omega)
  have hxV : ∀ i, x i ∈ V := by
    intro i; simp only [hx, triPt2]; split_ifs with h
    · exact hC1V _ h
    · exact hC2V _ (by have := ZMod.val_lt i; omega)
  -- distinct positions carry distinct points
  have hxinj : Function.Injective x := by
    intro i j he
    by_contra hij
    have hv : i.val ≠ j.val := fun h => hij (ZMod.val_injective _ h)
    have hi := ZMod.val_lt i; have hj := ZMod.val_lt j
    simp only [hx, triPt2] at he
    split_ifs at he with h1 h2 h2
    · have := (oblPt_inj hρ he).1
      rcases Nat.lt_or_gt_of_ne hv with h | h
      · exact absurd this (mono ca m hca _ _ h h2).ne
      · exact absurd this (mono ca m hca _ _ h h1).ne'
    · obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
      rcases Nat.eq_zero_or_pos (m + n + 1 - j.val) with h0 | h0
      · rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
        · rw [hi0, h0] at ez'; rw [ez'] at hap; exact lt_irrefl _ hap
        · have := mono ca m hca 0 i.val hi0 h1; rw [hca0, ea] at this; linarith
      · have := mono cb n hcb 0 _ h0 (by omega); rw [hcb0] at this; linarith
    · obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
      rcases Nat.eq_zero_or_pos (m + n + 1 - i.val) with h0 | h0
      · rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
        · rw [hj0, h0] at ez'; rw [← ez'] at hap; exact lt_irrefl _ hap
        · have := mono ca m hca 0 j.val hj0 h2; rw [hca0, ← ea] at this; linarith
      · have := mono cb n hcb 0 _ h0 (by omega); rw [hcb0] at this; linarith
    · have := (oblPt_inj hρ he).2.1
      rcases Nat.lt_or_gt_of_ne hv with h | h
      · exact absurd this (mono cb n hcb _ _ (by omega) (by omega)).ne'
      · exact absurd this (mono cb n hcb _ _ (by omega) (by omega)).ne
  -- the tilt
  set v : ℝ³ := oblPt 0 r1 r2 (-s * α) (s * β) 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ},
      TiltOK ap bp zp aq bq zq ay by' zy (-s * α) (s * β) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (-s * α) (s * β) h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (-s * α) (s * β) := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      s * ((bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (-s * α) (s * β) := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases hs with rfl | rfl
    · right; exact ⟨by linarith, by linarith⟩
    · left; exact ⟨by linarith, by linarith⟩
  have tests : ∀ y ∈ V, ∀ i : ZMod (m + n + 2), y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ez v := by
    intro y hy i hyi hyi1
    obtain ⟨a, b, z, rfl, ha, hb, hin, hap0, hr1, hr2⟩ := hVc y hy
    obtain ⟨w, hwlt, rfl⟩ : ∃ w, w < m + n + 2 ∧ (w : ZMod (m + n + 2)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    have hsucc : ((w : ZMod (m + n + 2)) + 1) = ((w + 1 : ℕ) : ZMod (m + n + 2)) := by simp
    rw [hsucc] at hyi1 ⊢
    rcases Nat.lt_or_ge w m with h1 | h1
    · rw [hxC1 w h1.le] at hyi ⊢
      rw [hxC1 (w + 1) h1] at hyi1 ⊢
      apply key
      rcases hb.lt_or_eq with hb | hb
      · exact tiltOK_side1_off (hca _ h1) hb
      · subst hb; exact side1 (hr1 rfl _ h1 hyi hyi1)
    rcases Nat.lt_or_ge w (m + 1) with h2 | h2
    · have hwm : w = m := by omega
      subst w
      have e1 : x ((m + 1 : ℕ) : ZMod (m + n + 2)) = oblPt O r1 r2 0 (cb n) (dz n) := by
        rw [show m + 1 = m + n + 1 - n by omega, hxC2 n le_rfl]
      rw [hxC1 m le_rfl] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases hin with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    rcases Nat.lt_or_ge w (m + n + 1) with h3 | h3
    · -- a segment of `C2`, inward
      obtain ⟨l, hln, rfl⟩ : ∃ l, l < n ∧ m + n - l = w := ⟨m + n - w, by omega, by omega⟩
      rw [show m + n - l = m + n + 1 - (l + 1) by omega] at hyi hyi1 ⊢
      rw [hxC2 (l + 1) (by omega)] at hyi ⊢
      rw [show m + n + 1 - (l + 1) + 1 = m + n + 1 - l by omega, hxC2 l hln.le] at hyi1 ⊢
      apply key
      rcases ha.lt_or_eq with ha | ha
      · exact tiltOK_side2_off (hcb _ hln) ha
      · subst ha; exact side2 (hr2 rfl _ hln hyi hyi1)
    · -- the vertical edge from `C2 0` up to `C1 0`
      have hwk : w = m + n + 1 := by omega
      subst w
      rw [show m + n + 1 = m + n + 1 - 0 by omega] at hyi hyi1 ⊢
      rw [hxC2 0 (Nat.zero_le _)] at hyi ⊢
      have e1 : x ((m + n + 1 - 0 + 1 : ℕ) : ZMod (m + n + 2)) = oblPt O r1 r2 (ca 0) 0 (cz 0) := by
        rw [show m + n + 1 - 0 + 1 = m + n + 2 by omega, ZMod.natCast_self,
          show (0 : ZMod (m + n + 2)) = ((0 : ℕ) : ZMod (m + n + 2)) by simp]
        exact hxC1 0 (Nat.zero_le _)
      rw [e1] at hyi1 ⊢
      rw [hca0] at hyi1 ⊢; rw [hcb0] at hyi ⊢
      apply key
      apply vert_tiltOK_tilt hα hβ (by linarith) ha hb
      by_contra hpos
      have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      rcases hap0 ha0 hb0 with e | e
      · rw [hca0] at e; exact hyi1 (by rw [← e, ha0, hb0])
      · rw [hcb0] at e; exact hyi (by rw [← e, ha0, hb0])
  have hcyc : ∀ i j : ZMod (m + n + 2), j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez v := by
    intro i j h1 h2
    exact tests (x j) (hxV j) i (fun h => h1 (hxinj h)) (fun h => h2 (hxinj h))
  have hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) ez v :=
    fun y hy hyx i => tests y hy i (hyx i) (hyx (i + 1))
  -- the depths are unimodal
  set Z : ZMod (m + n + 2) → ℝ := fun i => triZ2 m n cz dz i.val with hZ
  have hZpos : ∀ l, l < m + n + 2 → Z (l : ZMod (m + n + 2)) = triZ2 m n cz dz l := by
    intro l hl; simp only [hZ, hval l hl]
  have hZ1 : ∀ l, l ≤ m → Z (l : ZMod (m + n + 2)) = cz l := by
    intro l hl; rw [hZpos l (by omega)]; simp [triZ2, hl]
  have hZ2 : ∀ l, m + 1 ≤ l → l ≤ m + n + 1 → Z (l : ZMod (m + n + 2)) = dz (m + n + 1 - l) := by
    intro l h1 h2; rw [hZpos l (by omega)]; simp [triZ2, show ¬ l ≤ m by omega]
  have hZk : Z ((m + n + 2 : ℕ) : ZMod (m + n + 2)) = cz 0 := by
    rw [ZMod.natCast_self, show (0 : ZMod (m + n + 2)) = ((0 : ℕ) : ZMod (m + n + 2)) by simp,
      hZ1 0 (Nat.zero_le _)]
  have coords1 : ∀ l, l ≤ m → ∀ j, j < m → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca j) 0 (cz j) → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca (j + 1)) 0 (cz (j + 1)) →
      s * ((ca (j + 1) - ca j) * (cz l - cz j) - (cz (j + 1) - cz j) * (ca l - ca j)) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, hr1, -⟩ := hVc _ (hC1V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst ea ez'
    exact hr1 eb.symm j hj (he ▸ h1) (he ▸ h2)
  have coords2 : ∀ l, l ≤ n → ∀ j, j < n → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb (j + 1)) (dz (j + 1)) → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb j) (dz j) →
      s * ((cb j - cb (j + 1)) * (dz l - dz (j + 1)) - (dz j - dz (j + 1)) * (cb l - cb (j + 1))) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, -, hr2⟩ := hVc _ (hC2V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst eb ez'
    exact hr2 ea.symm j hj (he ▸ h1) (he ▸ h2)
  have ne1 : ∀ i j, i ≤ m → j ≤ m → i ≠ j →
      oblPt O r1 r2 (ca i) 0 (cz i) ≠ oblPt O r1 r2 (ca j) 0 (cz j) := by
    intro i j hi hj hij he
    have := (oblPt_inj hρ he).1
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact absurd this (mono ca m hca i j h hj).ne
    · exact absurd this (mono ca m hca j i h hi).ne'
  have ne2 : ∀ i j, i ≤ n → j ≤ n → i ≠ j →
      oblPt O r1 r2 0 (cb i) (dz i) ≠ oblPt O r1 r2 0 (cb j) (dz j) := by
    intro i j hi hj hij he
    have := (oblPt_inj hρ he).2.1
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact absurd this (mono cb n hcb i j h hj).ne
    · exact absurd this (mono cb n hcb j i h hi).ne'
  -- the sequence lemma's hypotheses for `s Z` (strict, so they survive the tilt)
  have hconcZ : ∀ l : ℕ, 1 ≤ l → l < m → min (s * Z ((l - 1 : ℕ) : ZMod (m + n + 2)))
      (s * Z ((l + 1 : ℕ) : ZMod (m + n + 2))) < s * Z (l : ZMod (m + n + 2)) := by
    intro l h1 h2
    rw [hZ1 _ (by omega), hZ1 _ (by omega), hZ1 _ (by omega)]
    have hc := coords1 (l + 1) (by omega) (l - 1) (by omega)
      (ne1 _ _ (by omega) (by omega) (by omega))
      (by rw [show l - 1 + 1 = l by omega]; exact ne1 _ _ (by omega) (by omega) (by omega))
    rw [show l - 1 + 1 = l by omega] at hc
    have d1 := mono ca m hca (l - 1) l (by omega) (by omega)
    have d2 := mono ca m hca l (l + 1) (by omega) (by omega)
    by_contra hcon
    push Not at hcon
    rw [le_min_iff] at hcon
    nlinarith [mul_nonneg (sub_nonneg.mpr d1.le) (sub_nonneg.mpr (hcon.2)),
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hcon.1) (sub_nonpos.mpr d2.le)]
  have hconvZ : ∀ l : ℕ, m + 2 ≤ l → l ≤ m + (n + 1) → s * Z (l : ZMod (m + n + 2)) <
      max (s * Z ((l - 1 : ℕ) : ZMod (m + n + 2))) (s * Z ((l + 1 : ℕ) : ZMod (m + n + 2))) := by
    intro l h1 h2
    rcases Nat.lt_or_ge l (m + n + 1) with hl | hl
    · set j := m + n + 1 - l with hj
      have hj1 : 1 ≤ j := by omega
      have hjn : j < n := by omega
      rw [hZ2 l (by omega) (by omega), hZ2 (l - 1) (by omega) (by omega),
        hZ2 (l + 1) (by omega) (by omega), show m + n + 1 - (l - 1) = j + 1 by omega,
        show m + n + 1 - (l + 1) = j - 1 by omega]
      have hc := coords2 (j - 1) (by omega) j hjn
        (ne2 _ _ (by omega) (by omega) (by omega)) (ne2 _ _ (by omega) (by omega) (by omega))
      have e1 := mono cb n hcb j (j + 1) (by omega) (by omega)
      have e2 := mono cb n hcb (j - 1) j (by omega) (by omega)
      by_contra hcon
      push Not at hcon
      rw [max_le_iff] at hcon
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr e1.le) (sub_nonpos.mpr hcon.2),
        mul_nonneg (sub_nonneg.mpr hcon.1) (sub_nonneg.mpr e2.le)]
    · have hl' : l = m + n + 1 := by omega
      subst hl'
      have e : ((m + n + 1 + 1 : ℕ) : ZMod (m + n + 2)) = ((m + n + 2 : ℕ) : ZMod (m + n + 2)) := rfl
      rw [hZ2 (m + n + 1) (by omega) le_rfl, show m + n + 1 - (m + n + 1) = 0 by omega, e, hZk]
      exact lt_max_of_lt_right hap
  have hw : ∀ v : ℕ, ((m + n + 2 + v : ℕ) : ZMod (m + n + 2)) = (v : ZMod (m + n + 2)) := by
    intro v; rw [Nat.cast_add, ZMod.natCast_self, zero_add]
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  have hrun : ∃ L c : ℕ, L < m + n + 2 ∧ RunSeq (m + n + 2) L c s Z := by
    rcases hmode with hAB | hinc | hFB
    · refine ⟨m, 0, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        rcases Nat.lt_or_ge l (m + 2) with h3 | h3
        · left
          obtain rfl : l = m + 1 := by omega
          rw [hZ2 (m + 1) (by omega) (by omega), show m + 1 - 1 = m by omega, hZ1 m le_rfl,
            show m + n + 1 - (m + 1) = n by omega]
          exact hAB
        · exact lt_max_iff.mp (hconvZ l h3 (by omega))
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        exact min_lt_iff.mp (hconcZ l (by omega) h2)
    · refine ⟨1, m, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        rcases Nat.lt_or_ge (m + l) (m + n + 2) with h3 | h3
        · exact lt_max_iff.mp (hconvZ (m + l) (by omega) (by omega))
        · right
          rw [show m + l = m + n + 2 + (m + l - (m + n + 2)) by omega,
            show m + n + 2 + (m + l - (m + n + 2)) + 1 = m + n + 2 + (m + l - (m + n + 2) + 1) by omega,
            hw, hw, hZ1 _ (by omega), hZ1 _ (by omega)]
          exact hinc _ (by omega)
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl; omega
    · refine ⟨m, 0, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        right
        rw [hZ2 l (by omega) (by omega)]
        rcases Nat.lt_or_ge l (m + n + 1) with h | h
        · rw [hZ2 (l + 1) (by omega) (by omega)]
          have := hFB (m + n - l) (by omega)
          rw [show m + n + 1 - (l + 1) = m + n - l by omega, show m + n + 1 - l = m + n - l + 1 by omega]
          exact this
        · obtain rfl : l = m + n + 1 := by omega
          have e : ((m + n + 1 + 1 : ℕ) : ZMod (m + n + 2)) = ((m + n + 2 : ℕ) : ZMod (m + n + 2)) := rfl
          rw [e, hZk, show m + n + 1 - (m + n + 1) = 0 by omega]
          exact hap
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        exact min_lt_iff.mp (hconcZ l (by omega) h2)
  obtain ⟨L, c, hLK, hR⟩ := hrun
  exact isRupert_of_tilted_localMax V ez v hez (k := m + n + 2) (by omega) x hxV hcyc hrest s hs
    (RunSeq (m + n + 2) L c s) (isOpen_runSeq _ _ _ s) (fun z k hk hz => runSeq_smul hk hz)
    (by rw [show (fun i => ⟪x i, ez⟫) = Z from funext hdepth]; exact hR)
    (fun z hz => runSeq_localMax hLK hz)

/-- A tilt ratio of either sign: `σ (A β - B α) > 0`. -/
theorem exists_tilt_sign {A B σ : ℝ} (hA : 0 < A) (hB : 0 < B) (hσ : σ = 1 ∨ σ = -1) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 0 < σ * (A * β - B * α) := by
  rcases hσ with rfl | rfl
  · refine ⟨1, 2 * B / A, one_pos, by positivity, ?_⟩
    have : A * (2 * B / A) = 2 * B := by field_simp
    rw [this]; linarith
  · refine ⟨2 * A / B, 1, by positivity, one_pos, ?_⟩
    have : B * (2 * A / B) = 2 * A := by field_simp
    rw [this]; linarith

/-- The chord test from the two signs: `σ (A β - B α) > 0` and `σ s D > 0` give
`s (A β - B α) D > 0`. -/
theorem chord_sign {σ s X D : ℝ} (hσ : σ = 1 ∨ σ = -1) (h1 : 0 < σ * X) (h2 : 0 < σ * s * D) :
    0 < s * X * D := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have := mul_pos h1 h2
  have e : σ * X * (σ * s * D) = (σ * σ) * (s * X * D) := by ring
  rw [e, hσσ, one_mul] at this; exact this

set_option maxHeartbeats 4000000 in
/-- The core of Lemma T′ over an edge with the tie modes of `isRupert_triShadow2_gen`:
chains `C1` (sign `s`) and `C2` (sign `-s`) from the two apex vertices, a mode, and
points on the far side (on the chord) on the side `σ` that the tilt ratio hides. -/
theorem edge_core_gen_chord (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s)
    {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOK Q1 z1s s m ca cz) (C2 : ChainOK Q2 z2s (-s) n cb dz)
    (hmode : s * dz n < s * cz m ∨ (∀ l, l < m → s * cz l < s * cz (l + 1)) ∨
      (∀ j, j < n → s * dz (j + 1) < s * dz j))
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n) ∨
        (0 < a ∧ 0 < b ∧ a * cb n + b * ca m = ca m * cb n ∧
          0 < σ * s * (cb n * (z - cz m) - b * (dz n - cz m))))) : IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have far1 : ∀ a z, Q1 a z → a * cb n < ca m * cb n ∨ (a = ca m ∧ z = cz m) := by
    intro a z hq
    by_cases h : a = ca m ∧ z = cz m
    · exact Or.inr h
    · left; exact mul_lt_mul_of_pos_right (C1.far a z hq h) hB0
  have far2 : ∀ b z, Q2 b z → b * ca m < cb n * ca m ∨ (b = cb n ∧ z = dz n) := by
    intro b z hq
    by_cases h : b = cb n ∧ z = dz n
    · exact Or.inr h
    · left; exact mul_lt_mul_of_pos_right (C2.far b z hq h) hA0
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  -- the apex points
  have apx : ∀ z, z = z1s ∨ z = z2s → oblPt O r1 r2 0 0 z = oblPt O r1 r2 (ca 0) 0 (cz 0) ∨
      oblPt O r1 r2 0 0 z = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rintro z (rfl | rfl)
    · left; rw [c10.1, c10.2]
    · right; rw [c20.1, c20.2]
  have q1of : ∀ z, Q2 0 z → Q1 0 z := by
    intro z h; rcases hap2 z h with rfl | rfl
    · exact (by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _))
    · exact hQ1z2
  have q2of : ∀ z, Q1 0 z → Q2 0 z := by
    intro z h; rcases hap1 z h with rfl | rfl
    · exact hQ2z1
    · exact (by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _))
  -- the tilt ratio, from the side `σ` of the chord points
  obtain ⟨α, β, hα, hβ, hsg⟩ := exists_tilt_sign hA0 hB0 hσ
  refine isRupert_triShadow2_gen_tilt O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]; exact hap) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hmode
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩ | ⟨ha, hb, hch, hside⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | ⟨e1, e2⟩
      · left; exact far_tiltOK (by linarith)
      · right; left; rw [e1, e2]
    · intro ha _; subst ha; exact apx z (hap1 z hq)
    · intro ha; subst ha; exact side2 0 z (q2of z hq)
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | ⟨e1, e2⟩
      · left; exact far_tiltOK (by linarith)
      · right; right; rw [e1, e2]
    · intro _ hb; subst hb; exact apx z (hap2 z hq)
    · intro hb; subst hb; exact side1 0 z (q1of z hq)
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK hin), fun h => absurd h ha.ne',
      fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩
  · exact ⟨a, b, z, rfl, ha.le, hb.le,
      Or.inl (chord_tiltOK hB0 hch (chord_sign hσ hsg hside)),
      fun h => absurd h ha.ne', fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 8000000 in
/-- **Lemma T′ over an edge, the tie allowed, in frame coordinates** (`isRupert_edge_coords_chord`
with the far ends allowed to tie): `s z_xb < s z_xa`, or the far end `xa` of `Q1` is its
strict top in `s z` (so the chain of `Q1` rises to it, the mode "`C1` rises" of
`isRupert_triShadow2_gen`); and
every point off both faces is strictly inside the shadow triangle or on its far side,
there on the side `σ` of the segment `xa xb` (one tilt ratio hides them all). -/
theorem isRupert_edge_coords_mode_chord (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v w : ℝ³) (hvw : v 2 < w 2) (a b : ℝ³ → ℝ)
    (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinjv : Set.InjOn (fun p => (a p, b p)) ((V.erase v : Finset ℝ³) : Set ℝ³))
    (hinjw : Set.InjOn (fun p => (a p, b p)) ((V.erase w : Finset ℝ³) : Set ℝ³))
    (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2) (hxa2 : xa ∉ Q2) (hxb1 : xb ∉ Q1)
    (hamax : ∀ p ∈ Q1, a p ≤ a xa) (hbmax : ∀ q ∈ Q2, b q ≤ b xb)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hmode : s * xb 2 < s * xa 2 ∨ ∀ p ∈ Q1, p ≠ xa → s * p 2 < s * xa 2)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hin : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 ∨
      (a y / a xa + b y / b xb = 1 ∧ 0 < σ * s * (b xb * (y 2 - xa 2) - b y * (xb 2 - xa 2)))) :
    IsRupert V := by
  have mem12 : ∀ p, p ∈ Q1 → p ∈ Q2 → p = v ∨ p = w := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this; simpa using this
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have hav := ha2 v hv2; have haw := ha2 w hw2
  have hbv := hb1 v hv1; have hbw := hb1 w hw1
  have hvw' : v ≠ w := fun e => by rw [e] at hvw; exact lt_irrefl _ hvw
  -- the faces in their planes
  set S1 := Q1.image (fun p => (a p, p 2)) with hS1
  set S2 := Q2.image (fun p => (b p, p 2)) with hS2
  have ofS1 : ∀ x z, (x, z) ∈ S1 → ∃ p ∈ Q1, a p = x ∧ p 2 = z := by
    intro x z h; rw [hS1, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have ofS2 : ∀ x z, (x, z) ∈ S2 → ∃ p ∈ Q2, b p = x ∧ p 2 = z := by
    intro x z h; rw [hS2, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have pt1 : ∀ p ∈ Q1, p = oblPt O r1 r2 (a p) 0 (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h1V hp), hb1 p hp]
  have pt2 : ∀ p ∈ Q2, p = oblPt O r1 r2 0 (b p) (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h2V hp), ha2 p hp]
  have d1 : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
      u' 2 = r'.2 → u ≠ u' := by
    intro r r' u u' h h1 h2 h1' h2' hu; apply h
    exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
  have d2 : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
      u' 2 = r'.2 → u ≠ u' := by
    intro r r' u u' h h1 h2 h1' h2' hu; apply h
    exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
  -- chains of the first face
  have chains1 : ∀ (s : ℝ) (u u' : ℝ³), (s = 1 ∨ s = -1) → (u = v ∧ u' = w ∨ u = w ∧ u' = v) →
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S1) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu1 : u ∈ Q1 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hau : a u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hinj : Set.InjOn (fun p => (a p, b p)) ((V.erase u' : Finset ℝ³) : Set ℝ³) := by
      rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hinjw
      · exact hinjv
    apply exists_chainOK_edge S1 (u 2) (u' 2) s hs hso
      (by rw [hS1, Finset.mem_image]; exact ⟨u, hu1, by rw [hau]⟩)
    · intro q hq h0 h1
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      by_cases hp2 : p ∈ Q2
      · exfalso
        have hpe : p = u ∨ p = u' := by
          rcases mem12 p hp hp2 with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        rcases hpe with rfl | rfl
        · exact h0 (Prod.ext (by rw [← e1, hau]) (by rw [← e2]))
        · apply h1; refine Prod.ext ?_ (by rw [← e2])
          show q.1 = 0; rw [← e1]; exact ha2 p hp2
      · rw [← e1]; exact ha2' p (h1V hp) hp2
    · obtain ⟨p, hp, hp2⟩ := hne1
      exact ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, ha2' p (h1V hp) hp2⟩
    · intro q hq q' hq' e
      have hq0 := Finset.ne_of_mem_erase hq; have hq0' := Finset.ne_of_mem_erase hq'
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 (Finset.mem_of_mem_erase hq')
      have pu : p ≠ u' := fun h => hq0 (Prod.ext (by
        show q.1 = 0; rw [← e1, h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2, h]))
      have pu' : p' ≠ u' := fun h => hq0' (Prod.ext (by
        show q'.1 = 0; rw [← e1', h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2', h]))
      have : p = p' := hinj (Finset.mem_erase.mpr ⟨pu, h1V hp⟩) (Finset.mem_erase.mpr ⟨pu', h1V hp'⟩)
        (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨by rw [e1, e1']; exact e, rfl⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have := orient_ne_of_frame1' (O := O) (r1 := r1) (r2 := r2) (ai := a p) (zi := p 2)
        (aj := a p') (zj := p' 2) (zk := p'' 2) (ak := a p'')
        (by rw [e1, e2, e1', e2']; exact n1) (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d1 n1 e1 e2 e1' e2')
            (d1 n2 e1 e2 e1'' e2'') (d1 n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
  have chains2 : ∀ (s : ℝ) (u u' : ℝ³), (s = 1 ∨ s = -1) → (u = v ∧ u' = w ∨ u = w ∧ u' = v) →
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu2 : u ∈ Q2 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hbu : b u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hinj : Set.InjOn (fun p => (a p, b p)) ((V.erase u' : Finset ℝ³) : Set ℝ³) := by
      rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hinjw
      · exact hinjv
    apply exists_chainOK_edge S2 (u 2) (u' 2) s hs hso
      (by rw [hS2, Finset.mem_image]; exact ⟨u, hu2, by rw [hbu]⟩)
    · intro q hq h0 h1
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      by_cases hp1 : p ∈ Q1
      · exfalso
        have hpe : p = u ∨ p = u' := by
          rcases mem12 p hp1 hp with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        rcases hpe with rfl | rfl
        · exact h0 (Prod.ext (by rw [← e1, hbu]) (by rw [← e2]))
        · apply h1; refine Prod.ext ?_ (by rw [← e2])
          show q.1 = 0; rw [← e1]; exact hb1 p hp1
      · rw [← e1]; exact hb1' p (h2V hp) hp1
    · obtain ⟨p, hp, hp1⟩ := hne2
      exact ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, hb1' p (h2V hp) hp1⟩
    · intro q hq q' hq' e
      have hq0 := Finset.ne_of_mem_erase hq; have hq0' := Finset.ne_of_mem_erase hq'
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 (Finset.mem_of_mem_erase hq')
      have pu : p ≠ u' := fun h => hq0 (Prod.ext (by
        show q.1 = 0; rw [← e1, h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2, h]))
      have pu' : p' ≠ u' := fun h => hq0' (Prod.ext (by
        show q'.1 = 0; rw [← e1', h]; rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)
        (by rw [← e2', h]))
      have : p = p' := hinj (Finset.mem_erase.mpr ⟨pu, h2V hp⟩) (Finset.mem_erase.mpr ⟨pu', h2V hp'⟩)
        (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, by rw [e1, e1']; exact e⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have := orient_ne_of_frame2' (O := O) (r1 := r1) (r2 := r2) (bi := b p) (zi := p 2)
        (bj := b p') (zj := p' 2) (zk := p'' 2) (bk := b p'')
        (by rw [e1, e2, e1', e2']; exact n1) (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d2 n1 e1 e2 e1' e2')
            (d2 n2 e1 e2 e1'' e2'') (d2 n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
  have hA := ha2' xa (h1V hxa) hxa2
  have hB := hb1' xb (h2V hxb) hxb1
  -- the apex vertex of each chain: `C1` starts at the top for `s = 1`
  obtain ⟨u, u', huu, hso⟩ : ∃ u u' : ℝ³, (u = v ∧ u' = w ∨ u = w ∧ u' = v) ∧ s * u' 2 < s * u 2 := by
    rcases hs with rfl | rfl
    · exact ⟨w, v, Or.inr ⟨rfl, rfl⟩, by linarith⟩
    · exact ⟨v, w, Or.inl ⟨rfl, rfl⟩, by linarith⟩
  have huu' : u' = v ∧ u = w ∨ u' = w ∧ u = v := by
    rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  have hns : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨m, ca, cz, C1⟩ := chains1 s u u' hs huu hso
  obtain ⟨n, cb, dz, C2⟩ := chains2 (-s) u' u hns huu' (by linarith)
  have hu1 : u ∈ Q1 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hu'1 : u' ∈ Q1 := by rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hu2 : u ∈ Q2 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hu'2 : u' ∈ Q2 := by rcases huu with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hau : a u = 0 := ha2 u hu2
  have hau' : a u' = 0 := ha2 u' hu'2
  have hbu : b u = 0 := hb1 u hu1
  have hbu' : b u' = 0 := hb1 u' hu'1
  -- the far ends of the chains are `xa`, `xb`
  have fa : ca m = a xa ∧ cz m = xa 2 := by
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    by_contra hne
    have := C1.far (a xa) (xa 2) (Finset.mem_image_of_mem _ hxa)
      (fun h => hne ⟨h.1.symm, h.2.symm⟩)
    have := hamax p hp; linarith
  have fb : cb n = b xb ∧ dz n = xb 2 := by
    obtain ⟨q, hq, e1, e2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    by_contra hne
    have := C2.far (b xb) (xb 2) (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb)
      (fun h => hne ⟨h.1.symm, h.2.symm⟩)
    have := hbmax q hq; linarith
  refine edge_core_gen_chord O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2) s hs
    (z1s := u 2) (z2s := u' 2) hso C1 (by simpa using C2) ?_ ?_ ?_
    (Finset.mem_image.mpr ⟨u', hu'1, by rw [hau']⟩) (Finset.mem_image.mpr ⟨u, hu2, by rw [hbu]⟩)
    ?_ ?_ σ hσ V ?_ ?_ ?_
  · -- far depths distinct, or `C1` rises to `xa`, its strict top
    rcases hmode with hlt | htop
    · left; rw [fa.2, fb.2]; exact hlt
    right; left
    refine C1.rise_of_far_top fun x z hq hn => ?_
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z hq
    have hpa : p ≠ xa := fun h => hn ⟨by rw [← e1, h, fa.1], by rw [← e2, h, fa.2]⟩
    rw [← e2, fa.2]; exact htop p hp hpa
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hp2 : p ∈ Q2
    · rcases mem12 p hp hp2 with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [← e2]
    · linarith [ha2' p (h1V hp) hp2]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hp1 : p ∈ Q1
    · rcases mem12 p hp1 hp with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [← e2]
    · linarith [hb1' p (h2V hp) hp1]
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    by_cases hp2 : p ∈ Q2
    · rw [← e1, ha2 p hp2]
    · rw [← e1]; exact (ha2' p (h1V hp) hp2).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    by_cases hp1 : p ∈ Q1
    · rw [← e1, hb1 p hp1]
    · rw [← e1]; exact (hb1' p (h2V hp) hp1).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    rw [← e1, ← e2, ← pt1 p hp]; exact h1V hp
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    rw [← e1, ← e2, ← pt2 p hp]; exact h2V hp
  · intro y hy'
    refine ⟨a y, b y, y 2, hy y hy', ?_⟩
    by_cases h1 : y ∈ Q1
    · exact Or.inl ⟨hb1 y h1, Finset.mem_image_of_mem _ h1⟩
    by_cases h2 : y ∈ Q2
    · exact Or.inr (Or.inl ⟨ha2 y h2, Finset.mem_image_of_mem (fun p => (b p, p 2)) h2⟩)
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    rw [fa.1, fa.2, fb.1, fb.2]
    rcases hin y hy' h1 h2 with hlt | ⟨heq, hside⟩
    · refine Or.inr (Or.inr (Or.inl ⟨ha, hb, ?_⟩))
      rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at hlt
      linarith
    · refine Or.inr (Or.inr (Or.inr ⟨ha, hb, ?_, hside⟩))
      rw [div_add_div _ _ hA.ne' hB.ne', div_eq_one_iff_eq (mul_pos hA hB).ne'] at heq
      linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma T′ at a vertex with vertical companions at the far ends, the core.** As
`vertex_core_par`, with points on the far side (on the chord) allowed where the tilt
ratio hides them (`chord_tiltOK`). -/
theorem vertex_core_parc (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ} (s : ℝ) (hs : s = 1 ∨ s = -1) {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z0 s m ca cz) (C2 : ChainOKc Q2 z0 (-s) n cb dz)
    (hAB : s * dz n < s * cz m) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hr1 : ∀ z, Q1 (ca m) z → z ≠ cz m → ca m * β < cb n * α)
    (hr2 : ∀ z, Q2 (cb n) z → z ≠ dz n → cb n * α < ca m * β)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n) ∨
        (0 < a ∧ 0 < b ∧ a * cb n + b * ca m = ca m * cb n ∧
          0 < s * (ca m * β - cb n * α) * (cb n * (z - cz m) - b * (dz n - cz m))))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
  -- the far tests, with the companions
  have far1 : ∀ a z, Q1 a z →
      TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 (cz m) := by
    intro a z hq
    by_cases h : a = ca m ∧ z = cz m
    · right; rw [h.1, h.2]
    rcases C1.far a z hq h with hlt | ⟨ea, hc⟩
    · left; exact far_tiltOK (by nlinarith)
    · left; subst ea
      have hz : z ≠ cz m := fun e => by rw [e] at hc; simp at hc
      exact tiltOK_farComp1 hc (hr1 z hq hz)
  have far2 : ∀ b z, Q2 b z →
      TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 0 (cb n) (dz n) := by
    intro b z hq
    by_cases h : b = cb n ∧ z = dz n
    · right; rw [h.1, h.2]
    rcases C2.far b z hq h with hlt | ⟨eb, hc⟩
    · left; exact far_tiltOK (by nlinarith)
    · left; subst eb
      have hz : z ≠ dz n := fun e => by rw [e] at hc; simp at hc
      exact tiltOK_farComp2 (by linarith) (hr2 z hq hz)
  refine isRupert_triShadow_tilt O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hAB
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩ | ⟨ha, hb, hch, hpos⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | h
      · exact Or.inl h
      · right; left; exact h
    · intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | h
      · exact Or.inl h
      · right; right; exact h
    · intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK hin), fun h => absurd h hb.ne',
      fun h => absurd h ha.ne'⟩
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (chord_tiltOK hB0 hch hpos), fun h => absurd h hb.ne',
      fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 8000000 in
/-- **Lemma T′ at a vertex with a vertical edge over a far corner, in frame coordinates.**
As `isRupert_vertex_coords_par`, for one mixed sector given explicitly: `xa` is the far
end of `Q1` shown by its chain of sign `s` (the top in `s z` of its vertical), `xb` that
of `Q2` for the sign `-s`, and `s z_xb < s z_xa`. Vertical companions are allowed at the
far ends (hidden by the tilt ratio, whose side is `σ`), and points off both faces may lie
on the far side when they are on the side `σ` of the segment `xa xb`. This is the
Extension of Lemma T′ (`FEWER-FACES-PROOFS.md` §7, corrected in §23) in the mixed
sectors where the vertical edge shows one end. -/
theorem isRupert_vertex_coords_parc (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (s : ℝ) (hs : s = 1 ∨ s = -1) (xa xb : ℝ³) (hxa : xa ∈ Q1) (hxb : xb ∈ Q2)
    (hamax : ∀ p ∈ Q1, a p ≤ a xa) (hbmax : ∀ q ∈ Q2, b q ≤ b xb)
    (htopa : ∀ p ∈ Q1, a p = a xa → p ≠ xa → s * p 2 < s * xa 2)
    (hbotb : ∀ q ∈ Q2, b q = b xb → q ≠ xb → s * xb 2 < s * q 2)
    (hAB : s * xb 2 < s * xa 2)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hc1 : (∃ p ∈ Q1, a p = a xa ∧ p ≠ xa) → σ = -1)
    (hc2 : (∃ q ∈ Q2, b q = b xb ∧ q ≠ xb) → σ = 1)
    (hin : ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 ∨
      (a y / a xa + b y / b xb = 1 ∧ 0 < σ * s * (b xb * (y 2 - xa 2) - b y * (xb 2 - xa 2)))) :
    IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have hav : a v = 0 := ha2 v hv2
  have hbv : b v = 0 := hb1 v hv1
  have apos : ∀ p ∈ Q1, p ≠ v → 0 < a p := fun p hp hpv =>
    ha2' p (h1V hp) (fun h => hpv (only p hp h))
  have bpos : ∀ p ∈ Q2, p ≠ v → 0 < b p := fun p hp hpv =>
    hb1' p (h2V hp) (fun h => hpv (only p h hp))
  -- the faces in their planes
  set S1 := Q1.image (fun p => (a p, p 2)) with hS1
  set S2 := Q2.image (fun p => (b p, p 2)) with hS2
  have ofS1 : ∀ x z, (x, z) ∈ S1 → ∃ p ∈ Q1, a p = x ∧ p 2 = z := by
    intro x z h; rw [hS1, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have ofS2 : ∀ x z, (x, z) ∈ S2 → ∃ p ∈ Q2, b p = x ∧ p 2 = z := by
    intro x z h; rw [hS2, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have pt1 : ∀ p ∈ Q1, p = oblPt O r1 r2 (a p) 0 (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h1V hp), hb1 p hp]
  have pt2 : ∀ p ∈ Q2, p = oblPt O r1 r2 0 (b p) (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h2V hp), ha2 p hp]
  -- chains
  have chains1 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOKc (fun x z => (x, z) ∈ S1) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOKc S1 (v 2) (by rw [hS1, Finset.mem_image]; exact ⟨v, hv1, by rw [hav]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      rw [← e1]; refine apos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hav]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne1
      refine ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [apos p hp hpv]
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : (a p, p 2) ≠ (a p', p' 2) := by rw [e1, e2, e1', e2']; exact n1
      have := orient_ne_of_frame1' (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (ak := a p'') hne (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  have chains2 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOKc (fun x z => (x, z) ∈ S2) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOKc S2 (v 2) (by rw [hS2, Finset.mem_image]; exact ⟨v, hv2, by rw [hbv]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      rw [← e1]; refine bpos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hbv]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne2
      refine ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [bpos p hp hpv]
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : (b p, p 2) ≠ (b p', p' 2) := by rw [e1, e2, e1', e2']; exact n1
      have := orient_ne_of_frame2' (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (bk := b p'') hne (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  have hxav : xa ≠ v := by
    intro e; subst e
    obtain ⟨p, hp, hpv⟩ := hne1
    have := hamax p hp; linarith [apos p hp hpv]
  have hxbv : xb ≠ v := by
    intro e; subst e
    obtain ⟨p, hp, hpv⟩ := hne2
    have := hbmax p hp; linarith [bpos p hp hpv]
  have hA := apos xa hxa hxav
  have hB := bpos xb hxb hxbv
  have hns : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨m, ca, cz, C1⟩ := chains1 s hs
  obtain ⟨n, cb, dz, C2⟩ := chains2 (-s) hns
  -- the far ends of the chains are `xa`, `xb`
  have fa : ca m = a xa ∧ cz m = xa 2 := by
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    by_contra hne
    rcases C1.far (a xa) (xa 2) (Finset.mem_image_of_mem _ hxa) (fun h => hne ⟨h.1.symm, h.2.symm⟩)
      with h | ⟨h1, h2⟩
    · have := hamax p hp; linarith
    · have hpx : p ≠ xa := fun e => hne ⟨by rw [← e1, e], by rw [← e2, e]⟩
      have := htopa p hp (by rw [e1, h1]) hpx
      rw [e2] at this; linarith
  have fb : cb n = b xb ∧ dz n = xb 2 := by
    obtain ⟨q, hq, e1, e2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    by_contra hne
    rcases C2.far (b xb) (xb 2) (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb)
      (fun h => hne ⟨h.1.symm, h.2.symm⟩) with h | ⟨h1, h2⟩
    · have := hbmax q hq; linarith
    · have hqx : q ≠ xb := fun e => hne ⟨by rw [← e1, e], by rw [← e2, e]⟩
      have := hbotb q hq (by rw [e1, h1]) hqx
      rw [e2] at this; linarith
  -- the tilt ratio
  obtain ⟨α, β, hα, hβ, hsg⟩ := exists_tilt_sign (A := ca m) (B := cb n) C1.far_pos C2.far_pos hσ
  refine vertex_core_parc O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2) s hs C1 C2
    (by rw [fa.2, fb.2]; exact hAB) hα hβ ?_ ?_ ?_ ?_ ?_ ?_ V ?_ ?_ ?_
  · intro z hz hne
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ hz
    have hpx : p ≠ xa := fun e => hne (by rw [← e2, e, fa.2])
    have := hc1 ⟨p, hp, by rw [e1, fa.1], hpx⟩
    subst this; linarith
  · intro z hz hne
    obtain ⟨q, hq, e1, e2⟩ := ofS2 _ _ hz
    have hqx : q ≠ xb := fun e => hne (by rw [← e2, e, fb.2])
    have := hc2 ⟨q, hq, by rw [e1, fb.1], hqx⟩
    subst this; linarith
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hpv : p = v
    · rw [← e2, hpv]
    · linarith [apos p hp hpv]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hpv : p = v
    · rw [← e2, hpv]
    · linarith [bpos p hp hpv]
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    by_cases hpv : p = v
    · rw [← e1, hpv, hav]
    · rw [← e1]; exact (apos p hp hpv).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    by_cases hpv : p = v
    · rw [← e1, hpv, hbv]
    · rw [← e1]; exact (bpos p hp hpv).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    rw [← e1, ← e2, ← pt1 p hp]; exact h1V hp
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    rw [← e1, ← e2, ← pt2 p hp]; exact h2V hp
  · intro y hy'
    refine ⟨a y, b y, y 2, hy y hy', ?_⟩
    by_cases h1 : y ∈ Q1
    · exact Or.inl ⟨hb1 y h1, Finset.mem_image_of_mem _ h1⟩
    by_cases h2 : y ∈ Q2
    · exact Or.inr (Or.inl ⟨ha2 y h2, Finset.mem_image_of_mem (fun p => (b p, p 2)) h2⟩)
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    rw [fa.1, fa.2, fb.1, fb.2]
    rcases hin y hy' h1 h2 with hlt | ⟨heq, hside⟩
    · refine Or.inr (Or.inr (Or.inl ⟨ha, hb, ?_⟩))
      rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at hlt
      linarith
    · refine Or.inr (Or.inr (Or.inr ⟨ha, hb, ?_, ?_⟩))
      · rw [div_add_div _ _ hA.ne' hB.ne', div_eq_one_iff_eq (mul_pos hA hB).ne'] at heq
        linarith
      · rw [fa.1, fb.1] at hsg
        exact chord_sign hσ hsg hside


end Minimality

end
