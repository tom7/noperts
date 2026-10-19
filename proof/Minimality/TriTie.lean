module

public import Minimality.TriShadowChord
public import Minimality.TriFacesChord
public import Minimality.TriFacets
public import Minimality.TriFacetsEdge

@[expose] public section

/-!
# Lemma T at the tie

"Lemma T at the tie" of `FEWER-FACES-PROOFS.md` §7: at the view along the line
of two face planes, the far ends `xa`, `xb` of the shadow triangle may have the
same depth, and some tilt is still unimodal when (b) the lowest vertex of a
face's chain is the shared vertex or its far end, or (c) the same with the
highest. Every case comes down to one sequence fact
(`localMax_unique_of_run`): if every position of a cyclic sequence outside a
run has a strictly larger neighbour, and the run has no interior local
minimum, the local maximum is unique. These conditions are strict at the
untilted view, so `isRupert_of_tilted_localMax` applies without breaking the
tie by hand.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- **One concave run.** Positions `0, …, L` of a cyclic sequence form a run
with no interior local minimum, and every other position has a strictly larger
neighbour. Then the sequence has at most one strict local maximum. -/
theorem localMax_unique_of_run {K L : ℕ} [NeZero K] (hL : L < K) (w : ZMod K → ℝ)
    (hout : ∀ l : ℕ, L < l → l < K →
      w (l : ZMod K) < w ((l - 1 : ℕ) : ZMod K) ∨ w (l : ZMod K) < w ((l + 1 : ℕ) : ZMod K))
    (hconc : ∀ l : ℕ, 1 ≤ l → l < L →
      min (w ((l - 1 : ℕ) : ZMod K)) (w ((l + 1 : ℕ) : ZMod K)) < w (l : ZMod K)) :
    ∀ a b : ZMod K, w (a - 1) < w a → w (a + 1) < w a →
      w (b - 1) < w b → w (b + 1) < w b → a = b := by
  have hcast : ∀ a : ZMod K, ((a.val : ℕ) : ZMod K) = a := ZMod.natCast_zmod_val
  have hsub : ∀ l : ℕ, 1 ≤ l → ((l : ZMod K) - 1) = ((l - 1 : ℕ) : ZMod K) := by
    intro l hl; rw [Nat.cast_sub hl]; simp
  have hadd : ∀ l : ℕ, ((l : ZMod K) + 1) = ((l + 1 : ℕ) : ZMod K) := by intro l; simp
  -- a local maximum lies in the run
  have inrun' : ∀ l : ℕ, l < K → w ((l : ZMod K) - 1) < w (l : ZMod K) →
      w ((l : ZMod K) + 1) < w (l : ZMod K) → l ≤ L := by
    intro l hlK h1 h2
    by_contra hv; push Not at hv
    rw [hsub l (by omega)] at h1
    rw [hadd] at h2
    rcases hout l hv hlK with h | h <;> linarith
  have inrun : ∀ a : ZMod K, w (a - 1) < w a → w (a + 1) < w a → a.val ≤ L := by
    intro a h1 h2
    have ha := hcast a
    rw [← ha] at h1 h2
    exact inrun' a.val (ZMod.val_lt a) h1 h2
  -- two local maxima in the run would enclose an interior local minimum
  have key : ∀ p q : ℕ, p < q → q ≤ L →
      w ((p + 1 : ℕ) : ZMod K) < w (p : ZMod K) → w ((q - 1 : ℕ) : ZMod K) < w (q : ZMod K) → False := by
    intro p q hpq hqL hp hq
    obtain ⟨c, hc, hcmin⟩ := (Finset.Icc p q).exists_min_image (fun l : ℕ => w (l : ZMod K))
      ⟨p, Finset.mem_Icc.mpr ⟨le_rfl, hpq.le⟩⟩
    obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.mp hc
    have cp : c ≠ p := by
      rintro rfl
      exact absurd (hcmin (c + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (not_le.mpr hp)
    have cq : c ≠ q := by
      rintro rfl
      exact absurd (hcmin (c - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (not_le.mpr hq)
    have := hconc c (by omega) (by omega)
    have e1 := hcmin (c - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have e2 := hcmin (c + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [min_lt_iff] at this
    rcases this with h | h <;> linarith
  intro a b ha1 ha2 hb1 hb2
  have hav := inrun a ha1 ha2
  have hbv := inrun b hb1 hb2
  have ea := hcast a; have eb := hcast b
  have lmax : ∀ x : ZMod K, w (x - 1) < w x → w (x + 1) < w x →
      w ((x.val + 1 : ℕ) : ZMod K) < w (x.val : ZMod K) ∧
        (1 ≤ x.val → w ((x.val - 1 : ℕ) : ZMod K) < w (x.val : ZMod K)) := by
    intro x h1 h2
    have ex := hcast x
    refine ⟨by rw [← hadd, ex]; exact h2, fun h => by rw [← hsub _ h, ex]; exact h1⟩
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact (key a.val b.val h hbv (lmax a ha1 ha2).1 ((lmax b hb1 hb2).2 (by omega))).elim
  · exact ZMod.val_injective K h
  · exact (key b.val a.val h hav (lmax b hb1 hb2).1 ((lmax a ha1 ha2).2 (by omega))).elim

/-- `localMax_unique_of_run` for a run starting at position `c`. -/
theorem localMax_unique_of_run_shift {K L : ℕ} [NeZero K] (hL : L < K) (c : ℕ) (w : ZMod K → ℝ)
    (hout : ∀ l : ℕ, L < l → l < K →
      w ((c + l : ℕ) : ZMod K) < w ((c + l - 1 : ℕ) : ZMod K) ∨
        w ((c + l : ℕ) : ZMod K) < w ((c + l + 1 : ℕ) : ZMod K))
    (hconc : ∀ l : ℕ, 1 ≤ l → l < L →
      min (w ((c + l - 1 : ℕ) : ZMod K)) (w ((c + l + 1 : ℕ) : ZMod K)) < w ((c + l : ℕ) : ZMod K)) :
    ∀ a b : ZMod K, w (a - 1) < w a → w (a + 1) < w a →
      w (b - 1) < w b → w (b + 1) < w b → a = b := by
  set w' : ZMod K → ℝ := fun i => w (i + (c : ZMod K)) with hw'
  have shift : ∀ l : ℕ, w' (l : ZMod K) = w ((c + l : ℕ) : ZMod K) := by
    intro l; simp only [hw']; push_cast; ring_nf
  have shiftm : ∀ l : ℕ, 1 ≤ l → w' ((l - 1 : ℕ) : ZMod K) = w ((c + l - 1 : ℕ) : ZMod K) := by
    intro l hl; rw [shift]; congr 2; omega
  have shiftp : ∀ l : ℕ, w' ((l + 1 : ℕ) : ZMod K) = w ((c + l + 1 : ℕ) : ZMod K) := by
    intro l; rw [shift]; congr 2
  have h := localMax_unique_of_run hL w'
    (fun l h1 h2 => by rw [shiftm l (by omega), shiftp, shift]; exact hout l h1 h2)
    (fun l h1 h2 => by rw [shiftm l h1, shiftp, shift]; exact hconc l h1 h2)
  intro a b ha1 ha2 hb1 hb2
  have e : ∀ x : ZMod K, w' (x - (c : ZMod K)) = w x := fun x => by simp [hw']
  have := h (a - c) (b - c)
    (by rw [show a - (c : ZMod K) - 1 = (a - 1) - c by ring, e, e]; exact ha1)
    (by rw [show a - (c : ZMod K) + 1 = (a + 1) - c by ring, e, e]; exact ha2)
    (by rw [show b - (c : ZMod K) - 1 = (b - 1) - c by ring, e, e]; exact hb1)
    (by rw [show b - (c : ZMod K) + 1 = (b + 1) - c by ring, e, e]; exact hb2)
  exact sub_left_injective this

/-- The hypotheses of `localMax_unique_of_run_shift` for `s z` (run of length
`L` from position `c`), as an open, scale-invariant condition on `z`. -/
def RunSeq (K L c : ℕ) (s : ℝ) (z : ZMod K → ℝ) : Prop :=
  (∀ l ∈ Finset.Ioo L K, s * z ((c + l : ℕ) : ZMod K) < s * z ((c + l - 1 : ℕ) : ZMod K) ∨
      s * z ((c + l : ℕ) : ZMod K) < s * z ((c + l + 1 : ℕ) : ZMod K)) ∧
    (∀ l ∈ Finset.Ioo 0 L, s * z ((c + l - 1 : ℕ) : ZMod K) < s * z ((c + l : ℕ) : ZMod K) ∨
      s * z ((c + l + 1 : ℕ) : ZMod K) < s * z ((c + l : ℕ) : ZMod K))

theorem isOpen_runSeq (K L c : ℕ) (s : ℝ) : IsOpen {z | RunSeq K L c s z} := by
  have cc : ∀ a : ZMod K, Continuous fun z : ZMod K → ℝ => s * z a :=
    fun a => continuous_const.mul (continuous_apply a)
  have e : {z | RunSeq K L c s z} =
      (⋂ l ∈ Finset.Ioo L K, ({z : ZMod K → ℝ | s * z ((c + l : ℕ) : ZMod K) <
        s * z ((c + l - 1 : ℕ) : ZMod K)} ∪ {z | s * z ((c + l : ℕ) : ZMod K) <
        s * z ((c + l + 1 : ℕ) : ZMod K)})) ∩
      (⋂ l ∈ Finset.Ioo 0 L, ({z : ZMod K → ℝ | s * z ((c + l - 1 : ℕ) : ZMod K) <
        s * z ((c + l : ℕ) : ZMod K)} ∪ {z | s * z ((c + l + 1 : ℕ) : ZMod K) <
        s * z ((c + l : ℕ) : ZMod K)})) := by
    ext z; simp only [RunSeq, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union]
  rw [e]
  refine (isOpen_biInter_finset fun l _ => ?_).inter (isOpen_biInter_finset fun l _ => ?_)
  · exact (isOpen_lt (cc _) (cc _)).union (isOpen_lt (cc _) (cc _))
  · exact (isOpen_lt (cc _) (cc _)).union (isOpen_lt (cc _) (cc _))

theorem runSeq_smul {K L c : ℕ} {s : ℝ} {z : ZMod K → ℝ} {k : ℝ} (hk : 0 < k)
    (h : RunSeq K L c s z) : RunSeq K L c s (fun i => k * z i) := by
  have m : ∀ a b : ZMod K, s * z a < s * z b → s * (k * z a) < s * (k * z b) := by
    intro a b hab
    rw [show s * (k * z a) = k * (s * z a) by ring, show s * (k * z b) = k * (s * z b) by ring]
    exact mul_lt_mul_of_pos_left hab hk
  exact ⟨fun l hl => (h.1 l hl).imp (m _ _) (m _ _), fun l hl => (h.2 l hl).imp (m _ _) (m _ _)⟩

theorem runSeq_localMax {K L c : ℕ} [NeZero K] (hL : L < K) {s : ℝ} {z : ZMod K → ℝ}
    (h : RunSeq K L c s z) : ∀ a b : ZMod K, s * z (a - 1) < s * z a →
      s * z (a + 1) < s * z a → s * z (b - 1) < s * z b → s * z (b + 1) < s * z b → a = b :=
  localMax_unique_of_run_shift hL c (fun i => s * z i)
    (fun l h1 h2 => h.1 l (Finset.mem_Ioo.mpr ⟨h1, h2⟩))
    (fun l h1 h2 => min_lt_iff.mpr ((h.2 l (Finset.mem_Ioo.mpr ⟨by omega, h2⟩)).imp id id))

set_option maxHeartbeats 4000000 in
/-- **Lemma T, general sectors and the tie.** As `isRupert_triShadow_tilt`, with
the tilt `(-t α, s β)`: `t = s` is a mixed sector (as there), `t = -s` a
same-sign sector (`C2` then lies on the other side of its ray). Instead of
`s z_B < s z_A` it takes one of four modes, each with a run for
`localMax_unique_of_run`: strict (`t = s`, `s z_B < s z_A`); `C1` rises
strictly in `s z` to `A` (`t = s`); `C2` reversed rises strictly from `B`
to the apex (any `t`); `C1` falls strictly from the apex (`t = -s`). The last
three allow `z_A = z_B` ("Lemma T at the tie", cases (b) and (c)). -/
theorem isRupert_triShadow_gen (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) (t : ℝ) (ht : t = 1 ∨ t = -1) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hdz0 : dz 0 = cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) a b z (-t * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 (cz m) ∨ y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        t * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0))
    (hmode : (t = s ∧ s * dz n < s * cz m) ∨ (t = s ∧ ∀ l, l < m → s * cz l < s * cz (l + 1)) ∨
      (∀ j, j < n → s * dz (j + 1) < s * dz j) ∨ (t = -s ∧ ∀ l, l < m → s * cz (l + 1) < s * cz l)) :
    IsRupert V := by
  have hNZ : NeZero (m + n + 1) := ⟨by omega⟩
  have hval : ∀ v : ℕ, v < m + n + 1 → ((v : ZMod (m + n + 1))).val = v := fun v hv => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv]
  have hcam : ∀ i j, i < j → j ≤ m → ca i < ca j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (hca j (by omega))
      · subst h; exact hca i (by omega)
  have hcbm : ∀ i j, i < j → j ≤ n → cb i < cb j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (hcb j (by omega))
      · subst h; exact hcb i (by omega)
  set x : ZMod (m + n + 1) → ℝ³ := fun i => triPt O r1 r2 m n ca cz cb dz i.val with hx
  -- positions
  have hxC1 : ∀ v, v ≤ m → x (v : ZMod (m + n + 1)) = oblPt O r1 r2 (ca v) 0 (cz v) := by
    intro v hv; simp only [hx, hval v (by omega), triPt, hv, ite_true]
  have hxC2 : ∀ l, l < n → x ((m + n - l : ℕ) : ZMod (m + n + 1)) =
      oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) := by
    intro l hl
    simp only [hx, hval (m + n - l) (by omega), triPt, show ¬ m + n - l ≤ m by omega, ite_false]
    rw [show m + n + 1 - (m + n - l) = l + 1 by omega]
  have hapex : oblPt O r1 r2 (ca 0) 0 (cz 0) = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rw [hca0, hcb0, hdz0]
  have hdepth : ∀ i : ZMod (m + n + 1), ⟪x i, ez⟫ = triZ m n cz dz i.val := by
    intro i; simp only [hx, triPt, triZ]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  have hxinj : Function.Injective x := by
    have pos : ∀ w, w < m + n + 1 → (w ≤ m ∧ x w = oblPt O r1 r2 (ca w) 0 (cz w)) ∨
        (m < w ∧ x w = oblPt O r1 r2 0 (cb (m + n + 1 - w)) (dz (m + n + 1 - w))) := by
      intro w hw
      by_cases h : w ≤ m
      · exact Or.inl ⟨h, hxC1 w h⟩
      · refine Or.inr ⟨by omega, ?_⟩
        have := hxC2 (m + n - w) (by omega)
        rwa [show m + n - (m + n - w) = w by omega, show m + n - w + 1 = m + n + 1 - w by omega]
          at this
    intro i j h
    obtain ⟨wi, hwi, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    obtain ⟨wj, hwj, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = j :=
      ⟨j.val, ZMod.val_lt j, ZMod.natCast_zmod_val j⟩
    suffices wi = wj by rw [this]
    rcases pos wi hwi with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases pos wj hwj with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rw [e1, e2] at h <;> have c := oblPt_inj hρ h
    · rcases lt_trichotomy wi wj with l | l | l
      · exact absurd c.1 (hcam _ _ l h2).ne
      · exact l
      · exact absurd c.1 (hcam _ _ l h1).ne'
    · have := hcbm 0 (m + n + 1 - wj) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · have := hcbm 0 (m + n + 1 - wi) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · rcases lt_trichotomy (m + n + 1 - wi) (m + n + 1 - wj) with l | l | l
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne
      · omega
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne'
  -- the tilt
  set v : ℝ³ := oblPt 0 r1 r2 (-t * α) (s * β) 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ},
      TiltOK ap bp zp aq bq zq ay by' zy (-t * α) (s * β) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (-t * α) (s * β) h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (-t * α) (s * β) := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      t * ((bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (-t * α) (s * β) := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases ht with rfl | rfl
    · right; exact ⟨by linarith, by linarith⟩
    · left; exact ⟨by linarith, by linarith⟩
  -- every test of Lemma 8.0
  have tests : ∀ y ∈ V, ∀ i : ZMod (m + n + 1), y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ez v := by
    intro y hy i hyi hyi1
    obtain ⟨a, b, z, rfl, ha, hb, hin, hr1, hr2⟩ := hVc y hy
    obtain ⟨w, hwlt, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    have hsucc : ((w : ZMod (m + n + 1)) + 1) = ((w + 1 : ℕ) : ZMod (m + n + 1)) := by simp
    rw [hsucc] at hyi1 ⊢
    rcases Nat.lt_or_ge w m with h1 | h1
    · -- a segment of `C1`
      rw [hxC1 w h1.le] at hyi ⊢
      rw [hxC1 (w + 1) h1] at hyi1 ⊢
      apply key
      rcases hb.lt_or_eq with hb | hb
      · exact tiltOK_side1_off (hca _ h1) hb
      · subst hb; exact side1 (hr1 rfl _ h1 hyi hyi1)
    rcases Nat.lt_or_ge w (m + 1) with h2 | h2
    · -- the far edge `A → B`
      have hwm : w = m := by omega
      subst w
      have e1 : x ((m + 1 : ℕ) : ZMod (m + n + 1)) = oblPt O r1 r2 0 (cb n) (dz n) := by
        rw [show m + 1 = m + n - (n - 1) by omega, hxC2 (n - 1) (by omega),
          show n - 1 + 1 = n by omega]
      rw [hxC1 m le_rfl] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases hin with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    · -- a segment of `C2` (inward), the last one ending at the apex
      obtain ⟨l, hln, rfl⟩ : ∃ l, l < n ∧ m + n - l = w := ⟨m + n - w, by omega, by omega⟩
      have e1 : x ((m + n - l + 1 : ℕ) : ZMod (m + n + 1)) = oblPt O r1 r2 0 (cb l) (dz l) := by
        rcases Nat.eq_zero_or_pos l with hl0 | hl0
        · subst hl0
          rw [show m + n - 0 + 1 = m + n + 1 by omega, ZMod.natCast_self, ← hapex,
            show (0 : ZMod (m + n + 1)) = ((0 : ℕ) : ZMod (m + n + 1)) by simp]
          exact hxC1 0 (Nat.zero_le _)
        · rw [show m + n - l + 1 = m + n - (l - 1) by omega, hxC2 (l - 1) (by omega),
            show l - 1 + 1 = l by omega]
      rw [hxC2 l hln] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases ha.lt_or_eq with ha | ha
      · exact tiltOK_side2_off (hcb _ hln) ha
      · subst ha; exact side2 (hr2 rfl _ hln hyi hyi1)
  have hcyc : ∀ i j : ZMod (m + n + 1), j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez v := by
    intro i j h1 h2
    refine tests (x j) ?_ i (fun h => h1 (hxinj h)) (fun h => h2 (hxinj h))
    simp only [hx, triPt]; split_ifs with h
    · exact hC1V _ h
    · exact hC2V _ (by have := ZMod.val_lt j; omega)
  have hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) ez v :=
    fun y hy hyx i => tests y hy i (hyx i) (hyx (i + 1))
  -- the depths are unimodal
  have hxV : ∀ i, x i ∈ V := by
    intro i; simp only [hx, triPt]; split_ifs with h
    · exact hC1V _ h
    · exact hC2V _ (by have := ZMod.val_lt i; omega)
  set Z : ZMod (m + n + 1) → ℝ := fun i => triZ m n cz dz i.val with hZ
  have hZpos : ∀ l, l < m + n + 1 → Z (l : ZMod (m + n + 1)) = triZ m n cz dz l := by
    intro l hl; simp only [hZ, hval l hl]
  have hZ1 : ∀ l, l ≤ m → Z (l : ZMod (m + n + 1)) = cz l := by
    intro l hl; rw [hZpos l (by omega)]; simp [triZ, hl]
  have hZ2 : ∀ l, m + 1 ≤ l → l ≤ m + n → Z (l : ZMod (m + n + 1)) = dz (m + n + 1 - l) := by
    intro l h1 h2; rw [hZpos l (by omega)]; simp [triZ, show ¬ l ≤ m by omega]
  have hZk : Z ((m + n + 1 : ℕ) : ZMod (m + n + 1)) = dz 0 := by
    rw [ZMod.natCast_self, show (0 : ZMod (m + n + 1)) = ((0 : ℕ) : ZMod (m + n + 1)) by simp,
      hZ1 0 (Nat.zero_le _), hdz0]
  -- chain coordinates from `hVc`
  have coords1 : ∀ l, l ≤ m → ∀ j, j < m → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca j) 0 (cz j) → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca (j + 1)) 0 (cz (j + 1)) →
      s * ((ca (j + 1) - ca j) * (cz l - cz j) - (cz (j + 1) - cz j) * (ca l - ca j)) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, hr1, -⟩ := hVc _ (hC1V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst ea ez'
    exact hr1 eb.symm j hj (he ▸ h1) (he ▸ h2)
  have coords2 : ∀ l, l ≤ n → ∀ j, j < n → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb (j + 1)) (dz (j + 1)) → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb j) (dz j) →
      t * ((cb j - cb (j + 1)) * (dz l - dz (j + 1)) - (dz j - dz (j + 1)) * (cb l - cb (j + 1))) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, hr2⟩ := hVc _ (hC2V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst eb ez'
    exact hr2 ea.symm j hj (he ▸ h1) (he ▸ h2)
  have ne1 : ∀ i j, i ≤ m → j ≤ m → i ≠ j →
      oblPt O r1 r2 (ca i) 0 (cz i) ≠ oblPt O r1 r2 (ca j) 0 (cz j) := by
    intro i j hi hj hij he
    have := (oblPt_inj hρ he).1
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact absurd this (hcam i j h hj).ne
    · exact absurd this (hcam j i h hi).ne'
  have ne2 : ∀ i j, i ≤ n → j ≤ n → i ≠ j →
      oblPt O r1 r2 0 (cb i) (dz i) ≠ oblPt O r1 r2 0 (cb j) (dz j) := by
    intro i j hi hj hij he
    have := (oblPt_inj hρ he).2.1
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact absurd this (hcbm i j h hj).ne
    · exact absurd this (hcbm j i h hi).ne'
  -- the sequence lemma's hypotheses for `s Z` (strict, so they survive the tilt)
  have hconcZ : ∀ l : ℕ, 1 ≤ l → l < m → min (s * Z ((l - 1 : ℕ) : ZMod (m + n + 1)))
      (s * Z ((l + 1 : ℕ) : ZMod (m + n + 1))) < s * Z (l : ZMod (m + n + 1)) := by
    intro l h1 h2
    rw [hZ1 _ (by omega), hZ1 _ (by omega), hZ1 _ (by omega)]
    have hc := coords1 (l + 1) (by omega) (l - 1) (by omega)
      (ne1 _ _ (by omega) (by omega) (by omega))
      (by rw [show l - 1 + 1 = l by omega]; exact ne1 _ _ (by omega) (by omega) (by omega))
    rw [show l - 1 + 1 = l by omega] at hc
    have d1 := hcam (l - 1) l (by omega) (by omega)
    have d2 := hcam l (l + 1) (by omega) (by omega)
    by_contra hcon
    push Not at hcon
    rw [le_min_iff] at hcon
    nlinarith [mul_nonneg (sub_nonneg.mpr d1.le) (sub_nonneg.mpr (hcon.2)),
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hcon.1) (sub_nonpos.mpr d2.le)]
  have hconvZ : ∀ l : ℕ, m + 2 ≤ l → l ≤ m + (n) → t * Z (l : ZMod (m + n + 1)) <
      max (t * Z ((l - 1 : ℕ) : ZMod (m + n + 1))) (t * Z ((l + 1 : ℕ) : ZMod (m + n + 1))) := by
    intro l h1 h2
    set j := m + n + 1 - l with hj
    have hj1 : 1 ≤ j := by omega
    have hjn : j < n := by omega
    rw [hZ2 l (by omega) h2, hZ2 (l - 1) (by omega) (by omega),
      show m + n + 1 - (l - 1) = j + 1 by omega]
    have hnext : Z ((l + 1 : ℕ) : ZMod (m + n + 1)) = dz (j - 1) := by
      rcases Nat.lt_or_ge l (m + n) with hl | hl
      · rw [hZ2 (l + 1) (by omega) (by omega), show m + n + 1 - (l + 1) = j - 1 by omega]
      · rw [show l + 1 = m + n + 1 by omega, hZk, show j - 1 = 0 by omega]
    rw [hnext]
    have hc := coords2 (j - 1) (by omega) j hjn
      (ne2 _ _ (by omega) (by omega) (by omega)) (ne2 _ _ (by omega) (by omega) (by omega))
    have e1 := hcbm j (j + 1) (by omega) (by omega)
    have e2 := hcbm (j - 1) j (by omega) (by omega)
    by_contra hcon
    push Not at hcon
    rw [max_le_iff] at hcon
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr e1.le) (sub_nonpos.mpr hcon.2),
      mul_nonneg (sub_nonneg.mpr hcon.1) (sub_nonneg.mpr e2.le)]
  have hw : ∀ v : ℕ, ((m + n + 1 + v : ℕ) : ZMod (m + n + 1)) = (v : ZMod (m + n + 1)) := by
    intro v; rw [Nat.cast_add, ZMod.natCast_self, zero_add]
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  -- the run of the sequence lemma, by the mode
  have hrun : ∃ L c : ℕ, L < m + n + 1 ∧ RunSeq (m + n + 1) L c s Z := by
    rcases hmode with ⟨hts, hAB⟩ | ⟨hts, hinc⟩ | hFB | ⟨hts, hdec⟩
    · -- the strict case: the run is `C1`
      refine ⟨m, 0, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        rcases Nat.lt_or_ge l (m + 2) with h3 | h3
        · left
          obtain rfl : l = m + 1 := by omega
          rw [hZ2 (m + 1) (by omega) (by omega), show m + 1 - 1 = m by omega, hZ1 m le_rfl,
            show m + n + 1 - (m + 1) = n by omega]
          exact hAB
        · have := hconvZ l h3 (by omega); rw [hts] at this; exact lt_max_iff.mp this
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        exact min_lt_iff.mp (hconcZ l (by omega) h2)
    · -- `C1` rises to `A`: the run is `A, B`
      refine ⟨1, m, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        rcases Nat.lt_or_ge (m + l) (m + n + 1) with h3 | h3
        · have := hconvZ (m + l) (by omega) (by omega); rw [hts] at this; exact lt_max_iff.mp this
        · right
          rw [show m + l = m + n + 1 + (m + l - (m + n + 1)) by omega,
            show m + n + 1 + (m + l - (m + n + 1)) + 1 = m + n + 1 + (m + l - (m + n + 1) + 1) by omega,
            hw, hw, hZ1 _ (by omega), hZ1 _ (by omega)]
          exact hinc _ (by omega)
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl; omega
    · -- `C2` reversed rises from `B` to the apex: the run is `C1`
      refine ⟨m, 0, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        right
        have hl1 : Z ((l + 1 : ℕ) : ZMod (m + n + 1)) = dz (m + n - l) := by
          rcases Nat.lt_or_ge l (m + n) with h | h
          · rw [hZ2 (l + 1) (by omega) (by omega)]; congr 1; omega
          · rw [show l + 1 = m + n + 1 by omega, hZk, show m + n - l = 0 by omega]
        rw [hZ2 l (by omega) (by omega), hl1]
        have := hFB (m + n - l) (by omega)
        rwa [show m + n - l + 1 = m + n + 1 - l by omega] at this
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        exact min_lt_iff.mp (hconcZ l (by omega) h2)
    · -- same-sign sector, `C1` falls from the apex: the run is `C2` reversed and the apex
      refine ⟨n, m + 1, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        left
        rw [show m + 1 + l = m + n + 1 + (l - n) by omega,
          show m + n + 1 + (l - n) - 1 = m + n + 1 + (l - n - 1) by omega,
          hw, hw, hZ1 _ (by omega), hZ1 _ (by omega)]
        have := hdec (l - n - 1) (by omega)
        rwa [show l - n - 1 + 1 = l - n by omega] at this
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have := hconvZ (m + 1 + l) (by omega) (by omega)
        rw [hts, lt_max_iff] at this
        rcases this with h | h
        · left; linarith
        · right; linarith
  obtain ⟨L, c, hLK, hR⟩ := hrun
  exact isRupert_of_tilted_localMax V ez v hez (k := m + n + 1) (by omega) x hxV hcyc hrest s hs
    (RunSeq (m + n + 1) L c s) (isOpen_runSeq _ _ _ s) (fun z k hk hz => runSeq_smul hk hz)
    (by rw [show (fun i => ⟪x i, ez⟫) = Z from funext hdepth]; exact hR)
    (fun z hz => runSeq_localMax hLK hz)

/-- A chain is strictly concave in `s z`: no interior point is below both
neighbours. -/
theorem ChainOK.conc {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOK Q z0 s m ca cz) :
    ∀ l, 1 ≤ l → l < m → min (s * cz (l - 1)) (s * cz (l + 1)) < s * cz l := by
  intro l h1 h2
  have d1 := C.inc (l - 1) (by omega); rw [show l - 1 + 1 = l by omega] at d1
  have d2 := C.inc l h2
  have hc := C.side (ca (l + 1)) (cz (l + 1)) (C.mem (l + 1) (by omega)) (l - 1) (by omega)
    (fun h => by linarith [h.1]) (fun h => by rw [show l - 1 + 1 = l by omega] at h; linarith [h.1])
  rw [show l - 1 + 1 = l by omega] at hc
  by_contra hcon
  push Not at hcon
  rw [le_min_iff] at hcon
  nlinarith [mul_nonneg (sub_nonneg.mpr d1.le) (sub_nonneg.mpr (hcon.2)),
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hcon.1) (sub_nonpos.mpr d2.le)]

/-- If the far end is the face's strict top in `s z`, `s z` rises strictly
along the whole chain. -/
theorem ChainOK.rise_of_far_top {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOK Q z0 s m ca cz)
    (htop : ∀ a z, Q a z → ¬ (a = ca m ∧ z = cz m) → s * z < s * cz m) :
    ∀ l, l < m → s * cz l < s * cz (l + 1) := by
  have conc := C.conc
  have step : ∀ d : ℕ, ∀ l, m = l + 1 + d → s * cz l < s * cz (l + 1) := by
    intro d
    induction d with
    | zero =>
      intro l hl
      have hm : m = l + 1 := by omega
      subst hm
      exact htop (ca l) (cz l) (C.mem l (by omega))
        (fun h => by have := C.inc l (by omega); linarith [h.1])
    | succ d ih =>
      intro l hl
      have h1 := ih (l + 1) (by omega)
      have h2 := conc (l + 1) (by omega) (by omega)
      rw [show l + 1 - 1 = l by omega] at h2
      rw [min_lt_iff] at h2
      rcases h2 with h | h
      · exact h
      · linarith
  intro l hl
  exact step (m - l - 1) l (by omega)

/-- If the apex is the face's strict top in `s z`, `s z` falls strictly along
the whole chain. -/
theorem ChainOK.fall_of_apex_top {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOK Q z0 s m ca cz)
    (htop : ∀ a z, Q a z → ¬ (a = 0 ∧ z = z0) → s * z < s * z0) :
    ∀ l, l < m → s * cz (l + 1) < s * cz l := by
  have conc := C.conc
  intro l hl
  induction l with
  | zero =>
    have := htop (ca 1) (cz 1) (C.mem 1 (by omega))
      (fun h => by have := C.inc 0 (by omega); rw [C.start.1] at this; linarith [h.1])
    rw [C.start.2]; exact this
  | succ l ih =>
    have h1 := ih (by omega)
    have h2 := conc (l + 1) (by omega) (by omega)
    rw [show l + 1 - 1 = l by omega] at h2
    rw [min_lt_iff] at h2
    rcases h2 with h | h
    · linarith
    · exact h

/-- The cases of "Lemma T at the tie" for two faces given by their point sets
`Q1`, `Q2` (oblique `(t, z)` coordinates on the two rays, apex `(0, z0)`, far
ends `(A, zA)`, `(B, zB)`): for a sign `s`, the far end `A` is the strict top of
`Q1` in `s z`, or `B` the strict bottom of `Q2`, or the apex the strict top of
`Q1` or of `Q2`. With `s = ±1` these are cases (b) and (c) of
`FEWER-FACES-PROOFS.md` (lowest or highest vertex at a far end or at the shared
vertex). -/
def VTie (Q1 Q2 : ℝ → ℝ → Prop) (z0 A zA B zB : ℝ) : Prop :=
  ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ((∀ a z, Q1 a z → ¬ (a = A ∧ z = zA) → s * z < s * zA) ∨
      (∀ b z, Q2 b z → ¬ (b = B ∧ z = zB) → s * zB < s * z) ∨
      (∀ a z, Q1 a z → ¬ (a = 0 ∧ z = z0) → s * z < s * z0) ∨
      (∀ b z, Q2 b z → ¬ (b = 0 ∧ z = z0) → s * z < s * z0))

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, from chains, at the tie.** As
`isRupert_vertex_frame`, but the far depths may tie when one of the cases of
`VTie` holds (Lemma T at the tie, (b) and (c)). -/
theorem isRupert_vertex_frame_tie (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ}
    (hU1 : ∃ m ca cz, ChainOK Q1 z0 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 z0 (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 z0 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (hfarT : ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
      cz m ≠ dz n ∨ VTie Q1 Q2 z0 (ca m) (cz m) (cb n) (dz n)) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  have hne := hfarT m0 ca0 cz0 n0 cb0 dz0 U1 U2
  -- the core, for a sign `s` and chains `C1` (sign `s`) and `C2` (sign `-s`)
  have core : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ (t : ℝ), (t = 1 ∨ t = -1) →
      ∀ {m n : ℕ} {ca cz cb dz : ℕ → ℝ},
      ChainOK Q1 z0 s m ca cz → ChainOK Q2 z0 (-t) n cb dz →
      ((t = s ∧ s * dz n < s * cz m) ∨ (t = s ∧ ∀ l, l < m → s * cz l < s * cz (l + 1)) ∨
        (∀ j, j < n → s * dz (j + 1) < s * dz j) ∨ (t = -s ∧ ∀ l, l < m → s * cz (l + 1) < s * cz l)) →
      ca m = ca0 m0 → cb n = cb0 n0 → IsRupert V := by
    intro s hs t ht m n ca cz cb dz C1 C2 hmode ea eb
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
        t * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
      intro b z hq l hl h1 h2
      have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
        (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      have e : t * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
        -t * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
      rw [e]; exact this
    have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
    have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
    refine isRupert_triShadow_gen O r1 r2 hρ C1.one_le C2.one_le s hs t ht one_pos one_pos ca cz cb dz
      c10.1 c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
      (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hmode
    intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
    · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
      · rcases far1 a z hq with h | ⟨e1, e2⟩
        · left; exact far_tiltOK (by linarith)
        · right; left; rw [e1, e2]
      · intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
    · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
      · rcases far2 b z hq with h | ⟨e1, e2⟩
        · left; exact far_tiltOK (by linarith)
        · right; right; rw [e1, e2]
      · intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
    · refine ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK ?_), fun h => absurd h hb.ne',
        fun h => absurd h ha.ne'⟩
      rw [ea, eb]; exact hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have ch1 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ m ca cz, ChainOK Q1 z0 σ m ca cz := by
    rintro σ (rfl | rfl)
    exacts [⟨m0, ca0, cz0, U1⟩, ⟨m1, ca1, cz1, L1⟩]
  have ch2 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ n cb dz, ChainOK Q2 z0 σ n cb dz := by
    rintro σ (rfl | rfl)
    exacts [⟨n0, cb0, dz0, U2⟩, ⟨n1, cb1, dz1, L2⟩]
  have neg : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (-σ = 1 ∨ -σ = -1) := by
    rintro σ (rfl | rfl) <;> norm_num
  rcases hne with hne | ⟨s, hs, hv | hv | hv | hv⟩
  · have eU1 := L1.far_eq U1
    have eU2 := L2.far_eq U2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact core (-1) (Or.inr rfl) (-1) (Or.inr rfl) L1 (by simpa using U2)
        (Or.inl ⟨rfl, by rw [eU1.2]; linarith⟩) eU1.1 rfl
    · exact core 1 (Or.inl rfl) 1 (Or.inl rfl) U1 (by simpa using L2)
        (Or.inl ⟨rfl, by rw [eU2.2]; linarith⟩) rfl eU2.1
  · -- `A` is the top of `Q1` in `s z`: `C1` rises to it (mixed sector)
    obtain ⟨m, ca, cz, C1⟩ := ch1 s hs
    obtain ⟨n, cb, dz, C2⟩ := ch2 (-s) (neg s hs)
    have e1 := C1.far_eq U1
    have e2 := C2.far_eq U2
    refine core s hs s hs C1 C2 (Or.inr (Or.inl ⟨rfl, C1.rise_of_far_top ?_⟩)) e1.1 e2.1
    intro a z hq hn
    rw [e1.2]; exact hv a z hq (fun h => hn ⟨by rw [e1.1]; exact h.1, by rw [e1.2]; exact h.2⟩)
  · -- `B` is the bottom of `Q2` in `s z`: `C2` reversed rises from it (mixed sector)
    obtain ⟨m, ca, cz, C1⟩ := ch1 s hs
    obtain ⟨n, cb, dz, C2⟩ := ch2 (-s) (neg s hs)
    have e1 := C1.far_eq U1
    have e2 := C2.far_eq U2
    have hr := C2.rise_of_far_top (fun b z hq hn => by
      rw [e2.2]
      have := hv b z hq (fun h => hn ⟨by rw [e2.1]; exact h.1, by rw [e2.2]; exact h.2⟩)
      linarith)
    exact core s hs s hs C1 C2 (Or.inr (Or.inr (Or.inl fun j hj => by
      have := hr j hj; linarith))) e1.1 e2.1
  · -- the apex is the top of `Q1` in `s z`: `C1` falls from it (same-sign sector)
    obtain ⟨m, ca, cz, C1⟩ := ch1 s hs
    obtain ⟨n, cb, dz, C2⟩ := ch2 s hs
    have e1 := C1.far_eq U1
    have e2 := C2.far_eq U2
    exact core s hs (-s) (neg s hs) C1 (by simpa using C2)
      (Or.inr (Or.inr (Or.inr ⟨rfl, C1.fall_of_apex_top hv⟩))) e1.1 e2.1
  · -- the apex is the top of `Q2` in `s z`: `C2` reversed rises to it (same-sign sector)
    obtain ⟨m, ca, cz, C1⟩ := ch1 s hs
    obtain ⟨n, cb, dz, C2⟩ := ch2 s hs
    have e1 := C1.far_eq U1
    have e2 := C2.far_eq U2
    exact core s hs (-s) (neg s hs) C1 (by simpa using C2)
      (Or.inr (Or.inr (Or.inl (C2.fall_of_apex_top hv)))) e1.1 e2.1


/-- The far-end condition of Lemma T with the tie allowed, for faces `Q1`, `Q2`
meeting in `v` with far ends `p ∈ Q1`, `q ∈ Q2` and heights `h`: the far
heights differ, or for a sign `s` the far end `p` is the strict top of `Q1` in
`s h`, or `q` the strict bottom of `Q2`, or `v` the strict top of `Q1` or of
`Q2` (`VTie`). -/
def TieH (Q1 Q2 : Finset ℝ³) (v p q : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  h p ≠ h q ∨ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ((∀ x ∈ Q1, x ≠ p → s * h x < s * h p) ∨ (∀ x ∈ Q2, x ≠ q → s * h q < s * h x) ∨
      (∀ x ∈ Q1, x ≠ v → s * h x < s * h v) ∨ (∀ x ∈ Q2, x ≠ v → s * h x < s * h v))

/-- Exchanging the two faces. -/
theorem TieH.swap {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h : ℝ³ → ℝ} (H : TieH Q1 Q2 v p q h) :
    TieH Q2 Q1 v q p h := by
  rcases H with hne | ⟨s, hs, hv | hv | hv | hv⟩
  · exact Or.inl (Ne.symm hne)
  · refine Or.inr ⟨-s, by rcases hs with rfl | rfl <;> norm_num, Or.inr (Or.inl fun x hx hxp => ?_)⟩
    have := hv x hx hxp; linarith
  · refine Or.inr ⟨-s, by rcases hs with rfl | rfl <;> norm_num, Or.inl fun x hx hxq => ?_⟩
    have := hv x hx hxq; linarith
  · exact Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr hv))⟩
  · exact Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl hv))⟩

/-- Transport by an injective map that rescales the heights by `r > 0`. -/
theorem TieH.map {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h h' : ℝ³ → ℝ} (g : ℝ³ → ℝ³)
    (hg : Function.Injective g) {r : ℝ} (hr : 0 < r) (hh : ∀ x, h' (g x) = h x / r)
    (H : TieH Q1 Q2 v p q h) [DecidableEq ℝ³] : TieH (Q1.image g) (Q2.image g) (g v) (g p) (g q) h' := by
  have lt : ∀ {a b : ℝ} {s : ℝ}, s * a < s * b → s * (a / r) < s * (b / r) := by
    intro a b s hab
    rw [show s * (a / r) = (s * a) / r by ring, show s * (b / r) = (s * b) / r by ring]
    exact div_lt_div_of_pos_right hab hr
  rcases H with hne | ⟨s, hs, hv | hv | hv | hv⟩
  · left; rw [hh, hh]; intro e; apply hne
    have := congrArg (· * r) e; simp only [div_mul_cancel₀ _ hr.ne'] at this; exact this
  all_goals refine Or.inr ⟨s, hs, ?_⟩
  · refine Or.inl fun y hy hyc => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hh, hh]; exact lt (hv x hx (fun e => hyc (by rw [e])))
  · refine Or.inr (Or.inl fun y hy hyc => ?_)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hh, hh]; exact lt (hv x hx (fun e => hyc (by rw [e])))
  · refine Or.inr (Or.inr (Or.inl fun y hy hyc => ?_))
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hh, hh]; exact lt (hv x hx (fun e => hyc (by rw [e])))
  · refine Or.inr (Or.inr (Or.inr fun y hy hyc => ?_))
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hh, hh]; exact lt (hv x hx (fun e => hyc (by rw [e])))

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, in frame coordinates.** As
`isRupert_vertex_coords`, with the far depths allowed to tie when a far end or
the shared vertex is a strict top or bottom of its face (`VTie`).  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
every other point at `a, b > 0`. -/
theorem isRupert_vertex_coords_tie (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieH Q1 Q2 v p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1) : IsRupert V := by
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
  have chains1 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S1) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK S1 (v 2) (by rw [hS1, Finset.mem_image]; exact ⟨v, hv1, by rw [hav]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      rw [← e1]; refine apos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hav]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne1
      refine ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [apos p hp hpv]
    · intro q hq q' hq' e
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      have : p = p' := hinj (h1V hp) (h1V hp') (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨by rw [e1, e1']; exact e, rfl⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : a p ≠ a p' := fun h => d n1 e1 e2 e1' e2'
        (hinj (h1V hp) (h1V hp') (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨h, rfl⟩))
      have := orient_ne_of_frame1 (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (ak := a p'') hne (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  have chains2 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK S2 (v 2) (by rw [hS2, Finset.mem_image]; exact ⟨v, hv2, by rw [hbv]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      rw [← e1]; refine bpos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hbv]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne2
      refine ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [bpos p hp hpv]
    · intro q hq q' hq' e
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      have : p = p' := hinj (h2V hp) (h2V hp') (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, by rw [e1, e1']; exact e⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : b p ≠ b p' := fun h => d n1 e1 e2 e1' e2'
        (hinj (h2V hp) (h2V hp') (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, h⟩))
      have := orient_ne_of_frame2 (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (bk := b p'') hne (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_vertex_frame_tie O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (z0 := v 2) (chains1 1 (Or.inl rfl)) (chains1 (-1) (Or.inr rfl)) (chains2 1 (Or.inl rfl))
    (chains2 (-1) (Or.inr rfl)) ?_ ?_ ?_ ?_ V ?_ ?_ ?_ ?_
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
    refine Or.inr (Or.inr ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩)
    intro m ca cz n cb dz C1 C2
    have hA := C1.far_pos
    have hB := C2.far_pos
    have hxa0 := apos xa hxa hxav
    have hxb0 := bpos xb hxb hxbv
    have le1 : a xa ≤ ca m := by
      by_cases e : a xa = ca m ∧ xa 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
    have le2 : b xb ≤ cb n := by
      by_cases e : b xb = cb n ∧ xb 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith
  · intro m ca cz n cb dz C1 C2
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    obtain ⟨q, hq, f1, f2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    have hpq : p ≠ q := by
      intro e; subst e
      have := only p hp hq; subst this
      linarith [C1.far_pos]
    have pmax : ∀ p' ∈ Q1, a p' ≤ a p := fun p' hp' => by
      rw [e1]
      by_cases e : a p' = ca m ∧ p' 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hp') e).le
    have qmax : ∀ q' ∈ Q2, b q' ≤ b q := fun q' hq' => by
      rw [f1]
      by_cases e : b q' = cb n ∧ q' 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq') e).le
    rcases hfarZ p hp q hq hpq pmax qmax with hne | ⟨s, hs, hv | hv | hv | hv⟩
    · left; rw [← e2, ← f2]; exact hne
    · refine Or.inr ⟨s, hs, Or.inl fun x z hxz hn => ?_⟩
      obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
      rw [← g2, ← e2]
      exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, e1], by rw [← g2, h, e2]⟩)
    · refine Or.inr ⟨s, hs, Or.inr (Or.inl fun x z hxz hn => ?_)⟩
      obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
      rw [← g2, ← f2]
      exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, f1], by rw [← g2, h, f2]⟩)
    · refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl fun x z hxz hn => ?_))⟩
      obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
      rw [← g2]
      exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, hav], by rw [← g2, h]⟩)
    · refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr fun x z hxz hn => ?_))⟩
      obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
      rw [← g2]
      exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, hbv], by rw [← g2, h]⟩)

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, the planes vertical.**  `Q1`, `Q2` are facets
(functionals `f1`, `f2`) meeting in `v`, both planes containing the vertical line
through `v`. -/
theorem isRupert_facets_vertex_vertical_tie (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieH Q1 Q2 v p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨p1, hp1, hp1v⟩ := hne1
  obtain ⟨p2, hp2, hp2v⟩ := hne2
  have m21 : f2 p1 < 0 := n2 p1 (h1V hp1) (fun h => hp1v (only p1 hp1 h))
  have m12 : f1 p2 < 0 := n1 p2 (h2V hp2) (fun h => hp2v (only p2 h hp2))
  obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
  have v1 := z1 v hv1; have v2 := z2 v hv2
  have hγ1 : γ1 = 0 := by
    rw [h1] at e1 v1; simp [ez] at e1; linarith
  have hγ2 : γ2 = 0 := by
    rw [h2] at e2 v2; simp [ez] at e2; linarith
  have g1 : ∀ p, f1 p = α1 * (p 0 - v 0) + β1 * (p 1 - v 1) := by
    intro p; have := v1; rw [h1, hγ1] at this ⊢; linarith
  have g2 : ∀ p, f2 p = α2 * (p 0 - v 0) + β2 * (p 1 - v 1) := by
    intro p; have := v2; rw [h2, hγ2] at this ⊢; linarith
  -- the frame
  set O : ℝ² := !₂[v 0, v 1] with hO
  set r1 : ℝ² := !₂[p1 0 - v 0, p1 1 - v 1] with hr1
  set r2 : ℝ² := !₂[p2 0 - v 0, p2 1 - v 1] with hr2
  have q11 : α1 * (p1 0 - v 0) + β1 * (p1 1 - v 1) = 0 := by rw [← g1]; exact z1 p1 hp1
  have q22 : α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) = 0 := by rw [← g2]; exact z2 p2 hp2
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 p2 * (p1 0 - v 0) = 0 := by
      rw [g1]; linear_combination (p2 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 p2 * (p1 1 - v 1) = 0 := by
      rw [g1]; linear_combination (p2 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 p1; rw [r10, r11] at this; linarith
  set ρ := cross2 r1 r2 with hρdef
  set a : ℝ³ → ℝ := fun p => cross2 !₂[p 0 - v 0, p 1 - v 1] r2 / ρ with ha
  set b : ℝ³ → ℝ := fun p => cross2 r1 !₂[p 0 - v 0, p 1 - v 1] / ρ with hb
  have hxy : ∀ p : ℝ³, p 0 - v 0 = a p * r1 0 + b p * r2 0 ∧ p 1 - v 1 = a p * r1 1 + b p * r2 1 := by
    intro p
    obtain ⟨c0, c1⟩ := cramer2 !₂[p 0 - v 0, p 1 - v 1] r1 r2 hρ
    simp at c0 c1; exact ⟨c0, c1⟩
  have hy : ∀ p : ℝ³, p = oblPt O r1 r2 (a p) (b p) (p 2) := by
    intro p; obtain ⟨c0, c1⟩ := hxy p
    ext j; fin_cases j
    · simp only [oblPt, hO]; simp; linarith
    · simp only [oblPt, hO]; simp; linarith
    · simp [oblPt]
  have r10 : r1 0 = p1 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = p1 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = p2 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = p2 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 p2 := by
    intro p; rw [g1 p, g1 p2, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 p1 := by
    intro p; rw [g2 p, g2 p1, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination b p * q22
  have hb1 : ∀ p ∈ Q1, b p = 0 := fun p hp => by
    have := G1 p; rw [z1 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m12.ne
  have ha2 : ∀ p ∈ Q2, a p = 0 := fun p hp => by
    have := G2 p; rw [z2 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m21.ne
  have hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p := fun p hp hq => by
    have := n1 p hp hq; rw [G1] at this; nlinarith
  have ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p := fun p hp hq => by
    have := n2 p hp hq; rw [G2] at this; nlinarith
  have hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³) := by
    intro p hp q hq e
    simp only [Prod.mk.injEq] at e
    by_contra hpq
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [e.1, e.2] at c0 c1
    rcases hpar p hp q hq hpq with h | h <;> apply h <;> linarith
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieH Q1 Q2 v p q (fun x => x 2) := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hin' : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 := by
    obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨xa, hxa, xb, hxb, hxav, hxbv, fun y hy hy1 hy2 => ?_⟩
    have k := h y hy hy1 hy2
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne] at k
    exact k
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · -- negative orientation: exchange the two faces
    have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_vertex_coords_tie O r2 r1 hpos' V Q2 Q1 v b a (fun p _ => by rw [swap]; exact hy p)
      h2V h1V (by rw [Finset.inter_comm]; exact hint) ha2 ha2' hb1 hb1' ⟨p2, hp2, hp2v⟩
      ⟨p1, hp1, hp1v⟩ hcol ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).swap) ?_
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinj hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxbv, hxav, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_vertex_coords_tie O r1 r2 hpos V Q1 Q2 v a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ hcol hinj hfar' hin'

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie** for two facets `Q1`, `Q2` (functionals `f1`, `f2`)
meeting in `v`, viewed along the line `v + ℝ e` of their planes: no three points
collinear, no segment parallel to `e`, distinct depths along `e` at the far ends
(the point of `Q1` where `f2` is least, that of `Q2` where `f1` is least), and
every point off both facets inside the shadow triangle of `v` and some `xa ∈
Q1`, `xb ∈ Q2`. -/
theorem isRupert_facets_vertex_tie (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e : ℝ³) (he : e ≠ 0) (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieH Q1 Q2 v p q (fun x => ⟪x, e⟫))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos e he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  have hgz : ∀ p, g p 2 = ⟪p, e⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p e
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • e := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  -- functionals transported by the inverse rotation
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  have tF1 : ∀ p, F1 (g p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (g p) = f2 p := fun p => by simp [hF2, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f (v + e) = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = f (v + r⁻¹ • e) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 h1 _
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have memg : ∀ (S : Finset ℝ³) p, g p ∈ S.image g ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e], Finset.mem_image_of_mem g⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (g p)) → ∀ q ∈ S.image g, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_facets_vertex_vertical_tie (V.image g) (Q1.image g) (Q2.image g) (g v)
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) e1) (tz f2 (z2 v hv2) e2) ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨p, hp, hpv⟩ := hne1
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hpv (hginj h)⟩
  · obtain ⟨p, hp, hpv⟩ := hne2
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hpv (hginj h)⟩
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun w hw => ?_)))
    intro hpq hpw hqw c h
    apply hcol p hp q hq w hw (fun e => hpq (by rw [e])) (fun e => hpw (by rw [e]))
      (fun e => hqw (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · refine allg V _ (fun p hp => allg V _ (fun q hq => ?_))
    intro hpq
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hpar p hp q hq (fun e => hpq (by rw [e])) ((g (q - p)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2
    refine (hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)).map g
      hginj hr (fun x => hgz x)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxav (hginj e), fun e => hxbv (hginj e), allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

/-- General position for Lemma T at the line of the planes of two facets, with
the tie allowed: no segment parallel to the line, and at the far ends `TieH`
(far depths distinct, or a far end or the shared vertex a strict top or bottom
of its face). Weaker than `TriGenFar` (`TriGenFar.tie`). -/
def TriGenTie (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieH Q1 Q2 v p q (fun x => ⟪x, e⟫)

theorem TriGenFar.tie {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenFar V Q1 Q2 v) :
    TriGenTie V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq h1 h2 => Or.inl (hfar p hp q hq hpq h1 h2)⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, facet form** (`FEWER-FACES-PROOFS.md` §7): two facets
`Q1`, `Q2` of `V` (no three points collinear) meeting in the single vertex `v`,
with `TriGenFar` at the line of their planes, and every point off both facets
inside the shadow triangle of `v`, `xa ∈ Q1`, `xb ∈ Q2` (stated with any facet
functionals `f1`, `f2`): Rupert. -/
theorem isRupert_of_facets_vertex_tie (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenTie V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨p1, hp1, hp1v⟩ := hne1
  obtain ⟨p2, hp2, hp2v⟩ := hne2
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨K1, α1, β1, γ1, hf1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, hf2⟩ := affine_xyz f2
  set e : ℝ³ := !₂[β1 * γ2 - γ1 * β2, γ1 * α2 - α1 * γ2, α1 * β2 - β1 * α2] with he
  have dif : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (K α β γ : ℝ), (∀ p, f p = K + α * p 0 + β * p 1 + γ * p 2) →
      ∀ p q, f q - f p = α * (q 0 - p 0) + β * (q 1 - p 1) + γ * (q 2 - p 2) := by
    intro f K α β γ h p q; rw [h, h]; ring
  have e1 : f1 (v + e) = 0 := by
    have := dif f1 K1 α1 β1 γ1 hf1 v (v + e)
    rw [z1 v hv1] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have e2 : f2 (v + e) = 0 := by
    have := dif f2 K2 α2 β2 γ2 hf2 v (v + e)
    rw [z2 v hv2] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have hn1 : f1 p2 < 0 := n1 p2 (h2V hp2) (fun h => hp2v (only p2 h hp2))
  have hn2 : f2 p1 < 0 := n2 p1 (h1V hp1) (fun h => hp1v (only p1 hp1 h))
  have hne : e ≠ 0 := by
    intro h0
    have c0 := congrArg (fun p : ℝ³ => p 0) h0
    have c1 := congrArg (fun p : ℝ³ => p 1) h0
    have c2 := congrArg (fun p : ℝ³ => p 2) h0
    simp [he] at c0 c1 c2
    have d14 := dif f1 K1 α1 β1 γ1 hf1 v p2
    have d21 := dif f2 K2 α2 β2 γ2 hf2 v p1
    have d11 := dif f1 K1 α1 β1 γ1 hf1 v p1
    rw [z1 v hv1, sub_zero] at d14
    rw [z1 v hv1, z1 p1 hp1, sub_zero] at d11
    rw [z2 v hv2, sub_zero] at d21
    have key : (f1 p2) * (f2 p1) = 0 := by
      rw [d14, d21]
      have := d11
      linear_combination (α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) + γ2 * (p2 2 - v 2)) * this.symm +
        ((p1 1 - v 1) * (p2 0 - v 0) - (p1 0 - v 0) * (p2 1 - v 1)) * c2 +
        ((p1 2 - v 2) * (p2 1 - v 1) - (p1 1 - v 1) * (p2 2 - v 2)) * c0 +
        ((p1 0 - v 0) * (p2 2 - v 2) - (p1 2 - v 2) * (p2 0 - v 0)) * c1
    nlinarith
  obtain ⟨hpar, hfarZ⟩ := hT f1 f2 z1 n1 z2 n2 e hne e1 e2
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_facets_vertex_tie V Q1 Q2 v h1V h2V hint f1 f2 z1 n1 z2 n2 e hne e1 e2
    ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ ?_ hpar hfarZ
    ⟨xa, hxa, xb, hxb, hxav, hxbv, hin' f1 f2 z1 n1 z2 n2⟩
  exact hgen


/-- Three heights, the first two different: one of the first two is the strict
top or bottom of the three. -/
theorem three_heights {hv hp hw : ℝ} (h : hv ≠ hp) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ((s * hv < s * hp ∧ s * hw < s * hp) ∨ (s * hp < s * hv ∧ s * hw < s * hv)) := by
  rcases lt_or_gt_of_ne h with h1 | h1
  · rcases lt_or_ge hw hp with h2 | h2
    · exact ⟨1, Or.inl rfl, Or.inl ⟨by linarith, by linarith⟩⟩
    · exact ⟨-1, Or.inr rfl, Or.inr ⟨by linarith, by linarith⟩⟩
  · rcases lt_or_ge hw hv with h2 | h2
    · exact ⟨1, Or.inl rfl, Or.inr ⟨by linarith, by linarith⟩⟩
    · exact ⟨-1, Or.inr rfl, Or.inl ⟨by linarith, by linarith⟩⟩

/-- General position for Lemma T when one face is a triangle: no segment
parallel to the line of the planes, and the far ends do not tie with each other
and with the shared vertex at once (a coincidence of codimension 2). With a
triangle face this gives `TriGenTie` (`TriGenTri.tie`). -/
def TriGenTri (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        ⟪p, e⟫ ≠ ⟪q, e⟫ ∨ ⟪p, e⟫ ≠ ⟪v, e⟫

/-- A triangle `{v, p, w}` (`v`, `p` given, distinct): its points are `v`, `p` and
one more. -/
theorem exists_third_of_card_three {Q : Finset ℝ³} (hQ : Q.card = 3) {v p : ℝ³} (hv : v ∈ Q)
    (hp : p ∈ Q) (hvp : v ≠ p) : ∃ w, ∀ x ∈ Q, x = v ∨ x = p ∨ x = w := by
  classical
  have h1 : ((Q.erase v).erase p).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hvp, hp⟩), Finset.card_erase_of_mem hv, hQ]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
  refine ⟨w, fun x hx => ?_⟩
  by_cases e1 : x = v
  · exact Or.inl e1
  by_cases e2 : x = p
  · exact Or.inr (Or.inl e2)
  have : x ∈ (Q.erase v).erase p := Finset.mem_erase.mpr ⟨e2, Finset.mem_erase.mpr ⟨e1, hx⟩⟩
  rw [hw, Finset.mem_singleton] at this
  exact Or.inr (Or.inr this)

theorem TriGenTri.tie {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (hint : Q1 ∩ Q2 = {v}) (hcard : Q1.card = 3 ∨ Q2.card = 3) (h : TriGenTri V Q1 Q2 v) :
    TriGenTie V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  refine ⟨hpar, fun p hp q hq hpq hpm hqm => ?_⟩
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ x ∈ Q1, x ∈ Q2 → x = v := by
    intro x h1 h2
    have : x ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  rcases hfar p hp q hq hpq hpm hqm with hne | hpv
  · exact Or.inl hne
  by_cases ht : ⟪p, e⟫ = ⟪q, e⟫
  swap
  · exact Or.inl ht
  right
  rcases hcard with hc | hc
  · -- `Q1` is a triangle: `p` or `v` is its strict top or bottom
    have hpv' : v ≠ p := fun e' => hpv (by rw [e'])
    obtain ⟨w, hw⟩ := exists_third_of_card_three hc hv1 hp hpv'
    obtain ⟨s, hs, hst | hst⟩ := three_heights (hv := ⟪v, e⟫) (hp := ⟪p, e⟫) (hw := ⟪w, e⟫)
      (fun e' => hpv e'.symm)
    · refine ⟨s, hs, Or.inl fun x hx hxp => ?_⟩
      rcases hw x hx with rfl | rfl | rfl
      · exact hst.1
      · exact absurd rfl hxp
      · exact hst.2
    · refine ⟨s, hs, Or.inr (Or.inr (Or.inl fun x hx hxv => ?_))⟩
      rcases hw x hx with rfl | rfl | rfl
      · exact absurd rfl hxv
      · exact hst.1
      · exact hst.2
  · -- `Q2` is a triangle: `q` or `v` is its strict top or bottom
    have hqv : ⟪q, e⟫ ≠ ⟪v, e⟫ := by rw [← ht]; exact hpv
    have hvq : v ≠ q := fun e' => hqv (by rw [e'])
    obtain ⟨w, hw⟩ := exists_third_of_card_three hc hv2 hq hvq
    obtain ⟨s, hs, hst | hst⟩ := three_heights (hv := ⟪v, e⟫) (hp := ⟪q, e⟫) (hw := ⟪w, e⟫)
      (fun e' => hqv e'.symm)
    · refine ⟨-s, by rcases hs with rfl | rfl <;> norm_num, Or.inr (Or.inl fun x hx hxq => ?_)⟩
      rcases hw x hx with rfl | rfl | rfl
      · linarith [hst.1]
      · exact absurd rfl hxq
      · linarith [hst.2]
    · refine ⟨s, hs, Or.inr (Or.inr (Or.inr fun x hx hxv => ?_))⟩
      rcases hw x hx with rfl | rfl | rfl
      · exact absurd rfl hxv
      · exact hst.1
      · exact hst.2

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, the tie allowed.** As `isRupert_triShadow2`, with
three modes in place of `s z_B < s z_A`: strict; `C1` rises strictly in `s z`
to `A`; `C2` reversed rises strictly from `B` to its start `C2 0` (and on to
`C1 0` by `hap`). The last two allow `z_A = z_B` (Lemma T at the tie, (b), (c),
mixed sectors). -/
theorem isRupert_triShadow2_gen (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hap : s * dz 0 < s * cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (a * cb n + b * ca m < ca m * cb n ∨ y = oblPt O r1 r2 (ca m) 0 (cz m) ∨
        y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
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
  set v : ℝ³ := oblPt 0 r1 r2 (-s) s 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (-s) s →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (-s) s h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (-s) s := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨one_pos, by linarith⟩
    · right; exact ⟨by norm_num, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      s * ((bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (-s) s := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases hs with rfl | rfl
    · right; exact ⟨by norm_num, by linarith⟩
    · left; exact ⟨by norm_num, by linarith⟩
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
      · exact far_tiltOK hin
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
      apply vert_tiltOK (by linarith)
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

set_option maxHeartbeats 4000000 in
/-- The core of `isRupert_edge_frame_tie` in the mixed sectors, for given chains and a
mode of `isRupert_triShadow2_gen`. -/
theorem edge_core_gen (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s)
    {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOK Q1 z1s s m ca cz) (C2 : ChainOK Q2 z2s (-s) n cb dz)
    (hmode : s * dz n < s * cz m ∨ (∀ l, l < m → s * cz l < s * cz (l + 1)) ∨
      (∀ j, j < n → s * dz (j + 1) < s * dz j))
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) : IsRupert V := by
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
  refine isRupert_triShadow2_gen O r1 r2 hρ C1.one_le C2.one_le s hs ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]; exact hap) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hmode
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | ⟨e1, e2⟩
      · left; linarith
      · right; left; rw [e1, e2]
    · intro ha _; subst ha; exact apx z (hap1 z hq)
    · intro ha; subst ha; exact side2 0 z (q2of z hq)
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | ⟨e1, e2⟩
      · left; linarith
      · right; right; rw [e1, e2]
    · intro _ hb; subst hb; exact apx z (hap2 z hq)
    · intro hb; subst hb; exact side1 0 z (q1of z hq)
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl hin, fun h => absurd h ha.ne',
      fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 4000000 in
/-- The core of `isRupert_edge_frame_tie` in the same-sign sectors: both chains
start at the apex vertex `z1s` that is higher in `s z`, and the other apex vertex
`z2s` is an ordinary point of both faces (hidden inside the cycle). Modes: `C1`
falls strictly from the apex, or `C2` does (`isRupert_triShadow_gen`, `t = -s`). -/
theorem edge_same_core (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s)
    {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOK Q1 z1s s m ca cz) (C2 : ChainOK Q2 z1s s n cb dz)
    (hmode : (∀ l, l < m → s * cz (l + 1) < s * cz l) ∨ (∀ j, j < n → s * dz (j + 1) < s * dz j))
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z2 : Q2 0 z2s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have hns : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
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
      -s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : -s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have q10 : Q1 0 z1s := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
  have q20 : Q2 0 z1s := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q2of : ∀ z, Q1 0 z → Q2 0 z := by
    intro z h; rcases hap1 z h with rfl | rfl
    · exact q20
    · exact hQ2z2
  have q1of : ∀ z, Q2 0 z → Q1 0 z := by
    intro z h; rcases hap2 z h with rfl | rfl
    · exact q10
    · exact hQ1z2
  refine isRupert_triShadow_gen O r1 r2 hρ C1.one_le C2.one_le s hs (-s) hns one_pos one_pos ca cz
    cb dz c10.1 c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ ?_
  · intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
    · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
      · rcases far1 a z hq with h | ⟨e1, e2⟩
        · left; exact far_tiltOK (by linarith)
        · right; left; rw [e1, e2]
      · intro ha; subst ha; exact side2 0 z (q2of z hq)
    · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
      · rcases far2 b z hq with h | ⟨e1, e2⟩
        · left; exact far_tiltOK (by linarith)
        · right; right; rw [e1, e2]
      · intro hb; subst hb; exact side1 0 z (q1of z hq)
    · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK hin), fun h => absurd h hb.ne',
        fun h => absurd h ha.ne'⟩
  · rcases hmode with hdec | hfb
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, hdec⟩))
    · exact Or.inr (Or.inr (Or.inl hfb))

/-- The tie cases of Lemma T over an edge: as `VTie`, the apex now carrying two
vertices `zx < zx'`, either of which may be the strict top in `s z`. -/
def ETie (Q1 Q2 : ℝ → ℝ → Prop) (zx zx' A zA B zB : ℝ) : Prop :=
  ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ((∀ a z, Q1 a z → ¬ (a = A ∧ z = zA) → s * z < s * zA) ∨
      (∀ b z, Q2 b z → ¬ (b = B ∧ z = zB) → s * zB < s * z) ∨
      (∃ zt, (zt = zx ∨ zt = zx') ∧ ∀ a z, Q1 a z → ¬ (a = 0 ∧ z = zt) → s * z < s * zt) ∨
      (∃ zt, (zt = zx ∨ zt = zx') ∧ ∀ b z, Q2 b z → ¬ (b = 0 ∧ z = zt) → s * z < s * zt))

set_option maxHeartbeats 8000000 in
/-- **Lemma T over an edge, from chains, at the tie.** As `isRupert_edge_frame`,
with "far depths distinct" weakened to "far depths distinct or `ETie`". -/
theorem isRupert_edge_frame_tie (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {zx zx' : ℝ} (hxx : zx < zx')
    (hU1 : ∃ m ca cz, ChainOK Q1 zx' 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 zx (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 zx' 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 zx (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = zx ∨ z = zx') (hap2 : ∀ z, Q2 0 z → z = zx ∨ z = zx')
    (hQ1x : Q1 0 zx) (hQ1x' : Q1 0 zx') (hQ2x : Q2 0 zx) (hQ2x' : Q2 0 zx')
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (hfarT : ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz →
      cz m ≠ dz n ∨ ETie Q1 Q2 zx zx' (ca m) (cz m) (cb n) (dz n)) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  have conv : ∀ {m n : ℕ} {ca cb : ℕ → ℝ}, ca m = ca0 m0 → cb n = cb0 n0 →
      ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
        ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n)) := by
    intro m n ca cb e1 e2 y hy
    obtain ⟨a, b, z, e, hc⟩ := hVc y hy
    refine ⟨a, b, z, e, ?_⟩
    rcases hc with h | h | ⟨ha, hb, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; refine ⟨ha, hb, ?_⟩
      rw [e1, e2]; exact hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have eU1 := L1.far_eq U1
  have eU2 := L2.far_eq U2
  have eU1' := U1.far_eq U1
  have eU2' := U2.far_eq U2
  have eL2 := U2.far_eq L2
  -- the two mixed cores (`s = 1`: `U1`, `L2`; `s = -1`: `L1`, `U2`) and the same-sign ones
  have mix1 : (1 * dz1 n1 < 1 * cz0 m0 ∨ (∀ l, l < m0 → 1 * cz0 l < 1 * cz0 (l + 1)) ∨
      (∀ j, j < n1 → 1 * dz1 (j + 1) < 1 * dz1 j)) → IsRupert V := fun hmode =>
    edge_core_gen O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) (z1s := zx') (z2s := zx) (by linarith)
      U1 (by simpa using L2) hmode (fun z h => (hap1 z h).symm) (fun z h => (hap2 z h).symm)
      hQ1x hQ2x' hpos1 hpos2 V hV1 hV2 (conv eU1'.1 eU2.1)
  have mixm : (-1 * dz0 n0 < -1 * cz1 m1 ∨ (∀ l, l < m1 → -1 * cz1 l < -1 * cz1 (l + 1)) ∨
      (∀ j, j < n0 → -1 * dz0 (j + 1) < -1 * dz0 j)) → IsRupert V := fun hmode =>
    edge_core_gen O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) (z1s := zx) (z2s := zx') (by linarith)
      L1 (by simpa using U2) hmode hap1 (fun z h => hap2 z h) hQ1x' hQ2x hpos1 hpos2 V hV1 hV2
      (conv eU1.1 eU2'.1)
  have same1 : ((∀ l, l < m0 → 1 * cz0 (l + 1) < 1 * cz0 l) ∨
      (∀ j, j < n0 → 1 * dz0 (j + 1) < 1 * dz0 j)) → IsRupert V := fun hmode =>
    edge_same_core O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) (z1s := zx') (z2s := zx) (by linarith)
      U1 U2 hmode (fun z h => (hap1 z h).symm) (fun z h => (hap2 z h).symm) hQ1x hQ2x
      hpos1 hpos2 V hV1 hV2 (conv eU1'.1 eU2'.1)
  have samem : ((∀ l, l < m1 → -1 * cz1 (l + 1) < -1 * cz1 l) ∨
      (∀ j, j < n1 → -1 * dz1 (j + 1) < -1 * dz1 j)) → IsRupert V := fun hmode =>
    edge_same_core O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) (z1s := zx) (z2s := zx') (by linarith)
      L1 L2 hmode hap1 hap2 hQ1x' hQ2x' hpos1 hpos2 V hV1 hV2 (conv eU1.1 eU2.1)
  -- the apex vertex that is a strict top in `s z` is the upper one for `s = 1`
  have top1 : ∀ zt, (zt = zx ∨ zt = zx') → (∀ a z, Q1 a z → ¬ (a = 0 ∧ z = zt) → 1 * z < 1 * zt) →
      zt = zx' := by
    rintro zt (rfl | rfl) h
    · have := h 0 zx' hQ1x' (fun e => by linarith [e.2]); linarith
    · rfl
  have topm : ∀ zt, (zt = zx ∨ zt = zx') → (∀ a z, Q1 a z → ¬ (a = 0 ∧ z = zt) → -1 * z < -1 * zt) →
      zt = zx := by
    rintro zt (rfl | rfl) h
    · rfl
    · have := h 0 zx hQ1x (fun e => by linarith [e.2]); linarith
  have top2 : ∀ zt, (zt = zx ∨ zt = zx') → (∀ b z, Q2 b z → ¬ (b = 0 ∧ z = zt) → 1 * z < 1 * zt) →
      zt = zx' := by
    rintro zt (rfl | rfl) h
    · have := h 0 zx' hQ2x' (fun e => by linarith [e.2]); linarith
    · rfl
  have topm2 : ∀ zt, (zt = zx ∨ zt = zx') → (∀ b z, Q2 b z → ¬ (b = 0 ∧ z = zt) → -1 * z < -1 * zt) →
      zt = zx := by
    rintro zt (rfl | rfl) h
    · rfl
    · have := h 0 zx hQ2x (fun e => by linarith [e.2]); linarith
  rcases hfarT m0 ca0 cz0 n0 cb0 dz0 U1 U2 with hne | ⟨s, hs, hv | hv | ⟨zt, hzt, hv⟩ | ⟨zt, hzt, hv⟩⟩
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mixm (Or.inl (by rw [eU1.2]; linarith))
    · exact mix1 (Or.inl (by rw [eU2.2]; linarith))
  · -- `A` the top of `Q1`: `C1` rises to it
    rcases hs with rfl | rfl
    · exact mix1 (Or.inr (Or.inl (U1.rise_of_far_top fun a z hq hn => by
        rw [eU1'.2]; exact hv a z hq (fun h => hn ⟨by rw [eU1'.1]; exact h.1, by rw [eU1'.2]; exact h.2⟩))))
    · exact mixm (Or.inr (Or.inl (L1.rise_of_far_top fun a z hq hn => by
        rw [eU1.2]; exact hv a z hq (fun h => hn ⟨by rw [eU1.1]; exact h.1, by rw [eU1.2]; exact h.2⟩))))
  · -- `B` the bottom of `Q2`: `C2` reversed rises from it
    rcases hs with rfl | rfl
    · have hr := L2.rise_of_far_top (fun b z hq hn => by
        rw [eU2.2]
        have := hv b z hq (fun h => hn ⟨by rw [eU2.1]; exact h.1, by rw [eU2.2]; exact h.2⟩)
        linarith)
      exact mix1 (Or.inr (Or.inr fun j hj => by have := hr j hj; linarith))
    · have hr := U2.rise_of_far_top (fun b z hq hn => by
        rw [eU2'.2]
        have := hv b z hq (fun h => hn ⟨by rw [eU2'.1]; exact h.1, by rw [eU2'.2]; exact h.2⟩)
        linarith)
      exact mixm (Or.inr (Or.inr fun j hj => by have := hr j hj; linarith))
  · -- an apex vertex the top of `Q1`: the same-sign sector, `C1` falls from it
    rcases hs with rfl | rfl
    · obtain rfl := top1 zt hzt hv
      exact same1 (Or.inl (U1.fall_of_apex_top hv))
    · obtain rfl := topm zt hzt hv
      exact samem (Or.inl (L1.fall_of_apex_top hv))
  · -- an apex vertex the top of `Q2`: the same-sign sector, `C2` falls from it
    rcases hs with rfl | rfl
    · obtain rfl := top2 zt hzt hv
      exact same1 (Or.inr (U2.fall_of_apex_top hv))
    · obtain rfl := topm2 zt hzt hv
      exact samem (Or.inr (L2.fall_of_apex_top hv))

/-- `TieH` over an edge `v w`: the far heights differ, or for a sign `s` a far
end or one of `v`, `w` is a strict top (bottom for `q`) of its face in `s h`. -/
def TieHE (Q1 Q2 : Finset ℝ³) (v w p q : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  h p ≠ h q ∨ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ((∀ x ∈ Q1, x ≠ p → s * h x < s * h p) ∨ (∀ x ∈ Q2, x ≠ q → s * h q < s * h x) ∨
      (∃ u, (u = v ∨ u = w) ∧ ∀ x ∈ Q1, x ≠ u → s * h x < s * h u) ∨
      (∃ u, (u = v ∨ u = w) ∧ ∀ x ∈ Q2, x ≠ u → s * h x < s * h u))

theorem TieHE.swap {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHE Q1 Q2 v w p q h) :
    TieHE Q2 Q1 v w q p h := by
  rcases H with hne | ⟨s, hs, hv | hv | hv | hv⟩
  · exact Or.inl (Ne.symm hne)
  · refine Or.inr ⟨-s, by rcases hs with rfl | rfl <;> norm_num, Or.inr (Or.inl fun x hx hxp => ?_)⟩
    have := hv x hx hxp; linarith
  · refine Or.inr ⟨-s, by rcases hs with rfl | rfl <;> norm_num, Or.inl fun x hx hxq => ?_⟩
    have := hv x hx hxq; linarith
  · exact Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr hv))⟩
  · exact Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl hv))⟩

theorem TieHE.comm {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHE Q1 Q2 v w p q h) :
    TieHE Q1 Q2 w v p q h := by
  rcases H with hne | ⟨s, hs, hv | hv | ⟨u, hu, hv⟩ | ⟨u, hu, hv⟩⟩
  · exact Or.inl hne
  · exact Or.inr ⟨s, hs, Or.inl hv⟩
  · exact Or.inr ⟨s, hs, Or.inr (Or.inl hv)⟩
  · exact Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl ⟨u, hu.symm, hv⟩))⟩
  · exact Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr ⟨u, hu.symm, hv⟩))⟩

theorem TieHE.map {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h h' : ℝ³ → ℝ} (g : ℝ³ → ℝ³)
    {r : ℝ} (hr : 0 < r) (hh : ∀ x, h' (g x) = h x / r)
    (H : TieHE Q1 Q2 v w p q h) [DecidableEq ℝ³] :
    TieHE (Q1.image g) (Q2.image g) (g v) (g w) (g p) (g q) h' := by
  have lt : ∀ {a b : ℝ} {s : ℝ}, s * a < s * b → s * (a / r) < s * (b / r) := by
    intro a b s hab
    rw [show s * (a / r) = (s * a) / r by ring, show s * (b / r) = (s * b) / r by ring]
    exact div_lt_div_of_pos_right hab hr
  have im : ∀ (S : Finset ℝ³) (c : ℝ³) {s : ℝ} (top : Bool),
      (∀ x ∈ S, x ≠ c → (if top then s * h x < s * h c else s * h c < s * h x)) →
      ∀ y ∈ S.image g, y ≠ g c → (if top then s * h' y < s * h' (g c) else s * h' (g c) < s * h' y) := by
    intro S c s top H y hy hyc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have := H x hx (fun e => hyc (by rw [e]))
    cases top <;> simp only [hh] at this ⊢ <;> exact lt this
  rcases H with hne | ⟨s, hs, hv | hv | ⟨u, hu, hv⟩ | ⟨u, hu, hv⟩⟩
  · left; rw [hh, hh]; intro e; apply hne
    have := congrArg (· * r) e; simp only [div_mul_cancel₀ _ hr.ne'] at this; exact this
  · exact Or.inr ⟨s, hs, Or.inl (im Q1 p true hv)⟩
  · exact Or.inr ⟨s, hs, Or.inr (Or.inl (im Q2 q false hv))⟩
  · refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl ⟨g u, ?_, im Q1 u true hv⟩))⟩
    rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr ⟨g u, ?_, im Q2 u true hv⟩))⟩
    rcases hu with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, in frame coordinates.**  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
they share the vertical edge `v w`, every other point at `a, b > 0`. -/
theorem isRupert_edge_coords_tie (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v w : ℝ³) (hvw : v 2 < w 2) (a b : ℝ³ → ℝ)
    (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinjv : Set.InjOn (fun p => (a p, b p)) ((V.erase v : Finset ℝ³) : Set ℝ³))
    (hinjw : Set.InjOn (fun p => (a p, b p)) ((V.erase w : Finset ℝ³) : Set ℝ³))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHE Q1 Q2 v w p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1) : IsRupert V := by
  classical
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
  have up : (1 : ℝ) * v 2 < 1 * w 2 := by linarith
  have lo : (-1 : ℝ) * w 2 < -1 * v 2 := by linarith
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  refine isRupert_edge_frame_tie O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (zx := v 2) (zx' := w 2) hvw
    (chains1 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains1 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo)
    (chains2 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains2 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo) ?_ ?_
    (Finset.mem_image.mpr ⟨v, hv1, by rw [hav]⟩) (Finset.mem_image.mpr ⟨w, hw1, by rw [haw]⟩)
    (Finset.mem_image.mpr ⟨v, hv2, by rw [hbv]⟩) (Finset.mem_image.mpr ⟨w, hw2, by rw [hbw]⟩)
    ?_ ?_ V ?_ ?_ ?_ ?_
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hp2 : p ∈ Q2
    · rcases mem12 p hp hp2 with rfl | rfl
      · exact Or.inl e2.symm
      · exact Or.inr e2.symm
    · linarith [ha2' p (h1V hp) hp2]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hp1 : p ∈ Q1
    · rcases mem12 p hp1 hp with rfl | rfl
      · exact Or.inl e2.symm
      · exact Or.inr e2.symm
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
    refine Or.inr (Or.inr ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩)
    intro m ca cz n cb dz C1 C2
    have hA := C1.far_pos
    have hB := C2.far_pos
    have hxa0 := ha2' xa (h1V hxa) hxa2
    have hxb0 := hb1' xb (h2V hxb) hxb1
    have le1 : a xa ≤ ca m := by
      by_cases e : a xa = ca m ∧ xa 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
    have le2 : b xb ≤ cb n := by
      by_cases e : b xb = cb n ∧ xb 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith
  · intro m ca cz n cb dz C1 C2
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    obtain ⟨q, hq, f1, f2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    have hpq : p ≠ q := by
      intro e; subst e
      have := C1.far_pos
      rw [← e1, ha2 p hq] at this; exact lt_irrefl _ this
    have pmax : ∀ p' ∈ Q1, a p' ≤ a p := fun p' hp' => by
      rw [e1]
      by_cases e : a p' = ca m ∧ p' 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hp') e).le
    have qmax : ∀ q' ∈ Q2, b q' ≤ b q := fun q' hq' => by
      rw [f1]
      by_cases e : b q' = cb n ∧ q' 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq') e).le
    rcases hfarZ p hp q hq hpq pmax qmax with hne | ⟨s, hs, hv | hv | ⟨u, hu, hv⟩ | ⟨u, hu, hv⟩⟩
    · left; rw [← e2, ← f2]; exact hne
    · refine Or.inr ⟨s, hs, Or.inl fun x z hxz hn => ?_⟩
      obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
      rw [← g2, ← e2]
      exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, e1], by rw [← g2, h, e2]⟩)
    · refine Or.inr ⟨s, hs, Or.inr (Or.inl fun x z hxz hn => ?_)⟩
      obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
      rw [← g2, ← f2]
      exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, f1], by rw [← g2, h, f2]⟩)
    · have hau : a u = 0 := by rcases hu with rfl | rfl; exacts [hav, haw]
      refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl ⟨u 2, ?_, fun x z hxz hn => ?_⟩))⟩
      · rcases hu with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
      obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
      rw [← g2]
      exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, hau], by rw [← g2, h]⟩)
    · have hbu : b u = 0 := by rcases hu with rfl | rfl; exacts [hbv, hbw]
      refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr ⟨u 2, ?_, fun x z hxz hn => ?_⟩))⟩
      · rcases hu with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
      obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
      rw [← g2]
      exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, hbu], by rw [← g2, h]⟩)

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, the edge vertical**, with `v` below `w`. -/
theorem isRupert_facets_edge_vertical_lt_tie (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v 2 < w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHE Q1 Q2 v w p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  obtain ⟨p1, hp1, hp12⟩ := hne1
  obtain ⟨p2, hp2, hp21⟩ := hne2
  have m21 : f2 p1 < 0 := n2 p1 (h1V hp1) hp12
  have m12 : f1 p2 < 0 := n1 p2 (h2V hp2) hp21
  obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
  have v1 := z1 v hv1; have v2 := z2 v hv2
  have hγ1 : γ1 = 0 := by
    rw [h1] at e1 v1; simp [ez] at e1; linarith
  have hγ2 : γ2 = 0 := by
    rw [h2] at e2 v2; simp [ez] at e2; linarith
  have g1 : ∀ p, f1 p = α1 * (p 0 - v 0) + β1 * (p 1 - v 1) := by
    intro p; have := v1; rw [h1, hγ1] at this ⊢; linarith
  have g2 : ∀ p, f2 p = α2 * (p 0 - v 0) + β2 * (p 1 - v 1) := by
    intro p; have := v2; rw [h2, hγ2] at this ⊢; linarith
  set O : ℝ² := !₂[v 0, v 1] with hO
  set r1 : ℝ² := !₂[p1 0 - v 0, p1 1 - v 1] with hr1
  set r2 : ℝ² := !₂[p2 0 - v 0, p2 1 - v 1] with hr2
  have q11 : α1 * (p1 0 - v 0) + β1 * (p1 1 - v 1) = 0 := by rw [← g1]; exact z1 p1 hp1
  have q22 : α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) = 0 := by rw [← g2]; exact z2 p2 hp2
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 p2 * (p1 0 - v 0) = 0 := by
      rw [g1]; linear_combination (p2 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 p2 * (p1 1 - v 1) = 0 := by
      rw [g1]; linear_combination (p2 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 p1; rw [r10, r11] at this; linarith
  set ρ := cross2 r1 r2 with hρdef
  set a : ℝ³ → ℝ := fun p => cross2 !₂[p 0 - v 0, p 1 - v 1] r2 / ρ with ha
  set b : ℝ³ → ℝ := fun p => cross2 r1 !₂[p 0 - v 0, p 1 - v 1] / ρ with hb
  have hxy : ∀ p : ℝ³, p 0 - v 0 = a p * r1 0 + b p * r2 0 ∧ p 1 - v 1 = a p * r1 1 + b p * r2 1 := by
    intro p
    obtain ⟨c0, c1⟩ := cramer2 !₂[p 0 - v 0, p 1 - v 1] r1 r2 hρ
    simp at c0 c1; exact ⟨c0, c1⟩
  have hy : ∀ p : ℝ³, p = oblPt O r1 r2 (a p) (b p) (p 2) := by
    intro p; obtain ⟨c0, c1⟩ := hxy p
    ext j; fin_cases j
    · simp only [oblPt, hO]; simp; linarith
    · simp only [oblPt, hO]; simp; linarith
    · simp [oblPt]
  have r10 : r1 0 = p1 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = p1 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = p2 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = p2 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 p2 := by
    intro p; rw [g1 p, g1 p2, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 p1 := by
    intro p; rw [g2 p, g2 p1, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination b p * q22
  have hb1 : ∀ p ∈ Q1, b p = 0 := fun p hp => by
    have := G1 p; rw [z1 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m12.ne
  have ha2 : ∀ p ∈ Q2, a p = 0 := fun p hp => by
    have := G2 p; rw [z2 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m21.ne
  have hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p := fun p hp hq => by
    have := n1 p hp hq; rw [G1] at this; nlinarith
  have ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p := fun p hp hq => by
    have := n2 p hp hq; rw [G2] at this; nlinarith
  have hinj : ∀ u ∈ ({v, w} : Finset ℝ³),
      Set.InjOn (fun p => (a p, b p)) ((V.erase u : Finset ℝ³) : Set ℝ³) := by
    intro u hu p hp q hq e
    simp only [Prod.mk.injEq] at e
    by_contra hpq
    have hp' := Finset.mem_erase.mp hp; have hq' := Finset.mem_erase.mp hq
    have hne : ({p, q} : Finset ℝ³) ≠ {v, w} := by
      intro h
      have : u ∈ ({p, q} : Finset ℝ³) := h ▸ hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hp'.1 rfl
      · exact hq'.1 rfl
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [e.1, e.2] at c0 c1
    rcases hpar p hp'.2 q hq'.2 hpq hne with h | h <;> apply h <;> linarith
  have hinjv := hinj v (by simp)
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHE Q1 Q2 v w p q (fun x => x 2) := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hinjw := hinj w (by simp)
  have hin' : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 := by
    obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨xa, hxa, xb, hxb, hxa2, hxb1, fun y hy hy1 hy2 => ?_⟩
    have k := h y hy hy1 hy2
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne] at k
    exact k
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_edge_coords_tie O r2 r1 hpos' V Q2 Q1 v w hvw b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' ⟨p2, hp2, hp21⟩ ⟨p1, hp1, hp12⟩ hcol ?_ ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).swap) ?_
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinjv hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinjw hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxb1, hxa2, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_edge_coords_tie O r1 r2 hpos V Q1 Q2 v w hvw a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp12⟩ ⟨p2, hp2, hp21⟩ hcol hinjv hinjw hfar' hin'

/-- **Lemma T over an edge, the edge vertical.** -/
theorem isRupert_facets_edge_vertical_tie (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hvw2 : v 2 ≠ w 2)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHE Q1 Q2 v w p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  rcases lt_or_gt_of_ne hvw2 with hlt | hgt
  · exact isRupert_facets_edge_vertical_lt_tie V Q1 Q2 v w hlt h1V h2V hint f1 f2 z1 n1 z2 n2 e1 e2
      hne1 hne2 hcol hpar hfarZ hin
  · -- the line through `w` is the same vertical line
    have hw : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ), f v = 0 → f (v + ez) = 0 → f w = 0 → f (w + ez) = 0 := by
      intro f h0 h1 hw0
      have k1 : f (v + ez) = f.linear ez + f v := by
        rw [show v + ez = ez +ᵥ v by rw [vadd_eq_add, add_comm]]; exact f.map_vadd v ez
      have k2 : f (w + ez) = f.linear ez + f w := by
        rw [show w + ez = ez +ᵥ w by rw [vadd_eq_add, add_comm]]; exact f.map_vadd w ez
      rw [k2, hw0]; rw [k1, h0] at h1; linarith
    have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
    have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
    refine isRupert_facets_edge_vertical_lt_tie V Q1 Q2 w v hgt h1V h2V
      (by rw [Finset.pair_comm]; exact hint) f1 f2 z1 n1 z2 n2
      (hw f1 (z1 v hv1) e1 (z1 w hw1)) (hw f2 (z2 v hv2) e2 (z2 w hw2)) hne1 hne2 hcol
      (fun p hp q hq hpq h => hpar p hp q hq hpq (by rw [Finset.pair_comm v w]; exact h))
      (fun p hp q hq hpq h1 h2 => (hfarZ p hp q hq hpq h1 h2).comm) hin

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge** for two facets `Q1`, `Q2` (functionals `f1`, `f2`)
sharing the edge `v w`, viewed along it: no three points collinear, no other
segment parallel to it, distinct far depths along it, and every point off both
facets inside the shadow triangle of the edge and some `xa ∈ Q1 \ Q2`,
`xb ∈ Q2 \ Q1`. -/
theorem isRupert_facets_edge_tie (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p ≠ c • (w - v))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHE Q1 Q2 v w p q (fun x => ⟪x, w - v⟫))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have he : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos (w - v) he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  have hgz : ∀ p, g p 2 = ⟪p, w - v⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p (w - v)
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • (w - v) := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  have tF1 : ∀ p, F1 (g p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (g p) = f2 p := fun p => by simp [hF2, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f w = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) =
        f (v + r⁻¹ • (w - v)) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 (by rw [add_sub_cancel]; exact h1) _
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have memg : ∀ (S : Finset ℝ³) p, g p ∈ S.image g ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e], Finset.mem_image_of_mem g⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (g p)) → ∀ q ∈ S.image g, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_facets_edge_vertical_tie (V.image g) (Q1.image g) (Q2.image g) (g v) (g w)
    (fun h => hvw (hginj h))
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_insert, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) (z1 w hw1)) (tz f2 (z2 v hv2) (z2 w hw2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨p, hp, hp2⟩ := hne1
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hp2 ((memg Q2 p).mp h)⟩
  · obtain ⟨p, hp, hp1⟩ := hne2
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hp1 ((memg Q1 p).mp h)⟩
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun u hu => ?_)))
    intro hpq hpu hqu c h
    apply hcol p hp q hq u hu (fun e => hpq (by rw [e])) (fun e => hpu (by rw [e]))
      (fun e => hqu (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · refine allg V _ (fun p hp => allg V _ (fun q hq => ?_))
    intro hpq hpair
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hpar p hp q hq (fun e => hpq (by rw [e])) (fun e => hpair (by
      rw [show ({g p, g q} : Finset ℝ³) = Finset.image g {p, q} by simp,
        show ({g v, g w} : Finset ℝ³) = Finset.image g {v, w} by simp, e]))
      ((g (q - p)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
  · rw [hgz, hgz]
    intro h
    have k : ⟪v, w - v⟫ = ⟪w, w - v⟫ := by simpa [hr.ne'] using h
    have : ⟪w - v, w - v⟫ = 0 := by rw [inner_sub_left]; linarith
    exact hvw (sub_eq_zero.mp (inner_self_eq_zero.mp this)).symm
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2
    refine (hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)).map g
      hr (fun x => hgz x)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxa2 ((memg Q2 xa).mp e), fun e => hxb1 ((memg Q1 xb).mp e),
      allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

/-- General position for Lemma T along an edge with the tie allowed: no other
segment parallel to the edge, and `TieHE` at the far ends. Weaker than `EdgeFar`
(`EdgeFar.tie`). -/
def EdgeTie (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p ≠ c • (w - v)) ∧
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHE Q1 Q2 v w p q (fun x => ⟪x, w - v⟫)

theorem EdgeFar.tie {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h : EdgeFar V Q1 Q2 v w) : EdgeTie V Q1 Q2 v w :=
  ⟨h.1, fun f1 f2 z1 n1 z2 n2 p hp q hq hpq h1 h2 => Or.inl (h.2 f1 f2 z1 n1 z2 n2 p hp q hq hpq h1 h2)⟩

/-- A triangle face `{v, w, p}` through the edge `v w` settles the tie: of three
heights with `h v ≠ h w`, `v` or `w` is the strict top or bottom. -/
theorem tieHE_of_tri1 {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h : ℝ³ → ℝ} (hc : Q1.card = 3)
    (hv : v ∈ Q1) (hw : w ∈ Q1) (hp : p ∈ Q1) (hpv : p ≠ v) (hpw : p ≠ w) (hvw : h v ≠ h w) :
    TieHE Q1 Q2 v w p q h := by
  have hvw' : v ≠ w := fun e => hvw (by rw [e])
  obtain ⟨t, ht⟩ := exists_third_of_card_three hc hv hw hvw'
  have hQ : ∀ x ∈ Q1, x = v ∨ x = w ∨ x = p := by
    rcases ht p hp with e | e | e
    · exact absurd e hpv
    · exact absurd e hpw
    · subst e; exact ht
  right
  obtain ⟨s, hs, hst | hst⟩ := three_heights (hv := h v) (hp := h w) (hw := h p) hvw
  · refine ⟨s, hs, Or.inr (Or.inr (Or.inl ⟨w, Or.inr rfl, fun x hx hxu => ?_⟩))⟩
    rcases hQ x hx with rfl | rfl | rfl
    · exact hst.1
    · exact absurd rfl hxu
    · exact hst.2
  · refine ⟨s, hs, Or.inr (Or.inr (Or.inl ⟨v, Or.inl rfl, fun x hx hxu => ?_⟩))⟩
    rcases hQ x hx with rfl | rfl | rfl
    · exact absurd rfl hxu
    · exact hst.1
    · exact hst.2

theorem tieHE_of_tri2 {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h : ℝ³ → ℝ} (hc : Q2.card = 3)
    (hv : v ∈ Q2) (hw : w ∈ Q2) (hq : q ∈ Q2) (hqv : q ≠ v) (hqw : q ≠ w) (hvw : h v ≠ h w) :
    TieHE Q1 Q2 v w p q h :=
  (tieHE_of_tri1 (Q2 := Q1) (p := q) (q := p) hc hv hw hq hqv hqw hvw).swap

/-- **Lemma T at the tie over an edge with a triangle face.** If one face through
the edge `v w` is a triangle, the far-end condition of `EdgeFar` is not needed:
only no other segment parallel to the edge. -/
theorem edgeTie_of_tri {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (hv1 : v ∈ Q1) (hw1 : w ∈ Q1) (hv2 : v ∈ Q2) (hw2 : w ∈ Q2) (hvw : v ≠ w)
    (h12 : ∃ x ∈ Q1, x ∉ Q2) (h21 : ∃ x ∈ Q2, x ∉ Q1) (hcard : Q1.card = 3 ∨ Q2.card = 3)
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ,
      q - p ≠ c • (w - v)) : EdgeTie V Q1 Q2 v w := by
  refine ⟨hpar, fun f1 f2 z1 n1 z2 n2 p hp q hq hpq hpm hqm => ?_⟩
  have hh : ⟪v, w - v⟫ ≠ ⟪w, w - v⟫ := by
    intro e
    have : ⟪w - v, w - v⟫ = 0 := by rw [inner_sub_left, e, sub_self]
    exact hvw (sub_eq_zero.mp (inner_self_eq_zero.mp this)).symm
  rcases hcard with hc | hc
  · obtain ⟨x, hx1, hx2⟩ := h12
    have hlt : f2 p < 0 := lt_of_le_of_lt (hpm x hx1) (n2 x (h1V hx1) hx2)
    refine tieHE_of_tri1 hc hv1 hw1 hp (fun e => ?_) (fun e => ?_) hh
    · rw [e, z2 v hv2] at hlt; exact lt_irrefl _ hlt
    · rw [e, z2 w hw2] at hlt; exact lt_irrefl _ hlt
  · obtain ⟨x, hx2, hx1⟩ := h21
    have hlt : f1 q < 0 := lt_of_le_of_lt (hqm x hx2) (n1 x (h2V hx2) hx1)
    refine tieHE_of_tri2 hc hv2 hw2 hq (fun e => ?_) (fun e => ?_) hh
    · rw [e, z1 v hv1] at hlt; exact lt_irrefl _ hlt
    · rw [e, z1 w hw1] at hlt; exact lt_irrefl _ hlt

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge at the tie, facet form** (`FEWER-FACES-PROOFS.md` §7): two
facets `Q1`, `Q2` of `V` (no three points collinear) sharing exactly the edge
`v w`, general position along it (`EdgeFar`), and every point off both
facets inside the shadow triangle of the edge and some `xa ∈ Q1 \ Q2`,
`xb ∈ Q2 \ Q1` (stated with any facet functionals `f1`, `f2`): Rupert. -/
theorem isRupert_of_facets_edge_tie (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hfarZ : EdgeTie V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  refine isRupert_facets_edge_tie V Q1 Q2 v w hvw h1V h2V hint f1 f2 z1 n1 z2 n2 hne1 hne2 ?_ ?_
    (hfarZ.2 f1 f2 z1 n1 z2 n2)
    ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin' f1 f2 z1 n1 z2 n2⟩
  · exact hgen
  · exact hfarZ.1

end Minimality

end
