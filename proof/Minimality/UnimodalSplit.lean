module

public import Minimality.SplitEdgePlane

/-!
# Unimodal strict rims are depth-separated (generic case)

Proves the discrete intermediate-value theorem for strictly unimodal generic rims (Task FE1):
if `X : ZMod k → ℝ³` (`4 ≤ k`) is a strict ccw rim at `w` (`StrictRimCcw X w`) with pairwise
distinct depths `⟪X i, w⟫`, strictly unimodal along the cycle with unique minimum `m` and
maximum `M` (`StrictlyUnimodal X w m M`), and no two rim edges are parallel in projection
(`NoParallelRimEdges X w`), then there exists `(a, c)` such that `Split.IsDepthSeparatedAt X w a c`.

As a corollary (`edgePlaneAny_of_unimodal`), adding `HiddenInTriangles` and the non-degeneracy
condition `hnd` yields `Gen.EdgePlaneAny x` via `splitRows_of_isDepthSeparatedAt` and
`EV.epRows_of_splitRows`.
-/

@[expose] public section

set_option autoImplicit false

namespace Minimality.Split.UnimodalSplit

open scoped RealInnerProductSpace
open Finset

/-- `X : ZMod k → ℝ³` is a strict ccw rim at `w` (polygon-level form of `StrictRimN`). -/
def StrictRimCcw {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) : Prop :=
  ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < det3 (X (i + 1) - X i) (X j - X i) w

theorem strictRimCcw_of_strictRimN {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab) :
    StrictRimCcw (fun i => x (lab i)) w := fun i j hji hj1 =>
  hrim (lab j) i (fun e => hji (hinj e)) (fun e => hj1 (hinj e))

/-- Strictly unimodal depths along the cycle `ZMod k`, with unique minimum `m` and maximum `M`. -/
def StrictlyUnimodal {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (m M : ZMod k) : Prop :=
  m ≠ M ∧
    (∀ s : ℕ, s < (M - m).val → ⟪X (m + (s : ZMod k)), w⟫ < ⟪X (m + ((s + 1 : ℕ) : ZMod k)), w⟫) ∧
    (∀ s : ℕ, (M - m).val ≤ s → s < k →
      ⟪X (m + ((s + 1 : ℕ) : ZMod k)), w⟫ < ⟪X (m + (s : ZMod k)), w⟫)

/-- No two distinct rim edges are parallel in projection perpendicular to `w`. -/
def NoParallelRimEdges {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) : Prop :=
  ∀ i j : ZMod k, i ≠ j → det3 (X (i + 1) - X i) (X (j + 1) - X j) w ≠ 0

private lemma det3_sub_right (a w b c : ℝ³) :
    det3 a w (b - c) = det3 a w b - det3 a w c := by
  simp only [det3, PiLp.sub_apply]; ring

private lemma det3_swap_mid (a b c : ℝ³) : det3 a b c = -det3 a c b := by
  simp only [det3]; ring

private lemma projP_isCcw {k : ℕ} [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³)
    (hrim : StrictRimCcw X w) (a : ZMod k) :
    let d := X (a + 1) - X a
    let N := cross d w
    0 < ⟪N, N⟫ ∧ Minimality.IsCcwPolygon (fun i => projP N w (X i)) := by
  intro d N
  have hj : ∃ j : ZMod k, j ≠ a ∧ j ≠ a + 1 := by
    refine ⟨a + 2, ?_, ?_⟩
    · have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) a
      simpa using this.symm
    · have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) a
      simpa using this.symm
  obtain ⟨j, hj1, hj2⟩ := hj
  have hrj := hrim a j hj1 hj2
  have hN0 : N ≠ 0 := by
    intro hN
    have h0 : det3 d (X j - X a) w = -⟪N, X j - X a⟫ := by
      rw [det3_swap_mid, det3_eq_inner]
    rw [hN, inner_zero_left, neg_zero] at h0
    linarith
  have hnn0 : 0 < ⟪N, N⟫ := (real_inner_self_nonneg (x := N)).lt_of_ne' (fun h => hN0 (inner_self_eq_zero.mp h))
  refine ⟨hnn0, hk, fun i l hli hl1 => ?_⟩
  rw [projP_sub, projP_sub, cross2_projP]
  exact mul_pos hnn0 (hrim i l hli hl1)

/-- Every rim edge `a` has a unique strict far corner `far(a) ∉ {a, a + 1}`. -/
theorem exists_farCorner {k : ℕ} [NeZero k] (hk : 4 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³)
    (hrim : StrictRimCcw X w) (hgen : NoParallelRimEdges X w) (a : ZMod k) :
    ∃! c : ZMod k, c ≠ a ∧ c ≠ a + 1 ∧
      ∀ i : ZMod k, i ≠ c → det3 (X (a + 1) - X a) w (X c) < det3 (X (a + 1) - X a) w (X i) := by
  classical
  set d := X (a + 1) - X a
  set N := cross d w
  set p : ZMod k → ℝ² := fun i => projP N w (X i)
  obtain ⟨_, hp⟩ := projP_isCcw (by omega) X w hrim a
  let ν : ℝ² := !₂[-1, 0]
  have hν : ν ≠ 0 := by
    intro h
    have := congrArg (fun v => v 0) h
    simp [ν] at this
  have hinner : ∀ i : ZMod k, ⟪ν, p i⟫ = -det3 d w (X i) := fun i => by
    have h1 : ⟪ν, p i⟫ = -(p i 0) := by
      simp [ν, PiLp.inner_apply, Fin.sum_univ_two]
    have h2 : p i 0 = ⟪X i, N⟫ := by simp [p, projP]
    have h3 : ⟪X i, N⟫ = det3 d w (X i) := by
      rw [real_inner_comm]; exact (det3_eq_inner d w (X i)).symm
    linarith
  have hne : (Finset.univ : Finset (ZMod k)).Nonempty := Finset.univ_nonempty
  obtain ⟨c, _, hcmax⟩ := Finset.univ.exists_max_image (fun i => ⟪ν, p i⟫) hne
  have hcmax' : ∀ i : ZMod k, ⟪ν, p i⟫ ≤ ⟪ν, p c⟫ := fun i => hcmax i (Finset.mem_univ i)
  have hj2 : a + 2 ≠ a ∧ a + 2 ≠ a + 1 := by
    refine ⟨?_, ?_⟩
    · have := Minimality.zmod_add_ne (k := k) (a := 0) (b := 2) (by omega) (by omega) (by decide) a
      simpa using this.symm
    · have := Minimality.zmod_add_ne (k := k) (a := 1) (b := 2) (by omega) (by omega) (by decide) a
      simpa using this.symm
  have ha_lt_j : ⟪ν, p a⟫ < ⟪ν, p (a + 2)⟫ := by
    have hpos := hrim a (a + 2) hj2.1 hj2.2
    rw [det3_swap_mid, det3_sub_right] at hpos
    linarith [hinner a, hinner (a + 2)]
  have ha_eq_a1 : ⟪ν, p (a + 1)⟫ = ⟪ν, p a⟫ := by
    have h0 : det3 d w (X (a + 1) - X a) = 0 := by
      change det3 (X (a + 1) - X a) w (X (a + 1) - X a) = 0
      simp only [det3]; ring
    rw [det3_sub_right] at h0
    linarith [hinner a, hinner (a + 1)]
  have hca : c ≠ a := by
    intro h; rw [h] at hcmax'; linarith [hcmax' (a + 2)]
  have hca1 : c ≠ a + 1 := by
    intro h; rw [h] at hcmax'; linarith [hcmax' (a + 2)]
  have hstrict : ∀ i : ZMod k, i ≠ c → det3 d w (X c) < det3 d w (X i) := by
    intro i hic
    have hle := hcmax' i
    rcases lt_or_eq_of_le hle with hlt | heq
    · linarith [hinner i, hinner c]
    · exfalso
      have hadj := hp.max_adjacent hν hcmax' heq
      rcases hadj with rfl | rfl | rfl
      · have hia : c - 1 ≠ a := by
          intro h; apply hca1; linear_combination h
        have h0 : det3 d (X (c - 1 + 1) - X (c - 1)) w = 0 := by
          have hc1 : c - 1 + 1 = c := by ring
          rw [hc1, det3_swap_mid, det3_sub_right]
          linarith [hinner c, hinner (c - 1)]
        exact hgen a (c - 1) hia.symm h0
      · exact absurd rfl hic
      · have h0 : det3 d (X (c + 1) - X c) w = 0 := by
          rw [det3_swap_mid, det3_sub_right]
          linarith [hinner c, hinner (c + 1)]
        exact hgen a c hca.symm h0
  refine ⟨c, ⟨hca, hca1, hstrict⟩, ?_⟩
  rintro c' ⟨_, _, hc'⟩
  by_contra hne'
  have h1 := hstrict c' hne'
  have h2 := hc' c (Ne.symm hne')
  linarith

/-- Noncomputable far-corner map `far X w a`. -/
noncomputable def farCorner {k : ℕ} [NeZero k] (hk : 4 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³)
    (hrim : StrictRimCcw X w) (hgen : NoParallelRimEdges X w) (a : ZMod k) : ZMod k :=
  Classical.choose (exists_farCorner hk X w hrim hgen a).exists

lemma farCorner_spec {k : ℕ} [NeZero k] (hk : 4 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³)
    (hrim : StrictRimCcw X w) (hgen : NoParallelRimEdges X w) (a : ZMod k) :
    let c := farCorner hk X w hrim hgen a
    c ≠ a ∧ c ≠ a + 1 ∧
      ∀ i : ZMod k, i ≠ c → det3 (X (a + 1) - X a) w (X c) < det3 (X (a + 1) - X a) w (X i) :=
  Classical.choose_spec (exists_farCorner hk X w hrim hgen a).exists

/-- Height monotonicity from `farCorner`: on `(c .. a)` the height `det3 E_a w (X ·)` strictly
increases, and on `(a + 1 .. c)` it strictly decreases. -/
lemma farCorner_height_arcs {k : ℕ} [NeZero k] (hk : 4 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³)
    (hrim : StrictRimCcw X w) (hgen : NoParallelRimEdges X w) (a : ZMod k) :
    let c := farCorner hk X w hrim hgen a
    (∀ s : ℕ, s < (a - c).val →
      det3 (X (a + 1) - X a) w (X (c + (s : ZMod k))) <
        det3 (X (a + 1) - X a) w (X (c + ((s + 1 : ℕ) : ZMod k)))) ∧
    (∀ s : ℕ, (a + 1 - c).val ≤ s → s < k →
      det3 (X (a + 1) - X a) w (X (c + ((s + 1 : ℕ) : ZMod k))) <
        det3 (X (a + 1) - X a) w (X (c + (s : ZMod k)))) := by
  intro c
  set d := X (a + 1) - X a
  set N := cross d w
  set p : ZMod k → ℝ² := fun i => projP N w (X i)
  obtain ⟨_, hp⟩ := projP_isCcw (by omega) X w hrim a
  let ν : ℝ² := !₂[-1, 0]
  have hinner : ∀ i : ZMod k, ⟪ν, p i⟫ = -det3 d w (X i) := fun i => by
    have h1 : ⟪ν, p i⟫ = -(p i 0) := by
      simp [ν, PiLp.inner_apply, Fin.sum_univ_two]
    have h2 : p i 0 = ⟪X i, N⟫ := by simp [p, projP]
    have h3 : ⟪X i, N⟫ = det3 d w (X i) := by
      rw [real_inner_comm]; exact (det3_eq_inner d w (X i)).symm
    linarith
  have hc := farCorner_spec hk X w hrim hgen a
  have hcmax : ∀ i : ZMod k, ⟪ν, p i⟫ ≤ ⟪ν, p c⟫ := fun i => by
    by_cases hi : i = c
    · subst hi; exact le_rfl
    · linarith [hc.2.2 i hi, hinner i, hinner c]
  obtain ⟨t, htk, ht1, ht2⟩ := hp.pattern_from_max ν c hcmax
  have ha_min : ∀ j : ZMod k, j ≠ a → j ≠ a + 1 → ⟪ν, p a⟫ < ⟪ν, p j⟫ := fun j hj1 hj2 => by
    have hpos := hrim a j hj1 hj2
    rw [det3_swap_mid, det3_sub_right] at hpos
    linarith [hinner a, hinner j]
  have ha_eq : ⟪ν, p (a + 1)⟫ = ⟪ν, p a⟫ := by
    have h0 : det3 d w (X (a + 1) - X a) = 0 := by
      change det3 (X (a + 1) - X a) w (X (a + 1) - X a) = 0
      simp only [det3]; ring
    rw [det3_sub_right] at h0
    linarith [hinner a, hinner (a + 1)]
  have h_ac_lt : (a - c).val < k := ZMod.val_lt _
  have h_a1c_lt : (a + 1 - c).val < k := ZMod.val_lt _
  have h_ac_pos : 0 < (a - c).val := by
    by_contra h0
    have hz : (a - c).val = 0 := by omega
    have : a - c = 0 := by rw [← ZMod.natCast_zmod_val (a - c), hz]; simp
    exact hc.1 (sub_eq_zero.mp this).symm
  have h_a1c_eq : (a + 1 - c).val = (a - c).val + 1 ∨
      ((a - c).val + 1 = k ∧ (a + 1 - c).val = 0) := by
    have : Fact (1 < k) := ⟨by omega⟩
    have hsum : a + 1 - c = (a - c) + 1 := by ring
    rw [hsum, ZMod.val_add, ZMod.val_one]
    by_cases hlt : (a - c).val + 1 < k
    · left; exact Nat.mod_eq_of_lt hlt
    · right; have : (a - c).val + 1 = k := by omega
      exact ⟨this, by rw [this, Nat.mod_self]⟩
  have h_a1c_pos : 0 < (a + 1 - c).val := by
    by_contra h0
    have hz : (a + 1 - c).val = 0 := by omega
    have : a + 1 - c = 0 := by rw [← ZMod.natCast_zmod_val (a + 1 - c), hz]; simp
    exact hc.2.1 (sub_eq_zero.mp this).symm
  have h_step : (a + 1 - c).val = (a - c).val + 1 := by
    rcases h_a1c_eq with h | ⟨_, h0⟩
    · exact h
    · omega
  -- Show `(a - c).val ≤ t` and `t ≤ (a + 1 - c).val`
  have hle_t : (a - c).val ≤ t := by
    by_contra hlt
    push Not at hlt
    -- `t < (a - c).val`, so `⟪ν, p (c + t)⟫ ≤ ⟪ν, p a⟫`
    have hinc : ∀ m : ℕ, t ≤ m → m ≤ (a - c).val → ⟪ν, p (c + (t : ZMod k))⟫ ≤ ⟪ν, p (c + (m : ZMod k))⟫ := by
      intro m htm hma
      induction m with
      | zero =>
        have : t = 0 := by omega
        subst this; exact le_rfl
      | succ m ih =>
        by_cases htm' : t ≤ m
        · have ih' := ih htm' (by omega)
          have hstep := ht2 m htm' (by omega)
          rw [inner_sub_right] at hstep
          linarith
        · have : t = m + 1 := by omega
          subst this; exact le_rfl
    have hle := hinc (a - c).val (by omega) le_rfl
    have ha_rw : c + ((a - c).val : ZMod k) = a := by
      rw [ZMod.natCast_zmod_val]; ring
    rw [ha_rw] at hle
    have hct_ne_a : c + (t : ZMod k) ≠ a := by
      intro h
      have hsub : (t : ZMod k) = a - c := by linear_combination h
      have := congrArg ZMod.val hsub
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hct_ne_a1 : c + (t : ZMod k) ≠ a + 1 := by
      intro h
      have hsub : (t : ZMod k) = a + 1 - c := by linear_combination h
      have := congrArg ZMod.val hsub
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), h_step] at this
      omega
    linarith [ha_min (c + (t : ZMod k)) hct_ne_a hct_ne_a1]
  have ht_le : t ≤ (a + 1 - c).val := by
    by_contra hlt
    push Not at hlt
    have hstep := ht1 (a + 1 - c).val hlt
    rw [inner_sub_right] at hstep
    have ha1_rw : c + ((a + 1 - c).val : ZMod k) = a + 1 := by
      rw [ZMod.natCast_zmod_val]; ring
    rw [ha1_rw, ha_eq] at hstep
    by_cases hk1 : (a + 1 - c).val + 1 = k
    · have hcw : c + (((a + 1 - c).val + 1 : ℕ) : ZMod k) = c := by
        rw [hk1]; simp
      rw [hcw] at hstep
      have hltc := ha_min c hc.1 hc.2.1
      linarith
    · have hne_a : c + (((a + 1 - c).val + 1 : ℕ) : ZMod k) ≠ a := by
        intro h
        have hsub : (((a + 1 - c).val + 1 : ℕ) : ZMod k) = a - c := by linear_combination h
        have := congrArg ZMod.val hsub
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
        omega
      have hne_a1 : c + (((a + 1 - c).val + 1 : ℕ) : ZMod k) ≠ a + 1 := by
        intro h
        have hsub : (((a + 1 - c).val + 1 : ℕ) : ZMod k) = a + 1 - c := by linear_combination h
        have := congrArg ZMod.val hsub
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
        omega
      linarith [ha_min _ hne_a hne_a1]
  refine ⟨fun s hs => ?_, fun s hs1 hs2 => ?_⟩
  · have hle := ht1 s (by omega)
    rw [inner_sub_right] at hle
    have hle' : ⟪ν, p (c + ((s + 1 : ℕ) : ZMod k))⟫ - ⟪ν, p (c + (s : ZMod k))⟫ ≤ 0 := hle
    have hne_a : c + (s : ZMod k) ≠ a := by
      intro h
      have hsub : (s : ZMod k) = a - c := by linear_combination h
      have := congrArg ZMod.val hsub
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hne : det3 d w (X (c + ((s + 1 : ℕ) : ZMod k))) - det3 d w (X (c + (s : ZMod k))) ≠ 0 := by
      rw [← det3_sub_right]
      have hsucc : (c + ((s + 1 : ℕ) : ZMod k)) = (c + (s : ZMod k)) + 1 := by push_cast; ring
      rw [hsucc]
      intro h0
      apply hgen a (c + (s : ZMod k)) hne_a.symm
      rw [det3_swap_mid]; linarith
    have hlt : det3 d w (X (c + (s : ZMod k))) ≤ det3 d w (X (c + ((s + 1 : ℕ) : ZMod k))) := by
      linarith [hinner (c + (s : ZMod k)), hinner (c + ((s + 1 : ℕ) : ZMod k))]
    exact lt_of_le_of_ne hlt (fun h => hne (by linarith))
  · have hle := ht2 s (by omega) hs2
    rw [inner_sub_right] at hle
    have hle' : 0 ≤ ⟪ν, p (c + ((s + 1 : ℕ) : ZMod k))⟫ - ⟪ν, p (c + (s : ZMod k))⟫ := hle
    have hne_a : c + (s : ZMod k) ≠ a := by
      intro h
      have hsub : (s : ZMod k) = a - c := by linear_combination h
      have := congrArg ZMod.val hsub
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hne : det3 d w (X (c + ((s + 1 : ℕ) : ZMod k))) - det3 d w (X (c + (s : ZMod k))) ≠ 0 := by
      rw [← det3_sub_right]
      have hsucc : (c + ((s + 1 : ℕ) : ZMod k)) = (c + (s : ZMod k)) + 1 := by push_cast; ring
      rw [hsucc]
      intro h0
      apply hgen a (c + (s : ZMod k)) hne_a.symm
      rw [det3_swap_mid]; linarith
    have hlt : det3 d w (X (c + ((s + 1 : ℕ) : ZMod k))) ≤ det3 d w (X (c + (s : ZMod k))) := by
      linarith [hinner (c + (s : ZMod k)), hinner (c + ((s + 1 : ℕ) : ZMod k))]
    exact lt_of_le_of_ne hlt (fun h => hne (by linarith))

/-! ## Unimodal depth structure and discrete intermediate-value theorem -/

private lemma strictlyUnimodal_chain1_lt {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {w : ℝ³}
    {m M : ZMod k} (huni : StrictlyUnimodal X w m M) :
    ∀ s t : ℕ, s < t → t ≤ (M - m).val →
      ⟪X (m + (s : ZMod k)), w⟫ < ⟪X (m + (t : ZMod k)), w⟫ := by
  intro s t hst ht
  induction t with
  | zero => omega
  | succ t ih =>
    have hstep := huni.2.1 t (by omega)
    by_cases hst' : s < t
    · exact lt_trans (ih hst' (by omega)) hstep
    · have : s = t := by omega
      subst this; exact hstep

private lemma strictlyUnimodal_chain2_lt {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {w : ℝ³}
    {m M : ZMod k} (huni : StrictlyUnimodal X w m M) :
    ∀ s t : ℕ, (M - m).val ≤ s → s < t → t ≤ k →
      ⟪X (m + (t : ZMod k)), w⟫ < ⟪X (m + (s : ZMod k)), w⟫ := by
  intro s t hs hst ht
  induction t with
  | zero => omega
  | succ t ih =>
    have hstep := huni.2.2 t (by omega) (by omega)
    by_cases hst' : s < t
    · exact lt_trans hstep (ih hst' (by omega))
    · have : s = t := by omega
      subst this; exact hstep

private lemma strictlyUnimodal_min_max {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {w : ℝ³}
    {m M : ZMod k} (huni : StrictlyUnimodal X w m M) :
    (∀ i : ZMod k, i ≠ m → ⟪X m, w⟫ < ⟪X i, w⟫) ∧
    (∀ i : ZMod k, i ≠ M → ⟪X i, w⟫ < ⟪X M, w⟫) := by
  have hk_pos : 0 < k := NeZero.pos k
  have hL_pos : 0 < (M - m).val := by
    by_contra h0
    have hz : (M - m).val = 0 := by omega
    have : M - m = 0 := by rw [← ZMod.natCast_zmod_val (M - m), hz]; simp
    exact huni.1 (sub_eq_zero.mp this).symm
  have hL_lt : (M - m).val < k := ZMod.val_lt _
  have hm_eq : X (m + ((0 : ℕ) : ZMod k)) = X m := by simp
  have hM_eq : m + ((M - m).val : ZMod k) = M := by rw [ZMod.natCast_zmod_val]; ring
  have hk_eq : m + (k : ZMod k) = m := by simp
  refine ⟨fun i him => ?_, fun i hiM => ?_⟩
  · set s := (i - m).val
    have hs_lt : s < k := ZMod.val_lt _
    have hs_pos : 0 < s := by
      by_contra h0
      have hz_eq : s = 0 := by omega
      have hs_eq : (i - m : ZMod k) = 0 := by
        rw [← ZMod.natCast_zmod_val (i - m)]
        change ((s : ℕ) : ZMod k) = 0
        rw [hz_eq]; simp
      exact him (sub_eq_zero.mp hs_eq)
    have hi_eq : m + (s : ZMod k) = i := by rw [ZMod.natCast_zmod_val]; ring
    rw [← hi_eq]
    by_cases hsL : s ≤ (M - m).val
    · simpa using strictlyUnimodal_chain1_lt huni 0 s hs_pos hsL
    · have := strictlyUnimodal_chain2_lt huni s k (by omega) hs_lt le_rfl
      simpa [hk_eq] using this
  · set s := (i - m).val
    have hs_lt : s < k := ZMod.val_lt _
    have hs_ne : s ≠ (M - m).val := by
      intro h
      apply hiM
      have : i - m = M - m := by
        rw [← ZMod.natCast_zmod_val (i - m), ← ZMod.natCast_zmod_val (M - m)]
        change ((s : ℕ) : ZMod k) = _
        rw [h]
      linear_combination this
    have hi_eq : m + (s : ZMod k) = i := by rw [ZMod.natCast_zmod_val]; ring
    rw [← hi_eq, ← hM_eq]
    by_cases hsL : s < (M - m).val
    · exact strictlyUnimodal_chain1_lt huni s (M - m).val hsL le_rfl
    · exact strictlyUnimodal_chain2_lt huni (M - m).val s le_rfl (by omega) (by omega)

/-- Depth-separation arc condition at `(e2, c)` when `c` is on Chain 1 (`0 < (c - m).val < L`)
and `e2` is on Chain 2 (`L ≤ (e2 - m).val < k`) with `⟪X (e2 + 1), w⟫ < ⟪X c, w⟫ < ⟪X e2, w⟫`. -/
private lemma depthArcs_of_chain1 {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {w : ℝ³}
    {m M : ZMod k} (huni : StrictlyUnimodal X w m M) {c e2 : ZMod k}
    (_hc1 : 0 < (c - m).val) (hc2 : (c - m).val < (M - m).val)
    (he1 : (M - m).val ≤ (e2 - m).val) (he2 : (e2 - m).val < k)
    (hz1 : ⟪X (e2 + 1), w⟫ < ⟪X c, w⟫) (hz2 : ⟪X c, w⟫ < ⟪X e2, w⟫) :
    ((∀ s : ℕ, 0 < s → s ≤ (e2 - c).val → ⟪X c, w⟫ < ⟪X (c + (s : ZMod k)), w⟫) ∧
      ∀ s : ℕ, (e2 - c).val < s → s < k → ⟪X (c + (s : ZMod k)), w⟫ < ⟪X c, w⟫) ∨
    ((∀ s : ℕ, 0 < s → s ≤ (e2 - c).val → ⟪X (c + (s : ZMod k)), w⟫ < ⟪X c, w⟫) ∧
      ∀ s : ℕ, (e2 - c).val < s → s < k → ⟪X c, w⟫ < ⟪X (c + (s : ZMod k)), w⟫) := by
  left
  have hec : (e2 - c).val = (e2 - m).val - (c - m).val := by
    have hsum : (e2 - m) = (e2 - c) + (c - m) := by ring
    have hlt1 : (e2 - m).val < k := ZMod.val_lt _
    have hlt2 : (c - m).val < k := ZMod.val_lt _
    have hlt3 : (e2 - c).val < k := ZMod.val_lt _
    have hval := congrArg ZMod.val hsum
    rw [ZMod.val_add] at hval
    by_cases hsum_lt : (e2 - c).val + (c - m).val < k
    · rw [Nat.mod_eq_of_lt hsum_lt] at hval; omega
    · exfalso
      have : ((e2 - c).val + (c - m).val) % k = (e2 - c).val + (c - m).val - k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
  · have hc_s : c + (s : ZMod k) = m + (((c - m).val + s : ℕ) : ZMod k) := by
      push_cast; rw [ZMod.natCast_zmod_val]; ring
    rw [hc_s]
    by_cases hL : (c - m).val + s ≤ (M - m).val
    · have hc_eq : c = m + ((c - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
      conv_lhs => rw [hc_eq]
      exact strictlyUnimodal_chain1_lt huni (c - m).val ((c - m).val + s) (by omega) hL
    · have hle : (c - m).val + s ≤ (e2 - m).val := by omega
      have he2_eq : e2 = m + ((e2 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
      by_cases heq : (c - m).val + s = (e2 - m).val
      · rw [heq, ← he2_eq]; exact hz2
      · have := strictlyUnimodal_chain2_lt huni ((c - m).val + s) (e2 - m).val (by omega) (by omega) (by omega)
        rw [← he2_eq] at this; exact lt_trans hz2 this
  · have hc_s : c + (s : ZMod k) = m + (((c - m).val + s : ℕ) : ZMod k) := by
      push_cast; rw [ZMod.natCast_zmod_val]; ring
    rw [hc_s]
    by_cases hlt_k : (c - m).val + s < k
    · have he1_pos : (e2 - m).val + 1 ≤ (c - m).val + s := by omega
      have he1_eq : e2 + 1 = m + (((e2 - m).val + 1 : ℕ) : ZMod k) := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      by_cases heq : (e2 - m).val + 1 = (c - m).val + s
      · rw [← heq, ← he1_eq]; exact hz1
      · have := strictlyUnimodal_chain2_lt huni ((e2 - m).val + 1) ((c - m).val + s) (by omega) (by omega) (by omega)
        rw [← he1_eq] at this; exact lt_trans this hz1
    · have hmod : (((c - m).val + s : ℕ) : ZMod k) = (((c - m).val + s - k : ℕ) : ZMod k) := by
        have : (c - m).val + s = ((c - m).val + s - k) + k := by omega
        rw [this]; push_cast; simp
      rw [hmod]
      have hlt_c : (c - m).val + s - k < (c - m).val := by omega
      have hc_eq : c = m + ((c - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
      conv_rhs => rw [hc_eq]
      exact strictlyUnimodal_chain1_lt huni ((c - m).val + s - k) (c - m).val hlt_c (by omega)

/-- Depth-separation arc condition at `(e1, c)` when `c` is on Chain 2 (`L < (c - m).val < k`)
and `e1` is on Chain 1 (`(e1 - m).val < L`) with `⟪X e1, w⟫ < ⟪X c, w⟫ < ⟪X (e1 + 1), w⟫`. -/
private lemma depthArcs_of_chain2 {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {w : ℝ³}
    {m M : ZMod k} (huni : StrictlyUnimodal X w m M) {c e1 : ZMod k}
    (hc1 : (M - m).val < (c - m).val) (hc2 : (c - m).val < k)
    (he1 : (e1 - m).val < (M - m).val)
    (hz1 : ⟪X e1, w⟫ < ⟪X c, w⟫) (hz2 : ⟪X c, w⟫ < ⟪X (e1 + 1), w⟫) :
    ((∀ s : ℕ, 0 < s → s ≤ (e1 - c).val → ⟪X c, w⟫ < ⟪X (c + (s : ZMod k)), w⟫) ∧
      ∀ s : ℕ, (e1 - c).val < s → s < k → ⟪X (c + (s : ZMod k)), w⟫ < ⟪X c, w⟫) ∨
    ((∀ s : ℕ, 0 < s → s ≤ (e1 - c).val → ⟪X (c + (s : ZMod k)), w⟫ < ⟪X c, w⟫) ∧
      ∀ s : ℕ, (e1 - c).val < s → s < k → ⟪X c, w⟫ < ⟪X (c + (s : ZMod k)), w⟫) := by
  right
  have hec : (e1 - c).val = k - (c - m).val + (e1 - m).val := by
    have hsum : (e1 - c) + (c - m) = (e1 - m) := by ring
    have hlt1 : (e1 - m).val < k := ZMod.val_lt _
    have hlt2 : (c - m).val < k := ZMod.val_lt _
    have hlt3 : (e1 - c).val < k := ZMod.val_lt _
    have hval := congrArg ZMod.val hsum
    rw [ZMod.val_add] at hval
    by_cases hsum_lt : (e1 - c).val + (c - m).val < k
    · rw [Nat.mod_eq_of_lt hsum_lt] at hval; omega
    · have : ((e1 - c).val + (c - m).val) % k = (e1 - c).val + (c - m).val - k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [this] at hval; omega
  refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
  · by_cases hlt_k : (c - m).val + s < k
    · have hc_s : c + (s : ZMod k) = m + (((c - m).val + s : ℕ) : ZMod k) := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      have hc_eq : c = m + ((c - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
      rw [hc_s]; conv_rhs => rw [hc_eq]
      exact strictlyUnimodal_chain2_lt huni (c - m).val ((c - m).val + s) (by omega) (by omega) (by omega)
    · have hmod : c + (s : ZMod k) = m + (((c - m).val + s - k : ℕ) : ZMod k) := by
        have h1 : (c - m).val + s = ((c - m).val + s - k) + k := by omega
        have h2 : c + (s : ZMod k) = m + (((c - m).val + s : ℕ) : ZMod k) := by
          push_cast; rw [ZMod.natCast_zmod_val]; ring
        rw [h2, h1]; push_cast; simp
      rw [hmod]
      have hle_e1 : (c - m).val + s - k ≤ (e1 - m).val := by omega
      have he1_eq : e1 = m + ((e1 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
      by_cases heq : (c - m).val + s - k = (e1 - m).val
      · rw [heq, ← he1_eq]; exact hz1
      · have := strictlyUnimodal_chain1_lt huni ((c - m).val + s - k) (e1 - m).val (by omega) (by omega)
        rw [← he1_eq] at this; exact lt_trans this hz1
  · have hmod : c + (s : ZMod k) = m + (((c - m).val + s - k : ℕ) : ZMod k) := by
      have h1 : (c - m).val + s = ((c - m).val + s - k) + k := by omega
      have h2 : c + (s : ZMod k) = m + (((c - m).val + s : ℕ) : ZMod k) := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      rw [h2, h1]; push_cast; simp
    rw [hmod]
    have hge_e11 : (e1 - m).val + 1 ≤ (c - m).val + s - k := by omega
    have hlt_k' : (c - m).val + s - k < (c - m).val := by omega
    have he11_eq : e1 + 1 = m + (((e1 - m).val + 1 : ℕ) : ZMod k) := by
      push_cast; rw [ZMod.natCast_zmod_val]; ring
    by_cases hL : (c - m).val + s - k ≤ (M - m).val
    · by_cases heq : (e1 - m).val + 1 = (c - m).val + s - k
      · rw [← heq, ← he11_eq]; exact hz2
      · have := strictlyUnimodal_chain1_lt huni ((e1 - m).val + 1) ((c - m).val + s - k) (by omega) hL
        rw [← he11_eq] at this; exact lt_trans hz2 this
    · have := strictlyUnimodal_chain2_lt huni ((M - m).val) ((c - m).val + s - k) le_rfl (by omega) (by omega)
      have hM_eq : m + ((M - m).val : ZMod k) = M := by rw [ZMod.natCast_zmod_val]; ring
      rw [hM_eq] at this
      have hc_eq : c = m + ((c - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
      have h2 := strictlyUnimodal_chain2_lt huni ((c - m).val + s - k) (c - m).val (by omega) hlt_k' (by omega)
      rw [← hc_eq] at h2; exact h2

/-- **Main theorem (Task FE1):** Every generic strictly unimodal ccw rim (`k ≥ 4`) is
depth-separated at some `(a, c)`. -/
theorem isDepthSeparatedAt_of_unimodal {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (X : ZMod k → ℝ³) (w : ℝ³) (m M : ZMod k)
    (hrim : StrictRimCcw X w)
    (hdist : ∀ i j : ZMod k, i ≠ j → ⟪X i, w⟫ ≠ ⟪X j, w⟫)
    (huni : StrictlyUnimodal X w m M)
    (hgen : NoParallelRimEdges X w) :
    ∃ a c : ZMod k, IsDepthSeparatedAt X w a c := by
  classical
  have : Fact (1 < k) := ⟨by omega⟩
  let z : ZMod k → ℝ := fun i => ⟪X i, w⟫
  let far : ZMod k → ZMod k := fun a => farCorner hk X w hrim hgen a
  have hfar := fun a => farCorner_spec hk X w hrim hgen a
  have harcs := fun a => farCorner_height_arcs hk X w hrim hgen a
  obtain ⟨hmin, hmax⟩ := strictlyUnimodal_min_max huni
  -- Sort `ZMod k` by `z` via `Finset.orderIsoOfFin` on `Finset.univ.image z`
  have hz_inj : Function.Injective z := fun i j hij => by
    by_contra hne; exact hdist i j hne hij
  let S := (Finset.univ : Finset (ZMod k)).image z
  have hS_card : S.card = k := by
    rw [Finset.card_image_of_injective _ hz_inj, Finset.card_univ, ZMod.card]
  let f := S.orderIsoOfFin hS_card
  let v : ℕ → ZMod k := fun r =>
    if hr : r < k then (Finset.mem_image.mp (f ⟨r, hr⟩).2).choose else m
  have hv_z : ∀ r : ℕ, (hr : r < k) → z (v r) = (f ⟨r, hr⟩).1 := fun r hr => by
    simp only [v]
    split_ifs
    exact (Finset.mem_image.mp (f ⟨r, hr⟩).2).choose_spec.2
  have hv_lt : ∀ r1 r2 : ℕ, r1 < r2 → r2 < k → z (v r1) < z (v r2) := fun r1 r2 h12 hr2 => by
    rw [hv_z r1 (by omega), hv_z r2 hr2]
    exact f.strictMono (Fin.mk_lt_mk.mpr h12)
  have hv_mem : ∀ i : ZMod k, ∃ r : ℕ, r < k ∧ v r = i := by
    intro i
    have hiS : z i ∈ S := Finset.mem_image_of_mem z (Finset.mem_univ i)
    obtain ⟨idx, hidx⟩ := f.surjective ⟨z i, hiS⟩
    refine ⟨idx.val, idx.isLt, ?_⟩
    apply hz_inj
    rw [hv_z idx.val idx.isLt]
    exact congrArg Subtype.val hidx
  have hv0 : v 0 = m := by
    by_contra hne
    obtain ⟨r, hr, hvr⟩ := hv_mem m
    have hr0 : 0 < r := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hvr; exact hne hvr)
    have := hv_lt 0 r hr0 hr
    rw [hvr] at this
    have := hmin (v 0) hne
    linarith
  have hvk : v (k - 1) = M := by
    by_contra hne
    obtain ⟨r, hr, hvr⟩ := hv_mem M
    have hrk : r < k - 1 := by
      by_contra hge
      have hrk' : r = k - 1 := by omega
      rw [hrk'] at hvr; exact hne hvr
    have := hv_lt r (k - 1) hrk (by omega)
    rw [hvr] at this
    have := hmax (v (k - 1)) hne
    linarith
  -- Construct `e1 r` and `e2 r` by recursion for `0 ≤ r ≤ k - 2`
  -- Step function: given `(e1, e2)` at level `r`, advance whichever has `v (r + 1)`
  let stepPair : ℕ → ZMod k × ZMod k → ZMod k × ZMod k := fun r p =>
    if v (r + 1) = p.1 + 1 then (p.1 + 1, p.2) else (p.1, p.2 - 1)
  let pairAt : ℕ → ZMod k × ZMod k := fun r =>
    Nat.rec (m, m - 1) (fun n p => stepPair n p) r
  let e1 : ℕ → ZMod k := fun r => (pairAt r).1
  let e2 : ℕ → ZMod k := fun r => (pairAt r).2
  -- Prove the invariants of `(e1 r, e2 r)` for `0 ≤ r ≤ k - 2`
  have hinv : ∀ r : ℕ, r ≤ k - 2 →
      (e1 r - m).val < (M - m).val ∧
      (M - m).val ≤ (e2 r - m).val ∧ (e2 r - m).val < k ∧
      (e1 r - m).val + (k - (e2 r - m).val) = r + 1 ∧
      z (e1 r) ≤ z (v r) ∧ z (v (r + 1)) ≤ z (e1 r + 1) ∧
      z (e2 r + 1) ≤ z (v r) ∧ z (v (r + 1)) ≤ z (e2 r) := by
    intro r hr
    induction r with
    | zero =>
      have hL_pos : 0 < (M - m).val := by
        by_contra h0
        have hz : (M - m).val = 0 := by omega
        have : M - m = 0 := by rw [← ZMod.natCast_zmod_val (M - m), hz]; simp
        exact huni.1 (sub_eq_zero.mp this).symm
      have hL_lt : (M - m).val < k := ZMod.val_lt _
      have he1_0 : e1 0 = m := rfl
      have he2_0 : e2 0 = m - 1 := rfl
      have hm1_val : (m - 1 - m : ZMod k).val = k - 1 := by
        have : (m - 1 - m : ZMod k) = -1 := by ring
        rw [this, ← Minimality.zmod_natCast_pred (by omega), ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [he1_0, he2_0, sub_self, ZMod.val_zero, hm1_val, hv0]
      have h12 : e1 0 + 1 ≠ e2 0 := by
        rw [he1_0, he2_0]
        exact (Minimality.zmod_sub_one_ne_add_one (by omega) m).symm
      have hmin_e11 : z (v 1) ≤ z (m + 1) := by
        by_contra hlt; push Not at hlt
        -- `v 1` has `z m < z (v 1) < z (m + 1)` and `z (v 1) < z (m - 1)`? Wait: `v 1` is the 2nd smallest!
        have hm1_ne : m + 1 ≠ m := Minimality.zmod_ne_add_one (by omega) m |>.symm
        obtain ⟨s, hs, hvs⟩ := hv_mem (m + 1)
        have hs0 : 0 < s := Nat.pos_of_ne_zero (fun h0 => by rw [h0, hv0] at hvs; exact hm1_ne hvs.symm)
        have hs1 : 1 < s := Nat.lt_of_le_of_ne hs0 (fun h1 => by
          rw [← h1] at hvs; rw [hvs] at hlt; exact lt_irrefl _ hlt)
        have := hv_lt 1 s hs1 hs
        rw [hvs] at this; linarith
      have hmin_e20 : z (v 1) ≤ z (m - 1) := by
        by_contra hlt; push Not at hlt
        have hm1_ne : m - 1 ≠ m := fun h => by
          have : (1 : ZMod k) = 0 := by linear_combination -h
          have hf : Fact (1 < k) := ⟨by omega⟩
          exact one_ne_zero this
        obtain ⟨s, hs, hvs⟩ := hv_mem (m - 1)
        have hs0 : 0 < s := Nat.pos_of_ne_zero (fun h0 => by rw [h0, hv0] at hvs; exact hm1_ne hvs.symm)
        have hs1 : 1 < s := Nat.lt_of_le_of_ne hs0 (fun h1 => by
          rw [← h1] at hvs; rw [hvs] at hlt; exact lt_irrefl _ hlt)
        have := hv_lt 1 s hs1 hs
        rw [hvs] at this; linarith
      refine ⟨hL_pos, by omega, by omega, by omega, le_rfl, hmin_e11, by simp, hmin_e20⟩
    | succ r ih =>
      obtain ⟨ih1, ih2, ih3, ih4, ihz1, ihz2, ihz3, ihz4⟩ := ih (by omega)
      -- At step `r`, either `v (r + 1) = e1 r + 1` or `v (r + 1) = e2 r`
      -- Why must `v (r + 1)` be one of `e1 r + 1` or `e2 r`?
      have hv_step : v (r + 1) = e1 r + 1 ∨ v (r + 1) = e2 r := by
        by_contra hneither
        push Not at hneither
        obtain ⟨s, hs, hvs⟩ := hv_mem (e1 r + 1)
        obtain ⟨t, ht, hvt⟩ := hv_mem (e2 r)
        -- Both `e1 r + 1` and `e2 r` have `z ≥ z (v (r + 1))`, and neither equals `v (r + 1)`, so both have index `> r + 1`!
        -- Wait: then `Below(r + 1)` has `r + 2` vertices, all on `Chain 1` (`≤ e1 r`) or `Chain 2` (`≥ e2 r + 1`),
        -- which has size `(e1 r - m).val + 1 + (k - 1 - (e2 r - m).val) = r + 1`! Contradiction by cardinality!
        -- Let's prove this cleanly using `Finset.card` or direct index bound!
        have h_all : ∀ q : ℕ, q ≤ r + 1 →
            (v q - m).val ≤ (e1 r - m).val ∨ (e2 r - m).val + 1 ≤ (v q - m).val := by
          intro q hq
          by_contra hmid
          push Not at hmid
          have hq1 : (e1 r - m).val + 1 ≤ (v q - m).val := by omega
          have hq2 : (v q - m).val ≤ (e2 r - m).val := by omega
          have hvq_eq : v q = m + ((v q - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
          by_cases hL : (v q - m).val ≤ (M - m).val
          · have he11_eq : e1 r + 1 = m + (((e1 r - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z (e1 r + 1) ≤ z (v q) := by
              rw [hvq_eq, he11_eq]
              by_cases heq : (e1 r - m).val + 1 = (v q - m).val
              · rw [heq]
              · exact (strictlyUnimodal_chain1_lt huni ((e1 r - m).val + 1) (v q - m).val (by omega) hL).le
            have hzq : z (v q) ≤ z (v (r + 1)) := by
              by_cases hqr : q = r + 1
              · subst hqr; exact le_rfl
              · exact (hv_lt q (r + 1) (by omega) (by omega)).le
            have heq_z : z (v (r + 1)) = z (e1 r + 1) := by linarith
            have heq_v : v (r + 1) = e1 r + 1 := by
              by_contra hne'; exact hdist _ _ hne' heq_z
            exact hneither.1 heq_v
          · have he2_eq : e2 r = m + ((e2 r - m).val : ZMod k) := by
              rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z (e2 r) ≤ z (v q) := by
              rw [hvq_eq, he2_eq]
              by_cases heq : (v q - m).val = (e2 r - m).val
              · rw [heq]
              · exact (strictlyUnimodal_chain2_lt huni (v q - m).val (e2 r - m).val (by omega) (by omega) (by omega)).le
            have hzq : z (v q) ≤ z (v (r + 1)) := by
              by_cases hqr : q = r + 1
              · subst hqr; exact le_rfl
              · exact (hv_lt q (r + 1) (by omega) (by omega)).le
            have heq_z : z (v (r + 1)) = z (e2 r) := by linarith
            have heq_v : v (r + 1) = e2 r := by
              by_contra hne'; exact hdist _ _ hne' heq_z
            exact hneither.2 heq_v
        -- Now inject `{0, ..., r + 1}` into `Iic (e1 r - m).val ∪ Ici ((e2 r - m).val + 1) ∩ Iio k`
        let f : ℕ → ℕ := fun q => (v q - m).val
        have hf_inj : Set.InjOn f (Finset.range (r + 2)) := by
          intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_range] at ha hb
          have hvab : v a = v b := by
            dsimp only [f] at hab
            have : (v a - m : ZMod k) = v b - m := by
              rw [← ZMod.natCast_zmod_val (v a - m), ← ZMod.natCast_zmod_val (v b - m), hab]
            linear_combination this
          by_contra hne'
          rcases lt_or_gt_of_ne hne' with hlt | hlt
          · exact (hv_lt a b hlt (by omega)).ne (by rw [hvab])
          · exact (hv_lt b a hlt (by omega)).ne (by rw [hvab])
        let S : Finset ℕ := Finset.Iic (e1 r - m).val ∪ Finset.Ico ((e2 r - m).val + 1) k
        have hf_maps : ∀ q ∈ Finset.range (r + 2), f q ∈ S := by
          intro q hq
          rw [Finset.mem_range] at hq
          rw [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ico]
          rcases h_all q (by omega) with h1 | h2
          · left; exact h1
          · right; exact ⟨h2, ZMod.val_lt _⟩
        have hcard := Finset.card_le_card_of_injOn f hf_maps hf_inj
        rw [Finset.card_range] at hcard
        have hScard : S.card ≤ ((e1 r - m).val + 1) + (k - ((e2 r - m).val + 1)) := by
          refine le_trans (Finset.card_union_le _ _) ?_
          rw [Nat.card_Iic, Nat.card_Ico]
        omega
      -- Now update `e1 (r + 1)` and `e2 (r + 1)` using `hv_step`
      have he1_succ : e1 (r + 1) = (stepPair r (e1 r, e2 r)).1 := rfl
      have he2_succ : e2 (r + 1) = (stepPair r (e1 r, e2 r)).2 := rfl
      by_cases hcase : v (r + 1) = e1 r + 1
      · have he1' : e1 (r + 1) = e1 r + 1 := by simp [he1_succ, stepPair, hcase]
        have he2' : e2 (r + 1) = e2 r := by simp [he2_succ, stepPair, hcase]
        have he11_val : (e1 r + 1 - m).val = (e1 r - m).val + 1 := by
          have hsum : e1 r + 1 - m = (e1 r - m) + 1 := by ring
          rw [hsum, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
        have he11_lt_L : (e1 r + 1 - m).val < (M - m).val := by
          by_contra hge
          have heq : (e1 r + 1 - m).val = (M - m).val := by omega
          have hM' : e1 r + 1 = M := by
            have : e1 r + 1 - m = M - m := by
              rw [← ZMod.natCast_zmod_val (e1 r + 1 - m), ← ZMod.natCast_zmod_val (M - m), heq]
            linear_combination this
          rw [← hcase, ← hvk] at hM'
          have hlt := hv_lt (r + 1) (k - 1) (by omega) (by omega)
          rw [hM'] at hlt; exact lt_irrefl _ hlt
        have hz_e12 : z (v (r + 2)) ≤ z (e1 r + 2) := by
          by_contra hlt; push Not at hlt
          have h12 : (e1 r + 2 - m).val ≤ (M - m).val := by
            have hsum : e1 r + 2 - m = (e1 r + 1 - m) + 1 := by ring
            rw [hsum, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
            omega
          have hz_lt : z (v (r + 1)) < z (e1 r + 2) := by
            rw [hcase]
            have hA : e1 r + 1 = m + (((e1 r + 1 - m).val : ℕ) : ZMod k) := by
              rw [ZMod.natCast_zmod_val]; ring
            have hB : e1 r + 2 = m + (((e1 r + 1 - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            rw [hA, hB]
            exact strictlyUnimodal_chain1_lt huni _ _ (Nat.lt_succ_self _) (by omega)
          obtain ⟨s, hs, hvs⟩ := hv_mem (e1 r + 2)
          have hs_gt : r + 2 < s := by
            by_contra hle
            rcases lt_or_eq_of_le (by omega : s ≤ r + 2) with hlt' | heq'
            · by_cases hs1 : s ≤ r + 1
              · have : z (v s) ≤ z (v (r + 1)) := by
                  by_cases heq1 : s = r + 1
                  · subst heq1; exact le_rfl
                  · exact (hv_lt s (r + 1) (by omega) (by omega)).le
                rw [hvs] at this; linarith
              · omega
            · subst heq'; rw [hvs] at hlt; exact lt_irrefl _ hlt
          have := hv_lt (r + 2) s hs_gt hs
          rw [hvs] at this; linarith
        have hz_e2_next : z (v (r + 2)) ≤ z (e2 r) := by
          by_contra hlt; push Not at hlt
          have hz_lt : z (v (r + 1)) < z (e2 r) := lt_of_le_of_ne ihz4 (fun heq => by
            have : v (r + 1) = e2 r := by by_contra hne'; exact hdist _ _ hne' heq
            rw [hcase] at this
            have heq_val := congrArg ZMod.val (congrArg (· - m) this)
            rw [he11_val] at heq_val
            omega)
          obtain ⟨s, hs, hvs⟩ := hv_mem (e2 r)
          have hs_gt : r + 2 < s := by
            by_contra hle
            rcases lt_or_eq_of_le (by omega : s ≤ r + 2) with hlt' | heq'
            · have : z (v s) ≤ z (v (r + 1)) := by
                by_cases heq1 : s = r + 1
                · subst heq1; exact le_rfl
                · exact (hv_lt s (r + 1) (by omega) (by omega)).le
              rw [hvs] at this; linarith
            · subst heq'; rw [hvs] at hlt; exact lt_irrefl _ hlt
          have := hv_lt (r + 2) s hs_gt hs
          rw [hvs] at this; linarith
        rw [he1', he2', he11_val]
        rw [he11_val] at he11_lt_L
        refine ⟨he11_lt_L, ih2, ih3, by omega, by rw [hcase], ?_, ?_, hz_e2_next⟩
        · have : e1 r + 1 + 1 = e1 r + 2 := by ring
          rw [this]; exact hz_e12
        · exact le_trans ihz3 (hv_lt r (r + 1) (by omega) (by omega)).le
      · have hcase2 : v (r + 1) = e2 r := hv_step.resolve_left hcase
        have he1' : e1 (r + 1) = e1 r := by simp [he1_succ, stepPair, hcase]
        have he2' : e2 (r + 1) = e2 r - 1 := by simp [he2_succ, stepPair, hcase]
        have he21_ge_L : (M - m).val ≤ (e2 r - 1 - m).val := by
          have he2_gt : (M - m).val < (e2 r - m).val := by
            by_contra hle
            have heq : (e2 r - m).val = (M - m).val := by omega
            have hM' : e2 r = M := by
              have : e2 r - m = M - m := by
                rw [← ZMod.natCast_zmod_val (e2 r - m), ← ZMod.natCast_zmod_val (M - m), heq]
              linear_combination this
            rw [← hcase2, ← hvk] at hM'
            have hlt := hv_lt (r + 1) (k - 1) (by omega) (by omega)
            rw [hM'] at hlt; exact lt_irrefl _ hlt
          have hsum : e2 r - m = (e2 r - 1 - m) + 1 := by ring
          have hval := congrArg ZMod.val hsum
          rw [ZMod.val_add, ZMod.val_one] at hval
          have hlt_k : (e2 r - 1 - m).val < k := ZMod.val_lt _
          by_cases hlt1 : (e2 r - 1 - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hlt1] at hval; omega
          · exfalso
            have : (e2 r - 1 - m).val + 1 = k := by omega
            rw [this, Nat.mod_self] at hval; omega
        have he21_val : (e2 r - 1 - m).val + 1 = (e2 r - m).val := by
          have hsum : e2 r - m = (e2 r - 1 - m) + 1 := by ring
          have hval := congrArg ZMod.val hsum
          rw [ZMod.val_add, ZMod.val_one] at hval
          have hlt_k : (e2 r - 1 - m).val < k := ZMod.val_lt _
          by_cases hlt1 : (e2 r - 1 - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hlt1] at hval; omega
          · exfalso
            have : (e2 r - 1 - m).val + 1 = k := by omega
            rw [this, Nat.mod_self] at hval; omega
        have hz_e1_next : z (v (r + 2)) ≤ z (e1 r + 1) := by
          by_contra hlt; push Not at hlt
          have hz_lt : z (v (r + 1)) < z (e1 r + 1) := lt_of_le_of_ne ihz2 (fun heq => by
            have : v (r + 1) = e1 r + 1 := by by_contra hne'; exact hdist _ _ hne' heq
            exact hcase this)
          obtain ⟨s, hs, hvs⟩ := hv_mem (e1 r + 1)
          have hs_gt : r + 2 < s := by
            by_contra hle
            rcases lt_or_eq_of_le (by omega : s ≤ r + 2) with hlt' | heq'
            · have : z (v s) ≤ z (v (r + 1)) := by
                by_cases heq1 : s = r + 1
                · subst heq1; exact le_rfl
                · exact (hv_lt s (r + 1) (by omega) (by omega)).le
              rw [hvs] at this; linarith
            · subst heq'; rw [hvs] at hlt; exact lt_irrefl _ hlt
          have := hv_lt (r + 2) s hs_gt hs
          rw [hvs] at this; linarith
        have hz_e2_next : z (v (r + 2)) ≤ z (e2 r - 1) := by
          by_contra hlt; push Not at hlt
          have hz_lt : z (v (r + 1)) < z (e2 r - 1) := by
            rw [hcase2]
            have hA : e2 r - 1 = m + ((e2 r - 1 - m).val : ZMod k) := by
              rw [ZMod.natCast_zmod_val]; ring
            have hB : e2 r = m + (((e2 r - 1 - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            conv_rhs => rw [hA]
            conv_lhs => rw [hB]
            exact strictlyUnimodal_chain2_lt huni _ _ he21_ge_L (Nat.lt_succ_self _) (by omega)
          obtain ⟨s, hs, hvs⟩ := hv_mem (e2 r - 1)
          have hs_gt : r + 2 < s := by
            by_contra hle
            rcases lt_or_eq_of_le (by omega : s ≤ r + 2) with hlt' | heq'
            · have : z (v s) ≤ z (v (r + 1)) := by
                by_cases heq1 : s = r + 1
                · subst heq1; exact le_rfl
                · exact (hv_lt s (r + 1) (by omega) (by omega)).le
              rw [hvs] at this; linarith
            · subst heq'; rw [hvs] at hlt; exact lt_irrefl _ hlt
          have := hv_lt (r + 2) s hs_gt hs
          rw [hvs] at this; linarith
        rw [he1', he2']
        refine ⟨ih1, he21_ge_L, ZMod.val_lt _, by omega, le_trans ihz1 (hv_lt r (r + 1) (by omega) (by omega)).le,
          hz_e1_next, ?_, hz_e2_next⟩
        · have : e2 r - 1 + 1 = e2 r := by ring
          rw [this, hcase2]
  -- Define `a_of r` for `1 ≤ r ≤ k - 2`
  let a_of : ℕ → ZMod k := fun r => if v r = e1 r then e2 r else e1 r
  -- For `1 ≤ r ≤ k - 2`, either `v r = e1 r` (Chain 1) or `v r = e2 r + 1` (Chain 2)
  have hv_pos : ∀ r : ℕ, 1 ≤ r → r ≤ k - 2 → v r = e1 r ∨ v r = e2 r + 1 := by
    intro r hr1 hr2
    have hstep : v r = e1 (r - 1) + 1 ∨ v r = e2 (r - 1) := by
      obtain ⟨_, _, _, _, _, _, hz3', _⟩ := hinv r hr2
      have he1_r : e1 r = (stepPair (r - 1) (e1 (r - 1), e2 (r - 1))).1 := by
        have hr' : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hr']
      have he2_r : e2 r = (stepPair (r - 1) (e1 (r - 1), e2 (r - 1))).2 := by
        have hr' : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hr']
      by_cases hcase : v ((r - 1) + 1) = e1 (r - 1) + 1
      · left; have hr' : (r - 1) + 1 = r := by omega
        rw [hr'] at hcase; exact hcase
      · right; have hr' : (r - 1) + 1 = r := by omega
        rw [hr'] at hcase
        have hvr_eq : v r = e2 (r - 1) := by
          have he2_eq : e2 r = e2 (r - 1) - 1 := by rw [he2_r]; simp [stepPair, hr', hcase]
          have hinv' := hinv (r - 1) (by omega)
          have hle1 : z (v r) ≤ z (e2 (r - 1)) := by rw [← hr']; exact hinv'.2.2.2.2.2.2.2
          have hle2 : z (e2 (r - 1)) ≤ z (v r) := by
            have heq' : e2 r + 1 = e2 (r - 1) := by rw [he2_eq]; ring
            rw [← heq']; exact hz3'
          have hz_eq : z (v r) = z (e2 (r - 1)) := le_antisymm hle1 hle2
          by_contra hne; exact hdist _ _ hne hz_eq
        exact hvr_eq
    rcases hstep with h1 | h2
    · left
      have he1_r : e1 r = (stepPair (r - 1) (e1 (r - 1), e2 (r - 1))).1 := by
        have hr' : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hr']
      have hr' : (r - 1) + 1 = r := by omega
      rw [he1_r]; simp [stepPair, hr', h1]
    · right
      have he2_r : e2 r = (stepPair (r - 1) (e1 (r - 1), e2 (r - 1))).2 := by
        have hr' : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hr']
      have hr' : (r - 1) + 1 = r := by omega
      have hne : v ((r - 1) + 1) ≠ e1 (r - 1) + 1 := by
        intro heq; rw [hr'] at heq; rw [heq] at h2
        obtain ⟨ih1, ih2, ih3, _, _, _, _, _⟩ := hinv (r - 1) (by omega)
        have hsum : e1 (r - 1) + 1 - m = (e1 (r - 1) - m) + 1 := by ring
        have hval := congrArg ZMod.val (congrArg (· - m) h2)
        rw [hsum, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)] at hval
        omega
      rw [he2_r]; simp [stepPair, hne]; exact h2
  -- If `∃ r ∈ [1, k-2]` with `far (a_of r) = v r`, we win!
  by_cases hwin : ∃ r : ℕ, 1 ≤ r ∧ r ≤ k - 2 ∧ far (a_of r) = v r
  · obtain ⟨r, hr1, hr2, hfar_eq⟩ := hwin
    refine ⟨a_of r, v r, ?_, ?_⟩
    · intro i hiv
      rw [← hfar_eq]
      exact (hfar (a_of r)).2.2 i (fun h => hiv (by rw [← hfar_eq]; exact h))
    · obtain ⟨h_e1L, h_Le2, h_e2k, _, hz1, hz2, hz3, hz4⟩ := hinv r hr2
      rcases hv_pos r hr1 hr2 with h1 | h2
      · have ha : a_of r = e2 r := by simp [a_of, h1]
        rw [ha]
        have hc1 : 0 < (v r - m).val := by
          by_contra h0
          have hz : (v r - m).val = 0 := by omega
          have hvm : v r = m := by
            have : v r - m = 0 := by rw [← ZMod.natCast_zmod_val (v r - m), hz]; simp
            exact sub_eq_zero.mp this
          have hlt0 := hv_lt 0 r (by omega) (by omega)
          rw [hv0, hvm] at hlt0; exact lt_irrefl _ hlt0
        have hc2 : (v r - m).val < (M - m).val := by rw [h1]; exact h_e1L
        have hz_lo : z (e2 r + 1) < z (v r) := lt_of_le_of_ne hz3 (fun h => by
          have heq : e2 r + 1 = v r := by by_contra hne; exact hdist _ _ hne h
          rw [h1] at heq
          have := hfar (e2 r)
          have he2_val : (e2 r + 1 - m).val = (e2 r - m).val + 1 ∨ (e2 r - m).val + 1 = k := by
            have hs : e2 r + 1 - m = (e2 r - m) + 1 := by ring
            rw [hs, ZMod.val_add, ZMod.val_one]
            by_cases hlt : (e2 r - m).val + 1 < k
            · left; exact Nat.mod_eq_of_lt hlt
            · right; omega
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          rcases he2_val with h | h
          · rw [h] at heq_v; omega
          · have he2m : e2 r + 1 = m := by
              have hz_e : (e2 r - m).val + 1 = k := h
              have he2m' : e2 r + 1 - m = 0 := by
                have hs : e2 r + 1 - m = (e2 r - m) + 1 := by ring
                rw [hs, ← ZMod.natCast_zmod_val (e2 r - m), show ((e2 r - m).val : ZMod k) + 1 = ((k : ℕ) : ZMod k) by rw [← Nat.cast_one, ← Nat.cast_add, hz_e]]
                simp
              exact sub_eq_zero.mp he2m'
            rw [he2m] at heq; exact absurd heq.symm (by
              intro h'; have hlt0 := hv_lt 0 r (by omega) (by omega); rw [hv0, h1, h'] at hlt0; exact lt_irrefl _ hlt0))
        have hz_hi : z (v r) < z (e2 r) := lt_of_lt_of_le (hv_lt r (r + 1) (by omega) (by omega)) hz4
        exact depthArcs_of_chain1 huni hc1 hc2 h_Le2 h_e2k hz_lo hz_hi
      · have ha : a_of r = e1 r := by
          have hne : v r ≠ e1 r := by
            rw [h2]
            intro heq
            have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
            have hs : e2 r + 1 - m = (e2 r - m) + 1 := by ring
            rw [hs, ZMod.val_add, ZMod.val_one] at heq_v
            by_cases hlt : (e2 r - m).val + 1 < k
            · rw [Nat.mod_eq_of_lt hlt] at heq_v; omega
            · have hz_e : (e2 r - m).val + 1 = k := by omega
              rw [hz_e, Nat.mod_self] at heq_v
              have he1m' : (e1 r - m).val = 0 := heq_v.symm
              have he1m : e1 r = m := by
                have : e1 r - m = 0 := by rw [← ZMod.natCast_zmod_val (e1 r - m), he1m']; simp
                exact sub_eq_zero.mp this
              rw [he1m] at heq
              have he2m : e2 r + 1 = m := heq
              rw [← h2] at he2m
              have hlt' := hv_lt 0 r (by omega) (by omega)
              rw [hv0, he2m] at hlt'; exact lt_irrefl _ hlt'
          simp [a_of, hne]
        rw [ha]
        have hc1 : (M - m).val < (v r - m).val := by
          rw [h2]
          have hs : e2 r + 1 - m = (e2 r - m) + 1 := by ring
          rw [hs, ZMod.val_add, ZMod.val_one]
          by_cases hlt : (e2 r - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · exfalso
            have hz_e : (e2 r - m).val + 1 = k := by omega
            have he2m : e2 r + 1 = m := by
              have he2m' : e2 r + 1 - m = 0 := by
                rw [hs, ← ZMod.natCast_zmod_val (e2 r - m), show ((e2 r - m).val : ZMod k) + 1 = ((k : ℕ) : ZMod k) by rw [← Nat.cast_one, ← Nat.cast_add, hz_e]]; simp
              exact sub_eq_zero.mp he2m'
            rw [← h2] at he2m
            have hlt' := hv_lt 0 r (by omega) (by omega)
            rw [hv0, he2m] at hlt'; exact lt_irrefl _ hlt'
        have hz_lo : z (e1 r) < z (v r) := lt_of_le_of_ne hz1 (fun h => by
          have heq : e1 r = v r := by by_contra hne; exact hdist _ _ hne h
          have h12 : (M - m).val < (e1 r - m).val := by rw [heq]; exact hc1
          omega)
        have hz_hi : z (v r) < z (e1 r + 1) := lt_of_lt_of_le (hv_lt r (r + 1) (by omega) (by omega)) hz2
        exact depthArcs_of_chain2 huni hc1 (ZMod.val_lt _) h_e1L hz_lo hz_hi
  · -- Contradiction: no `r ∈ [1, k-2]` has `far (a_of r) = v r`
    exfalso
    push Not at hwin
    -- Show `z (v 1) < z (far (a_of 1))`
    have hstart : z (v 1) < z (far (a_of 1)) := by
      have hne1 : far (a_of 1) ≠ v 1 := hwin 1 (by omega) (by omega)
      have hne0 : far (a_of 1) ≠ v 0 := by
        rw [hv0]
        rcases hv_pos 1 (by omega) (by omega) with h1 | h2
        · -- `v 1 = e1 1`, so `a_of 1 = e2 1`, and `v 1 = m + 1`?
          have ha : a_of 1 = e2 1 := by simp [a_of, h1]
          rw [ha]
          have : e2 1 + 1 = m := by
            obtain ⟨_, _, _, h4, _, _, _, _⟩ := hinv 1 (by omega)
            have : (e1 1 - m).val = 1 := by
              -- `e1 1 = v 1` and `e1 0 = m`, `v 0 = m`
              have he1_1 : e1 1 = m + 1 := by
                have : e1 1 = (stepPair 0 (m, m - 1)).1 := rfl
                by_cases hc : v 1 = m + 1
                · simp [this, stepPair, hc]
                · exfalso
                  have h1' : e1 1 = m := by simp [this, stepPair, hc]
                  rw [h1'] at h1
                  have := hv_lt 0 1 (by omega) (by omega)
                  rw [hv0, h1] at this; exact lt_irrefl _ this
              rw [he1_1]; ring_nf; rw [ZMod.val_one]
            have : (e2 1 - m).val = k - 1 := by omega
            have : e2 1 - m = -1 := by
              rw [← ZMod.natCast_zmod_val (e2 1 - m), this, Minimality.zmod_natCast_pred (by omega)]
            linear_combination this
          intro hfm
          rw [← this] at hfm
          exact (hfar (e2 1)).2.1 hfm
        · have ha : a_of 1 = e1 1 := by
            have hne : v 1 ≠ e1 1 := by
              intro heq; rw [heq] at h2
              obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv 1 (by omega)
              have heq_v := congrArg ZMod.val (congrArg (· - m) h2)
              have hs : e2 1 + 1 - m = (e2 1 - m) + 1 := by ring
              rw [hs, ZMod.val_add, ZMod.val_one] at heq_v
              by_cases hlt : (e2 1 - m).val + 1 < k
              · rw [Nat.mod_eq_of_lt hlt] at heq_v; omega
              · have hz_e : (e2 1 - m).val + 1 = k := by omega
                rw [hz_e, Nat.mod_self] at heq_v
                have he1m' : (e1 1 - m).val = 0 := heq_v
                have he1m : e1 1 = m := by
                  have : e1 1 - m = 0 := by rw [← ZMod.natCast_zmod_val (e1 1 - m), he1m']; simp
                  exact sub_eq_zero.mp this
                rw [he1m] at heq
                have hlt1 := hv_lt 0 1 (by omega) (by omega)
                rw [hv0, heq] at hlt1; exact lt_irrefl _ hlt1
            simp [a_of, hne]
          rw [ha]
          have he1m : e1 1 = m := by
            have : e1 1 = (stepPair 0 (m, m - 1)).1 := rfl
            by_cases hc : v 1 = m + 1
            · exfalso
              have he2_1' : e2 1 = m - 1 := by
                have h2d : e2 1 = (stepPair 0 (m, m - 1)).2 := rfl
                rw [h2d]; simp [stepPair, hc]
              rw [he2_1'] at h2; ring_nf at h2
              have hlt1 := hv_lt 0 1 (by omega) (by omega)
              rw [hv0, ← h2] at hlt1; exact lt_irrefl _ hlt1
            · rw [this]; simp [stepPair, hc]
          rw [he1m]
          exact (hfar m).1
      obtain ⟨s, hs, hvs⟩ := hv_mem (far (a_of 1))
      have hs0 : s ≠ 0 := by intro h0; subst h0; exact hne0 hvs.symm
      have hs1 : s ≠ 1 := by intro h1; subst h1; exact hne1 hvs.symm
      rw [← hvs]
      exact hv_lt 1 s (by omega) hs
    -- Show `z (far (a_of (k - 2))) < z (v (k - 2))`
    have hend : z (far (a_of (k - 2))) < z (v (k - 2)) := by
      have hnek2 : far (a_of (k - 2)) ≠ v (k - 2) := hwin (k - 2) (by omega) (by omega)
      have hnek1 : far (a_of (k - 2)) ≠ v (k - 1) := by
        rw [hvk]
        obtain ⟨h_e1L, h_Le2, h_e2k, h4, _, _, _, _⟩ := hinv (k - 2) (by omega)
        -- `(e1 (k-2) - m).val + (k - (e2 (k-2) - m).val) = k - 1`, with `(e1 - m).val < L ≤ (e2 - m).val`
        -- so `(e1 (k-2) - m).val = L - 1` and `(e2 (k-2) - m).val = L`, meaning `e1 (k-2) + 1 = M` and `e2 (k-2) = M`!
        have he1M : e1 (k - 2) + 1 = M := by
          have hz_e : (e1 (k - 2) - m).val = (M - m).val - 1 := by omega
          have hsum : e1 (k - 2) + 1 - m = (e1 (k - 2) - m) + 1 := by ring
          have hLp : 0 < (M - m).val := by omega
          have he1M' : ((e1 (k - 2) - m).val : ZMod k) + 1 = ((M - m).val : ZMod k) := by
            rw [hz_e]; norm_cast; rw [Nat.sub_add_cancel hLp]
          have : e1 (k - 2) + 1 - m = M - m := by
            rw [hsum]
            calc (e1 (k - 2) - m) + 1
                = ((e1 (k - 2) - m).val : ZMod k) + 1 := by rw [ZMod.natCast_zmod_val]
              _ = ((M - m).val : ZMod k) := he1M'
              _ = M - m := ZMod.natCast_zmod_val _
          linear_combination this
        have he2M : e2 (k - 2) = M := by
          have hz_e : (e2 (k - 2) - m).val = (M - m).val := by omega
          have : e2 (k - 2) - m = M - m := by
            rw [← ZMod.natCast_zmod_val (e2 (k - 2) - m), hz_e, ZMod.natCast_zmod_val]
          linear_combination this
        by_cases hcase : v (k - 2) = e1 (k - 2)
        · have ha : a_of (k - 2) = e2 (k - 2) := by simp [a_of, hcase]
          rw [ha, he2M]
          exact (hfar M).1
        · have ha : a_of (k - 2) = e1 (k - 2) := by simp [a_of, hcase]
          rw [ha, ← he1M]
          exact (hfar (e1 (k - 2))).2.1
      obtain ⟨s, hs, hvs⟩ := hv_mem (far (a_of (k - 2)))
      have hsk1 : s ≠ k - 1 := by intro h; subst h; exact hnek1 hvs.symm
      have hsk2 : s ≠ k - 2 := by intro h; subst h; exact hnek2 hvs.symm
      rw [← hvs]
      exact hv_lt s (k - 2) (by omega) (by omega)
    -- Discrete IVT: find `r ∈ [1, k - 3]` where `z (v r) < z (far (a_of r))` and `z (far (a_of (r + 1))) < z (v (r + 1))`
    have hcross : ∃ r : ℕ, 1 ≤ r ∧ r ≤ k - 3 ∧
        z (v r) < z (far (a_of r)) ∧ z (far (a_of (r + 1))) < z (v (r + 1)) := by
      have hall : ∀ n : ℕ, 1 ≤ n → n ≤ k - 2 →
          z (v n) < z (far (a_of n)) ∨
            ∃ r : ℕ, 1 ≤ r ∧ r < n ∧ z (v r) < z (far (a_of r)) ∧ z (far (a_of (r + 1))) < z (v (r + 1)) := by
        intro n hn1 hn2
        induction n with
        | zero => omega
        | succ n ih =>
          by_cases hn0 : n = 0
          · subst hn0; left; exact hstart
          · rcases ih (by omega) (by omega) with hpos | hex
            · by_cases hpos' : z (v (n + 1)) < z (far (a_of (n + 1)))
              · left; exact hpos'
              · right
                have hne' : far (a_of (n + 1)) ≠ v (n + 1) := hwin (n + 1) (by omega) (by omega)
                have hlt' : z (far (a_of (n + 1))) < z (v (n + 1)) :=
                  lt_of_le_of_ne (not_lt.mp hpos') (fun h => hne' (by
                    by_contra hne''; exact hdist _ _ hne'' h))
                exact ⟨n, by omega, by omega, hpos, hlt'⟩
            · right; obtain ⟨r, hr1, hr2, h1, h2⟩ := hex; exact ⟨r, hr1, by omega, h1, h2⟩
      rcases hall (k - 2) (by omega) le_rfl with hpos | ⟨r, hr1, hr2, h1, h2⟩
      · exfalso; linarith
      · exact ⟨r, hr1, by omega, h1, h2⟩
    obtain ⟨r, hr1, hr2, hgt, hlt⟩ := hcross
    -- Now analyze the 4 cases for `(v r, v (r + 1))`
    have hstep_r1 : v (r + 1) = e1 r + 1 ∨ v (r + 1) = e2 r := by
      have he1_r1 : e1 (r + 1) = (stepPair r (e1 r, e2 r)).1 := rfl
      have he2_r1 : e2 (r + 1) = (stepPair r (e1 r, e2 r)).2 := rfl
      rcases hv_pos (r + 1) (by omega) (by omega) with h1 | h2
      · left
        by_cases hc : v (r + 1) = e1 r + 1
        · exact hc
        · exfalso
          have : e1 (r + 1) = e1 r := by rw [he1_r1]; simp [stepPair, hc]
          rw [this] at h1
          have hinv_r := hinv r (by omega)
          have hlt_r := hv_lt r (r + 1) (by omega) (by omega)
          rw [h1] at hlt_r
          linarith [hinv_r.2.2.2.2.1, hlt_r]
      · right
        by_cases hc : v (r + 1) = e1 r + 1
        · exfalso
          have : e2 (r + 1) = e2 r := by simp [he2_r1, stepPair, hc]
          rw [this] at h2
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          rw [hc] at h2
          have heq_v := congrArg ZMod.val (congrArg (· - m) h2)
          have hs1 : e1 r + 1 - m = (e1 r - m) + 1 := by ring
          have hs2 : e2 r + 1 - m = (e2 r - m) + 1 := by ring
          rw [hs1, hs2, ZMod.val_add, ZMod.val_one, ZMod.val_add, ZMod.val_one,
            Nat.mod_eq_of_lt (by omega)] at heq_v
          by_cases hlt' : (e2 r - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hlt'] at heq_v; omega
          · have : (e2 r - m).val + 1 = k := by omega
            rw [this, Nat.mod_self] at heq_v; omega
        · have : e2 (r + 1) = e2 r - 1 := by rw [he2_r1]; simp [stepPair, hc]
          rw [this] at h2; ring_nf at h2; rw [add_comm 1 r] at h2; exact h2
    rcases hv_pos r hr1 (by omega) with hr_c1 | hr_c2 <;> rcases hstep_r1 with hr1_c1 | hr1_c2
    · -- Case 1: both `v r` and `v (r + 1)` on Chain 1 -> `a_of r = e2 r = a_of (r + 1)`
      have ha1 : a_of r = e2 r := by simp [a_of, hr_c1]
      have he1_r1 : e1 (r + 1) = e1 r + 1 := by
        have : e1 (r + 1) = (stepPair r (e1 r, e2 r)).1 := rfl
        simp [this, stepPair, hr1_c1]
      have he2_r1 : e2 (r + 1) = e2 r := by
        have : e2 (r + 1) = (stepPair r (e1 r, e2 r)).2 := rfl
        simp [this, stepPair, hr1_c1]
      have ha2 : a_of (r + 1) = e2 r := by
        have : v (r + 1) = e1 (r + 1) := by rw [hr1_c1, he1_r1]
        simp [a_of, this, he2_r1]
      rw [ha1] at hgt; rw [ha2] at hlt
      obtain ⟨s, hs, hvs⟩ := hv_mem (far (e2 r))
      have h1 : r < s := by
        by_contra hle
        have : z (v s) ≤ z (v r) := by
          by_cases heq : s = r
          · subst heq; exact le_rfl
          · exact (hv_lt s r (by omega) (by omega)).le
        rw [hvs] at this; linarith
      have h2 : s < r + 1 := by
        by_contra hge
        have : z (v (r + 1)) ≤ z (v s) := by
          by_cases heq : s = r + 1
          · subst heq; exact le_rfl
          · exact (hv_lt (r + 1) s (by omega) hs).le
        rw [hvs] at this; linarith
      omega
    · -- Case 3: `v r` on Chain 1 (`e1 r = v r`), `v (r + 1)` on Chain 2 (`e2 r = v (r + 1)`)
      have ha1 : a_of r = e2 r := by simp [a_of, hr_c1]
      have he1_r1 : e1 (r + 1) = e1 r := by
        have : e1 (r + 1) = (stepPair r (e1 r, e2 r)).1 := rfl
        have hne : v (r + 1) ≠ e1 r + 1 := by
          rw [hr1_c2]
          intro heq
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          have hs : e1 r + 1 - m = (e1 r - m) + 1 := by ring
          rw [hs, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)] at heq_v
          omega
        simp [this, stepPair, hne]
      have ha2 : a_of (r + 1) = e1 r := by
        have hne : v (r + 1) ≠ e1 (r + 1) := by
          rw [hr1_c2, he1_r1]
          intro heq
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          omega
        rw [he1_r1] at hne
        dsimp only [a_of]; rw [he1_r1]; split_ifs with h_eq
        · exact absurd h_eq hne
        · rfl
      rw [ha1] at hgt; rw [ha2] at hlt
      set c2 := far (e2 r)
      have hc2_spec := hfar (e2 r)
      have hc2_arc : (e2 r + 1 - c2).val ≤ (e1 r - c2).val := by
        obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
        have hc2_range : (e1 r - m).val < (c2 - m).val ∧ (c2 - m).val < (e2 r - m).val := by
          obtain ⟨s, hs, hvs⟩ := hv_mem c2
          have hs_gt : r + 1 ≤ s := by
            by_contra hlt'
            by_cases heqs : s = r
            · subst heqs; rw [← hvs] at hgt; exact lt_irrefl _ hgt
            · have := (hv_lt s r (by omega) (by omega)).le
              rw [hvs] at this; linarith
          have hs_gt' : r + 1 < s := by
            by_cases heq : s = r + 1
            · subst heq; rw [hr1_c2] at hvs; exact absurd hvs.symm hc2_spec.1
            · omega
          have hzs : z (v (r + 1)) < z c2 := by rw [← hvs]; exact hv_lt (r + 1) s hs_gt' hs
          rw [hr1_c2] at hzs
          by_contra hnot
          have hle_or : (c2 - m).val ≤ (e1 r - m).val ∨ (e2 r - m).val ≤ (c2 - m).val := by omega
          rcases hle_or with h1 | h2
          · have hc2_eq : c2 = m + ((c2 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he1_eq : e1 r = m + ((e1 r - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z c2 ≤ z (e1 r) := by
              by_cases heq : (c2 - m).val = (e1 r - m).val
              · rw [hc2_eq, he1_eq, heq]
              · rw [hc2_eq, he1_eq]
                exact (strictlyUnimodal_chain1_lt huni _ _ (by omega) (by omega)).le
            rw [← hr_c1] at hle_z; linarith
          · have hc2_eq : c2 = m + ((c2 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he2_eq : e2 r = m + ((e2 r - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z c2 ≤ z (e2 r) := by
              by_cases heq : (c2 - m).val = (e2 r - m).val
              · rw [hc2_eq, he2_eq, heq]
              · rw [hc2_eq, he2_eq]
                exact (strictlyUnimodal_chain2_lt huni _ _ h_Le2 (by omega) (ZMod.val_lt _).le).le
            linarith
        -- Now `(e2 r + 1 - c2).val ≤ (e1 r - c2).val` follows from `(e1 r - m).val < (c2 - m).val < (e2 r - m).val`!
        have h1 : (e1 r - c2).val = k - (c2 - m).val + (e1 r - m).val := by
          have hsum : (e1 r - c2) + (c2 - m) = e1 r - m := by ring
          have hval := congrArg ZMod.val hsum
          rw [ZMod.val_add] at hval
          have hlt1 : (e1 r - c2).val < k := ZMod.val_lt _
          have hlt2 : (c2 - m).val < k := ZMod.val_lt _
          by_cases hs : (e1 r - c2).val + (c2 - m).val < k
          · rw [Nat.mod_eq_of_lt hs] at hval; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
        have h2 : (e2 r + 1 - c2).val = k - (c2 - m).val + (e2 r - m).val + 1 - k := by
          have hsum : (e2 r + 1 - c2) + (c2 - m) = (e2 r - m) + 1 := by ring
          have hval := congrArg ZMod.val hsum
          rw [ZMod.val_add, ZMod.val_add, ZMod.val_one] at hval
          have hlt1 : (e2 r + 1 - c2).val < k := ZMod.val_lt _
          have hlt2 : (c2 - m).val < k := ZMod.val_lt _
          by_cases hs1 : (e2 r + 1 - c2).val + (c2 - m).val < k <;>
            by_cases hs2 : (e2 r - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt hs2] at hval; omega
          · rw [Nat.mod_eq_of_lt hs1, show (e2 r - m).val + 1 = k by omega, Nat.mod_self] at hval; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hs2] at hval; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
              show (e2 r - m).val + 1 = k by omega, Nat.mod_self] at hval; omega
        omega
      have harc2 := (harcs (e2 r)).2 (e1 r - c2).val hc2_arc (ZMod.val_lt _)
      have he1_rw1 : c2 + ((e1 r - c2).val : ZMod k) = e1 r := by rw [ZMod.natCast_zmod_val]; ring
      have he1_rw2 : c2 + (((e1 r - c2).val + 1 : ℕ) : ZMod k) = e1 r + 1 := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      rw [he1_rw1, he1_rw2] at harc2
      have hdet_pos1 : 0 < det3 (X (e2 r + 1) - X (e2 r)) (X (e1 r + 1) - X (e1 r)) w := by
        rw [det3_swap_mid, det3_sub_right]; linarith
      -- Similarly for `c1 := far (e1 r)`: `z c1 < z (v (r + 1))` and `c1 ≠ v r = e1 r`, `c1 ≠ e1 r + 1`,
      -- so `c1` is in `[e2 r + 1 .. e1 r - 1]`, meaning `(e1 r + 1 - c1).val ≤ (e2 r - c1).val`!
      set c1 := far (e1 r)
      have hc1_spec := hfar (e1 r)
      have hc1_arc : (e1 r + 1 - c1).val ≤ (e2 r - c1).val := by
        obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
        have hL_lt : (M - m).val < k := ZMod.val_lt _
        have hc1_range : (c1 - m).val < (e1 r - m).val ∨ (e2 r - m).val < (c1 - m).val := by
          obtain ⟨s, hs, hvs⟩ := hv_mem c1
          have hs_lt : s < r := by
            by_contra hge
            have hne' : s ≠ r := by intro heq; subst heq; rw [hr_c1] at hvs; exact hc1_spec.1 hvs.symm
            have hlt_r1 : s < r + 1 := by
              by_contra hge'; have hle'' : z (v (r + 1)) ≤ z (v s) := by
                by_cases heq : s = r + 1
                · subst heq; exact le_rfl
                · exact (hv_lt (r + 1) s (by omega) hs).le
              rw [hvs] at hle''; linarith
            omega
          have hzs : z c1 < z (v r) := by rw [← hvs]; exact hv_lt s r hs_lt (by omega)
          rw [hr_c1] at hzs
          by_contra hnot
          have hmid : (e1 r - m).val ≤ (c1 - m).val ∧ (c1 - m).val ≤ (e2 r - m).val := by omega
          by_cases hL : (c1 - m).val ≤ (M - m).val
          · have hc1_eq : c1 = m + ((c1 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he1_eq : e1 r = m + ((e1 r - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z (e1 r) ≤ z c1 := by
              by_cases heq : (e1 r - m).val = (c1 - m).val
              · rw [hc1_eq, he1_eq, heq]
              · rw [hc1_eq, he1_eq]
                exact (strictlyUnimodal_chain1_lt huni _ _ (by omega) hL).le
            linarith
          · have hc1_eq : c1 = m + ((c1 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he2_eq : e2 r = m + ((e2 r - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have hc1_L : (M - m).val ≤ (c1 - m).val := by omega
            have hle_z : z (e2 r) ≤ z c1 := by
              by_cases heq : (c1 - m).val = (e2 r - m).val
              · rw [hc1_eq, he2_eq, heq]
              · rw [hc1_eq, he2_eq]
                exact (strictlyUnimodal_chain2_lt huni _ _ hc1_L (by omega) (ZMod.val_lt _).le).le
            have hlt_r := hv_lt r (r + 1) (by omega) (by omega)
            have hinv_r := hinv r (by omega)
            rw [hr_c1] at hlt_r; linarith [hinv_r.2.2.2.2.2.2.2]
        rcases hc1_range with hl | hr
        · have h1 : (e1 r + 1 - c1).val = (e1 r - m).val + 1 - (c1 - m).val := by
            have hsum : (e1 r + 1 - c1) + (c1 - m) = (e1 r - m) + 1 := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add, ZMod.val_add, ZMod.val_one] at hval
            rw [Nat.mod_eq_of_lt (by omega : (e1 r - m).val + 1 < k)] at hval
            have hlt1 : (e1 r + 1 - c1).val < k := ZMod.val_lt _
            have hlt2 : (c1 - m).val < k := ZMod.val_lt _
            by_cases hs : (e1 r + 1 - c1).val + (c1 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          have h2 : (e2 r - c1).val = (e2 r - m).val - (c1 - m).val := by
            have hsum : (e2 r - c1) + (c1 - m) = e2 r - m := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add] at hval
            have hlt1 : (e2 r - c1).val < k := ZMod.val_lt _
            have hlt2 : (c1 - m).val < k := ZMod.val_lt _
            by_cases hs : (e2 r - c1).val + (c1 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          omega
        · have h1 : (e1 r + 1 - c1).val = (e1 r - m).val + 1 + k - (c1 - m).val := by
            have hsum : (e1 r + 1 - c1) + (c1 - m) = (e1 r - m) + 1 := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add, ZMod.val_add, ZMod.val_one] at hval
            rw [Nat.mod_eq_of_lt (by omega : (e1 r - m).val + 1 < k)] at hval
            have hlt1 : (e1 r + 1 - c1).val < k := ZMod.val_lt _
            have hlt2 : (c1 - m).val < k := ZMod.val_lt _
            by_cases hs : (e1 r + 1 - c1).val + (c1 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          have h2 : (e2 r - c1).val = (e2 r - m).val + k - (c1 - m).val := by
            have hsum : (e2 r - c1) + (c1 - m) = e2 r - m := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add] at hval
            have hlt1 : (e2 r - c1).val < k := ZMod.val_lt _
            have hlt2 : (c1 - m).val < k := ZMod.val_lt _
            by_cases hs : (e2 r - c1).val + (c1 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          omega
      have harc1 := (harcs (e1 r)).2 (e2 r - c1).val hc1_arc (ZMod.val_lt _)
      have he2_rw1 : c1 + ((e2 r - c1).val : ZMod k) = e2 r := by rw [ZMod.natCast_zmod_val]; ring
      have he2_rw2 : c1 + (((e2 r - c1).val + 1 : ℕ) : ZMod k) = e2 r + 1 := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      rw [he2_rw1, he2_rw2] at harc1
      have hdet_pos2 : 0 < det3 (X (e1 r + 1) - X (e1 r)) (X (e2 r + 1) - X (e2 r)) w := by
        rw [det3_swap_mid, det3_sub_right]; linarith
      have hskew : det3 (X (e1 r + 1) - X (e1 r)) (X (e2 r + 1) - X (e2 r)) w =
          -det3 (X (e2 r + 1) - X (e2 r)) (X (e1 r + 1) - X (e1 r)) w := by
        simp only [det3]; ring
      linarith
    · -- Case 4: `v r` on Chain 2 (`e2 r + 1 = v r`), `v (r + 1)` on Chain 1 (`e1 r + 1 = v (r + 1)`)
      have ha1 : a_of r = e1 r := by
        have hne : v r ≠ e1 r := by
          rw [hr_c2]
          intro heq
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          have hs : e2 r + 1 - m = (e2 r - m) + 1 := by ring
          rw [hs, ZMod.val_add, ZMod.val_one] at heq_v
          by_cases hlt' : (e2 r - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hlt'] at heq_v; omega
          · have hz_e : (e2 r - m).val + 1 = k := by omega
            rw [hz_e, Nat.mod_self] at heq_v
            have he1m' : (e1 r - m).val = 0 := heq_v.symm
            have he1m : e1 r = m := by
              have : e1 r - m = 0 := by rw [← ZMod.natCast_zmod_val (e1 r - m), he1m']; simp
              exact sub_eq_zero.mp this
            rw [he1m] at heq
            have hlt0 := hv_lt 0 r (by omega) (by omega)
            rw [hv0, hr_c2, heq] at hlt0; exact lt_irrefl _ hlt0
        simp [a_of, hne]
      have he1_r1 : e1 (r + 1) = e1 r + 1 := by
        have : e1 (r + 1) = (stepPair r (e1 r, e2 r)).1 := rfl
        simp [this, stepPair, hr1_c1]
      have he2_r1 : e2 (r + 1) = e2 r := by
        have : e2 (r + 1) = (stepPair r (e1 r, e2 r)).2 := rfl
        simp [this, stepPair, hr1_c1]
      have ha2 : a_of (r + 1) = e2 r := by
        have : v (r + 1) = e1 (r + 1) := by rw [hr1_c1, he1_r1]
        simp [a_of, this, he2_r1]
      rw [ha1] at hgt; rw [ha2] at hlt
      -- `c1 := far (e1 r)` has `z c1 > z (v r)` and `c1 ≠ e1 r`, `c1 ≠ e1 r + 1 = v (r + 1)`:
      -- so `c1` is in `[e1 r + 2 .. e2 r]`, meaning `(e2 r - c1).val < (e1 r - c1).val`!
      set c1 := far (e1 r)
      have hc1_spec := hfar (e1 r)
      have hc1_arc : (e2 r - c1).val < (e1 r - c1).val := by
        obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
        have hL_lt : (M - m).val < k := ZMod.val_lt _
        have hc1_range : (e1 r - m).val + 1 < (c1 - m).val ∧ (c1 - m).val ≤ (e2 r - m).val := by
          obtain ⟨s, hs, hvs⟩ := hv_mem c1
          have hs_gt : r + 1 < s := by
            by_contra hle
            have hle' : z (v s) ≤ z (v r) := by
              by_cases heq : s = r
              · exfalso; rw [heq] at hvs; rw [← hvs] at hgt; exact lt_irrefl _ hgt
              · by_cases heq1 : s = r + 1
                · subst heq1; rw [hr1_c1] at hvs; exact absurd hvs.symm hc1_spec.2.1
                · exact (hv_lt s r (by omega) (by omega)).le
            rw [hvs] at hle'; linarith
          have hzs : z (v (r + 1)) < z c1 := by rw [← hvs]; exact hv_lt (r + 1) s hs_gt hs
          rw [hr1_c1] at hzs
          have he11_val : (e1 r + 1 - m).val = (e1 r - m).val + 1 := by
            have hs' : e1 r + 1 - m = (e1 r - m) + 1 := by ring
            rw [hs', ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
          by_contra hnot
          have hle_or : (c1 - m).val ≤ (e1 r - m).val + 1 ∨ (e2 r - m).val < (c1 - m).val := by omega
          rcases hle_or with h1 | h2
          · have hc1_eq : c1 = m + ((c1 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he11_eq : e1 r + 1 = m + (((e1 r - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z c1 ≤ z (e1 r + 1) := by
              by_cases heq : (c1 - m).val = (e1 r - m).val + 1
              · rw [hc1_eq, he11_eq, heq]
              · rw [hc1_eq, he11_eq]
                exact (strictlyUnimodal_chain1_lt huni _ _ (by omega) (by omega)).le
            linarith
          · have hc1_eq : c1 = m + ((c1 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he21_eq : e2 r + 1 = m + (((e2 r - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z c1 ≤ z (e2 r + 1) := by
              by_cases heq : (c1 - m).val = (e2 r - m).val + 1
              · rw [hc1_eq, he21_eq, heq]
              · rw [hc1_eq, he21_eq]
                exact (strictlyUnimodal_chain2_lt huni _ _ (by omega) (by omega) (ZMod.val_lt _).le).le
            rw [← hr_c2] at hle_z; linarith
        have h1 : (e2 r - c1).val = (e2 r - m).val - (c1 - m).val := by
          have hsum : (e2 r - c1) + (c1 - m) = e2 r - m := by ring
          have hval := congrArg ZMod.val hsum
          rw [ZMod.val_add] at hval
          have hlt1 : (e2 r - c1).val < k := ZMod.val_lt _
          have hlt2 : (c1 - m).val < k := ZMod.val_lt _
          by_cases hs : (e2 r - c1).val + (c1 - m).val < k
          · rw [Nat.mod_eq_of_lt hs] at hval; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
        have h2 : (e1 r - c1).val = k - (c1 - m).val + (e1 r - m).val := by
          have hsum : (e1 r - c1) + (c1 - m) = e1 r - m := by ring
          have hval := congrArg ZMod.val hsum
          rw [ZMod.val_add] at hval
          have hlt1 : (e1 r - c1).val < k := ZMod.val_lt _
          have hlt2 : (c1 - m).val < k := ZMod.val_lt _
          by_cases hs : (e1 r - c1).val + (c1 - m).val < k
          · rw [Nat.mod_eq_of_lt hs] at hval; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
        omega
      have harc1 := (harcs (e1 r)).1 (e2 r - c1).val hc1_arc
      have he2_rw1 : c1 + ((e2 r - c1).val : ZMod k) = e2 r := by rw [ZMod.natCast_zmod_val]; ring
      have he2_rw2 : c1 + (((e2 r - c1).val + 1 : ℕ) : ZMod k) = e2 r + 1 := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      rw [he2_rw1, he2_rw2] at harc1
      have hdet_neg1 : det3 (X (e1 r + 1) - X (e1 r)) (X (e2 r + 1) - X (e2 r)) w < 0 := by
        rw [det3_swap_mid, det3_sub_right]; linarith
      -- Similarly `c2 := far (e2 r)` has `z c2 < z (v (r + 1))` and `c2 ≠ e2 r`, `c2 ≠ e2 r + 1 = v r`:
      -- so `c2` is in `[e2 r + 2 .. e1 r]`, meaning `(e1 r - c2).val < (e2 r - c2).val`!
      set c2 := far (e2 r)
      have hc2_spec := hfar (e2 r)
      have hc2_arc : (e1 r - c2).val < (e2 r - c2).val := by
        obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
        have hL_lt : (M - m).val < k := ZMod.val_lt _
        have hc2_range : (c2 - m).val ≤ (e1 r - m).val ∨ (e2 r - m).val + 1 < (c2 - m).val := by
          obtain ⟨s, hs, hvs⟩ := hv_mem c2
          have hs_lt : s < r := by
            by_contra hge
            have hne' : s ≠ r := by intro heq; subst heq; rw [hr_c2] at hvs; exact hc2_spec.2.1 hvs.symm
            have hne'' : s ≠ r + 1 := by
              intro heq; subst heq; rw [← hvs] at hlt; exact lt_irrefl _ hlt
            have hlt_r := hv_lt (r + 1) s (by omega) hs
            rw [hvs] at hlt_r; linarith
          have hzs : z c2 < z (v r) := by rw [← hvs]; exact hv_lt s r hs_lt (by omega)
          rw [hr_c2] at hzs
          by_contra hnot
          have hmid : (e1 r - m).val < (c2 - m).val ∧ (c2 - m).val ≤ (e2 r - m).val + 1 := by omega
          by_cases hL : (c2 - m).val ≤ (M - m).val
          · have hc2_eq : c2 = m + ((c2 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he11_eq : e1 r + 1 = m + (((e1 r - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z (e1 r + 1) ≤ z c2 := by
              by_cases heq : (e1 r - m).val + 1 = (c2 - m).val
              · rw [hc2_eq, he11_eq, heq]
              · rw [hc2_eq, he11_eq]
                exact (strictlyUnimodal_chain1_lt huni _ _ (by omega) hL).le
            rw [← hr1_c1] at hle_z
            have hlt_r := hv_lt r (r + 1) (by omega) (by omega)
            rw [hr_c2] at hlt_r; linarith
          · have hc2_eq : c2 = m + ((c2 - m).val : ZMod k) := by rw [ZMod.natCast_zmod_val]; ring
            have he21_eq : e2 r + 1 = m + (((e2 r - m).val + 1 : ℕ) : ZMod k) := by
              push_cast; rw [ZMod.natCast_zmod_val]; ring
            have hle_z : z (e2 r + 1) ≤ z c2 := by
              by_cases heq : (c2 - m).val = (e2 r - m).val + 1
              · rw [hc2_eq, he21_eq, heq]
              · rw [hc2_eq, he21_eq]
                exact (strictlyUnimodal_chain2_lt huni _ _ (by omega) (by omega) (by omega)).le
            rw [← hr_c2] at hle_z; linarith
        rcases hc2_range with hl | hr
        · have h1 : (e1 r - c2).val = (e1 r - m).val - (c2 - m).val := by
            have hsum : (e1 r - c2) + (c2 - m) = e1 r - m := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add] at hval
            have hlt1 : (e1 r - c2).val < k := ZMod.val_lt _
            have hlt2 : (c2 - m).val < k := ZMod.val_lt _
            by_cases hs : (e1 r - c2).val + (c2 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          have h2 : (e2 r - c2).val = (e2 r - m).val - (c2 - m).val := by
            have hsum : (e2 r - c2) + (c2 - m) = e2 r - m := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add] at hval
            have hlt1 : (e2 r - c2).val < k := ZMod.val_lt _
            have hlt2 : (c2 - m).val < k := ZMod.val_lt _
            by_cases hs : (e2 r - c2).val + (c2 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          omega
        · have h1 : (e1 r - c2).val = (e1 r - m).val + k - (c2 - m).val := by
            have hsum : (e1 r - c2) + (c2 - m) = e1 r - m := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add] at hval
            have hlt1 : (e1 r - c2).val < k := ZMod.val_lt _
            have hlt2 : (c2 - m).val < k := ZMod.val_lt _
            by_cases hs : (e1 r - c2).val + (c2 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          have h2 : (e2 r - c2).val = (e2 r - m).val + k - (c2 - m).val := by
            have hsum : (e2 r - c2) + (c2 - m) = e2 r - m := by ring
            have hval := congrArg ZMod.val hsum
            rw [ZMod.val_add] at hval
            have hlt1 : (e2 r - c2).val < k := ZMod.val_lt _
            have hlt2 : (c2 - m).val < k := ZMod.val_lt _
            by_cases hs : (e2 r - c2).val + (c2 - m).val < k
            · rw [Nat.mod_eq_of_lt hs] at hval; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
          have hc2_k : (c2 - m).val < k := ZMod.val_lt _
          omega
      have harc2 := (harcs (e2 r)).1 (e1 r - c2).val hc2_arc
      have he1_rw1 : c2 + ((e1 r - c2).val : ZMod k) = e1 r := by rw [ZMod.natCast_zmod_val]; ring
      have he1_rw2 : c2 + (((e1 r - c2).val + 1 : ℕ) : ZMod k) = e1 r + 1 := by
        push_cast; rw [ZMod.natCast_zmod_val]; ring
      rw [he1_rw1, he1_rw2] at harc2
      have hdet_neg2 : det3 (X (e2 r + 1) - X (e2 r)) (X (e1 r + 1) - X (e1 r)) w < 0 := by
        rw [det3_swap_mid, det3_sub_right]; linarith
      have hskew : det3 (X (e1 r + 1) - X (e1 r)) (X (e2 r + 1) - X (e2 r)) w =
          -det3 (X (e2 r + 1) - X (e2 r)) (X (e1 r + 1) - X (e1 r)) w := by
        simp only [det3]; ring
      linarith
    · -- Case 2: both `v r` and `v (r + 1)` on Chain 2 -> `a_of r = e1 r = a_of (r + 1)`
      have ha1 : a_of r = e1 r := by
        have hne : v r ≠ e1 r := by
          rw [hr_c2]
          intro heq
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          have hs : e2 r + 1 - m = (e2 r - m) + 1 := by ring
          rw [hs, ZMod.val_add, ZMod.val_one] at heq_v
          by_cases hlt' : (e2 r - m).val + 1 < k
          · rw [Nat.mod_eq_of_lt hlt'] at heq_v; omega
          · have hz_e : (e2 r - m).val + 1 = k := by omega
            rw [hz_e, Nat.mod_self] at heq_v
            have he1m' : (e1 r - m).val = 0 := heq_v.symm
            have he1m : e1 r = m := by
              have : e1 r - m = 0 := by rw [← ZMod.natCast_zmod_val (e1 r - m), he1m']; simp
              exact sub_eq_zero.mp this
            rw [he1m] at heq
            have hlt0 := hv_lt 0 r (by omega) (by omega)
            rw [hv0, hr_c2, heq] at hlt0; exact lt_irrefl _ hlt0
        simp [a_of, hne]
      have he1_r1 : e1 (r + 1) = e1 r := by
        have : e1 (r + 1) = (stepPair r (e1 r, e2 r)).1 := rfl
        have hne : v (r + 1) ≠ e1 r + 1 := by
          rw [hr1_c2]
          intro heq
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          have hs : e1 r + 1 - m = (e1 r - m) + 1 := by ring
          rw [hs, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)] at heq_v
          omega
        simp [this, stepPair, hne]
      have ha2 : a_of (r + 1) = e1 r := by
        have hne : v (r + 1) ≠ e1 (r + 1) := by
          rw [hr1_c2, he1_r1]
          intro heq
          obtain ⟨h_e1L, h_Le2, _, _, _, _, _, _⟩ := hinv r (by omega)
          have heq_v := congrArg ZMod.val (congrArg (· - m) heq)
          omega
        rw [he1_r1] at hne
        dsimp only [a_of]; rw [he1_r1]; split_ifs with h_eq
        · exact absurd h_eq hne
        · rfl
      rw [ha1] at hgt; rw [ha2] at hlt
      obtain ⟨s, hs, hvs⟩ := hv_mem (far (e1 r))
      have h1 : r < s := by
        by_contra hle
        have : z (v s) ≤ z (v r) := by
          by_cases heq : s = r
          · subst heq; exact le_rfl
          · exact (hv_lt s r (by omega) (by omega)).le
        rw [hvs] at this; linarith
      have h2 : s < r + 1 := by
        by_contra hge
        have : z (v (r + 1)) ≤ z (v s) := by
          by_cases heq : s = r + 1
          · subst heq; exact le_rfl
          · exact (hv_lt (r + 1) s (by omega) hs).le
        rw [hvs] at this; linarith
      omega

/-- **Corollary (Task FE1):** A generic strictly unimodal `k`-rim (`4 ≤ k`) with
`HiddenInTriangles` and non-degeneracy `hnd` yields `Gen.EdgePlaneAny x`. -/
theorem edgePlaneAny_of_unimodal {n k : ℕ} [NeZero k] (hk : 4 ≤ k) (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w : ℝ³)
    (hrim : StrictRimN x w lab) (hhid : HiddenInTriangles x w lab)
    (m M : ZMod k)
    (hdist : ∀ i j : ZMod k, i ≠ j → ⟪x (lab i), w⟫ ≠ ⟪x (lab j), w⟫)
    (huni : StrictlyUnimodal (fun i => x (lab i)) w m M)
    (hgen : NoParallelRimEdges (fun i => x (lab i)) w)
    (hnd : ∀ a c : ZMod k, c ≠ a → c ≠ a + 1 →
      ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c), x (lab (a + 1)) - x (lab a)⟫ ≠ 0) :
    Gen.EdgePlaneAny x := by
  let X : ZMod k → ℝ³ := fun i => x (lab i)
  have hccw := strictRimCcw_of_strictRimN x w lab hinj hrim
  obtain ⟨a, c, hsep⟩ := isDepthSeparatedAt_of_unimodal hk X w m M hccw hdist huni hgen
  have hca : c ≠ a := by
    intro h; subst h; exact (hsep.1 (c + 1) (Minimality.zmod_ne_add_one (by omega) c).symm).ne (by
      simp only [X, det3, PiLp.sub_apply]; ring)
  have hca1 : c ≠ a + 1 := by
    intro h; subst h; exact (hsep.1 a (Minimality.zmod_ne_add_one (by omega) a)).ne (by
      simp only [X, det3, PiLp.sub_apply]; ring)
  obtain ⟨⟨σ, hS⟩, hD⟩ := splitRows_of_isDepthSeparatedAt (by omega) x w lab hinj hrim a c hsep
  have hcv : det3 (X (c + 1) - X c) (X (c - 1) - X c) w ≠ 0 := by
    have h1 : c - 1 ≠ c := fun h => by
      have : (1 : ZMod k) = 0 := by linear_combination -h
      have hf : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero this
    have h2 : c - 1 ≠ c + 1 := (Minimality.zmod_sub_one_ne_add_one (by omega) c)
    exact (hrim (lab (c - 1)) c (fun h => h1 (hinj h)) (fun h => h2 (hinj h))).ne'
  obtain ⟨s, α, μ, hrow⟩ := EV.epRows_of_splitRows (by omega) X w a c σ hca hca1 hS hD (hnd a c hca hca1) hcv
  exact ⟨k, inferInstance, lab, w, a, s, α, μ, by omega, hinj, hrim, hhid, hD, hrow⟩

/-! ## Satisfiability example -/

/-- Concrete 6-point, 5-rim configuration in `ℝ³` with strictly unimodal depths `0, 1, 4, 3, 2`
at `w = (0, 0, 1)` and no parallel rim edges. -/
noncomputable def exU5 : Fin 6 → ℝ³
  | 0 => !₂[2, 0, 0]
  | 1 => !₂[1, 2, 1]
  | 2 => !₂[-2, 3, 4]
  | 3 => !₂[-3, 0, 3]
  | 4 => !₂[0, -2, 2]
  | 5 => !₂[-1, 1, 0]

def exULab5 : ZMod 5 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4

theorem example_unimodal_edgePlane : Gen.EdgePlaneAny exU5 := by
  let w : ℝ³ := !₂[0, 0, 1]
  have hinj : Function.Injective exULab5 := by decide
  have hrim : StrictRimN exU5 w exULab5 := by
    intro p i hp1 hp2
    have hi : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
    rcases hi i with rfl | rfl | rfl | rfl | rfl <;>
      (try rw [show (4 + 1 : ZMod 5) = 0 from by decide] at hp2 ⊢) <;>
      (try rw [show (3 + 1 : ZMod 5) = 4 from by decide] at hp2 ⊢) <;>
      (try rw [show (2 + 1 : ZMod 5) = 3 from by decide] at hp2 ⊢) <;>
      (try rw [show (1 + 1 : ZMod 5) = 2 from by decide] at hp2 ⊢) <;>
      (try rw [show (0 + 1 : ZMod 5) = 1 from by decide] at hp2 ⊢) <;>
      fin_cases p <;>
      simp_all [exULab5, exU5, w, det3, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      try norm_num
  have hhid : HiddenInTriangles exU5 w exULab5 := by
    intro m hm
    have hm5 : m = 5 := by
      fin_cases m
      · exact absurd rfl (hm 0)
      · exact absurd rfl (hm 1)
      · exact absurd rfl (hm 2)
      · exact absurd rfl (hm 3)
      · exact absurd rfl (hm 4)
      · rfl
    subst hm5
    refine ⟨exU5 0, mem_image_of_mem _ (mem_univ 0),
            exU5 2, mem_image_of_mem _ (mem_univ 2),
            exU5 3, mem_image_of_mem _ (mem_univ 3), ?_, ?_, ?_, ?_⟩ <;>
      · simp [exU5, w, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; try norm_num
  refine edgePlaneAny_of_unimodal (k := 5) (by norm_num) exU5 exULab5 hinj w hrim hhid 0 2
    ?_ ?_ ?_ ?_
  · intro i j hij
    have hi : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
    rcases hi i with rfl | rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl | rfl <;>
      (try exact absurd rfl hij) <;>
      simp [exULab5, exU5, w, inner3, Matrix.cons_val_zero, Matrix.cons_val_one] <;> try norm_num
  · refine ⟨by decide, fun s hs => ?_, fun s hs1 hs2 => ?_⟩
    · have hL : ((2 : ZMod 5) - 0).val = 2 := by decide
      rw [hL] at hs
      have hs' : s = 0 ∨ s = 1 := by omega
      rcases hs' with rfl | rfl <;>
        · simp [exULab5, exU5, w, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]; try norm_num
    · have hL : ((2 : ZMod 5) - 0).val = 2 := by decide
      rw [hL] at hs1
      have hs' : s = 2 ∨ s = 3 ∨ s = 4 := by omega
      rcases hs' with rfl | rfl | rfl <;>
        · simp [exULab5, exU5, w, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]; try norm_num
  · intro i j hij
    have hi : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
    rcases hi i with rfl | rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl | rfl <;>
      (try exact absurd rfl hij) <;>
      (try rw [show (4 + 1 : ZMod 5) = 0 from by decide]) <;>
      (try rw [show (3 + 1 : ZMod 5) = 4 from by decide]) <;>
      (try rw [show (2 + 1 : ZMod 5) = 3 from by decide]) <;>
      (try rw [show (1 + 1 : ZMod 5) = 2 from by decide]) <;>
      (try rw [show (0 + 1 : ZMod 5) = 1 from by decide]) <;>
      simp [exULab5, exU5, w, det3, Matrix.cons_val_zero, Matrix.cons_val_one] <;> try norm_num
  · intro a c hca hca1
    have hi : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
    rcases hi a with rfl | rfl | rfl | rfl | rfl <;> rcases hi c with rfl | rfl | rfl | rfl | rfl <;>
      (try exact absurd rfl hca) <;> (try exact absurd rfl hca1) <;>
      (try rw [show (4 + 1 : ZMod 5) = 0 from by decide]) <;>
      (try rw [show (3 + 1 : ZMod 5) = 4 from by decide]) <;>
      (try rw [show (2 + 1 : ZMod 5) = 3 from by decide]) <;>
      (try rw [show (1 + 1 : ZMod 5) = 2 from by decide]) <;>
      (try rw [show (0 + 1 : ZMod 5) = 1 from by decide]) <;>
      simp [levelPoint, exULab5, exU5, w, inner3, Matrix.cons_val_zero, Matrix.cons_val_one] <;> try norm_num

end Minimality.Split.UnimodalSplit
