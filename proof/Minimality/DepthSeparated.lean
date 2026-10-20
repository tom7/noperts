module

public import Minimality.UnimodalCert

@[expose] public section

/-!
# Depth-separated parallel pairs (Theorem 8.10)

FEWER-FACES-PROOFS.md Theorem 8.10 (CRIT5-WRITEUP.md §3), which generalizes
Theorem 7.3.  Let `p` be a strictly convex counterclockwise polygon with corner
depths `z`, `e = [p a, p (a + 1)]` an edge with outward normal `n_e` and `c` a
corner with `−n_e ∈ N_c` (`c` minimizes `⟪n_e, ·⟫`).  Removing `c` and the open
edge `e` leaves two chains: `A = c + 1, …, a` (counterclockwise from `c` to the
first end of `e`) and `B = a + 1, …, c − 1`.  The pair is *depth-separated*
(`IsDepthSeparatedPair`) if every corner of one chain lies strictly above
`z c` and every corner of the other strictly below.

* `forces_parallel_of_depthSeparated`: corner forces in the normal cones with
  zero sum (E1) and zero depth moment (E2) are all parallel to `n_e`.  This is
  the edge-force proof: `E2 − z_c E1`, crossed with `n_e`, is a sum of terms
  `(z i − z c) · cross2 n_e (f i)` of one sign (the edges from `c` to `a` climb
  in `⟪n_e, ·⟫`, those from `a + 1` back to `c` descend), so every corner other
  than `c` has its force parallel to `n_e`, and then so does `c` by (E1).
* `hasHorizontalDoubleNormal_of_forces_depthSeparated` (Theorem 8.10, polygon
  form, the analogue of `hasHorizontalDoubleNormal_of_forces`): a nonzero
  balanced system with zero torque gives a horizontal double normal.
* `isRupert_of_depthSeparatedView` (Rupert form, as `isRupert_of_unimodalView`)
  and the certificate form `exists_tiltCert_of_depthSeparated` (as
  `exists_tiltCert_of_unimodal`), with the crossing corollaries
  `isRupert_of_chords_depthSeparated` (Proposition 8.8) and
  `isRupert_of_edgeChords_depthSeparated` (Theorem 8.9).

The paper asks `−n_e ∈ int N_c`, which makes the cone of balanced systems the
single parallel ray; for the conclusion used here (all forces parallel, hence a
horizontal double normal once the torque vanishes) `−n_e ∈ N_c` suffices.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset

/-- A *depth-separated parallel pair* `(e, c)` of the polygon `p` with depths
`z`: the edge `e = [p a, p (a + 1)]` and the corner `c` with `−n_e ∈ N_c`, such
that the corners `c + s` for `0 < s ≤ (a − c).val` (the chain from `c` to `a`)
lie strictly on one side of the level `z c` and those for
`(a − c).val < s < k` (the chain from `a + 1` back to `c`) strictly on the
other. -/
def IsDepthSeparatedPair {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) (a c : ZMod k) : Prop :=
  -outNormal (p a) (p (a + 1)) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p c) ∧
    (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → z c < z (c + s)) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → z (c + s) < z c) ∨
      ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → z (c + s) < z c) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → z c < z (c + s)))

theorem cross2_outNormal_left (x y w : ℝ²) : cross2 (outNormal x y) w = ⟪w, y - x⟫ := by
  simp [outNormal, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- Nondecreasing steps between two values that do not increase are zero. -/
theorem step_eq_zero_of_nonneg {w : ℕ → ℝ} {i j : ℕ} (h : ∀ s, i ≤ s → s < j → 0 ≤ w (s + 1) - w s)
    (hji : w j ≤ w i) : ∀ s, i ≤ s → s < j → w (s + 1) - w s = 0 := by
  have mono : ∀ s t, i ≤ s → s ≤ t → t ≤ j → w s ≤ w t := by
    intro s t hs hst htj
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ t hst ih => linarith [ih (by omega), h t (by omega) (by omega)]
  intro s hs hsj
  have h1 := mono i s le_rfl hs (by omega)
  have h2 := mono (s + 1) j (by omega) (by omega) le_rfl
  linarith [h s hs hsj]

theorem zmod_add_val_sub {k : ℕ} [NeZero k] (c i : ZMod k) : c + ((i - c).val : ZMod k) = i := by
  rw [ZMod.natCast_zmod_val]; ring

namespace IsCcwPolygon

variable {k : ℕ} [NeZero k] {p : ZMod k → ℝ²}

omit [NeZero k] in
/-- The ends of an edge maximize its outward normal. -/
theorem inner_outNormal_le (hp : IsCcwPolygon p) (a j : ZMod k) :
    ⟪outNormal (p a) (p (a + 1)), p j⟫ ≤ ⟪outNormal (p a) (p (a + 1)), p a⟫ := by
  have e : ⟪outNormal (p a) (p (a + 1)), p j⟫ =
      ⟪outNormal (p a) (p (a + 1)), p a⟫ - cross2 (p (a + 1) - p a) (p j - p a) := by
    have := inner_outNormal (p a) (p (a + 1)) (p j - p a)
    rw [inner_sub_right] at this; linarith
  rw [e]
  by_cases hj : j = a
  · subst hj; simp [cross2]
  by_cases hj' : j = a + 1
  · subst hj'; rw [cross2_self]; simp
  linarith [hp.2 a j hj hj']

/-- **The edge normal along the two chains.**  If `c` minimizes `⟪n_e, ·⟫`,
the increments of `⟪−n_e, ·⟫` read from `c` are `≤ 0` up to `a` and `≥ 0` from
`a` on. -/
theorem incr_outNormal (hp : IsCcwPolygon p) {a c : ZMod k}
    (hc : -outNormal (p a) (p (a + 1)) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p c)) :
    (∀ n, n < (a - c).val → ⟪-outNormal (p a) (p (a + 1)),
        p (c + ((n + 1 : ℕ) : ZMod k)) - p (c + (n : ZMod k))⟫ ≤ 0) ∧
      (∀ n, (a - c).val ≤ n → n < k → 0 ≤ ⟪-outNormal (p a) (p (a + 1)),
        p (c + ((n + 1 : ℕ) : ZMod k)) - p (c + (n : ZMod k))⟫) := by
  set D := -outNormal (p a) (p (a + 1)) with hD
  set m := (a - c).val with hm
  set w : ℕ → ℝ := fun n => ⟪D, p (c + (n : ZMod k))⟫ with hw
  have hinc : ∀ n, ⟪D, p (c + ((n + 1 : ℕ) : ZMod k)) - p (c + (n : ZMod k))⟫ = w (n + 1) - w n :=
    fun n => by simp only [hw, inner_sub_right]
  simp only [hinc]
  have hcmax : ∀ i, ⟪D, p i⟫ ≤ ⟪D, p c⟫ := fun i => by
    have := hc (p i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    rw [inner_sub_right] at this; linarith
  have hamin : ∀ n, w m ≤ w n := fun n => by
    simp only [hw, hm, zmod_add_val_sub, hD, inner_neg_left, neg_le_neg_iff]
    exact hp.inner_outNormal_le a _
  obtain ⟨t, htk, hle, hge⟩ := hp.pattern_from_max D c hcmax
  simp only [hinc] at hle hge
  have hmk : m < k := ZMod.val_lt _
  rcases le_or_gt t m with htm | hmt
  · have h0 := step_eq_zero_of_nonneg (w := w) (i := t) (j := m)
      (fun s h1 h2 => hge s h1 (by omega)) (hamin t)
    refine ⟨fun n hn => ?_, fun n hn hnk => hge n (by omega) hnk⟩
    rcases lt_or_ge n t with h | h
    · exact hle n h
    · exact (h0 n h hn).le
  · have h0 := step_eq_zero_of_nonneg (w := fun n => -w n) (i := m) (j := t)
      (fun s h1 h2 => by linarith [hle s h2]) (by simp only [neg_le_neg_iff]; exact hamin t)
    refine ⟨fun n hn => hle n (by omega), fun n hn hnk => ?_⟩
    rcases lt_or_ge n t with h | h
    · linarith [h0 n hn h]
    · exact hge n h hnk

end IsCcwPolygon

/-- **Theorem 8.10, core (one orientation).**  The chain from `c` to `a` lies
above `z c`, the chain from `a + 1` back to `c` below. -/
theorem forces_parallel_of_depthSeparated_aux {k : ℕ} [NeZero k] {p : ZMod k → ℝ²}
    {z : ZMod k → ℝ} (hp : IsCcwPolygon p) {a c : ZMod k}
    (hc : -outNormal (p a) (p (a + 1)) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p c))
    (hA : ∀ s : ℕ, 0 < s → s ≤ (a - c).val → z c < z (c + s))
    (hB : ∀ s : ℕ, (a - c).val < s → s < k → z (c + s) < z c)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) :
    ∀ i, cross2 (outNormal (p a) (p (a + 1))) (f i) = 0 := by
  classical
  set n := outNormal (p a) (p (a + 1)) with hn
  set m := (a - c).val with hm
  obtain ⟨hle, hge⟩ := hp.incr_outNormal hc
  obtain ⟨hpos, hneg⟩ := hp.corner_signs hf (-n) c m hle hge
  have hneg' : ∀ v : ℝ², cross2 (-n) v = -cross2 n v := fun v => by simp [cross2]; ring
  -- the sign of `cross2 n (f i)` on the two chains
  have hsA : ∀ s : ℕ, 0 < s → s ≤ m → cross2 n (f (c + s)) ≤ 0 := by
    intro s hs0 hsm
    rcases lt_or_eq_of_le hsm with h | h
    · have := hpos s hs0 h; rw [hneg'] at this; linarith
    · rw [h, hm, zmod_add_val_sub, hn, cross2_outNormal_left]
      have := hf a (p (a + 1)) (subset_convexHull ℝ _ ⟨a + 1, rfl⟩)
      exact this
  have hsB : ∀ s : ℕ, m < s → s < k → 0 ≤ cross2 n (f (c + s)) := by
    intro s h1 h2
    have := hneg s (by omega) h2; rw [hneg'] at this; linarith
  -- `E2 − z_c E1` crossed with `n`: every term is `≤ 0`
  have hsum : ∑ i, (z i - z c) * cross2 n (f i) = 0 := by
    have : ∑ i, (z i - z c) * cross2 n (f i) = cross2 n (∑ i, z i • f i - z c • ∑ i, f i) := by
      rw [cross2_sub_right, cross2_sum_right, smul_sum, cross2_sum_right, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [cross2_smul_right, cross2_smul_right]; ring
    rw [this, h1, h2, smul_zero, sub_zero]; simp [cross2]
  have hterm : ∀ i, (z i - z c) * cross2 n (f i) ≤ 0 := by
    intro i
    set s := (i - c).val with hs
    have hi : c + (s : ZMod k) = i := zmod_add_val_sub c i
    have hsk : s < k := ZMod.val_lt _
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.cast_zero, add_zero] at hi; subst hi; simp
    rcases le_or_gt s m with h | h
    · have := hA s h0 h; have := hsA s h0 h; rw [hi] at *; nlinarith
    · have := hB s h hsk; have := hsB s h hsk; rw [hi] at *; nlinarith
  have hzero := (sum_eq_zero_iff_of_nonpos fun i _ => hterm i).mp hsum
  have hoff : ∀ i, i ≠ c → cross2 n (f i) = 0 := by
    intro i hic
    set s := (i - c).val with hs
    have hi : c + (s : ZMod k) = i := zmod_add_val_sub c i
    have hsk : s < k := ZMod.val_lt _
    have hz : z i - z c ≠ 0 := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [h0, Nat.cast_zero, add_zero] at hi; exact absurd hi.symm hic
      rcases le_or_gt s m with h | h
      · have := hA s h0 h; rw [hi] at this; linarith
      · have := hB s h hsk; rw [hi] at this; linarith
    exact (mul_eq_zero.mp (hzero i (mem_univ _))).resolve_left hz
  intro i
  by_cases hic : i = c
  · subst hic
    have h1' : cross2 n (∑ j, f j) = 0 := by rw [h1]; simp [cross2]
    rw [cross2_sum_right, ← add_sum_erase _ _ (mem_univ i)] at h1'
    rwa [sum_eq_zero fun j hj => hoff j (mem_erase.mp hj).1, add_zero] at h1'
  · exact hoff i hic

/-- **Theorem 8.10, core.**  At a depth-separated parallel pair `(e, c)`,
corner forces in the normal cones with zero sum and zero depth moment are all
parallel to the normal `n_e` of `e`. -/
theorem forces_parallel_of_depthSeparated {k : ℕ} [NeZero k] {p : ZMod k → ℝ²}
    {z : ZMod k → ℝ} (hp : IsCcwPolygon p) {a c : ZMod k} (hds : IsDepthSeparatedPair p z a c)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) :
    ∀ i, cross2 (outNormal (p a) (p (a + 1))) (f i) = 0 := by
  obtain ⟨hc, ⟨hA, hB⟩ | ⟨hA, hB⟩⟩ := hds
  · exact forces_parallel_of_depthSeparated_aux hp hc hA hB hf h1 h2
  · refine forces_parallel_of_depthSeparated_aux (z := fun i => -z i) hp hc
      (fun s h1 h2 => neg_lt_neg (hA s h1 h2)) (fun s h1 h2 => neg_lt_neg (hB s h1 h2)) hf h1 ?_
    simp only [neg_smul, sum_neg_distrib, h2, neg_zero]

/-- **Theorem 8.10 (⇒), polygon form.**  Forces in the normal cones of a
strictly convex counterclockwise polygon with a depth-separated parallel pair,
not all zero, with zero sum, zero depth moment and zero torque, force a
horizontal double normal. -/
theorem hasHorizontalDoubleNormal_of_forces_depthSeparated {k : ℕ} [NeZero k] (p : ZMod k → ℝ²)
    (z : ZMod k → ℝ) (hp : IsCcwPolygon p) {a c : ZMod k} (hds : IsDepthSeparatedPair p z a c)
    (f : ZMod k → ℝ²) (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (hne : ∃ i, f i ≠ 0) (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0)
    (h3 : ∑ i, cross2 (p i) (f i) = 0) : HasHorizontalDoubleNormal p z := by
  have hn0 : outNormal (p a) (p (a + 1)) ≠ 0 := by
    intro h0
    have hne := hp.injective.ne (zmod_ne_add_one (by have := hp.1; omega) a)
    apply hne
    have e0 := congrArg (fun v : ℝ² => v 0) h0
    have e1 := congrArg (fun v : ℝ² => v 1) h0
    simp [outNormal] at e0 e1
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
  have hpar := forces_parallel_of_depthSeparated hp hds hf h1 h2
  obtain ⟨B, hfB⟩ := hne
  have he2 : 0 < ‖f B‖ ^ 2 := by have := norm_pos_iff.mpr hfB; positivity
  refine hp.hdn_of_parallel z hf hfB (fun i => ⟪f B, f i⟫ / ‖f B‖ ^ 2) (fun i => ?_) (B := B)
    ?_ h1 h2 h3
  · have := norm_sq_smul_of_cross2 (v := f i) (e := f B)
      (by rw [cross2_comm, cross2_trans hn0 (hpar B) (hpar i), neg_zero])
    apply smul_right_injective ℝ² he2.ne'
    simp only
    rw [this, smul_smul, mul_div_cancel₀ _ he2.ne']
  · simp only [real_inner_self_eq_norm_sq, div_self he2.ne']; exact one_pos

/-- **Lemma 7.1 glue for any polygon criterion.**  At the standard view the
silhouette is the cycle `x`, every other point of `V` projects into the
interior, and every nonzero balanced corner-force system of the silhouette with
zero torque gives a horizontal double normal (`H`).  If there is none, some
first-order motion is strictly inward.  (`exists_firstOrderInward_of_unimodal`
is the case `H = ` Theorem 7.3.) -/
theorem exists_firstOrderInward_of_forces_hdn (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    (H : ∀ f : ZMod k → ℝ²,
      (∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range fun i => proj_xy (x i))) (proj_xy (x i))) →
      (∃ i, f i ≠ 0) → ∑ i, f i = 0 → ∑ i, x i 2 • f i = 0 →
      ∑ i, cross2 (proj_xy (x i)) (f i) = 0 →
      HasHorizontalDoubleNormal (fun i => proj_xy (x i)) (fun i => x i 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (x i)) (fun i => x i 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  classical
  by_contra hno
  push Not at hno
  set p : ZMod k → ℝ² := fun i => proj_xy (x i) with hpdef
  set Q := convexHull ℝ (Set.range p) with hQdef
  have hSQ : proj_xy '' convexHull ℝ (V : Set ℝ³) = Q := by
    rw [show (proj_xy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
    apply le_antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hc : ∃ i, v = x i
      · obtain ⟨i, rfl⟩ := hc; exact subset_convexHull ℝ _ ⟨i, rfl⟩
      · push Not at hc; exact interior_subset (hin v hv hc)
    · apply convexHull_mono
      rintro _ ⟨i, rfl⟩; exact ⟨x i, hxV i, rfl⟩
  obtain ⟨f, hfN, ⟨v₀, hv₀, hf₀⟩, hE1, hE2, hE3⟩ :=
    exists_forces_of_not_firstOrderInward V (by rw [hSQ]; exact hp.interior_nonempty) hno
  rw [hSQ] at hfN
  have hzero : ∀ v ∈ V, (∀ i, v ≠ x i) → f v = 0 := fun v hv hc =>
    normalConeAt_eq_zero_of_mem_interior (hin v hv hc) (hfN v hv)
  have hxinj : Function.Injective x := fun i j h => hp.injective (by rw [hpdef]; dsimp only; rw [h])
  have himg : univ.image x ⊆ V := fun v hv => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv; exact hxV i
  have hred : ∀ {M : Type} [AddCommMonoid M] (G : ℝ³ → M), (∀ v, f v = 0 → G v = 0) →
      ∑ v ∈ V, G v = ∑ i, G (x i) := by
    intro M _ G hG
    rw [← sum_subset himg (fun v hv hni => hG v (hzero v hv fun i h => hni (by
      rw [h]; exact mem_image_of_mem x (mem_univ i)))), sum_image (fun i _ j _ h => hxinj h)]
  refine hnd (H (fun i => f (x i)) (fun i => hfN (x i) (hxV i)) ?_ ?_ ?_ ?_)
  · by_contra hall; push Not at hall
    by_cases hc : ∃ i, v₀ = x i
    · obtain ⟨i, rfl⟩ := hc; exact hf₀ (hall i)
    · push Not at hc; exact hf₀ (hzero v₀ hv₀ hc)
  · rw [← hred f (fun v h => h)]; exact hE1
  · rw [← hred (fun v => v 2 • f v) (fun v h => by simp [h])]; exact hE2
  · rw [← hred (fun v => cross2 (proj_xy v) (f v)) (fun v h => by simp [h, cross2])]; exact hE3

/-- **Theorem 8.10 at an explicit standard view.**  The silhouette is the
cycle `x`, every other point of `V` projects into the interior of the shadow,
the silhouette has a depth-separated parallel pair, and there is no horizontal
double normal.  Then some first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_depthSeparated (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (x i)) (fun i => x i 2) a c)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (x i)) (fun i => x i 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ :=
  exists_firstOrderInward_of_forces_hdn V x hxV hp hin
    (fun f hf hne h1 h2 h3 => hasHorizontalDoubleNormal_of_forces_depthSeparated _ _ hp hds f hf
      hne h1 h2 h3) hnd

/-- **Theorem 8.10 at a rotated view.**  The points are given before rotating
by `R`. -/
theorem exists_firstOrderInward_image_of_depthSeparated (V : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward (V.image R.toEuclideanLin) ω τ := by
  classical
  exact exists_firstOrderInward_of_depthSeparated (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    hds hnd

/-- **Theorem 8.10, Rupert form, at the view of a rotation `R`.**  A strictly
convex silhouette `x` (every other point inside) with a depth-separated
parallel pair and no horizontal double normal makes `V` Rupert. -/
theorem isRupert_of_depthSeparatedView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  obtain ⟨ω, τ, h⟩ := exists_firstOrderInward_image_of_depthSeparated V R x hxV hp hin hds hnd
  exact isRupert_of_firstOrderInward_image V R hR ω τ h

/-- **Theorem 8.10, certificate form.**  At a view `u₀` (`R u₀ = r e_z`,
`r > 0`) where the silhouette of `V` is the strictly convex counterclockwise
polygon `x`, every other point projecting strictly inside, with a
depth-separated parallel pair and no horizontal double normal, some first-order
motion `(ω, τ)` has a local certificate at every point of `V`, and moves each
corner strictly to the inner side of both of its edges. -/
theorem exists_tiltCert_of_depthSeparated (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, (∀ y ∈ V, TiltCert V u₀ ω τ y) ∧
      ∀ i, 0 < det3 (x (i + 1) - x i) (cross ω (x i) + τ) u₀ ∧
        0 < det3 (x (i + 1) - x i) (cross ω (x (i + 1)) + τ) u₀ :=
  exists_tiltCert_of_firstOrderInward V R hR hr hRu x hxV hp hin
    (exists_firstOrderInward_image_of_depthSeparated V R x hxV hp hin hds hnd)

/-- **Proposition 8.8 with a depth-separated `K′`.**  Let `M ⊆ V` be the
middles at the view `u₀` (`R u₀ = r e_z`, `r > 0`), each over a silhouette edge
`[x i, x (i + 1)]` of the rest `K′`: `m = x i + s (x (i + 1) − x i) + δ u₀`,
`0 < s < 1`, `δ ≠ 0`.  If the silhouette of `K′` at `u₀` is the strictly
convex counterclockwise polygon `x` (every other point of `K′` strictly inside)
with a depth-separated parallel pair and no horizontal double normal, then `V`
is Rupert. -/
theorem isRupert_of_chords_depthSeparated (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  exact isRupert_of_chords_of_firstOrderInward V M R hR hr hRu x hxV hxM hp hin
    (exists_firstOrderInward_image_of_depthSeparated (V \ M) R x
      (fun i => mem_sdiff.mpr ⟨hxV i, hxM i⟩) hp
      (fun v hv hvx => hin v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2 hvx) hds hnd) hM

/-- **Theorem 8.9 with a depth-separated `K_v`.**  Two faces share the edge
`vw`, `w = v − h u₀` (`h ≠ 0`), at the view `u₀` (`R u₀ = r e_z`, `r > 0`),
with middles `M` (`EdgeMiddle`).  If the silhouette of `K_v` (the hull without
the middles and `w`) at `u₀` is the strictly convex counterclockwise polygon `x`
(every other point of `K_v` strictly inside) with a depth-separated parallel
pair and no horizontal double normal, `v = x i₀`, and the far ends are its
neighbours `A = x (i₀ + 1)`, `B = x (i₀ − 1)`, then `V` is Rupert. -/
theorem isRupert_of_edgeChords_depthSeparated (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {a c : ZMod k} (hds : IsDepthSeparatedPair (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2) a c)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
  classical
  exact isRupert_of_edgeChords_of_firstOrderInward V M R hR hr hRu x i₀ w h hwV hw hh hxV hxM hp
    hin (exists_firstOrderInward_image_of_depthSeparated ((V \ M).erase w) R x
      (fun i => mem_erase.mpr ⟨corner_ne_axle hr hRu hp hw hh i, mem_sdiff.mpr ⟨hxV i, hxM i⟩⟩) hp
      (fun v hv hvx => by
        obtain ⟨hvw, hv'⟩ := mem_erase.mp hv
        exact hin v (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2 hvw hvx) hds hnd) hM

end Minimality

end
