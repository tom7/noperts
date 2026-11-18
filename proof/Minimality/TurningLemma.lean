module

public import Minimality.ChordTop

@[expose] public section

/-!
# The Turning Lemma (TL)

Pure 2D polygon lemma.  `p : ZMod k → ℝ²` strictly convex ccw, `z` injective, and an arc
`A = p (l), …, p (l + m)` (`m < k`, so `A` is the whole rim iff `m = k - 1`) with

* (U) `z` strictly unimodal on `A` (rises strictly up to an index `t`, falls strictly after),
* (S) every vertex outside `A` is strictly below every vertex of `A`,
* (T) `turn(A) ≥ π`, in cross form `cross2 (d (l-1)) (d (l+m)) ≤ 0`, `d i = p (i+1) - p i`.

Then some edge `a` and some vertex `c ∈ A` form a depth-separated pair (`IsDepthSeparatedPair`).
No angle is used: the superlevel arcs `A_j` of `z` in `A` are built greedily; the first one
whose turn crosses `π` (as a sign change of `cross2 (d (u-1)) (d w)`) gives `c` and `a`.
For `A` the whole rim, (S) is vacuous and (T) is automatic (`cross2 d d = 0`):
`isDepthSeparatedPair_of_unimodal`.
-/

namespace Minimality

open scoped RealInnerProductSpace

namespace TL

theorem up_mono {f : ℕ → ℝ} {t : ℕ} (h : ∀ s, s < t → f s < f (s + 1)) :
    ∀ s r, r < s → s ≤ t → f r < f s := by
  intro s
  induction s with
  | zero => intro r hr; omega
  | succ s ih =>
    intro r hr hs
    have h1 := h s (by omega)
    by_cases h2 : r < s
    · exact lt_trans (ih r h2 (by omega)) h1
    · have : r = s := by omega
      subst this; exact h1

theorem down_mono {f : ℕ → ℝ} {t m : ℕ} (h : ∀ s, t ≤ s → s < m → f (s + 1) < f s) :
    ∀ s r, t ≤ r → r < s → s ≤ m → f s < f r := by
  intro s
  induction s with
  | zero => intro r _ hr; omega
  | succ s ih =>
    intro r htr hr hs
    have h1 := h s (by omega) (by omega)
    by_cases h2 : r < s
    · exact lt_trans h1 (ih r htr h2 (by omega))
    · have : r = s := by omega
      subst this; exact h1

/-- A strictly unimodal sequence has no interior strict local minimum. -/
theorem no_valley {f : ℕ → ℝ} {t m : ℕ} (hu : ∀ s, s < t → f s < f (s + 1))
    (hd : ∀ s, t ≤ s → s < m → f (s + 1) < f s) {r1 r2 r3 : ℕ} (h12 : r1 < r2) (h23 : r2 < r3)
    (h3 : r3 ≤ m) : ¬ (f r2 < f r1 ∧ f r2 < f r3) := by
  rintro ⟨a, b⟩
  by_cases h : r2 ≤ t
  · have := up_mono hu r2 r1 h12 h; linarith
  · have := down_mono hd r3 r2 (by omega) h23 h3; linarith

theorem peak {f : ℕ → ℝ} {t m : ℕ} (hu : ∀ s, s < t → f s < f (s + 1))
    (hd : ∀ s, t ≤ s → s < m → f (s + 1) < f s) {r : ℕ} (hr : r ≤ m) (hrt : r ≠ t) :
    f r < f t := by
  by_cases h : r < t
  · exact up_mono hu t r h le_rfl
  · exact down_mono hd r t le_rfl (by omega) hr

/-- `[i, j]` is a top arc of `[0, m]`: contiguous, and above everything else in `[0, m]`. -/
def Inv (f : ℕ → ℝ) (m i j : ℕ) : Prop :=
  i ≤ j ∧ j ≤ m ∧ ∀ s, i ≤ s → s ≤ j → ∀ r, r ≤ m → (r < i ∨ j < r) → f r < f s

/-- Growing a top arc by its highest neighbour. -/
theorem step {f : ℕ → ℝ} {t m i j : ℕ} (hu : ∀ s, s < t → f s < f (s + 1))
    (hd : ∀ s, t ≤ s → s < m → f (s + 1) < f s)
    (hinj : ∀ r s, r ≤ m → s ≤ m → f r = f s → r = s)
    (hI : Inv f m i j) (hne : ¬ (i = 0 ∧ j = m)) :
    (j + 1 ≤ m ∧ Inv f m i (j + 1)) ∨ (∃ i', i = i' + 1 ∧ Inv f m i' j) := by
  obtain ⟨hij, hjm, hB⟩ := hI
  classical
  have hne' : ((Finset.range (m + 1)).filter (fun r => r < i ∨ j < r)).Nonempty := by
    by_cases hi : i = 0
    · have : j < m := by omega
      exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inr this⟩⟩
    · exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inl (by omega)⟩⟩
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image _ f hne'
  have hv' := Finset.mem_filter.mp hv
  have hvm : v ≤ m := by have := Finset.mem_range.mp hv'.1; omega
  have hmax' : ∀ r, r ≤ m → (r < i ∨ j < r) → r ≠ v → f r < f v := by
    intro r hr hr' hne
    have := hmax r (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr'⟩)
    exact lt_of_le_of_ne this (fun h => hne (hinj r v hr hvm h))
  rcases hv'.2 with hvi | hvj
  · -- v < i
    by_cases hv1 : v = i - 1
    · right
      refine ⟨i - 1, by omega, by omega, hjm, ?_⟩
      intro s hs1 hs2 r hr hr'
      by_cases hsi : i ≤ s
      · exact hB s hsi hs2 r hr (by omega)
      · have : s = v := by omega
        subst this
        exact hmax' r hr (by omega) (by omega)
    · exfalso
      refine no_valley hu hd (r1 := v) (r2 := i - 1) (r3 := i) (by omega) (by omega)
        (by omega) ⟨?_, ?_⟩
      · exact hmax' (i - 1) (by omega) (Or.inl (by omega)) (by omega)
      · exact hB i le_rfl hij (i - 1) (by omega) (Or.inl (by omega))
  · by_cases hv1 : v = j + 1
    · subst hv1
      left
      refine ⟨hvm, by omega, hvm, ?_⟩
      intro s hs1 hs2 r hr hr'
      by_cases hsj : s ≤ j
      · exact hB s hs1 hsj r hr (by omega)
      · have : s = j + 1 := by omega
        subst this
        exact hmax' r hr (by omega) (by omega)
    · exfalso
      refine no_valley hu hd (r1 := j) (r2 := j + 1) (r3 := v) (by omega) (by omega) hvm ⟨?_, ?_⟩
      · exact hB j hij le_rfl (j + 1) (by omega) (Or.inr (by omega))
      · exact hmax' (j + 1) (by omega) (Or.inr (by omega)) (by omega)

/-- The discrete induction: from a top arc with `T > 0`, grow until `T` becomes `≤ 0`. -/
theorem induct {f : ℕ → ℝ} {t m : ℕ} (hu : ∀ s, s < t → f s < f (s + 1))
    (hd : ∀ s, t ≤ s → s < m → f (s + 1) < f s)
    (hinj : ∀ r s, r ≤ m → s ≤ m → f r = f s → r = s) (Tf : ℕ → ℕ → ℝ) (G : Prop)
    (hR : ∀ i j, Inv f m i j → Inv f m i (j + 1) → 0 < Tf i j → Tf i (j + 1) ≤ 0 → G)
    (hL : ∀ i j, Inv f m (i + 1) j → Inv f m i j → 0 < Tf (i + 1) j → Tf i j ≤ 0 → G)
    (hT : Tf 0 m ≤ 0) : ∀ n i j, i + (m - j) = n → Inv f m i j → 0 < Tf i j → G := by
  intro n
  induction n with
  | zero =>
    intro i j hn hI hpos
    obtain ⟨_, hjm, _⟩ := hI
    obtain rfl : i = 0 := by omega
    obtain rfl : j = m := by omega
    exact absurd hT (not_le.mpr hpos)
  | succ n ih =>
    intro i j hn hI hpos
    rcases step hu hd hinj hI (by omega) with ⟨h1, hI'⟩ | ⟨i', rfl, hI'⟩
    · by_cases hT' : Tf i (j + 1) ≤ 0
      · exact hR i j hI hI' hpos hT'
      · exact ih i (j + 1) (by omega) hI' (not_le.mp hT')
    · by_cases hT' : Tf i' j ≤ 0
      · exact hL i' j hI hI' hpos hT'
      · exact ih i' j (by omega) hI' (not_le.mp hT')

/-! ### Geometry -/

/-- Edge direction `d x = p (x+1) - p x`. -/
def dd {k : ℕ} (p : ZMod k → ℝ²) (x : ZMod k) : ℝ² := p (x + 1) - p x

/-- `cross2 (d (l+i-1)) (d (l+j))`: the turn of the arc `l+i … l+j` is `≥ π` iff this is `≤ 0`. -/
def Tn {k : ℕ} (p : ZMod k → ℝ²) (l : ZMod k) (i j : ℕ) : ℝ :=
  cross2 (dd p (l + (i : ZMod k) - 1)) (dd p (l + (j : ZMod k)))

/-- Antipodal criterion in turn form: if `d (c-1)`, `d a`, `d c` turn so that `-d a` is
between `d (c-1)` and `d c`, then `-n_a` is in the normal cone at `p c`. -/
theorem cone_pair {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) (a c : ZMod k)
    (h1 : 0 ≤ cross2 (dd p a) (dd p (c - 1))) (h2 : cross2 (dd p a) (dd p c) ≤ 0) :
    -outNormal (p a) (p (a + 1)) ∈ normalConeAt (convexHull ℝ (Set.range p)) (p c) := by
  have he := hp.cross2_edge_pos a
  have hν : -outNormal (p a) (p (a + 1)) ≠ 0 := by
    intro h0
    have := congrArg (fun ν => ⟪ν, p a - p (a - 1)⟫) h0
    simp only [inner_zero_left, inner_neg_outNormal] at this
    rw [cross2_comm] at this
    linarith
  have e1 : dd p (c - 1) = p c - p (c - 1) := by simp [dd]
  have e2 : dd p a = p (a + 1) - p a := rfl
  refine IsCcwPolygon.mem_normalConeAt_of_local hp hν ?_ ?_
  · rw [inner_neg_outNormal, ← e2, ← e1]; exact h1
  · rw [inner_neg_outNormal, ← e2]; exact h2

theorem cast_wrap {k : ℕ} (o o' : ℕ) (h : o = o' + k) : ((o : ℕ) : ZMod k) = (o' : ZMod k) := by
  subst h; push_cast; rw [ZMod.natCast_self, add_zero]

theorem finish_right {k : ℕ} {p : ZMod k → ℝ²} {z : ZMod k → ℝ} (hp : IsCcwPolygon p)
    (l : ZMod k) (m : ℕ) (hm : m < k) (f : ℕ → ℝ) (hf : ∀ s, f s = z (l + (s : ZMod k)))
    (hS : ∀ s, s ≤ m → ∀ r, m < r → r < k → f r < f s) {i j : ℕ}
    (hI : Inv f m i j) (hI' : Inv f m i (j + 1))
    (hT1 : 0 < Tn p l i j) (hT2 : Tn p l i (j + 1) ≤ 0) (hj : j + 1 ≤ m) :
    ∃ a c, IsDepthSeparatedPair p z a c ∧ ∃ s : ℕ, s ≤ m ∧ c = l + (s : ZMod k) := by
  have hwrap : ∀ o o' : ℕ, o = o' + k → f o = f o' := by
    intro o o' h; rw [hf, hf, cast_wrap o o' h]
  obtain ⟨N, hN⟩ : ∃ N, N + j + 2 = k + i := ⟨k + i - j - 2, by have := hI.1; omega⟩
  have hval : (l + (i : ZMod k) - 1 - (l + ((j + 1 : ℕ) : ZMod k))).val = N := by
    have hcast : ((N : ℕ) : ZMod k) = l + (i : ZMod k) - 1 - (l + ((j + 1 : ℕ) : ZMod k)) := by
      have h := congrArg (fun n : ℕ => (n : ZMod k)) hN
      simp only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self] at h
      push_cast
      linear_combination h
    rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := hI.1; omega)]
  refine ⟨l + (i : ZMod k) - 1, l + ((j + 1 : ℕ) : ZMod k), ⟨?_, Or.inr ⟨?_, ?_⟩⟩, j + 1, hj, rfl⟩
  · apply cone_pair hp
    · have hc1 : l + ((j + 1 : ℕ) : ZMod k) - 1 = l + (j : ZMod k) := by push_cast; ring
      rw [hc1]; exact hT1.le
    · exact hT2
  · intro s hs0 hsN
    rw [hval] at hsN
    have e1 : z (l + ((j + 1 : ℕ) : ZMod k) + (s : ZMod k)) = f (j + 1 + s) := by
      rw [hf]; congr 1; push_cast; ring
    rw [e1, ← hf]
    by_cases ho1 : j + 1 + s ≤ m
    · exact hI'.2.2 (j + 1) (by have := hI.1; omega) le_rfl (j + 1 + s) ho1 (Or.inr (by omega))
    by_cases ho2 : j + 1 + s < k
    · exact hS (j + 1) hj (j + 1 + s) (by omega) ho2
    · rw [hwrap (j + 1 + s) (j + 1 + s - k) (by omega)]
      exact hI'.2.2 (j + 1) (by have := hI.1; omega) le_rfl (j + 1 + s - k) (by have := hI.1; omega)
        (Or.inl (by omega))
  · intro s hsN hsk
    rw [hval] at hsN
    have e1 : z (l + ((j + 1 : ℕ) : ZMod k) + (s : ZMod k)) = f (j + 1 + s) := by
      rw [hf]; congr 1; push_cast; ring
    rw [e1, ← hf, hwrap (j + 1 + s) (j + 1 + s - k) (by omega)]
    exact hI.2.2 (j + 1 + s - k) (by omega) (by omega) (j + 1) hj (Or.inr (by omega))

theorem finish_left {k : ℕ} {p : ZMod k → ℝ²} {z : ZMod k → ℝ} (hp : IsCcwPolygon p)
    (l : ZMod k) (m : ℕ) (hm : m < k) (f : ℕ → ℝ) (hf : ∀ s, f s = z (l + (s : ZMod k)))
    (hS : ∀ s, s ≤ m → ∀ r, m < r → r < k → f r < f s) {i j : ℕ}
    (hI : Inv f m (i + 1) j) (hI' : Inv f m i j)
    (hT1 : 0 < Tn p l (i + 1) j) (hT2 : Tn p l i j ≤ 0) :
    ∃ a c, IsDepthSeparatedPair p z a c ∧ ∃ s : ℕ, s ≤ m ∧ c = l + (s : ZMod k) := by
  have hwrap : ∀ o o' : ℕ, o = o' + k → f o = f o' := by
    intro o o' h; rw [hf, hf, cast_wrap o o' h]
  obtain ⟨N, hN⟩ : ∃ N, N + i = j := ⟨j - i, by have := hI.1; omega⟩
  have hjm := hI.2.1
  have hval : (l + (j : ZMod k) - (l + (i : ZMod k))).val = N := by
    have hcast : ((N : ℕ) : ZMod k) = l + (j : ZMod k) - (l + (i : ZMod k)) := by
      have h := congrArg (fun n : ℕ => (n : ZMod k)) hN
      push_cast at h
      linear_combination h
    rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  refine ⟨l + (j : ZMod k), l + (i : ZMod k), ⟨?_, Or.inl ⟨?_, ?_⟩⟩, i, by have := hI.1; omega, rfl⟩
  · apply cone_pair hp
    · have := cross2_comm (dd p (l + (i : ZMod k) - 1)) (dd p (l + (j : ZMod k)))
      have h2 : Tn p l i j = cross2 (dd p (l + (i : ZMod k) - 1)) (dd p (l + (j : ZMod k))) := rfl
      linarith
    · have hc : l + ((i + 1 : ℕ) : ZMod k) - 1 = l + (i : ZMod k) := by push_cast; ring
      have h2 : Tn p l (i + 1) j = cross2 (dd p (l + ((i + 1 : ℕ) : ZMod k) - 1)) (dd p (l + (j : ZMod k))) := rfl
      rw [hc] at h2
      have := cross2_comm (dd p (l + (i : ZMod k))) (dd p (l + (j : ZMod k)))
      linarith
  · intro s hs0 hsN
    rw [hval] at hsN
    have e1 : z (l + (i : ZMod k) + (s : ZMod k)) = f (i + s) := by
      rw [hf]; congr 1; push_cast; ring
    rw [e1, ← hf]
    exact hI.2.2 (i + s) (by omega) (by omega) i (by omega) (Or.inl (by omega))
  · intro s hsN hsk
    rw [hval] at hsN
    have e1 : z (l + (i : ZMod k) + (s : ZMod k)) = f (i + s) := by
      rw [hf]; congr 1; push_cast; ring
    rw [e1, ← hf]
    have hi := hI'.1
    by_cases ho1 : i + s ≤ m
    · exact hI'.2.2 i le_rfl hi (i + s) ho1 (Or.inr (by omega))
    by_cases ho2 : i + s < k
    · exact hS i (by omega) (i + s) (by omega) ho2
    · rw [hwrap (i + s) (i + s - k) (by omega)]
      exact hI'.2.2 i le_rfl hi (i + s - k) (by omega) (Or.inl (by omega))

end TL

/-- **Turning Lemma.**  `p` strictly convex ccw, `z` injective, `A = l, …, l + m` an arc
(`m < k`) on which `z` is strictly unimodal (U), whose vertices are all strictly above the
vertices outside `A` (S), with `turn(A) ≥ π` in cross form (T).  Then some edge `a` and some
vertex `c` of `A` form a depth-separated pair. -/
theorem turning_lemma {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) (hp : IsCcwPolygon p)
    (hz : Function.Injective z) (l : ZMod k) (m : ℕ) (hm : m < k)
    (hU : ∃ t, t ≤ m ∧ (∀ s : ℕ, s < t → z (l + (s : ZMod k)) < z (l + ((s + 1 : ℕ) : ZMod k))) ∧
      ∀ s : ℕ, t ≤ s → s < m → z (l + ((s + 1 : ℕ) : ZMod k)) < z (l + (s : ZMod k)))
    (hS : ∀ s : ℕ, s ≤ m → ∀ r : ℕ, m < r → r < k → z (l + (r : ZMod k)) < z (l + (s : ZMod k)))
    (hT : cross2 (p l - p (l - 1)) (p (l + (m : ZMod k) + 1) - p (l + (m : ZMod k))) ≤ 0) :
    ∃ a c, IsDepthSeparatedPair p z a c ∧ ∃ s : ℕ, s ≤ m ∧ c = l + (s : ZMod k) := by
  obtain ⟨t, ht, hu, hd⟩ := hU
  have hk := hp.1
  set f : ℕ → ℝ := fun s => z (l + (s : ZMod k)) with hfdef
  have hf : ∀ s, f s = z (l + (s : ZMod k)) := fun _ => rfl
  have hinj : ∀ r s, r ≤ m → s ≤ m → f r = f s → r = s := by
    intro r s hr hs h
    by_contra hne
    have h1 := hz h
    exact zmod_add_ne (by omega) (by omega) hne l h1
  have hS' : ∀ s, s ≤ m → ∀ r, m < r → r < k → f r < f s := hS
  have hT' : TL.Tn p l 0 m ≤ 0 := by simpa [TL.Tn, TL.dd] using hT
  have hpos : 0 < TL.Tn p l t t := by
    have := hp.cross2_edge_pos (l + (t : ZMod k))
    simpa [TL.Tn, TL.dd] using this
  have hI0 : TL.Inv f m t t :=
    ⟨le_rfl, ht, fun s hs1 hs2 r hr _ => by
      obtain rfl : s = t := by omega
      exact TL.peak hu hd hr (by omega)⟩
  refine TL.induct (f := f) hu hd hinj (TL.Tn p l)
    (∃ a c, IsDepthSeparatedPair p z a c ∧ ∃ s : ℕ, s ≤ m ∧ c = l + (s : ZMod k))
    (fun i j h1 h2 h3 h4 => TL.finish_right hp l m hm f hf hS' h1 h2 h3 h4 h2.2.1)
    (fun i j h1 h2 h3 h4 => TL.finish_left hp l m hm f hf hS' h1 h2 h3 h4)
    hT' (t + (m - t)) t t (by omega) hI0 hpos

/-- **Remark (`A` = the whole rim).**  A strictly unimodal injective depth sequence along the
rim `l, l+1, …, l + (k-1)` has a depth-separated pair: (S) is vacuous and (T) is automatic. -/
theorem isDepthSeparatedPair_of_unimodal {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ)
    (hp : IsCcwPolygon p) (hz : Function.Injective z) (l : ZMod k)
    (hU : ∃ t, t ≤ k - 1 ∧
      (∀ s : ℕ, s < t → z (l + (s : ZMod k)) < z (l + ((s + 1 : ℕ) : ZMod k))) ∧
      ∀ s : ℕ, t ≤ s → s < k - 1 → z (l + ((s + 1 : ℕ) : ZMod k)) < z (l + (s : ZMod k))) :
    ∃ a c, IsDepthSeparatedPair p z a c := by
  have hk := hp.1
  obtain ⟨a, c, h, _⟩ := turning_lemma p z hp hz l (k - 1) (by omega) hU
    (fun s hs r hr hrk => by omega) (by
      rw [zmod_natCast_pred (by omega)]
      have e1 : l + -1 + 1 = l := by ring
      have e2 : l + -1 = l - 1 := by ring
      rw [e1, e2]
      exact (cross2_self _).le)
  exact ⟨a, c, h⟩

end Minimality
