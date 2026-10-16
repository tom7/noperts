module

public import Minimality.Tilt

@[expose] public section

/-!
# The lower chain of a planar point set seen edge-on

Tools for Theorem A of `FEWER-FACES-PROOFS.md` (a face with 5 or 6 vertices):
at a view in the plane of a face, the face is seen edge-on, and tilting the
view shows its *lower chain* (Lemma 8.0).  In the plane coordinates
`(x, y) = (s 0, s 1)` (the view along `y`):

* `mem_convexHull_of_between`: a point between two segments (in `x`, above
  the first, below the second) is in the hull of their endpoints.
* `ConvPos S`: no point of `S` is in the hull of the others.
* `cross2_pos_of_consecutive`: the *lower chain* of `S` (its `x`-extremes `A`,
  `B` and the points below the chord `AB`): every other point of `S` lies
  strictly to the left of (above) the segment between two `x`-consecutive
  points of the chain.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem segment_pt_mem {a b : ℝ²} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    a + α • (b - a) ∈ segment ℝ a b := by
  refine ⟨1 - α, α, by linarith, h0, by ring, ?_⟩
  ext i; simp; ring

/-- **Betweenness.**  If `s` lies (in `x`) over both segments `[a, b]` and
`[a', b']`, on or above the line `ab` and on or below the line `a'b'`, then `s`
is in the convex hull of the four endpoints. -/
theorem mem_convexHull_of_between {a b a' b' s : ℝ²} (hab : a 0 < b 0)
    (has : a 0 ≤ s 0) (hsb : s 0 ≤ b 0) (hab' : a' 0 < b' 0) (has' : a' 0 ≤ s 0)
    (hsb' : s 0 ≤ b' 0) (habove : 0 ≤ cross2 (b - a) (s - a))
    (hbelow : cross2 (b' - a') (s - a') ≤ 0) :
    s ∈ convexHull ℝ ({a, b, a', b'} : Set ℝ²) := by
  set α := (s 0 - a 0) / (b 0 - a 0) with hα
  set β := (s 0 - a' 0) / (b' 0 - a' 0) with hβ
  have hd : 0 < b 0 - a 0 := by linarith
  have hd' : 0 < b' 0 - a' 0 := by linarith
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hd.le
  have hα1 : α ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) hd'.le
  have hβ1 : β ≤ 1 := (div_le_one hd').mpr (by linarith)
  set P1 := a + α • (b - a)
  set P2 := a' + β • (b' - a')
  have hC : Convex ℝ (convexHull ℝ ({a, b, a', b'} : Set ℝ²)) := convex_convexHull ℝ _
  have hP1 : P1 ∈ convexHull ℝ ({a, b, a', b'} : Set ℝ²) :=
    hC.segment_subset (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
      (segment_pt_mem hα0 hα1)
  have hP2 : P2 ∈ convexHull ℝ ({a, b, a', b'} : Set ℝ²) :=
    hC.segment_subset (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
      (segment_pt_mem hβ0 hβ1)
  have hx1 : P1 0 = s 0 := by
    simp only [P1, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hα]
    field_simp; ring
  have hx2 : P2 0 = s 0 := by
    simp only [P2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hβ]
    field_simp; ring
  have hy1 : P1 1 ≤ s 1 := by
    simp only [cross2, PiLp.sub_apply] at habove
    simp only [P1, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hα]
    rw [div_mul_eq_mul_div, add_div' _ _ _ hd.ne', div_le_iff₀ hd]
    nlinarith
  have hy2 : s 1 ≤ P2 1 := by
    simp only [cross2, PiLp.sub_apply] at hbelow
    simp only [P2, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hβ]
    rw [div_mul_eq_mul_div, add_div' _ _ _ hd'.ne', le_div_iff₀ hd']
    nlinarith
  rcases eq_or_lt_of_le (hy1.trans hy2) with heq | hlt
  · have : s = P1 := by
      ext i; fin_cases i
      · exact hx1.symm
      · simp only [Fin.mk_one]; linarith
    rw [this]; exact hP1
  · set γ := (s 1 - P1 1) / (P2 1 - P1 1)
    have hγ0 : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
    have hγ1 : γ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have : s = P1 + γ • (P2 - P1) := by
      ext i; fin_cases i
      · show s 0 = P1 0 + γ * (P2 0 - P1 0)
        rw [hx1, hx2]; ring
      · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, γ]
        field_simp; ring
    rw [this]; exact hC.segment_subset hP1 hP2 (segment_pt_mem hγ0 hγ1)

/-- Strict convex position: no point of `S` is in the convex hull of the others. -/
def ConvPos (S : Finset ℝ²) : Prop :=
  ∀ s ∈ S, s ∉ convexHull ℝ ((S.erase s : Finset ℝ²) : Set ℝ²)

theorem ConvPos.not_mem_hull4 {S : Finset ℝ²} (hS : ConvPos S) {s a b a' b' : ℝ²}
    (hs : s ∈ S) (ha : a ∈ S) (hb : b ∈ S) (ha' : a' ∈ S) (hb' : b' ∈ S)
    (h1 : s ≠ a) (h2 : s ≠ b) (h3 : s ≠ a') (h4 : s ≠ b') :
    s ∉ convexHull ℝ ({a, b, a', b'} : Set ℝ²) := by
  intro hm
  apply hS s hs
  refine convexHull_mono ?_ hm
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff]
  rcases hx with rfl | rfl | rfl | rfl
  exacts [⟨ha, h1.symm⟩, ⟨hb, h2.symm⟩, ⟨ha', h3.symm⟩, ⟨hb', h4.symm⟩]

/-- The orientation of a triangle is invariant under cyclic shifts. -/
theorem cross2_cyc (a b c : ℝ²) : cross2 (b - a) (c - a) = cross2 (c - b) (a - b) := by
  simp only [cross2, PiLp.sub_apply]; ring

theorem cross2_swap (a b c : ℝ²) : cross2 (b - a) (c - a) = -cross2 (c - a) (b - a) := by
  simp only [cross2, PiLp.sub_apply]; ring

/-- **The lower chain's edges.**  `A`, `B` are the `x`-extremes of `S` (distinct
`x`), `c, c'` are on or below the chord `AB`, with no point of `S` on or below
the chord strictly between them in `x`.  Then every other point of `S` is
strictly above the line `cc'`. -/
theorem cross2_pos_of_consecutive' {S : Finset ℝ²} (hS : ConvPos S) {A B c c' s : ℝ²}
    (hA : A ∈ S) (hB : B ∈ S) (hAmin : ∀ y ∈ S, A 0 ≤ y 0) (hBmax : ∀ y ∈ S, y 0 ≤ B 0)
    (hAB : A 0 < B 0) (hc : c ∈ S) (hc' : c' ∈ S) (hcc' : c 0 < c' 0)
    (hcL : cross2 (B - A) (c - A) ≤ 0) (hc'L : cross2 (B - A) (c' - A) ≤ 0)
    (hcons : ∀ y ∈ S, c 0 < y 0 → y 0 < c' 0 → 0 < cross2 (B - A) (y - A))
    (hlowc : ∀ y ∈ S, y ≠ c → y 0 = c 0 → c 1 < y 1)
    (hlowc' : ∀ y ∈ S, y ≠ c' → y 0 = c' 0 → c' 1 < y 1)
    (hs : s ∈ S) (hsc : s ≠ c) (hsc' : s ≠ c') :
    0 < cross2 (c' - c) (s - c) := by
  by_cases hx0 : s 0 = c 0
  · have := hlowc s hs hsc hx0
    simp only [cross2, PiLp.sub_apply, hx0, sub_self, mul_zero, sub_zero]
    exact mul_pos (by linarith) (by linarith)
  by_cases hx1 : s 0 = c' 0
  · have := hlowc' s hs hsc' hx1
    have e : cross2 (c' - c) (s - c) = (c' 0 - c 0) * (s 1 - c' 1) := by
      simp only [cross2, PiLp.sub_apply, hx1]; ring
    rw [e]; exact mul_pos (by linarith) (by linarith)
  by_contra hneg
  push Not at hneg
  have hxs : s 0 ≠ c 0 := hx0
  have hxs' : s 0 ≠ c' 0 := hx1
  rcases lt_or_gt_of_ne hxs with h1 | h1
  · -- `s` left of `c`: then `c` is between `[s, c']` and the chord
    have hcA : c ≠ A := by rintro rfl; linarith [hAmin s hs]
    have hcB : c ≠ B := by rintro rfl; linarith [hBmax c' hc']
    have hsc'x : s 0 < c' 0 := by linarith
    have habove : 0 ≤ cross2 (c' - s) (c - s) := by
      have : cross2 (c' - s) (c - s) = -cross2 (c' - c) (s - c) := by
        simp only [cross2, PiLp.sub_apply]; ring
      linarith
    exact hS.not_mem_hull4 hc hs hc' hA hB hsc.symm (by rintro rfl; exact lt_irrefl _ hcc') hcA hcB
      (mem_convexHull_of_between hsc'x h1.le hcc'.le hAB (hAmin c hc) (hBmax c hc) habove hcL)
  · rcases lt_or_gt_of_ne hxs' with h2 | h2
    · -- `s` strictly between: it is above the chord, so between the chord and `[c, c']`
      have hsA : s ≠ A := by rintro rfl; linarith [hAmin c hc]
      have hsB : s ≠ B := by rintro rfl; linarith [hBmax c' hc']
      have hup := hcons s hs h1 h2
      exact hS.not_mem_hull4 hs hA hB hc hc' hsA hsB hsc hsc'
        (mem_convexHull_of_between hAB (hAmin s hs) (hBmax s hs) hcc' h1.le h2.le hup.le hneg)
    · -- `s` right of `c'`: then `c'` is between `[c, s]` and the chord
      have hc'A : c' ≠ A := by rintro rfl; linarith [hAmin c hc]
      have hc'B : c' ≠ B := by rintro rfl; linarith [hBmax s hs]
      have hcs : c 0 < s 0 := by linarith
      have habove : 0 ≤ cross2 (s - c) (c' - c) := by
        have : cross2 (s - c) (c' - c) = -cross2 (c' - c) (s - c) := by
          simp only [cross2, PiLp.sub_apply]; ring
        linarith
      exact hS.not_mem_hull4 hc' hc hs hA hB (by rintro rfl; exact lt_irrefl _ hcc') hsc'.symm hc'A hc'B
        (mem_convexHull_of_between hcs hcc'.le h2.le hAB (hAmin c' hc') (hBmax c' hc') habove hc'L)

theorem cross2_pos_of_consecutive {S : Finset ℝ²} (hS : ConvPos S)
    (hinj : Set.InjOn (fun s : ℝ² => s 0) S) {A B c c' s : ℝ²}
    (hA : A ∈ S) (hB : B ∈ S) (hAmin : ∀ y ∈ S, A 0 ≤ y 0) (hBmax : ∀ y ∈ S, y 0 ≤ B 0)
    (hAB : A 0 < B 0) (hc : c ∈ S) (hc' : c' ∈ S) (hcc' : c 0 < c' 0)
    (hcL : cross2 (B - A) (c - A) ≤ 0) (hc'L : cross2 (B - A) (c' - A) ≤ 0)
    (hcons : ∀ y ∈ S, c 0 < y 0 → y 0 < c' 0 → 0 < cross2 (B - A) (y - A))
    (hs : s ∈ S) (hsc : s ≠ c) (hsc' : s ≠ c') :
    0 < cross2 (c' - c) (s - c) :=
  cross2_pos_of_consecutive' hS hA hB hAmin hBmax hAB hc hc' hcc' hcL hc'L hcons
    (fun _ hy hne he => absurd (hinj hy hc he) hne)
    (fun _ hy hne he => absurd (hinj hy hc' he) hne) hs hsc hsc'

/-- **The lower chain as a sequence.**  For a planar set `S` with distinct `x`
and `x`-extremes `A ≠ B`: the points on or below the chord `AB`, sorted by `x`,
form a sequence `c : Fin n → ℝ²` from `A` to `B`, strictly increasing in `x`,
with no point of `S` on or below the chord strictly between two consecutive
ones. -/
theorem exists_lowerChain' {S : Finset ℝ²} {A B : ℝ²}
    (hinj : Set.InjOn (fun s : ℝ² => s 0) (S.filter fun s => cross2 (B - A) (s - A) ≤ 0)) (hA : A ∈ S) (hB : B ∈ S) (hAmin : ∀ y ∈ S, A 0 ≤ y 0)
    (hBmax : ∀ y ∈ S, y 0 ≤ B 0) (hAB : A 0 < B 0) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ², ∃ h2 : 2 ≤ n,
      c ⟨0, by omega⟩ = A ∧ c ⟨n - 1, by omega⟩ = B ∧
      (∀ i, c i ∈ S) ∧ (∀ i, cross2 (B - A) (c i - A) ≤ 0) ∧
      (∀ i j : Fin n, i < j → c i 0 < c j 0) ∧
      (∀ i : Fin n, ∀ h : i.val + 1 < n, ∀ y ∈ S, c i 0 < y 0 → y 0 < c ⟨i.val + 1, h⟩ 0 →
        0 < cross2 (B - A) (y - A)) := by
  classical
  set L := S.filter (fun s => cross2 (B - A) (s - A) ≤ 0) with hL
  have hLS : L ⊆ S := filter_subset _ _
  have hAL : A ∈ L := mem_filter.mpr ⟨hA, by simp [cross2]⟩
  have hBL : B ∈ L := mem_filter.mpr ⟨hB, by simp [cross2]; ring_nf; rfl⟩
  set T := L.image (fun s : ℝ² => s 0) with hT
  have hinjL : Set.InjOn (fun s : ℝ² => s 0) L := hinj
  have hcard : T.card = L.card := card_image_of_injOn hinjL
  set n := T.card with hn
  have hAB' : A ≠ B := by rintro rfl; exact lt_irrefl _ hAB
  have h2 : 2 ≤ n := by
    rw [hcard]
    exact one_lt_card.mpr ⟨A, hAL, B, hBL, hAB'⟩
  set e := T.orderEmbOfFin rfl
  have heT : ∀ i, e i ∈ T := fun i => orderEmbOfFin_mem T rfl i
  have hpre : ∀ i, ∃ s ∈ L, s 0 = e i := fun i => by simpa [hT] using heT i
  set c : Fin n → ℝ² := fun i => (hpre i).choose
  have hcL : ∀ i, c i ∈ L := fun i => (hpre i).choose_spec.1
  have hcx : ∀ i, c i 0 = e i := fun i => (hpre i).choose_spec.2
  have hsurj : ∀ t ∈ T, ∃ j, e j = t := fun t ht => by
    have : t ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact ht
    exact this
  have hidx : ∀ s ∈ L, ∃ j, c j = s := fun s hs => by
    obtain ⟨j, hj⟩ := hsurj (s 0) (mem_image_of_mem _ hs)
    exact ⟨j, hinjL (hcL j) hs (by simp only; rw [hcx, hj])⟩
  -- the extremes
  have hmin : ∀ j, A 0 ≤ c j 0 := fun j => hAmin _ (hLS (hcL j))
  have hmax : ∀ j, c j 0 ≤ B 0 := fun j => hBmax _ (hLS (hcL j))
  refine ⟨n, c, h2, ?_, ?_, fun i => hLS (hcL i), fun i => (mem_filter.mp (hcL i)).2,
    fun i j hij => by rw [hcx, hcx]; exact e.strictMono hij, ?_⟩
  · obtain ⟨j, hj⟩ := hidx A hAL
    by_cases hj0 : j = ⟨0, by omega⟩
    · rw [← hj0, hj]
    · exfalso
      have : (⟨0, by omega⟩ : Fin n) < j := lt_of_le_of_ne (Fin.le_def.mpr (Nat.zero_le _)) (Ne.symm hj0)
      have := e.strictMono this
      rw [← hcx, ← hcx, hj] at this
      linarith [hmin ⟨0, by omega⟩]
  · obtain ⟨j, hj⟩ := hidx B hBL
    by_cases hj0 : j = ⟨n - 1, by omega⟩
    · rw [← hj0, hj]
    · exfalso
      have : j < (⟨n - 1, by omega⟩ : Fin n) :=
        lt_of_le_of_ne (Fin.le_def.mpr (by simp; omega)) hj0
      have := e.strictMono this
      rw [← hcx, ← hcx, hj] at this
      linarith [hmax ⟨n - 1, by omega⟩]
  · intro i hi y hy h1 h2'
    by_contra hneg
    push Not at hneg
    have hyL : y ∈ L := mem_filter.mpr ⟨hy, hneg⟩
    obtain ⟨j, hj⟩ := hidx y hyL
    rw [← hj, hcx, hcx] at h1 h2'
    have a1 := e.strictMono.lt_iff_lt.mp h1
    have a2 := e.strictMono.lt_iff_lt.mp h2'
    rw [Fin.lt_def] at a1 a2
    simp at a2
    omega

theorem exists_lowerChain {S : Finset ℝ²} (hinj : Set.InjOn (fun s : ℝ² => s 0) S)
    {A B : ℝ²} (hA : A ∈ S) (hB : B ∈ S) (hAmin : ∀ y ∈ S, A 0 ≤ y 0)
    (hBmax : ∀ y ∈ S, y 0 ≤ B 0) (hAB : A 0 < B 0) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ², ∃ h2 : 2 ≤ n,
      c ⟨0, by omega⟩ = A ∧ c ⟨n - 1, by omega⟩ = B ∧
      (∀ i, c i ∈ S) ∧ (∀ i, cross2 (B - A) (c i - A) ≤ 0) ∧
      (∀ i j : Fin n, i < j → c i 0 < c j 0) ∧
      (∀ i : Fin n, ∀ h : i.val + 1 < n, ∀ y ∈ S, c i 0 < y 0 → y 0 < c ⟨i.val + 1, h⟩ 0 →
        0 < cross2 (B - A) (y - A)) :=
  exists_lowerChain' (hinj.mono (fun _ hx => (mem_filter.mp hx).1)) hA hB hAmin hBmax hAB

/-- **Chain convexity.**  For three `x`-increasing points with the third
strictly left of the first two, the middle one is below the larger of the
outer `y`. -/
theorem y_lt_max_of_cross2 {a b c : ℝ²} (hab : a 0 < b 0) (hbc : b 0 < c 0)
    (h : 0 < cross2 (b - a) (c - a)) : b 1 < max (a 1) (c 1) := by
  simp only [cross2, PiLp.sub_apply] at h
  by_contra hc
  push Not at hc
  have h1 := (max_le_iff.mp hc).1
  have h2 := (max_le_iff.mp hc).2
  nlinarith

end Minimality

end
