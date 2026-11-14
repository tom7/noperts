module

public import Minimality.FaceCircleW
public import Minimality.TieMerge

@[expose] public section

/-!
# Lemma LC (the level chord)

On the circle of a face `F` (views `u₀` in `F`'s plane, `F` edge-on), take the view `u₀` where
the two chord ends `A = x 0`, `B = x 1` have equal depth.  On the side of the circle where the rest
of `F` is hidden, the rim is `A, B ++ R` (the closed corner cycle `Γ` of Lemma W′, the rim of
`conv (V \ F⁰)`), with the rim edge `A → B` an edge of `F`.  If the cycle with the chord merged into
one entry (`skipAt z 0`: `A` deleted, `B` carrying the common level) is strictly unimodal, then a
tilt that leaves the plane on the hidden side and moves along the circle in the direction that
continues the step `x (-1) → A` gives a strictly unimodal rim, so `V` is Rupert.  This is the
level-chord lemma LC of k1c/M4PROOF.md §1.1 (both cases (i), (ii) of its proof are the one
condition of Lemma TA's core `isCyclicUnimodal_of_tieMerge`).

* `isRupert_levelChord'`: tilt form (any tilt `v`; rows `TiltSignS σ` at `(u₀, v)`, the chain edge
  `A → B` by `tiltSignS_edge`).
* `isRupert_levelChord`: rows strict at `u₀` (`u₀` is not an event of the rim `A, B ++ R`), the
  other points of `F`'s plane strictly on one side of `AB`; the tilt is constructed.
* `isRupert_levelChord_four`: Corollary LC4, a 4-rim at the chord-tie view: distinct merged
  values suffice.
* `CU_levelChord_iff` (combinatorial form, Lemma W′ vocabulary): at regular views next to the tie,
  with both chord ends in the gap of `R` of the common level `ζ`, the closed corner cycle
  `a :: c :: R` is unimodal iff `ζ :: R` is and the ends are not ordered against the step through
  the chord (when `ζ` is a peak or valley of `ζ :: R`, both orders work).  Helpers:
  `CU_cons_iff_of_gap` (moving the head within its gap), `not_CU_bad` (the wrong order: two peaks).
* `levelChord_works`: with Lemma W′, the circle works there when `lo` or `hi` is an end (a triangle).

Not here: the converse of the geometric statement, and chord ties of longer chains (a quad `F`
whose chord ends are not adjacent in `F`), where the tie is not adjacent on the rim.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

lemma injective_getD_of_nodup {L : List ℝ} {k : ℕ} [NeZero k] (hk : L.length = k)
    (h : L.Nodup) : Function.Injective (fun i : ZMod k => L.getD i.val 0) := by
  subst hk
  intro i j hij
  apply ZMod.val_injective
  have hi := i.val_lt
  have hj := j.val_lt
  simp only [List.getD_eq_getElem?_getD] at hij
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hij
  simpa [h.getElem_inj_iff] using hij

lemma getD_cons_mem_tail {x : ℝ} {R : List ℝ} {i : ℕ} (hi : i < R.length + 1) (h0 : i ≠ 0) :
    (x :: R).getD i 0 ∈ R := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

/-- Replacing the head `x` of a cycle `x :: R` by `y` in the same gap of `R` keeps cyclic
unimodality. -/
lemma CU_cons_of_gap {x y : ℝ} {R : List ℝ} (hy : (y :: R).Nodup)
    (hxy : ∀ r ∈ R, (r < x ↔ r < y)) (h : CU (x :: R)) : CU (y :: R) := by
  have hl : (x :: R).length = R.length + 1 := rfl
  have hl' : (y :: R).length = R.length + 1 := rfl
  rw [CU_iff_of_length hl] at h
  rw [CU_iff_of_length hl']
  have hyR : y ∉ R := (List.nodup_cons.mp hy).1
  refine isCyclicUnimodal_of_refine h (injective_getD_of_nodup hl' hy) fun p q hpq => ?_
  have hp := p.val_lt
  have hq := q.val_lt
  by_cases hp0 : p.val = 0 <;> by_cases hq0 : q.val = 0
  · rw [hp0, hq0] at hpq ⊢; exact absurd hpq (lt_irrefl _)
  · have hm := getD_cons_mem_tail (x := x) hq hq0
    have hm' := getD_cons_mem_tail (x := y) hq hq0
    rw [hp0] at hpq ⊢
    simp only [List.getD_cons_zero] at hpq ⊢
    have e : (x :: R).getD q.val 0 = (y :: R).getD q.val 0 := by
      obtain ⟨j, hj⟩ : ∃ j, q.val = j + 1 := ⟨q.val - 1, by omega⟩
      rw [hj]; simp
    rw [e] at hpq hm
    have h1 := (hxy _ hm).not.mp (not_lt.mpr hpq.le)
    rcases lt_or_eq_of_le (not_lt.mp h1) with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hm) hyR
  · have hm := getD_cons_mem_tail (x := x) hp hp0
    rw [hq0] at hpq ⊢
    simp only [List.getD_cons_zero] at hpq ⊢
    have e : (x :: R).getD p.val 0 = (y :: R).getD p.val 0 := by
      obtain ⟨j, hj⟩ : ∃ j, p.val = j + 1 := ⟨p.val - 1, by omega⟩
      rw [hj]; simp
    rw [e] at hpq hm
    exact (hxy _ hm).mp hpq
  · obtain ⟨j, hj⟩ : ∃ j, p.val = j + 1 := ⟨p.val - 1, by omega⟩
    obtain ⟨l, hl⟩ : ∃ l, q.val = l + 1 := ⟨q.val - 1, by omega⟩
    rw [hj, hl] at hpq ⊢
    simpa using hpq

lemma CU_cons_iff_of_gap {x y : ℝ} {R : List ℝ} (hx : (x :: R).Nodup) (hy : (y :: R).Nodup)
    (hxy : ∀ r ∈ R, (r < x ↔ r < y)) : CU (x :: R) ↔ CU (y :: R) :=
  ⟨CU_cons_of_gap hy hxy, CU_cons_of_gap hx fun r hr => (hxy r hr).symm⟩


lemma gap_lt_of_iff {r x y : ℝ} (h : r < x ↔ r < y) (hx : x ≠ r) :
    (r < y → r < x) ∧ (y < r → x < r) := by
  refine ⟨h.mpr, fun hy => ?_⟩
  rcases lt_trichotomy r x with h1 | h1 | h1
  · exact absurd (h.mp h1) (not_lt.mpr hy.le)
  · exact absurd h1.symm hx
  · exact h1

/-- The bad tie-breaks: the chord ends `a`, `c` in the gap `(p, q)` of the neighbours but ordered
against the step, i.e. `a` a peak and `c` a valley (or the mirror image): two peaks. -/
lemma not_CU_bad {a c : ℝ} {R : List ℝ} (hR : R ≠ []) (hnd : (a :: c :: R).Nodup)
    (hb : (R.getLastD a < c ∧ c < a ∧ a < R.headD a) ∨ (R.headD a < a ∧ a < c ∧ c < R.getLastD a)) :
    ¬ CU (a :: c :: R) := by
  have hlen : (a :: c :: R).length = R.length + 1 + 1 := by simp
  have hR1 : 1 ≤ R.length := List.length_pos_iff.mpr hR
  rw [CU_iff_of_length hlen, isCyclicUnimodal_iff_numPeaks]
  set w : ZMod (R.length + 1 + 1) → ℝ := fun i => (a :: c :: R).getD i.val 0 with hw
  have hinj : Function.Injective w := injective_getD_of_nodup hlen hnd
  have hsinj : Function.Injective (skipAt w 0) := hinj.comp (phi_inj 0)
  have : Fact (1 < R.length + 1 + 1) := ⟨by omega⟩
  have v0 : w 0 = a := by simp [hw]
  have v1 : w (0 + 1) = c := by simp [hw, ZMod.val_one]
  have v2 : w (0 + 1 + 1) = R.headD a := by
    have e : (0 + 1 + 1 : ZMod (R.length + 1 + 1)) = ((2 : ℕ) : ZMod _) := by push_cast; ring
    simp only [hw, e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 2 < R.length + 1 + 1)]
    rcases R with _ | ⟨x, L⟩
    · exact absurd rfl hR
    · simp
  have vm : w (0 - 1) = R.getLastD a := by
    show (a :: c :: R).getD ((0 - 1 : ZMod (R.length + 1 + 1)).val) 0 = _
    rw [zero_sub, ZMod.val_neg_one]
    simp only [List.getD_cons_succ]
    rcases R.eq_nil_or_concat with h | ⟨L, x, rfl⟩
    · exact absurd h hR
    · simp [List.getD_eq_getElem?_getD]
  have hge := one_le_numPeaks (by omega : 2 ≤ R.length + 1) hsinj
  rintro ⟨-, h1⟩
  rcases hb with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
  · have key := numPeaks_skipAt_high (by omega : 2 ≤ R.length + 1) (z := w) (i := 0)
      (by rw [vm, v1]; exact b1) (by rw [v1, v0]; exact b2)
    rw [v2, v1, ite_eq_right (by linarith)] at key
    omega
  · have key := numPeaks_skipAt_low' (by omega : 2 ≤ R.length + 1) (z := w) (i := 0)
      (by rw [vm, v1]; exact b3) (by rw [v1, v0]; exact b2)
    rw [v2, v1, ite_eq_left (by linarith)] at key
    omega

/-- **Lemma LC, combinatorial form (closed corner cycle).**  The closed corner cycle
`Γ = a :: c :: R` of Lemma W′ (chord ends `A`, `B` with depths `a ≠ c`, corners `R ≠ []`) next to
the chord-tie view: both ends lie in the gap of `R` of the common level `ζ` (`hgap`).  Then `Γ` is
cyclically unimodal iff the merged cycle `ζ :: R` is and the ends are not ordered against the step
through the chord: if `ζ` lies strictly between its neighbours `p = R.getLastD ζ` (before `A`) and
`q = R.headD ζ` (after `B`), `A` must lie on `p`'s side of `B`.  When `ζ` is a peak or valley of
the merged cycle, both orders work (M4PROOF §1.1, case (ii)). -/
theorem CU_levelChord_iff {a c ζ : ℝ} {R : List ℝ} (hR : R ≠ []) (hnd : (ζ :: R).Nodup)
    (hac : a ≠ c) (haR : a ∉ R) (hcR : c ∉ R)
    (hgap : ∀ r ∈ R, (r < a ↔ r < ζ) ∧ (r < c ↔ r < ζ)) :
    CU (a :: c :: R) ↔ CU (ζ :: R) ∧ ¬ (R.getLastD ζ < ζ ∧ ζ < R.headD ζ ∧ c < a) ∧
      ¬ (R.headD ζ < ζ ∧ ζ < R.getLastD ζ ∧ a < c) := by
  have hRnd : R.Nodup := (List.nodup_cons.mp hnd).2
  have hζR : ζ ∉ R := (List.nodup_cons.mp hnd).1
  have haRnd : (a :: R).Nodup := List.nodup_cons.mpr ⟨haR, hRnd⟩
  have hcRnd : (c :: R).Nodup := List.nodup_cons.mpr ⟨hcR, hRnd⟩
  have hacR : (a :: c :: R).Nodup := List.nodup_cons.mpr ⟨by simp [hac, haR], hcRnd⟩
  have hgA : CU (a :: R) ↔ CU (ζ :: R) := CU_cons_iff_of_gap haRnd hnd fun r hr => (hgap r hr).1
  have hgC : CU (c :: R) ↔ CU (ζ :: R) := CU_cons_iff_of_gap hcRnd hnd fun r hr => (hgap r hr).2
  obtain ⟨q, t, rfl⟩ : ∃ q t, R = q :: t := by
    rcases R with _ | ⟨q, t⟩
    · exact absurd rfl hR
    · exact ⟨q, t, rfl⟩
  have hhead : ∀ d : ℝ, (q :: t).headD d = q := fun d => rfl
  obtain ⟨p, hpR, hlast⟩ : ∃ p ∈ q :: t, ∀ d : ℝ, (q :: t).getLastD d = p := by
    rcases (q :: t).eq_nil_or_concat with h | ⟨L, x, hL⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · exact ⟨x, by rw [hL]; simp, fun d => by rw [hL]; simp⟩
  simp only [hhead, hlast]
  -- deleting `a` or `c`
  have del_a : (p < a ∧ a < c) ∨ (c < a ∧ a < p) → (CU (a :: c :: q :: t) ↔ CU (c :: q :: t)) := by
    intro hb
    refine CU_cons_iff a (c :: q :: t) (by simp) hacR ?_
    have e1 : (c :: q :: t).getD ((c :: q :: t).length - 1) 0 = p := by
      rw [← hlast 0]
      rcases (q :: t).eq_nil_or_concat with h | ⟨L, x, hL⟩
      · exact absurd h (List.cons_ne_nil _ _)
      · rw [hL]; simp [List.getD_eq_getElem?_getD]
    rw [e1]
    simpa using hb
  have del_c : (a < c ∧ c < q) ∨ (q < c ∧ c < a) → (CU (a :: c :: q :: t) ↔ CU (a :: q :: t)) := by
    intro hb
    simpa using CU_del_mid [] a c q t (by simpa using hacR) hb
  -- the gap facts at `p` and `q`
  have hqm : q ∈ q :: t := List.mem_cons_self
  obtain ⟨pa1, pa2⟩ := gap_lt_of_iff (hgap p hpR).1 (fun e => haR (e ▸ hpR))
  obtain ⟨pc1, pc2⟩ := gap_lt_of_iff (hgap p hpR).2 (fun e => hcR (e ▸ hpR))
  obtain ⟨qa1, qa2⟩ := gap_lt_of_iff (hgap q hqm).1 (fun e => haR (e ▸ hqm))
  obtain ⟨qc1, qc2⟩ := gap_lt_of_iff (hgap q hqm).2 (fun e => hcR (e ▸ hqm))
  have hpζ : p ≠ ζ := fun e => hζR (e ▸ hpR)
  have hqζ : q ≠ ζ := fun e => hζR (e ▸ hqm)
  have bad := not_CU_bad (a := a) (c := c) (R := q :: t) (List.cons_ne_nil _ _) hacR
  simp only [hhead, hlast] at bad
  rcases lt_or_gt_of_ne hpζ with hp | hp <;> rcases lt_or_gt_of_ne hqζ with hq | hq <;>
    rcases lt_or_gt_of_ne hac with h | h
  · rw [del_a (Or.inl ⟨pa1 hp, h⟩), hgC]; exact ⟨fun hh => ⟨hh, by rintro ⟨h1, h2, h3⟩; linarith, by rintro ⟨h1, h2, h3⟩; linarith⟩,
      fun hh => hh.1⟩
  · rw [del_c (Or.inr ⟨qc1 hq, h⟩), hgA]; exact ⟨fun hh => ⟨hh, by rintro ⟨h1, h2, h3⟩; linarith, by rintro ⟨h1, h2, h3⟩; linarith⟩,
      fun hh => hh.1⟩
  · rw [del_a (Or.inl ⟨pa1 hp, h⟩), hgC]; exact ⟨fun hh => ⟨hh, by rintro ⟨h1, h2, h3⟩; linarith, by rintro ⟨h1, h2, h3⟩; linarith⟩,
      fun hh => hh.1⟩
  · exact iff_of_false (bad (Or.inl ⟨pc1 hp, h, qa2 hq⟩)) (fun hh => hh.2.1 ⟨hp, hq, h⟩)
  · exact iff_of_false (bad (Or.inr ⟨qa1 hq, h, pc2 hp⟩)) (fun hh => hh.2.2 ⟨hq, hp, h⟩)
  · rw [del_a (Or.inr ⟨h, pa2 hp⟩), hgC]; exact ⟨fun hh => ⟨hh, by rintro ⟨h1, h2, h3⟩; linarith, by rintro ⟨h1, h2, h3⟩; linarith⟩,
      fun hh => hh.1⟩
  · rw [del_c (Or.inl ⟨h, qc2 hq⟩), hgA]; exact ⟨fun hh => ⟨hh, by rintro ⟨h1, h2, h3⟩; linarith, by rintro ⟨h1, h2, h3⟩; linarith⟩,
      fun hh => hh.1⟩
  · rw [del_a (Or.inr ⟨h, pa2 hp⟩), hgC]; exact ⟨fun hh => ⟨hh, by rintro ⟨h1, h2, h3⟩; linarith, by rintro ⟨h1, h2, h3⟩; linarith⟩,
      fun hh => hh.1⟩


/-- **Lemma LC with Lemma W′ (a triangle face).**  Next to the chord-tie view, with the hypotheses
of `CU_levelChord_iff`, the merged cycle unimodal and the ends ordered with the step, and `lo`,
`hi` the lowest and highest depths of `F` with one of them an end (always so when `F` is a
triangle): `F`'s circle works, i.e. the lower or the upper skeleton is cyclically unimodal. -/
theorem levelChord_works {a c ζ lo hi : ℝ} {R : List ℝ} (hR : R ≠ []) (hnd : (ζ :: R).Nodup)
    (hac : a ≠ c) (haR : a ∉ R) (hcR : c ∉ R)
    (hgap : ∀ r ∈ R, (r < a ↔ r < ζ) ∧ (r < c ↔ r < ζ)) (hU : CU (ζ :: R))
    (hs1 : ¬ (R.getLastD ζ < ζ ∧ ζ < R.headD ζ ∧ c < a))
    (hs2 : ¬ (R.headD ζ < ζ ∧ ζ < R.getLastD ζ ∧ a < c))
    (hla : lo ≤ a) (hlc : lo ≤ c) (hha : a ≤ hi) (hhc : c ≤ hi) (hloR : lo ∉ R) (hhiR : hi ∉ R)
    (hf : lo = a ∨ lo = c ∨ hi = a ∨ hi = c) :
    CU (skel1 a lo c ++ R) ∨ CU (skel1 a hi c ++ R) := by
  have hacR : (a :: c :: R).Nodup :=
    List.nodup_cons.mpr ⟨by simp [hac, haR], List.nodup_cons.mpr ⟨hcR, (List.nodup_cons.mp hnd).2⟩⟩
  exact (lemmaW' hacR hla hlc hha hhc hloR hhiR).mpr
    ⟨(CU_levelChord_iff hR hnd hac haR hcR hgap).mpr ⟨hU, hs1, hs2⟩, Or.inr hf⟩

/-- With the merged cycle `skipAt z 0` injective, the tie `z 0 = z 1` and `x 0 ≠ x 1`, the rim
`x` is injective. -/
lemma injective_of_skipAt_tie {m : ℕ} [NeZero m] {x : ZMod (m + 1) → ℝ³} {u₀ : ℝ³}
    (hU : Function.Injective (skipAt (fun i => ⟪x i, u₀⟫) 0))
    (htie : ⟪x 0, u₀⟫ = ⟪x 1, u₀⟫) (h01 : x 0 ≠ x 1) : Function.Injective x := by
  have hz : ∀ p q : ZMod (m + 1), p ≠ 0 → q ≠ 0 → ⟪x p, u₀⟫ = ⟪x q, u₀⟫ → p = q := by
    intro p q hp hq hpq
    obtain ⟨p', rfl⟩ := phi_surj 0 p hp
    obtain ⟨q', rfl⟩ := phi_surj 0 q hq
    exact congrArg (phi 0) (hU hpq)
  have h1 : (1 : ZMod (m + 1)) ≠ 0 := by
    have : Fact (1 < m + 1) := ⟨by have := NeZero.pos m; omega⟩
    exact one_ne_zero
  have h0 : ∀ q : ZMod (m + 1), q ≠ 0 → x 0 = x q → False := by
    intro q hq hx
    have hq1 : q = 1 := hz q 1 hq h1 (by rw [← hx, htie])
    exact h01 (hq1 ▸ hx)
  intro p q hpq
  by_cases hp : p = 0 <;> by_cases hq : q = 0
  · rw [hp, hq]
  · exact (h0 q hq (hp ▸ hpq)).elim
  · exact (h0 p hp (hq ▸ hpq.symm)).elim
  · exact hz p q hp hq (by rw [hpq])

/-- **Lemma LC, tilt form.**  `F` is a face in the plane `⟪n, ·⟫ = h` with `V` on its closed
negative side; the view `u₀` is parallel to the plane.  The rim is a cycle `x` of `N + 1 ≥ 3`
points of `V` whose first edge `A = x 0 → B = x 1` is an edge of `F` (both ends in the plane,
`hdir` its direction on the screen line, `hchain` the other points of the plane on the
`σ⟪n, v⟫`-positive side), the other rows are `TiltSignS σ` tests at `(u₀, v)`.  At `u₀` the chord
ends have equal depth (`htie`), the cycle with the chord merged (`skipAt z 0`) is cyclically
unimodal, and `v` orders `A`, `B` so that `A` continues the step from `x (-1)`.  Then `V` is
Rupert. -/
theorem isRupert_levelChord' (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hA : ⟪n, x 0⟫ = h) (hB : ⟪n, x 1⟫ = h)
    (hdir : 0 < σ * det3 n (x 1 - x 0) u₀)
    (hchain : ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x 0 → y ≠ x 1 →
      0 < σ * ⟪n, v⟫ * det3 (x 1 - x 0) (y - x 0) n)
    (hR : ∀ i : ZMod (N + 1), i ≠ 0 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (htie : ⟪x 0, u₀⟫ = ⟪x 1, u₀⟫)
    (hU : IsCyclicUnimodal (skipAt (fun i => ⟪x i, u₀⟫) 0))
    (hv : (⟪x (-1), u₀⟫ < ⟪x 0, u₀⟫ ∧ 0 < ⟪x 1 - x 0, v⟫) ∨
      (⟪x 0, u₀⟫ < ⟪x (-1), u₀⟫ ∧ ⟪x 1 - x 0, v⟫ < 0)) : IsRupert V := by
  set z₀ : ZMod (N + 1) → ℝ := fun i => ⟪x i, u₀⟫ with hz₀
  have key : ∀ i, ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v := by
    intro i y hy hyi hyi1
    by_cases hi : i = 0
    · subst hi
      rw [zero_add] at hyi1 ⊢
      exact tiltSignS_edge hn hu hA hB (hV y hy) hdir (fun heq => hchain y hy heq hyi hyi1)
    · exact hR i hi y hy hyi hyi1
  have h01 : x 0 ≠ x 1 := by
    intro e
    rw [← e, sub_self] at hdir
    simp [det3_expand] at hdir
  have hxinj := injective_of_skipAt_tie hU.1 htie h01
  have e1 : ∀ (ε : ℝ) (p : ℝ³), ⟪p, u₀ + ε • v⟫ = ⟪p, u₀⟫ + ε * ⟪p, v⟫ := by
    intro ε p; rw [inner_add_right, inner_smul_right]
  refine isRupert_of_tilted_unimodal_σ V u₀ v hu₀ (by omega) x hxV σ hσ
    (fun i j hj1 hj2 => key i (x j) (hxV j) (fun e => hj1 (hxinj e)) (fun e => hj2 (hxinj e)))
    (fun y hy hyx i => key i y hy (hyx i) (hyx (i + 1)))
    (TieMergeQ z₀ 0) (isOpen_tieMergeQ z₀ 0) ?_ ?_ ?_
  · rintro z c hc ⟨h1, h2⟩
    refine ⟨fun p q h => mul_lt_mul_of_pos_left (h1 p q h) hc, ?_⟩
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨h3, mul_lt_mul_of_pos_left h4 hc⟩
    · exact Or.inr ⟨h3, mul_lt_mul_of_pos_left h4 hc⟩
  · have hpair : ∀ p q : ZMod (N + 1), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        z₀ p < z₀ q → ⟪x p, u₀ + ε • v⟫ < ⟪x q, u₀ + ε • v⟫ := by
      intro p q
      by_cases h : z₀ p < z₀ q
      · have := eventually_pos_affine (A := z₀ q - z₀ p) (B := ⟪x q, v⟫ - ⟪x p, v⟫)
          (Or.inl (sub_pos.2 h))
        filter_upwards [this] with ε hε _
        rw [e1, e1]; simp only [hz₀] at hε; nlinarith
      · exact Eventually.of_forall fun _ h' => absurd h' h
    have hall := eventually_all.2 fun p => eventually_all.2 fun q => hpair p q
    have hd : ∀ ε : ℝ, ⟪x (0 + 1), u₀ + ε • v⟫ - ⟪x 0, u₀ + ε • v⟫ =
        ε * ⟪x 1 - x 0, v⟫ := by
      intro ε; rw [zero_add, e1, e1, ← htie, inner_sub_left]; ring
    have em : (0 : ZMod (N + 1)) - 1 = -1 := by ring
    rcases hv with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · filter_upwards [hall, self_mem_nhdsWithin] with ε hε hε0
      refine ⟨hε, Or.inl ⟨by simpa [hz₀, em] using h3, ?_⟩⟩
      have := hd ε
      have : 0 < ε * ⟪x 1 - x 0, v⟫ := mul_pos hε0 h4
      linarith
    · filter_upwards [hall, self_mem_nhdsWithin] with ε hε hε0
      refine ⟨hε, Or.inr ⟨by simpa [hz₀, em] using h3, ?_⟩⟩
      have := hd ε
      have : ε * ⟪x 1 - x 0, v⟫ < 0 := mul_neg_of_pos_of_neg hε0 h4
      linarith
  · rintro z hz ⟨h1, h2⟩
    exact isCyclicUnimodal_of_tieMerge hN hU hz h1 h2

/-- **Lemma LC (level chord, M4PROOF §1.1).**  The set-up of `isRupert_levelChord'` with all
rows strict at `u₀` (the rim `A, B ++ R` is strictly convex at the chord-tie view and every other
point is strictly inside: `u₀` is not an event) and the other points of `F`'s plane strictly on one
side of the edge `AB` (sign `s`).  If the chord ends have equal depth at `u₀` and the cycle with the
chord merged into one entry is cyclically unimodal, `V` is Rupert.  The tilt is
`v = σ s n ± (B - A)`: off the circle on the side where the rest of `F` is hidden, along the
circle in the direction where `A` continues the step from `x (-1)`. -/
theorem isRupert_levelChord (V : Finset ℝ³) (n u₀ : ℝ³) (h σ s : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hA : ⟪n, x 0⟫ = h) (hB : ⟪n, x 1⟫ = h)
    (hdir : 0 < σ * det3 n (x 1 - x 0) u₀)
    (hF : ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x 0 → y ≠ x 1 → 0 < s * det3 (x 1 - x 0) (y - x 0) n)
    (hR : ∀ i : ZMod (N + 1), i ≠ 0 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      0 < σ * det3 (x (i + 1) - x i) (y - x i) u₀)
    (htie : ⟪x 0, u₀⟫ = ⟪x 1, u₀⟫)
    (hU : IsCyclicUnimodal (skipAt (fun i => ⟪x i, u₀⟫) 0)) : IsRupert V := by
  have h01 : x 1 - x 0 ≠ 0 := by
    intro e
    rw [e] at hdir
    simp [det3_expand] at hdir
  have hd0 : ⟪n, x 1 - x 0⟫ = 0 := by rw [inner_sub_right, hA, hB, sub_self]
  have hN0 : 0 < ⟪n, n⟫ := real_inner_self_pos.2 hn
  have hD0 : 0 < ⟪x 1 - x 0, x 1 - x 0⟫ := real_inner_self_pos.2 h01
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hne : ⟪x (-1), u₀⟫ ≠ ⟪x 0, u₀⟫ := by
    have := skipAt_ne_ends hN (z := fun i => ⟪x i, u₀⟫) (a := 0) hU.1
    simp only [zero_add, zero_sub] at this
    rw [htie]; exact this.symm
  have hrow : ∀ v : ℝ³, ∀ i : ZMod (N + 1), i ≠ 0 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v :=
    fun v i hi y hy h1 h2 => Or.inl (hR i hi y hy h1 h2)
  have hnv : ∀ t : ℝ, ⟪n, (σ * s) • n + t • (x 1 - x 0)⟫ = σ * s * ⟪n, n⟫ := by
    intro t; rw [inner_add_right, inner_smul_right, inner_smul_right, hd0]; ring
  have hch : ∀ t : ℝ, ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x 0 → y ≠ x 1 →
      0 < σ * ⟪n, (σ * s) • n + t • (x 1 - x 0)⟫ * det3 (x 1 - x 0) (y - x 0) n := by
    intro t y hy hyh h1 h2
    rw [hnv]
    have := mul_pos hN0 (hF y hy hyh h1 h2)
    calc (0 : ℝ) < ⟪n, n⟫ * (s * det3 (x 1 - x 0) (y - x 0) n) := this
      _ = σ * (σ * s * ⟪n, n⟫) * det3 (x 1 - x 0) (y - x 0) n := by
        linear_combination (-(⟪n, n⟫ * s * det3 (x 1 - x 0) (y - x 0) n)) * hσ2
  have hBv : ∀ t : ℝ, ⟪x 1 - x 0, (σ * s) • n + t • (x 1 - x 0)⟫ =
      t * ⟪x 1 - x 0, x 1 - x 0⟫ := by
    intro t
    rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm, hd0]; ring
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact isRupert_levelChord' V n u₀ _ h σ hσ hn hu₀ hu hV hN x hxV hA hB hdir (hch 1)
      (hrow _) htie hU (Or.inl ⟨hlt, by rw [hBv]; linarith⟩)
  · exact isRupert_levelChord' V n u₀ _ h σ hσ hn hu₀ hu hV hN x hxV hA hB hdir (hch (-1))
      (hrow _) htie hU (Or.inr ⟨hgt, by rw [hBv]; linarith⟩)

/-- **Corollary LC4 (M4PROOF §1.2).**  A 4-rim `A, B, C, D` at the chord-tie view: the merged cycle
is a 3-cycle, so distinct merged values `z B, z C, z D` suffice. -/
theorem isRupert_levelChord_four (V : Finset ℝ³) (n u₀ : ℝ³) (h σ s : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    (x : ZMod 4 → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hA : ⟪n, x 0⟫ = h) (hB : ⟪n, x 1⟫ = h)
    (hdir : 0 < σ * det3 n (x 1 - x 0) u₀)
    (hF : ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x 0 → y ≠ x 1 → 0 < s * det3 (x 1 - x 0) (y - x 0) n)
    (hR : ∀ i : ZMod 4, i ≠ 0 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      0 < σ * det3 (x (i + 1) - x i) (y - x i) u₀)
    (htie : ⟪x 0, u₀⟫ = ⟪x 1, u₀⟫)
    (hdist : Function.Injective (skipAt (m := 3) (fun i => ⟪x i, u₀⟫) 0)) : IsRupert V :=
  isRupert_levelChord V n u₀ h σ s hσ hn hu₀ hu hV (N := 3) (by norm_num) x hxV hA hB hdir hF hR
    htie (isCyclicUnimodal_three hdist)

end Minimality

end
