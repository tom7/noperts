module

public import Minimality.TurnCalculus
public import Minimality.Generic.PV.FaceCircle

@[expose] public section

/-!
# Lemma W′ (the face-circle criterion)

At a regular view `u₀` on the circle of a face `F` (views in `F`'s plane, `F` edge-on), the rim
is `F`'s chord from `A` to `B` followed by the corners `R` (from `B` back to `A`).  The closed
corner cycle is `Γ = (A, B) ++ R`, with depths `a :: b :: R`.  `F`'s circle *works* at `u₀` if the
lower skeleton `C₊ = (A, lo, B) ++ R` or the upper skeleton `C₋ = (A, hi, B) ++ R` is cyclically
unimodal (`lo`, `hi` the lowest and highest depths of `F`, omitted when an end: `skel1`); by
Corollary FC (`isRupert_faceCircle_skelV` / `_skelL`) the views just off the circle on the
corresponding side then have a strictly unimodal rim, so `K` is Rupert.

* `numPeaks_skipAt_valley`, `numPeaks_skipAt_peak` (Lemma TC (ii) for an inserted valley / peak,
  both neighbours on one side): the exact change of κ.
* `CU_skel1_low_iff`: `C₊` is unimodal iff `Γ` is and (`lo` is an end or the lower end is a
  valley of `Γ`, `EndValley`).  `CU_skel1_high_iff`: the same for `C₋` with `hi` and `EndPeak`.
* `lemmaW'` (**Lemma W′**, f29c/draft.md §2): the circle works iff κ(Γ) = 1 and
  (E(Γ): `A` or `B` is a peak or valley of `Γ`, or f: `lo` or `hi` is an end).  Both directions;
  "works" is the skeleton condition above, as in the paper.
* `isRupert_faceCircle_W'_low`, `_high` (the "if" direction, geometric): the set-up of Corollary
  FC with the skeleton hypothesis replaced by Lemma W′'s condition for that side.

Not here: the converse of Corollary FC (a non-unimodal skeleton forces non-unimodal views next
to the circle); the paper's Lemma W′ does not claim it.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

section ins
variable {m : ℕ} [NeZero m]

/-- Inserting a valley `z i` (below both neighbours `z (i - 1) ≠ z (i + 1)`): κ rises exactly
when the lower neighbour is not a valley of the cycle without `z i`. -/
theorem numPeaks_skipAt_valley (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z i < z (i - 1)) (h2 : z i < z (i + 1)) (h3 : z (i - 1) ≠ z (i + 1)) :
    numPeaks z = numPeaks (skipAt z i) +
      ((if z (i - 1 - 1) < z (i - 1) ∧ z (i - 1) < z (i + 1) then 1 else 0) +
        (if z (i + 1 + 1) < z (i + 1) ∧ z (i + 1) < z (i - 1) then 1 else 0)) := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  rcases lt_or_gt_of_ne h3 with h3 | h3 <;>
  split_ifs at this ⊢ <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

/-- Inserting a peak `z i` (above both neighbours): κ rises by one unless one of the two
neighbours was a peak of the cycle without `z i`. -/
theorem numPeaks_skipAt_peak (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i - 1) < z i) (h2 : z (i + 1) < z i) :
    numPeaks z + ((if z (i - 1 - 1) < z (i - 1) ∧ z (i + 1) < z (i - 1) then 1 else 0) +
        (if z (i - 1) < z (i + 1) ∧ z (i + 1 + 1) < z (i + 1) then 1 else 0)) =
      numPeaks (skipAt z i) + 1 := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  split_ifs at this ⊢ <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

end ins

/-! ### Lemma W′ for lists -/

theorem CU_iff_of_length {l : List ℝ} {k : ℕ} [NeZero k] (hl : l.length = k) :
    CU l ↔ IsCyclicUnimodal (fun i : ZMod k => l.getD i.val 0) := by
  subst hl
  unfold CU CUn
  simp [NeZero.ne]

lemma skipAt_one_ins (a e b : ℝ) (R : List ℝ) :
    skipAt (fun i : ZMod (R.length + 2 + 1) => (a :: e :: b :: R).getD i.val 0) 1 =
      fun j : ZMod (R.length + 2) => (b :: R ++ [a]).getD j.val 0 := by
  funext j
  simp only [skipAt]
  have hj := j.val_lt
  have e1 : (1 + 1 + (j.val : ZMod (R.length + 2 + 1))) = ((j.val + 2 : ℕ) : ZMod _) := by
    push_cast; ring
  rw [e1, ZMod.val_natCast]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simpa using h)]
    simp
  · rw [h, show R.length + 1 + 2 = R.length + 2 + 1 by ring, Nat.mod_self]
    simp [List.getD_eq_getElem?_getD]

lemma ins_val_neg (a e b : ℝ) (R : List ℝ) :
    (a :: e :: b :: R).getD ((1 - 1 - 1 : ZMod (R.length + 2 + 1)).val) 0 = R.getLastD b := by
  rw [show (1 - 1 - 1 : ZMod (R.length + 2 + 1)) = -1 by ring, ZMod.val_neg_one]
  simp only [List.getD_cons_succ]
  rcases R.eq_nil_or_concat with h | ⟨L, x, rfl⟩
  · subst h; simp
  · simp [List.getD_eq_getElem?_getD]

lemma ins_val_three (a e b : ℝ) (R : List ℝ) :
    (a :: e :: b :: R).getD ((1 + 1 + 1 : ZMod (R.length + 2 + 1)).val) 0 = R.headD a := by
  rw [show (1 + 1 + 1 : ZMod (R.length + 2 + 1)) = ((3 : ℕ) : ZMod _) by push_cast; ring,
    ZMod.val_natCast]
  rcases R with _ | ⟨x, L⟩
  · simp
  · rw [Nat.mod_eq_of_lt (by simp)]; simp

lemma injective_ins {a e b : ℝ} {R : List ℝ} (h : (a :: e :: b :: R).Nodup) :
    Function.Injective (fun i : ZMod (R.length + 2 + 1) => (a :: e :: b :: R).getD i.val 0) := by
  intro i j hij
  apply ZMod.val_injective
  have hi := i.val_lt
  have hj := j.val_lt
  simp only [List.getD_eq_getElem?_getD] at hij
  rw [List.getElem?_eq_getElem (by simpa using hi),
    List.getElem?_eq_getElem (by simpa using hj)] at hij
  simpa [h.getElem_inj_iff] using hij

/-- In the closed corner cycle `Γ = a :: b :: R` (ends `A`, `B` with depths `a`, `b`, corners `R`
from `B` back to `A`), the lower of the two ends is a valley. `R.getLastD b` is the cyclic
predecessor of `a`, `R.headD a` the cyclic successor of `b`. -/
def EndValley (a b : ℝ) (R : List ℝ) : Prop :=
  (a < R.getLastD b ∧ a < b) ∨ (b < a ∧ b < R.headD a)

/-- In the closed corner cycle `Γ = a :: b :: R`, the higher of the two ends is a peak. -/
def EndPeak (a b : ℝ) (R : List ℝ) : Prop :=
  (R.getLastD b < a ∧ b < a) ∨ (a < b ∧ R.headD a < b)

lemma valley_ind_iff {a b p q : ℝ} (hab : a ≠ b) (hp : p ≠ a) (hq : q ≠ b) :
    ((if p < a ∧ a < b then 1 else 0) + (if q < b ∧ b < a then 1 else 0) = (0 : ℕ)) ↔
      ((a < p ∧ a < b) ∨ (b < a ∧ b < q)) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hp with h2 | h2 <;>
    rcases lt_or_gt_of_ne hq with h3 | h3 <;>
    split_ifs <;> constructor <;> intro hh <;>
    first | omega | (exfalso; simp_all; done) | (exfalso; rcases hh with hh | hh <;> linarith [hh.1, hh.2]) |
      (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma peak_ind_iff {a b p q : ℝ} (hab : a ≠ b) :
    ((if p < a ∧ b < a then 1 else 0) + (if a < b ∧ q < b then 1 else 0) = (1 : ℕ)) ↔
      ((p < a ∧ b < a) ∨ (a < b ∧ q < b)) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;>
    split_ifs <;> constructor <;> intro hh <;>
    first | omega | (exfalso; simp_all; done) | (exfalso; rcases hh with hh | hh <;> linarith [hh.1, hh.2]) |
      (left; constructor <;> linarith) | (right; constructor <;> linarith) | (exfalso; tauto)

/-- Common set-up of the two skeleton lemmas: `C = (a, x, b) ++ R` with `x` inserted between the
ends, as a cycle `w` on `ZMod (|R| + 3)`; `Γ` is `w` with `x` deleted. -/
lemma skel_setup {a x b : ℝ} {R : List ℝ} (hnd : (a :: x :: b :: R).Nodup) :
    let w := fun i : ZMod (R.length + 2 + 1) => (a :: x :: b :: R).getD i.val 0
    (CU (a :: x :: b :: R) ↔ IsCyclicUnimodal w) ∧ (CU (a :: b :: R) ↔ IsCyclicUnimodal (skipAt w 1)) ∧
      Function.Injective w ∧ Function.Injective (skipAt w 1) ∧
      w (1 - 1) = a ∧ w 1 = x ∧ w (1 + 1) = b ∧ w (1 - 1 - 1) = R.getLastD b ∧
      w (1 + 1 + 1) = R.headD a := by
  intro w
  have : Fact (1 < R.length + 2 + 1) := ⟨by omega⟩
  have hinj : Function.Injective w := injective_ins hnd
  refine ⟨CU_iff_of_length (by simp), ?_, hinj, hinj.comp (phi_inj 1), by simp [w], ?_, ?_,
    ins_val_neg a x b R, ins_val_three a x b R⟩
  · rw [CU_rotate_one, CU_iff_of_length (k := R.length + 2) (by simp), skipAt_one_ins a x b R]
  · simp [w, ZMod.val_one]
  · have : (1 + 1 : ZMod (R.length + 2 + 1)) = ((2 : ℕ) : ZMod _) := by push_cast; ring
    simp only [w, this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 2 < R.length + 2 + 1)]
    simp

/-- **Lemma W′, lower skeleton.**  Ends `A`, `B` of the face `F` with depths `a ≠ b`, corners `R`
(from `B` back to `A`; the closed corner cycle `Γ = a :: b :: R` has distinct entries), `lo` the
lowest depth of `F` (`lo ≤ a, b`, not a corner depth).  The lower skeleton `C₊ = (A, lo, B) ++ R`
(`lo` omitted when it is an end) is cyclically unimodal iff `Γ` is and `lo` is an end or the lower
end is a valley of `Γ`. -/
theorem CU_skel1_low_iff {a b lo : ℝ} {R : List ℝ} (hnd : (a :: b :: R).Nodup) (hla : lo ≤ a)
    (hlb : lo ≤ b) (hR : lo ∉ R) :
    CU (skel1 a lo b ++ R) ↔ CU (a :: b :: R) ∧ (lo = a ∨ lo = b ∨ EndValley a b R) := by
  by_cases he : lo = a ∨ lo = b
  · simp only [skel1, he, ↓reduceIte, List.cons_append, List.nil_append]
    exact ⟨fun h => ⟨h, by tauto⟩, fun h => h.1⟩
  have hla' : lo < a := lt_of_le_of_ne hla (fun h => he (Or.inl h))
  have hlb' : lo < b := lt_of_le_of_ne hlb (fun h => he (Or.inr h))
  have hab : a ≠ b := by intro h; simp [h] at hnd
  have hnd' : (a :: lo :: b :: R).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd ⊢
    exact ⟨⟨hla'.ne', hab, hnd.1.2⟩, ⟨hlb'.ne, hR⟩, hnd.2⟩
  simp only [skel1, he, ↓reduceIte, List.cons_append, List.nil_append]
  obtain ⟨hC, hG, hinj, hsinj, v0, v1, v2, vm, v3⟩ := skel_setup hnd'
  set w := fun i : ZMod (R.length + 2 + 1) => (a :: lo :: b :: R).getD i.val 0 with hw
  rw [hC, hG, isCyclicUnimodal_iff_numPeaks, isCyclicUnimodal_iff_numPeaks]
  have : Fact (1 < R.length + 2 + 1) := ⟨by omega⟩
  have key := numPeaks_skipAt_valley (by omega : 2 ≤ R.length + 2)
    (z := w) (i := 1) (by rw [v1, v0]; exact hla') (by rw [v1, v2]; exact hlb')
    (by rw [v0, v2]; exact hab)
  rw [v0, v2, vm, v3] at key
  have hge := one_le_numPeaks (by omega) hsinj
  have hp : R.getLastD b ≠ a := by
    rw [← vm, ← v0]; exact hinj.ne (by simp)
  have hq : R.headD a ≠ b := by
    rw [← v3, ← v2]; exact hinj.ne (by simp)
  have hind := valley_ind_iff hab hp hq
  simp only [hinj, hsinj, true_and, hla'.ne, hlb'.ne, false_or, EndValley]
  rw [← hind]
  constructor
  · intro h; constructor <;> omega
  · rintro ⟨h1, h2⟩; omega

/-- **Lemma W′, upper skeleton.**  As `CU_skel1_low_iff`, with `hi` the highest depth of `F`: the
upper skeleton `C₋ = (A, hi, B) ++ R` is cyclically unimodal iff `Γ` is and `hi` is an end or the
higher end is a peak of `Γ`. -/
theorem CU_skel1_high_iff {a b hi : ℝ} {R : List ℝ} (hnd : (a :: b :: R).Nodup) (hha : a ≤ hi)
    (hhb : b ≤ hi) (hR : hi ∉ R) :
    CU (skel1 a hi b ++ R) ↔ CU (a :: b :: R) ∧ (hi = a ∨ hi = b ∨ EndPeak a b R) := by
  by_cases he : hi = a ∨ hi = b
  · simp only [skel1, he, ↓reduceIte, List.cons_append, List.nil_append]
    exact ⟨fun h => ⟨h, by tauto⟩, fun h => h.1⟩
  have hha' : a < hi := lt_of_le_of_ne hha (fun h => he (Or.inl h.symm))
  have hhb' : b < hi := lt_of_le_of_ne hhb (fun h => he (Or.inr h.symm))
  have hab : a ≠ b := by intro h; simp [h] at hnd
  have hnd' : (a :: hi :: b :: R).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd ⊢
    exact ⟨⟨hha'.ne, hab, hnd.1.2⟩, ⟨hhb'.ne', hR⟩, hnd.2⟩
  simp only [skel1, he, ↓reduceIte, List.cons_append, List.nil_append]
  obtain ⟨hC, hG, hinj, hsinj, v0, v1, v2, vm, v3⟩ := skel_setup hnd'
  set w := fun i : ZMod (R.length + 2 + 1) => (a :: hi :: b :: R).getD i.val 0 with hw
  rw [hC, hG, isCyclicUnimodal_iff_numPeaks, isCyclicUnimodal_iff_numPeaks]
  have : Fact (1 < R.length + 2 + 1) := ⟨by omega⟩
  have key := numPeaks_skipAt_peak (by omega : 2 ≤ R.length + 2)
    (z := w) (i := 1) (by rw [v1, v0]; exact hha') (by rw [v1, v2]; exact hhb')
  rw [v0, v2, vm, v3] at key
  have hge := one_le_numPeaks (by omega) hsinj
  have hind := peak_ind_iff (p := R.getLastD b) (q := R.headD a) hab
  have hle : ((if R.getLastD b < a ∧ b < a then 1 else 0) +
      (if a < b ∧ R.headD a < b then 1 else 0) : ℕ) ≤ 1 := by
    split_ifs <;> first | omega | (exfalso; simp_all)
  simp only [hinj, hsinj, true_and, hha'.ne', hhb'.ne', false_or, EndPeak]
  rw [← hind]
  constructor
  · intro h; constructor <;> omega
  · rintro ⟨h1, h2⟩; omega

/-- **Lemma W′ (closed corner cycle).**  With `Γ = a :: b :: R` the closed corner cycle of a
regular view on `F`'s circle (`a`, `b` the depths of the chord ends `A`, `B`; `R` the other rim
corners from `B` back to `A`; distinct depths) and `lo`, `hi` the lowest and highest depths of `F`
(not corner depths): `F`'s circle works, i.e. the lower or the upper skeleton is cyclically unimodal,
iff `Γ` is cyclically unimodal (κ(Γ) = 1) and an end condition holds: `A` or `B` is a peak or valley
of `Γ` (E(Γ)), or `lo` or `hi` is an end (f). -/
theorem lemmaW' {a b lo hi : ℝ} {R : List ℝ} (hnd : (a :: b :: R).Nodup) (hla : lo ≤ a)
    (hlb : lo ≤ b) (hha : a ≤ hi) (hhb : b ≤ hi) (hloR : lo ∉ R) (hhiR : hi ∉ R) :
    (CU (skel1 a lo b ++ R) ∨ CU (skel1 a hi b ++ R)) ↔
      CU (a :: b :: R) ∧
        ((EndPeak a b R ∨ EndValley a b R) ∨ (lo = a ∨ lo = b ∨ hi = a ∨ hi = b)) := by
  rw [CU_skel1_low_iff hnd hla hlb hloR, CU_skel1_high_iff hnd hha hhb hhiR]
  tauto

/-- The ends of a chain `A ++ B` (length ≥ 2) followed by the rest `R` of a rim with distinct
depths: the closed corner cycle `(first, last) ++ R` has distinct entries and no chain depth is a
corner depth. -/
lemma chain_ends_nodup {A B R : List ℝ} {a c e : ℝ} (hnd : (A ++ B ++ R).Nodup)
    (h2 : 2 ≤ A.length + B.length) (ha : (A ++ B).head? = some a)
    (hc : (A ++ B).getLast? = some c) (he : e ∈ A ++ B) : (a :: c :: R).Nodup ∧ e ∉ R := by
  constructor
  · refine hnd.sublist ?_
    obtain ⟨x, L, hL⟩ : ∃ x L, A ++ B = x :: L := by
      rcases h : A ++ B with _ | ⟨x, L⟩
      · simp [h] at ha
      · exact ⟨x, L, rfl⟩
    rw [hL] at ha hc ⊢
    have hL0 : L ≠ [] := by
      rintro rfl; have := congrArg List.length hL; simp at this; omega
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hL0] at hc
    simp only [Option.getD_some, Option.some.injEq] at hc
    subst hc
    exact List.Sublist.append (List.Sublist.cons_cons _
      (List.singleton_sublist.mpr (List.getLast_mem hL0))) (List.Sublist.refl R)
  · intro hR
    exact (List.nodup_append.mp hnd).2.2 e he e hR rfl

/-- Distinct rim depths from `hinj`, as a list. -/
lemma nodup_of_depth {N : ℕ} {x : ZMod (N + 1) → ℝ³} {u₀ : ℝ³} {L : List ℝ}
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (hdepth : List.ofFn (fun i : Fin (N + 1) => ⟪x ((i : ℕ) : ZMod (N + 1)), u₀⟫) = L) :
    L.Nodup := by
  rw [← hdepth, List.nodup_ofFn]
  intro i j hij
  have := hinj hij
  apply Fin.ext
  have h1 := congrArg ZMod.val this
  rwa [ZMod.val_cast_of_lt (by omega : (i : ℕ) < N + 1),
    ZMod.val_cast_of_lt (by omega : (j : ℕ) < N + 1)] at h1

/-- **Lemma W′, "if" direction, lower chain (Corollary FC + Lemma W′).**  The set-up of
`isRupert_faceCircle_skelV` (face `F` edge-on at `u₀`, the rim is `F`'s V-shaped chain from `A`
(depth `a`) to `B` (depth `c`) followed by the corners `R`; `e` the lowest chain depth), with the
skeleton hypothesis replaced by Lemma W′'s condition: the closed corner cycle `(a, c) ++ R` is
cyclically unimodal and `e` is an end or the lower end is a valley of it.  Then `V` is Rupert. -/
theorem isRupert_faceCircle_W'_low (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hplane : ∀ i : ZMod (N + 1), i.val < m → ⟪n, x i⟫ = h)
    (hdir : ∀ i : ZMod (N + 1), i.val + 1 < m → 0 < σ * det3 n (x (i + 1) - x i) u₀)
    (hchain : ∀ i : ZMod (N + 1), i.val + 1 < m → ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x i → y ≠ x (i + 1) →
      0 < σ * ⟪n, v⟫ * det3 (x (i + 1) - x i) (y - x i) n)
    (hR : ∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (A B R : List ℝ) (a e c : ℝ)
    (hdepth : List.ofFn (fun i : Fin (N + 1) => ⟪x ((i : ℕ) : ZMod (N + 1)), u₀⟫) = A ++ B ++ R)
    (hAB : A.length + B.length = m) (hA : A.Pairwise (· > ·)) (hB : B.Pairwise (· < ·))
    (ha : (A ++ B).head? = some a) (hc : (A ++ B).getLast? = some c) (he : e ∈ A ++ B)
    (hext : ∀ x ∈ A ++ B, e ≤ x) (hΓ : CU (a :: c :: R))
    (hE : e = a ∨ e = c ∨ EndValley a c R) : IsRupert V := by
  obtain ⟨hnd, heR⟩ := chain_ends_nodup (nodup_of_depth hinj hdepth) (by omega) ha hc he
  have hsk := (CU_skel1_low_iff hnd (hext a (List.mem_of_mem_head? ha))
    (hext c (List.mem_of_mem_getLast? hc)) heR).mpr ⟨hΓ, hE⟩
  exact isRupert_faceCircle_skelV V n u₀ v h σ hσ hn hu₀ hu hV hm hmN x hxV hplane hdir hchain hR
    hinj A B R a e c hdepth hAB hA hB ha hc he hext hsk

/-- **Lemma W′, "if" direction, upper chain.**  As `isRupert_faceCircle_W'_low` for the Λ-shaped
chain of `isRupert_faceCircle_skelL` (`e` the highest chain depth): the closed corner cycle
`(a, c) ++ R` is cyclically unimodal and `e` is an end or the higher end is a peak of it. -/
theorem isRupert_faceCircle_W'_high (V : Finset ℝ³) (n u₀ v : ℝ³) (h σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hn : n ≠ 0) (hu₀ : u₀ ≠ 0) (hu : ⟪n, u₀⟫ = 0) (hV : ∀ y ∈ V, ⟪n, y⟫ ≤ h)
    {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N)
    (x : ZMod (N + 1) → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hplane : ∀ i : ZMod (N + 1), i.val < m → ⟪n, x i⟫ = h)
    (hdir : ∀ i : ZMod (N + 1), i.val + 1 < m → 0 < σ * det3 n (x (i + 1) - x i) u₀)
    (hchain : ∀ i : ZMod (N + 1), i.val + 1 < m → ∀ y ∈ V, ⟪n, y⟫ = h → y ≠ x i → y ≠ x (i + 1) →
      0 < σ * ⟪n, v⟫ * det3 (x (i + 1) - x i) (y - x i) n)
    (hR : ∀ i : ZMod (N + 1), m ≤ i.val + 1 → ∀ y ∈ V, y ≠ x i → y ≠ x (i + 1) →
      TiltSignS σ (x (i + 1) - x i) (y - x i) u₀ v)
    (hinj : Function.Injective fun i => ⟪x i, u₀⟫)
    (A B R : List ℝ) (a e c : ℝ)
    (hdepth : List.ofFn (fun i : Fin (N + 1) => ⟪x ((i : ℕ) : ZMod (N + 1)), u₀⟫) = A ++ B ++ R)
    (hAB : A.length + B.length = m) (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· > ·))
    (ha : (A ++ B).head? = some a) (hc : (A ++ B).getLast? = some c) (he : e ∈ A ++ B)
    (hext : ∀ x ∈ A ++ B, x ≤ e) (hΓ : CU (a :: c :: R))
    (hE : e = a ∨ e = c ∨ EndPeak a c R) : IsRupert V := by
  obtain ⟨hnd, heR⟩ := chain_ends_nodup (nodup_of_depth hinj hdepth) (by omega) ha hc he
  have hsk := (CU_skel1_high_iff hnd (hext a (List.mem_of_mem_head? ha))
    (hext c (List.mem_of_mem_getLast? hc)) heR).mpr ⟨hΓ, hE⟩
  exact isRupert_faceCircle_skelL V n u₀ v h σ hσ hn hu₀ hu hV hm hmN x hxV hplane hdir hchain hR
    hinj A B R a e c hdepth hAB hA hB ha hc he hext hsk

end Minimality
