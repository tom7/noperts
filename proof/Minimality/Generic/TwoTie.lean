module

public import Minimality.Generic.LimitSeq
public import Minimality.Sector
public import Minimality.CaseC18Vertex

@[expose] public section

/-!
# TwoTie (generic, statements): Lemma R2T / Lemma 29.2 (robust corner rims from MF with ≤ 2 ties)

Phase 1 (statements).  Paper: `sp1621/draft.md` Lemma R2T; PROOFS §29 Lemma 29.2 (edge pair, one far
corner), 18.2 (b) (MF), 24.2 / 18.6 step 4 (every refinement is realized by a nearby metric).

Pieces:
* `isRobustUnimodal_iff_refinements`: `IsRobustUnimodal z` iff every injective refinement of `z` is
  cyclically unimodal (`4 ≤ k`; false for a tied triangle).
* `exists_good_view` (proved): the pigeonhole of R2T's proof.
* `lemma292`: the finite check (5 depths, ≥ 3 distinct values, `z_w < z_v`, MF at all refinements):
  `K_v` or `K_w` robust, or the straddling far triple.  Verified exhaustively in C++ (`ep.cc` in the
  scratchpad: 48/82/39 MF orders with 0/1/2 ties, both non-robust only for `v2 w0 f1=r=f2=1`).
* `ViewGroup`, `robust_corner_rim_of_MF` (R2T): MF as a statement about metrics near the identity
  (`mapShape L y`), ≤ 2 independent ties (`TieIndep`), edge pairs with one far corner and single
  tests.
-/

set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Refinements -/

/-- `z'` is an injective refinement of the weak order of `z`: all strict comparisons are kept. -/
def Refines {ι : Type*} (z z' : ι → ℝ) : Prop :=
  Function.Injective z' ∧ ∀ i j, z i < z j → z' i < z' j

/-- Refinement with prescribed tie-breaks (generic index type). -/
theorem exists_refinement_tb' {ι : Type*} [Fintype ι] (ν : ι → ℕ) (hν : Function.Injective ν)
    (z : ι → ℝ) (τ : ι → ℕ) :
    ∃ z' : ι → ℝ, Refines z z' ∧ ∀ i j, z i = z j → τ i < τ j → z' i < z' j := by
  classical
  let key : ι → ℝ ×ₗ (ℕ ×ₗ ℕ) := fun i => toLex (z i, toLex (τ i, ν i))
  have kinj : Function.Injective key := by
    intro i j h
    simp only [key, toLex_inj, Prod.mk.injEq] at h
    exact hν h.2.2
  have mono : ∀ i j, key i < key j →
      ((univ.filter fun x => key x < key i).card : ℝ) < (univ.filter fun x => key x < key j).card := by
    intro i j h
    have : (univ.filter fun x => key x < key i).card < (univ.filter fun x => key x < key j).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i, by simp [h], by simp⟩
      · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact hx.trans h
    exact_mod_cast this
  refine ⟨fun i => ((univ.filter fun x => key x < key i).card : ℝ), ⟨?_, ?_⟩, ?_⟩
  · intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (fun e => hne (kinj e)) with h1 | h1
    · exact (mono i j h1).ne h
    · exact (mono j i h1).ne h.symm
  · intro i j h
    exact mono i j (by simp only [key, Prod.Lex.toLex_lt_toLex]; left; exact h)
  · intro i j h h2
    exact mono i j (by simp only [key, Prod.Lex.toLex_lt_toLex]; right; exact ⟨h, Or.inl h2⟩)

theorem exists_refinement_tb {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (τ : ZMod k → ℕ) :
    ∃ z' : ZMod k → ℝ, Refines z z' ∧ ∀ i j, z i = z j → τ i < τ j → z' i < z' j :=
  exists_refinement_tb' (fun i => i.val) (ZMod.val_injective k) z τ

/-- Guided refinement: four distinct positions, ranks `r` compatible with `z`. -/
theorem exists_refinement_ranks {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (ps : Fin 4 → ZMod k)
    (hps : Function.Injective ps) (r : Fin 4 → ℕ) (hr : ∀ i j, z (ps i) < z (ps j) → r i < r j) :
    ∃ z' : ZMod k → ℝ, Refines z z' ∧ ∀ i j, r i < r j → z' (ps i) < z' (ps j) := by
  classical
  let τ : ZMod k → ℕ := fun x => if h : ∃ i, ps i = x then r h.choose else 0
  have hτ : ∀ i, τ (ps i) = r i := by
    intro i
    have h : ∃ j, ps j = ps i := ⟨i, rfl⟩
    simp only [τ, dif_pos h]
    rw [hps h.choose_spec]
  obtain ⟨z', hz', htb⟩ := exists_refinement_tb z τ
  refine ⟨z', hz', fun i j hij => ?_⟩
  rcases lt_trichotomy (z (ps i)) (z (ps j)) with h | h | h
  · exact hz'.2 _ _ h
  · exact htb _ _ h (by rw [hτ, hτ]; exact hij)
  · exact absurd (hr _ _ h) (by omega)

theorem zig_exists (w0 w1 w2 w3 t : ℝ) (s : Fin 4)
    (h : ∀ i : Fin 4, i ≠ s → ![w0, w1, w2, w3] i = t) :
    ∃ r : Fin 4 → ℕ, (∀ i j, ![w0, w1, w2, w3] i < ![w0, w1, w2, w3] j → r i < r j) ∧
      ((r 1 < r 0 ∧ r 1 < r 2 ∧ r 3 < r 2 ∧ r 3 < r 0) ∨
       (r 0 < r 1 ∧ r 2 < r 1 ∧ r 2 < r 3 ∧ r 0 < r 3)) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
    Matrix.cons_val_succ] at h0 h1 h2 h3
  fin_cases s <;> simp at h0 h1 h2 h3
  · by_cases hx : t < w0
    · refine ⟨![3,0,2,1], ?_, Or.inl (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
    · refine ⟨![0,2,1,3], ?_, Or.inr (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  · by_cases hx : t < w1
    · refine ⟨![0,3,1,2], ?_, Or.inr (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
    · refine ⟨![2,0,3,1], ?_, Or.inl (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  · by_cases hx : t < w2
    · refine ⟨![2,0,3,1], ?_, Or.inl (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
    · refine ⟨![1,2,0,3], ?_, Or.inr (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  · by_cases hx : t < w3
    · refine ⟨![0,2,1,3], ?_, Or.inr (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
    · refine ⟨![2,1,3,0], ?_, Or.inl (by simp)⟩
      intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith


theorem no_zig_of_refinements {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (H : ∀ z' : ZMod k → ℝ, Refines z z' → IsCyclicUnimodal z')
    (B : ZMod k) {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hdk : d < k)
    (r : Fin 4 → ℕ)
    (hr : ∀ i j, ![z (B + a), z (B + b), z (B + c), z (B + d)] i <
      ![z (B + a), z (B + b), z (B + c), z (B + d)] j → r i < r j)
    (hz : (r 1 < r 0 ∧ r 1 < r 2 ∧ r 3 < r 2 ∧ r 3 < r 0) ∨
       (r 0 < r 1 ∧ r 2 < r 1 ∧ r 2 < r 3 ∧ r 0 < r 3)) : False := by
  have n01 := zmod_add_ne (by omega : a < k) (by omega : b < k) hab.ne B
  have n02 := zmod_add_ne (by omega : a < k) (by omega : c < k) (by omega) B
  have n03 := zmod_add_ne (by omega : a < k) (by omega : d < k) (by omega) B
  have n12 := zmod_add_ne (by omega : b < k) (by omega : c < k) hbc.ne B
  have n13 := zmod_add_ne (by omega : b < k) (by omega : d < k) (by omega) B
  have n23 := zmod_add_ne (by omega : c < k) (by omega : d < k) hcd.ne B
  have hps : Function.Injective (![B + a, B + b, B + c, B + d] : Fin 4 → ZMod k) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨z', hz', hlt⟩ := exists_refinement_ranks z _ hps r (by
    intro i j h
    have e : ∀ i : Fin 4, ![z (B + a), z (B + b), z (B + c), z (B + d)] i =
        z ((![B + a, B + b, B + c, B + d] : Fin 4 → ZMod k) i) := by
      intro i; fin_cases i <;> rfl
    exact hr i j (by rw [e, e]; exact h))
  have hu := H z' hz'
  have := hu.noZig B hab hbc hcd hdk
  have l := fun i j => hlt i j
  rcases hz with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact this (Or.inr ⟨by simpa using l _ _ h1, by simpa using l _ _ h2, by simpa using l _ _ h3, by simpa using l _ _ h4⟩)
  · exact this (Or.inl ⟨by simpa using l _ _ h1, by simpa using l _ _ h2, by simpa using l _ _ h3, by simpa using l _ _ h4⟩)


theorem zig_four {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (H : ∀ z' : ZMod k → ℝ, Refines z z' → IsCyclicUnimodal z')
    (B : ZMod k) {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hdk : d < k)
    (p0 p1 p2 p3 : ZMod k) (e0 : B + (a : ZMod k) = p0) (e1 : B + (b : ZMod k) = p1)
    (e2 : B + (c : ZMod k) = p2) (e3 : B + (d : ZMod k) = p3) (s : Fin 4) (t : ℝ)
    (h : ∀ i : Fin 4, i ≠ s → ![z p0, z p1, z p2, z p3] i = t) : False := by
  subst e0 e1 e2 e3
  obtain ⟨r, hr, hz⟩ := zig_exists _ _ _ _ t s h
  exact no_zig_of_refinements H B hab hbc hcd hdk r hr hz

theorem three_equal_false {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (H : ∀ z' : ZMod k → ℝ, Refines z z' → IsCyclicUnimodal z')
    (i j l m : ZMod k) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (him : i ≠ m) (hjm : j ≠ m)
    (hlm : l ≠ m) (e1 : z i = z j) (e2 : z j = z l) (ho : (j - i).val < (l - i).val) : False := by
  have hv : ∀ x : ZMod k, i + (((x - i).val : ℕ) : ZMod k) = x := by
    intro x; rw [ZMod.natCast_zmod_val]; ring
  have hv0 : ∀ x : ZMod k, x ≠ i → 0 < (x - i).val := fun x hx =>
    ZMod.val_pos.mpr (sub_ne_zero.mpr hx)
  have hvne : ∀ x y : ZMod k, x ≠ y → (x - i).val ≠ (y - i).val := by
    intro x y hxy h
    apply hxy
    have := congrArg (fun n : ℕ => i + (n : ZMod k)) h
    simpa [hv] using this
  have hlt : ∀ x : ZMod k, (x - i).val < k := fun x => ZMod.val_lt _
  have hmo := hvne m j (Ne.symm hjm)
  have hmo' := hvne m l (Ne.symm hlm)
  have h0 : (0 : ℕ) < (j - i).val := hv0 j (Ne.symm hij)
  have i0 : i + ((0 : ℕ) : ZMod k) = i := by simp
  rcases lt_or_gt_of_ne hmo with c1 | c1
  · -- m before j : slots (i, m, j, l)
    exact zig_four H i (a := 0) (b := (m - i).val) (c := (j - i).val) (d := (l - i).val)
      (hv0 m (Ne.symm him)) c1 ho (hlt l) i m j l i0 (hv m) (hv j) (hv l) 1 (z i) (by
        intro x hx; fin_cases x <;> simp at hx ⊢ <;> linarith)
  · rcases lt_or_gt_of_ne hmo' with c2 | c2
    · exact zig_four H i (a := 0) (b := (j - i).val) (c := (m - i).val) (d := (l - i).val)
        h0 c1 c2 (hlt l) i j m l i0 (hv j) (hv m) (hv l) 2 (z i) (by
          intro x hx; fin_cases x <;> simp at hx ⊢ <;> linarith)
    · exact zig_four H i (a := 0) (b := (j - i).val) (c := (l - i).val) (d := (m - i).val)
        h0 ho c2 (hlt m) i j l m i0 (hv j) (hv l) (hv m) 3 (z i) (by
          intro x hx; fin_cases x <;> simp at hx ⊢ <;> linarith)


/-- **Robust unimodality = unimodality at every refinement.**  (R1)-(R3) of §18.0 are exactly what is
needed; for `k = 3` a tied triangle has only unimodal refinements but is not robust (R2), hence
`4 ≤ k`.  RISK: the equivalence is not in the tree; check (R3) in the proof. -/
theorem isRobustUnimodal_iff_refinements {k : ℕ} [NeZero k] (hk : 4 ≤ k) (z : ZMod k → ℝ) :
    IsRobustUnimodal z ↔ ∀ z' : ZMod k → ℝ, Refines z z' → IsCyclicUnimodal z' := by
  constructor
  · intro hz z' hr
    exact hz.isCyclicUnimodal_of_order (by omega) hr.2 hr.1
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro B a b c d hab hbc hcd hdk ⟨h1, h2, h3, h4⟩
      refine no_zig_of_refinements H B hab hbc hcd hdk
        (![if z (B + a) < z (B + c) then 2 else 3, if z (B + b) < z (B + d) then 0 else 1,
           if z (B + a) < z (B + c) then 3 else 2, if z (B + b) < z (B + d) then 1 else 0])
        ?_ (Or.inl (by split_ifs <;> simp)) 
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> split_ifs <;> simp <;> linarith
    · intro i j l hij hjl hil e1 e2
      obtain ⟨m, hm⟩ : ∃ m : ZMod k, m ≠ i ∧ m ≠ j ∧ m ≠ l := by
        have : (({i, j, l} : Finset (ZMod k))).card < Fintype.card (ZMod k) := by
          rw [ZMod.card]
          exact lt_of_le_of_lt (Finset.card_le_three) (by omega)
        obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (s := {i, j, l}) (t := (Finset.univ : Finset (ZMod k))) (by simpa using this)
        refine ⟨m, ?_, ?_, ?_⟩ <;> intro h <;> simp [h] at hm
      by_cases ho : (j - i).val < (l - i).val
      · exact three_equal_false H i j l m hij hil hjl (Ne.symm hm.1) (Ne.symm hm.2.1)
          (Ne.symm hm.2.2) e1 e2 ho
      · have ho' : (l - i).val < (j - i).val := by
          rcases lt_or_gt_of_ne (fun h : (j - i).val = (l - i).val => hjl (by
            have := congrArg (fun n : ℕ => i + (n : ZMod k)) h
            simpa [ZMod.natCast_zmod_val] using this)) with h | h
          · exact absurd h ho
          · exact h
        exact three_equal_false H i l j m hil hij hjl.symm (Ne.symm hm.1) (Ne.symm hm.2.2)
          (Ne.symm hm.2.1) (e1.trans e2) e2.symm ho'
    · intro B a b c d hab hbc hcd hdk he
      constructor
      · rintro ⟨h1, h2⟩
        exact no_zig_of_refinements H B hab hbc hcd hdk ![0, 2, 1, 3]
          (by intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith)
          (Or.inr (by simp))
      · rintro ⟨h1, h2⟩
        exact no_zig_of_refinements H B hab hbc hcd hdk ![3, 1, 2, 0]
          (by intro i j hij; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith)
          (Or.inl (by simp))


/-- The pigeonhole of R2T: if every combination of per-view patterns has a unimodal rim at some
view, some view is unimodal at all of its own patterns. -/
theorem exists_good_view {A : Type*} [Fintype A] {S : A → Type*} (U : (a : A) → S a → Prop)
    (hMF : ∀ σ : (a : A) → S a, ∃ a, U a (σ a)) : ∃ a, ∀ s, U a s := by
  by_contra h
  push Not at h
  choose σ hσ using h
  obtain ⟨a, ha⟩ := hMF σ
  exact hσ a ha

/-! ### Lemma 29.2: an edge pair with one far corner -/

/-- The 4-cycle `(top, f1, r, f2)` from the depths `z : Fin 5 → ℝ` indexed `(v, w, f1, r, f2)`. -/
def edgeRim (z : Fin 5 → ℝ) (top : Fin 5) : ZMod 4 → ℝ := fun i => ![z top, z 2, z 3, z 4] i

theorem nws_of_unimodal4 {z : ZMod 4 → ℝ} (h : IsCyclicUnimodal z) : NWS4 z := by
  have hz := h.noZig 0 (a := 0) (b := 1) (c := 2) (d := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hi := h.1
  have n01 : z 0 ≠ z 1 := hi.ne (by decide)
  have n03 : z 0 ≠ z 3 := hi.ne (by decide)
  have n12 : z 1 ≠ z 2 := hi.ne (by decide)
  have n23 : z 2 ≠ z 3 := hi.ne (by decide)
  have n02 : z 0 ≠ z 2 := hi.ne (by decide)
  have n13 : z 1 ≠ z 3 := hi.ne (by decide)
  simp only [zero_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hz
  unfold NWS4
  constructor
  · by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    exact hz (Or.inr ⟨lt_of_le_of_ne c1 n01.symm, lt_of_le_of_ne c3 n12, lt_of_le_of_ne c4 n23.symm,
      lt_of_le_of_ne c2 n03.symm⟩)
  · by_contra hc
    push Not at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    exact hz (Or.inl ⟨lt_of_le_of_ne c1 n01, lt_of_le_of_ne c3 n12.symm, lt_of_le_of_ne c4 n23,
      lt_of_le_of_ne c2 n03⟩)


/-- **Lemma 29.2 (real form).**  Depths `z = (v, w, f1, r, f2)` with `z_w < z_v` and at most two
ties (≥ 3 distinct values).  If at every refinement of the weak order one of the rims `(v,f1,r,f2)`,
`(w,f1,r,f2)` is unimodal, then one of them is robustly unimodal or `f1 ~ r ~ f2` is a far triple
tie strictly between `z_w` and `z_v`. -/
theorem lemma292 (z : Fin 5 → ℝ) (hvw : z 1 < z 0) (hcard : 3 ≤ (univ.image z).card)
    (hMF : ∀ z' : Fin 5 → ℝ, Refines z z' →
      IsCyclicUnimodal (edgeRim z' 0) ∨ IsCyclicUnimodal (edgeRim z' 1)) :
    IsRobustUnimodal (edgeRim z 0) ∨ IsRobustUnimodal (edgeRim z 1) ∨
      (z 2 = z 3 ∧ z 3 = z 4 ∧ z 1 < z 3 ∧ z 3 < z 0) := by
  have hrob : ∀ t : Fin 5, NWS4 (edgeRim z t) → IsRobustUnimodal (edgeRim z t) := by
    intro t h
    exact CaseC18.robust_quad_of_nws h.1 h.2
  by_cases hv : NWS4 (edgeRim z 0)
  · exact Or.inl (hrob _ hv)
  by_cases hw : NWS4 (edgeRim z 1)
  · exact Or.inr (Or.inl (hrob _ hw))
  right; right
  -- a refinement separating both rims is impossible
  have bad : ∀ (τ : Fin 5 → ℕ), (∀ x y : Fin 5, τ x < τ y → z x ≤ z y) → (τ 2 = τ 4) →
      (τ 0 = τ 1) → (τ 1 = τ 3) → (τ 2 < τ 0 ∨ τ 0 < τ 2) → False := by
    intro τ hτ h24 h01 h13 hc
    obtain ⟨z', hz', htb⟩ := exists_refinement_tb' (fun i : Fin 5 => (i : ℕ)) Fin.val_injective z τ
    have st : ∀ x y : Fin 5, τ x < τ y → z' x < z' y := by
      intro x y h
      rcases (hτ x y h).lt_or_eq with h1 | h1
      · exact hz'.2 _ _ h1
      · exact htb _ _ h1 h
    have hv' := hMF z' hz'
    rcases hc with hc | hc
    · have a1 := st 2 0 hc; have a2 := st 2 1 (by omega); have a3 := st 2 3 (by omega)
      have a4 := st 4 0 (by omega); have a5 := st 4 1 (by omega); have a6 := st 4 3 (by omega)
      rcases hv' with h | h <;> have := nws_of_unimodal4 h <;> simp [NWS4, edgeRim] at this <;>
        rcases this with ⟨h1, h2⟩ <;> rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
        linarith
    · have a1 := st 0 2 hc; have a2 := st 1 2 (by omega); have a3 := st 3 2 (by omega)
      have a4 := st 0 4 (by omega); have a5 := st 1 4 (by omega); have a6 := st 3 4 (by omega)
      rcases hv' with h | h <;> have := nws_of_unimodal4 h <;> simp [NWS4, edgeRim] at this <;>
        rcases this with ⟨h1, h2⟩ <;> rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
        linarith
  have D : ∀ t : Fin 5, ¬ NWS4 (edgeRim z t) →
      (z 2 ≤ z t ∧ z 4 ≤ z t ∧ z 2 ≤ z 3 ∧ z 4 ≤ z 3) ∨
      (z t ≤ z 2 ∧ z t ≤ z 4 ∧ z 3 ≤ z 2 ∧ z 3 ≤ z 4) := by
    intro t h
    by_contra hc
    apply h
    simp only [not_or, not_and_or, not_le] at hc
    simp only [NWS4, edgeRim]
    simp
    constructor <;> tauto
  have hv' := D 0 hv
  have hw' := D 1 hw
  have c1 : (z 2 ≤ z 1 ∧ z 4 ≤ z 1 ∧ z 2 ≤ z 3 ∧ z 4 ≤ z 3) → False := by
    intro h
    exact bad (fun i => if i = 2 ∨ i = 4 then 0 else 1) (by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]) (by simp)
      (by simp) (by simp) (Or.inl (by simp))
  have c2 : (z 0 ≤ z 2 ∧ z 0 ≤ z 4 ∧ z 3 ≤ z 2 ∧ z 3 ≤ z 4) → False := by
    intro h
    exact bad (fun i => if i = 2 ∨ i = 4 then 1 else 0) (by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]) (by simp)
      (by simp) (by simp) (Or.inr (by simp))
  rcases hv' with h | h
  · rcases hw' with g | g
    · exact (c1 g).elim
    · -- D1v and D2w
      have e2 : z 2 = z 3 := le_antisymm h.2.2.1 g.2.2.1
      have e4 : z 4 = z 3 := le_antisymm h.2.2.2 g.2.2.2
      refine ⟨e2, e4.symm, ?_, ?_⟩
      · by_contra hc
        have : (univ.image z) ⊆ {z 0, z 3} := by
          intro x hx
          simp only [mem_image, mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx
          fin_cases i <;> simp <;> first | (right; linarith [g.1, g.2.1, h.1, h.2.1, g.2.2.1, g.2.2.2, h.2.2.1, h.2.2.2]) | (left; linarith [g.1, g.2.1, h.1, h.2.1, g.2.2.1, g.2.2.2, h.2.2.1, h.2.2.2])
        have := (card_le_card this).trans (card_insert_le _ _)
        simp at this; omega
      · by_contra hc
        have : (univ.image z) ⊆ {z 1, z 3} := by
          intro x hx
          simp only [mem_image, mem_univ, true_and] at hx
          obtain ⟨i, rfl⟩ := hx
          fin_cases i <;> simp <;> first | (right; linarith [g.1, g.2.1, h.1, h.2.1, g.2.2.1, g.2.2.2, h.2.2.1, h.2.2.2]) | (left; linarith [g.1, g.2.1, h.1, h.2.1, g.2.2.1, g.2.2.2, h.2.2.1, h.2.2.2])
        have := (card_le_card this).trans (card_insert_le _ _)
        simp at this; omega
  · exact (c2 h).elim


/-! ### View groups and Lemma R2T -/

/-- A quadrilateral test. -/
def LabTest.quad {n : ℕ} (view : (Fin n → ℝ³) → ℝ³) (a b c d : Fin n) : LabTest n :=
  ⟨4, view, fun i => ![a, b, c, d] i⟩

/-- The tests of a certificate at one view: a single test, or the two closings `(v,f1,r,f2)`,
`(w,f1,r,f2)` of an edge crossing with one far corner `r`. -/
inductive ViewGroup (n : ℕ)
  | single (T : LabTest n)
  | edge (view : (Fin n → ℝ³) → ℝ³) (v w f1 r f2 : Fin n)

namespace ViewGroup
variable {n : ℕ}

def view : ViewGroup n → ((Fin n → ℝ³) → ℝ³)
  | single T => T.view
  | edge u _ _ _ _ _ => u

def tests : ViewGroup n → List (LabTest n)
  | single T => [T]
  | edge u v w f1 r f2 => [LabTest.quad u v f1 r f2, LabTest.quad u w f1 r f2]

/-- The straddling far triple `f1 ~ r ~ f2` of an edge pair (`z_w < c < z_v`): the exception of 29.2. -/
def Straddle (y : Fin n → ℝ³) : ViewGroup n → Prop
  | single _ => False
  | edge u v w f1 r f2 =>
      ⟪y f1, u y⟫ = ⟪y r, u y⟫ ∧ ⟪y r, u y⟫ = ⟪y f2, u y⟫ ∧
        ⟪y w, u y⟫ < ⟪y r, u y⟫ ∧ ⟪y r, u y⟫ < ⟪y v, u y⟫

/-- Edge groups are ordered `z_w < z_v`. -/
def Ordered (y : Fin n → ℝ³) : ViewGroup n → Prop
  | single _ => True
  | edge u v w _ _ _ => ⟪y w, u y⟫ < ⟪y v, u y⟫

end ViewGroup


/-- Unimodality depends only on the strict order. -/
theorem IsCyclicUnimodal.congr_order {k : ℕ} [NeZero k] {w w' : ZMod k → ℝ}
    (h : ∀ i j, w i < w j ↔ w' i < w' j) (hw : IsCyclicUnimodal w) : IsCyclicUnimodal w' := by
  refine ⟨?_, ?_⟩
  · intro i j e
    by_contra hne
    have := hw.1.ne hne
    rcases lt_or_gt_of_ne this with h1 | h1
    · exact (h i j).1 h1 |> fun h2 => absurd e (ne_of_lt h2)
    · exact (h j i).1 h1 |> fun h2 => absurd e (ne_of_gt h2)
  · have := hw.2
    convert this using 3
    simp only [h]

/-- Collapsing the ends of `m` edges leaves at least `|S| - m` classes. -/
theorem exists_collapse {n : ℕ} (E : List (Fin n × Fin n)) :
    ∃ ψ : Fin n → Fin n, (∀ e ∈ E, ψ e.1 = ψ e.2) ∧
      ∀ S : Finset (Fin n), S.card ≤ (S.image ψ).card + E.length := by
  classical
  induction E with
  | nil => exact ⟨id, by simp, by simp⟩
  | cons e E ih =>
    obtain ⟨ψ, hψ, hc⟩ := ih
    let φ : Fin n → Fin n := fun x => if x = ψ e.1 then ψ e.2 else x
    refine ⟨fun x => φ (ψ x), ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · by_cases h : ψ e'.2 = ψ e'.1
        · simp [φ, h]
        · simp [φ, h]
      · simp [hψ e' he']
    · intro S
      have h1 := hc S
      have h2 : (S.image ψ).card ≤ ((S.image ψ).image φ).card + 1 := by
        by_cases hm : ψ e.1 ∈ S.image ψ
        · have : (S.image ψ).erase (ψ e.1) ⊆ (S.image ψ).image φ := by
            intro x hx
            rw [mem_erase] at hx
            exact mem_image.2 ⟨x, hx.2, by simp [φ, hx.1]⟩
          have := card_le_card this
          rw [card_erase_of_mem hm] at this
          have := card_pos.2 ⟨_, hm⟩
          omega
        · have : S.image ψ ⊆ (S.image ψ).image φ := by
            intro x hx
            refine mem_image.2 ⟨x, hx, ?_⟩
            have : x ≠ ψ e.1 := fun h => hm (h ▸ hx)
            simp [φ, this]
          have := card_le_card this
          omega
      have himg : S.image (fun x => φ (ψ x)) = (S.image ψ).image φ := by
        rw [Finset.image_image]; rfl
      rw [himg]
      simp only [List.length_cons]
      omega


/-- Unimodular maps near the identity realizing small multiples of prescribed tie values. -/
theorem exists_L_scaled {q : ℕ} (d u : Fin q → ℝ³) (h0 : ∀ t, ⟪d t, u t⟫ = 0)
    (hind : TieIndep d u) (c0 : Fin q → ℝ) (P : (ℝ³ →L[ℝ] ℝ³) → Prop)
    (hP : ∀ᶠ L in 𝓝 (1 : ℝ³ →L[ℝ] ℝ³), P L) :
    ∃ ε > 0, ∃ L : ℝ³ →L[ℝ] ℝ³, P L ∧ LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 ∧
      ∀ t, ⟪L (d t), L (u t)⟫ = ε * c0 t := by
  obtain ⟨ν, hν, hball⟩ := Metric.eventually_nhds_iff.1 hP
  obtain ⟨η, hη, hL⟩ := exists_L_prescribed_ties d u h0 hind ν hν
  set M : ℝ := 1 + ∑ t, |c0 t| with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ t, |c0 t| := Finset.sum_nonneg (fun t _ => abs_nonneg _)
    linarith
  have hMpos : 0 < M := by linarith
  refine ⟨η / (2 * M), by positivity, ?_⟩
  obtain ⟨L, hLn, hdet, hLt⟩ := hL d u (fun t => η / (2 * M) * c0 t) (by
    intro t
    refine ⟨by simpa using hη, by simpa using hη, ?_⟩
    rw [abs_mul, abs_of_pos (by positivity : 0 < η / (2 * M))]
    have : |c0 t| ≤ ∑ t, |c0 t| := Finset.single_le_sum (f := fun t => |c0 t|)
      (fun t _ => abs_nonneg _) (mem_univ t)
    calc η / (2 * M) * |c0 t| ≤ η / (2 * M) * M := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = η / 2 := by field_simp
      _ < η := by linarith)
  exact ⟨L, hball (by rwa [dist_eq_norm]), hdet, hLt⟩


namespace ViewGroup
variable {n : ℕ}

/-- Labels occurring in some test of the group. -/
def Used (G : ViewGroup n) (ℓ : Fin n) : Prop := ∃ T ∈ G.tests, ∃ i, T.lab i = ℓ

theorem view_of_mem {G : ViewGroup n} {T : LabTest n} (h : T ∈ G.tests) : T.view = G.view := by
  cases G with
  | single T0 => simp [tests] at h; subst h; rfl
  | edge u v w f1 r f2 =>
    simp only [tests, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl

theorem mem_quad_iff {α : Type*} (a b c d ℓ : α) :
    (∃ i : ZMod 4, ![a, b, c, d] i = ℓ) ↔ ℓ = a ∨ ℓ = b ∨ ℓ = c ∨ ℓ = d := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

theorem common_test (y : Fin n → ℝ³) (G : ViewGroup n) (hG : G.Ordered y) {ℓ ℓ' : Fin n}
    (hl : G.Used ℓ) (hl' : G.Used ℓ') (e : ⟪y ℓ, G.view y⟫ = ⟪y ℓ', G.view y⟫) :
    ∃ T ∈ G.tests, (∃ i, T.lab i = ℓ) ∧ ∃ j, T.lab j = ℓ' := by
  cases G with
  | single T0 =>
    obtain ⟨T, hT, hi⟩ := hl
    obtain ⟨T', hT', hj⟩ := hl'
    simp [tests] at hT hT'
    subst hT hT'
    exact ⟨T', by simp [tests], hi, hj⟩
  | edge u v w f1 r f2 =>
    simp only [Ordered, view] at hG e
    have used : ∀ x : Fin n, Used (edge u v w f1 r f2) x ↔
        (x = v ∨ x = f1 ∨ x = r ∨ x = f2) ∨ (x = w ∨ x = f1 ∨ x = r ∨ x = f2) := by
      intro x
      constructor
      · rintro ⟨T, hT, hi⟩
        simp only [tests, List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl
        · exact Or.inl ((mem_quad_iff _ _ _ _ _).1 hi)
        · exact Or.inr ((mem_quad_iff _ _ _ _ _).1 hi)
      · rintro (h | h)
        · exact ⟨LabTest.quad u v f1 r f2, List.mem_cons_self, (mem_quad_iff _ _ _ _ _).2 h⟩
        · exact ⟨LabTest.quad u w f1 r f2, List.mem_cons_of_mem _ List.mem_cons_self, (mem_quad_iff _ _ _ _ _).2 h⟩
    rw [used] at hl hl'
    by_cases h1 : (ℓ = v ∨ ℓ = f1 ∨ ℓ = r ∨ ℓ = f2) ∧ (ℓ' = v ∨ ℓ' = f1 ∨ ℓ' = r ∨ ℓ' = f2)
    · exact ⟨LabTest.quad u v f1 r f2, List.mem_cons_self,
        (mem_quad_iff _ _ _ _ _).2 h1.1, (mem_quad_iff _ _ _ _ _).2 h1.2⟩
    by_cases h2 : (ℓ = w ∨ ℓ = f1 ∨ ℓ = r ∨ ℓ = f2) ∧ (ℓ' = w ∨ ℓ' = f1 ∨ ℓ' = r ∨ ℓ' = f2)
    · exact ⟨LabTest.quad u w f1 r f2, List.mem_cons_of_mem _ List.mem_cons_self,
        (mem_quad_iff _ _ _ _ _).2 h2.1, (mem_quad_iff _ _ _ _ _).2 h2.2⟩
    exfalso
    rcases hl with (h|h|h|h)|(h|h|h|h) <;> rcases hl' with (h'|h'|h'|h')|(h'|h'|h'|h') <;>
      subst h h' <;> simp_all

end ViewGroup

/-- `ρ` refines the weak order of the depths along the view of group `a`, on the labels of the group. -/
def RefOn {n : ℕ} {A : Type*} (y : Fin n → ℝ³) (g : A → ViewGroup n) (a : A) (ρ : Fin n → ℝ) : Prop :=
  (∀ ℓ ℓ', (g a).Used ℓ → (g a).Used ℓ' → ρ ℓ = ρ ℓ' → ℓ = ℓ') ∧
  ∀ ℓ ℓ', (g a).Used ℓ → (g a).Used ℓ' → ⟪y ℓ, (g a).view y⟫ < ⟪y ℓ', (g a).view y⟫ → ρ ℓ < ρ ℓ'

theorem r2t_claim {n q : ℕ} {A : Type*} [Fintype A]
    (y : Fin n → ℝ³) (g : A → ViewGroup n)
    (hcov : ∀ a, CovView (g a).view)
    (hord : ∀ a, (g a).Ordered y)
    (hinj : ∀ a, ∀ T ∈ (g a).tests, Function.Injective T.lab)
    (ties : Fin q → A × Fin n × Fin n)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (g (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (g (ties t).1).view y))
    (hcover : ∀ a, ∀ T ∈ (g a).tests, ∀ i j : ZMod T.k, T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j))
    (hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ a, ∀ T ∈ (g a).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ a, ∃ T ∈ (g a).tests, IsCyclicUnimodal (T.depth (mapShape L y)))
    (ρ : A → Fin n → ℝ) (hρ : ∀ a, RefOn y g a (ρ a)) :
    ∃ a, ∃ T ∈ (g a).tests, IsCyclicUnimodal (fun i => ρ a (T.lab i)) := by
  classical
  have hW : ∀ᶠ L in 𝓝 (1 : ℝ³ →L[ℝ] ℝ³), ∀ a ℓ ℓ', (g a).Used ℓ → (g a).Used ℓ' →
      ⟪y ℓ, (g a).view y⟫ < ⟪y ℓ', (g a).view y⟫ →
      ⟪L (y ℓ), L ((g a).view y)⟫ < ⟪L (y ℓ'), L ((g a).view y)⟫ := by
    refine eventually_all.2 fun a => eventually_all.2 fun ℓ => eventually_all.2 fun ℓ' => ?_
    by_cases hU : (g a).Used ℓ ∧ (g a).Used ℓ' ∧ ⟪y ℓ, (g a).view y⟫ < ⟪y ℓ', (g a).view y⟫
    · have hc : ∀ x w : ℝ³, Continuous fun L : ℝ³ →L[ℝ] ℝ³ => ⟪L x, L w⟫ := by
        intro x w; fun_prop
      have := ContinuousAt.eventually_lt (hc (y ℓ) ((g a).view y)).continuousAt
        (hc (y ℓ') ((g a).view y)).continuousAt (by
          show ⟪(1 : ℝ³ →L[ℝ] ℝ³) (y ℓ), (1 : ℝ³ →L[ℝ] ℝ³) ((g a).view y)⟫ < ⟪(1 : ℝ³ →L[ℝ] ℝ³) (y ℓ'), (1 : ℝ³ →L[ℝ] ℝ³) ((g a).view y)⟫
          simpa using hU.2.2)
      filter_upwards [this] with L hL _ _ _ using hL
    · exact Eventually.of_forall fun L h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hU
  obtain ⟨ε, hε, L, ⟨hMFL, hWL⟩, hdet, hLt⟩ := exists_L_scaled
    (fun t => y (ties t).2.1 - y (ties t).2.2) (fun t => (g (ties t).1).view y) hties hind
    (fun t => ρ (ties t).1 (ties t).2.1 - ρ (ties t).1 (ties t).2.2)
    (fun L => (LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ a, ∀ T ∈ (g a).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ a, ∃ T ∈ (g a).tests, IsCyclicUnimodal (T.depth (mapShape L y))) ∧
      ∀ a ℓ ℓ', (g a).Used ℓ → (g a).Used ℓ' → ⟪y ℓ, (g a).view y⟫ < ⟪y ℓ', (g a).view y⟫ →
        ⟪L (y ℓ), L ((g a).view y)⟫ < ⟪L (y ℓ'), L ((g a).view y)⟫)
    (hMF.and hW)
  have tele : ∀ a ℓ ℓ', Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) ℓ ℓ' →
      ⟪L (y ℓ), L ((g a).view y)⟫ - ⟪L (y ℓ'), L ((g a).view y)⟫ = ε * (ρ a ℓ - ρ a ℓ') := by
    intro a ℓ ℓ' h
    induction h with
    | rel x x' hr =>
      obtain ⟨t, rfl, h2⟩ := hr
      have e1 : (ties t).2.1 = x := by rw [h2]
      have e2 : (ties t).2.2 = x' := by rw [h2]
      have := hLt t
      simp only [map_sub, inner_sub_left, e1, e2] at this
      exact this
    | refl x => simp
    | symm x x' _ ih => linarith
    | trans x x' x'' _ _ ih1 ih2 => linarith
  have key : ∀ a ℓ ℓ', (g a).Used ℓ → (g a).Used ℓ' →
      (⟪L (y ℓ), L ((g a).view y)⟫ < ⟪L (y ℓ'), L ((g a).view y)⟫ ↔ ρ a ℓ < ρ a ℓ') := by
    intro a ℓ ℓ' hl hl'
    rcases lt_trichotomy ⟪y ℓ, (g a).view y⟫ ⟪y ℓ', (g a).view y⟫ with h | h | h
    · exact ⟨fun _ => (hρ a).2 _ _ hl hl' h, fun _ => hWL a ℓ ℓ' hl hl' h⟩
    · obtain ⟨T, hT, ⟨i, hi⟩, ⟨j, hj⟩⟩ := ViewGroup.common_test y (g a) (hord a) hl hl' h
      have hd : T.depth y i = T.depth y j := by
        simp only [LabTest.depth, ViewGroup.view_of_mem hT, hi, hj]; exact h
      have := tele a ℓ ℓ' (hi ▸ hj ▸ hcover a T hT i j hd)
      constructor
      · intro h1
        have : 0 < ε * (ρ a ℓ' - ρ a ℓ) := by linarith
        have := (mul_pos_iff_of_pos_left hε).1 this
        linarith
      · intro h1
        have : 0 < ε * (ρ a ℓ' - ρ a ℓ) := mul_pos hε (by linarith)
        linarith
    · exact ⟨fun h1 => absurd h1 (not_lt.2 (hWL a ℓ' ℓ hl' hl h).le),
        fun h1 => absurd h1 (not_lt.2 ((hρ a).2 _ _ hl' hl h).le)⟩
  have hdep : ∀ a, ∀ T ∈ (g a).tests, ∀ i, T.depth (mapShape L y) i = ⟪L (y (T.lab i)), L ((g a).view y)⟫ := by
    intro a T hT i
    simp only [LabTest.depth, ViewGroup.view_of_mem hT, mapShape, (hcov a).2 L y hdet]
  have hUsed : ∀ a, ∀ T ∈ (g a).tests, ∀ i, (g a).Used (T.lab i) := fun a T hT i => ⟨T, hT, i, rfl⟩
  have hinjL : ∀ a, ∀ T ∈ (g a).tests, Function.Injective (T.depth (mapShape L y)) := by
    intro a T hT i j hij
    rw [hdep a T hT, hdep a T hT] at hij
    have h1 := (key a (T.lab i) (T.lab j) (hUsed a T hT i) (hUsed a T hT j))
    have h2 := (key a (T.lab j) (T.lab i) (hUsed a T hT j) (hUsed a T hT i))
    have h3 : ¬ ρ a (T.lab i) < ρ a (T.lab j) := fun h => by rw [← h1] at h; linarith
    have h4 : ¬ ρ a (T.lab j) < ρ a (T.lab i) := fun h => by rw [← h2] at h; linarith
    exact hinj a T hT ((hρ a).1 _ _ (hUsed a T hT i) (hUsed a T hT j)
      (le_antisymm (not_lt.1 h4) (not_lt.1 h3)))
  obtain ⟨a, T, hT, hu⟩ := hMFL hdet hinjL
  refine ⟨a, T, hT, hu.congr_order fun i j => ?_⟩
  rw [hdep a T hT, hdep a T hT]
  exact key a _ _ (hUsed a T hT i) (hUsed a T hT j)


theorem ViewGroup.used_edge {n : ℕ} (u : (Fin n → ℝ³) → ℝ³) (v w f1 r f2 x : Fin n) :
    (ViewGroup.edge u v w f1 r f2).Used x ↔ x = v ∨ x = w ∨ x = f1 ∨ x = r ∨ x = f2 := by
  constructor
  · rintro ⟨T, hT, hi⟩
    simp only [ViewGroup.tests, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · rcases (ViewGroup.mem_quad_iff _ _ _ _ _).1 hi with h | h | h | h <;> simp [h]
    · rcases (ViewGroup.mem_quad_iff _ _ _ _ _).1 hi with h | h | h | h <;> simp [h]
  · intro h
    rcases h with h | h | h | h | h
    · exact ⟨LabTest.quad u v f1 r f2, List.mem_cons_self, (ViewGroup.mem_quad_iff _ _ _ _ _).2 (by simp [h])⟩
    · exact ⟨LabTest.quad u w f1 r f2, List.mem_cons_of_mem _ List.mem_cons_self,
        (ViewGroup.mem_quad_iff _ _ _ _ _).2 (by simp [h])⟩
    · exact ⟨LabTest.quad u v f1 r f2, List.mem_cons_self, (ViewGroup.mem_quad_iff _ _ _ _ _).2 (by simp [h])⟩
    · exact ⟨LabTest.quad u v f1 r f2, List.mem_cons_self, (ViewGroup.mem_quad_iff _ _ _ _ _).2 (by simp [h])⟩
    · exact ⟨LabTest.quad u v f1 r f2, List.mem_cons_self, (ViewGroup.mem_quad_iff _ _ _ _ _).2 (by simp [h])⟩

theorem exists_label_extension {ι : Type*} {n : ℕ} (lab : ι → Fin n) (hinj : Function.Injective lab)
    (ζ : ι → ℝ) : ∃ ρ : Fin n → ℝ, ∀ i, ρ (lab i) = ζ i := by
  classical
  refine ⟨fun ℓ => if h : ∃ i, lab i = ℓ then ζ h.choose else 0, fun i => ?_⟩
  have h : ∃ j, lab j = lab i := ⟨i, rfl⟩
  simp only [dif_pos h]
  rw [hinj h.choose_spec]


/-- **Lemma R2T** (robust rims from MF with two ties; any finite certificate).  A certificate is a
family of view groups `g a`.  `hMF`: at every unimodular metric near the identity at which all rims
have distinct depths, some rim of the certificate is unimodal (Lemma 18.2 (b); affine invariance
makes this a statement about `mapShape L y`).  There are at most two ties `ties t = (a, p, p')`
(tie of the depths of `p, p'` along the view of group `a`), independent, and every tie of every rim
follows from them (`hcover`, through the equivalence relation they generate in the group).  Then
some corner rim of the certificate is robustly unimodal at `y`, unless an edge pair has the
straddling far triple.  Edge groups have `z_w < z_v` at `y`; single tests have `k ≥ 4` (triangles
are robust unless all three depths are equal, `isRobustUnimodal_three`).

`hinj`: labels of every test are distinct (otherwise the depths are never injective and `hMF` is vacuous; ADDED to the planned statement).

Proof: the metrics `L` with prescribed tie values (`exists_L_prescribed_ties`, values `δ ∈ ℝ^q`
small: every refinement of every rim is realized by some `δ`, as depth differences of tied pairs are
affine in `δ`) make `hMF` apply at every combination of refinements; `exists_good_view` gives a view
`a`; inside it `isRobustUnimodal_iff_refinements` (single test) or `lemma292` (edge pair). -/
theorem robust_corner_rim_of_MF {n q : ℕ} {A : Type*} [Fintype A]
    (y : Fin n → ℝ³) (g : A → ViewGroup n)
    (hcov : ∀ a, CovView (g a).view)
    (hord : ∀ a, (g a).Ordered y)
    (hk : ∀ a T, g a = ViewGroup.single T → 4 ≤ T.k)
    (hinj : ∀ a, ∀ T ∈ (g a).tests, Function.Injective T.lab)
    (hq : q ≤ 2) (ties : Fin q → A × Fin n × Fin n)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (g (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (g (ties t).1).view y))
    (hcover : ∀ a, ∀ T ∈ (g a).tests, ∀ i j : ZMod T.k, T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j))
    (hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ a, ∀ T ∈ (g a).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ a, ∃ T ∈ (g a).tests, IsCyclicUnimodal (T.depth (mapShape L y))) :
    (∃ a, ∃ T ∈ (g a).tests, IsRobustUnimodal (T.depth y)) ∨ ∃ a, (g a).Straddle y := by
  classical
  have hgood := exists_good_view (A := A) (S := fun a => {ρ : Fin n → ℝ // RefOn y g a ρ})
    (fun a s => ∃ T ∈ (g a).tests, IsCyclicUnimodal (fun i => s.1 (T.lab i))) (fun σ =>
      r2t_claim y g hcov hord hinj ties hties hind hcover hMF (fun a => (σ a).1) (fun a => (σ a).2))
  obtain ⟨a, ha⟩ := hgood
  have ha' : ∀ ρ : Fin n → ℝ, RefOn y g a ρ → ∃ T ∈ (g a).tests, IsCyclicUnimodal (fun i => ρ (T.lab i)) :=
    fun ρ hρ => ha ⟨ρ, hρ⟩
  have hoa := hord a
  have hia := hinj a
  have hka := hk a
  clear ha
  cases hga : g a with
  | single T =>
    rw [hga] at ha' hia hoa
    left
    refine ⟨a, T, by rw [hga]; simp [ViewGroup.tests], ?_⟩
    refine (isRobustUnimodal_iff_refinements (hka T hga) _).2 ?_
    intro ζ hζ
    obtain ⟨ρ, hρ⟩ := exists_label_extension T.lab (hia T (by simp [ViewGroup.tests])) ζ
    have hU : ∀ ℓ, (ViewGroup.single T).Used ℓ ↔ ∃ i, T.lab i = ℓ := by
      intro ℓ
      constructor
      · rintro ⟨T', hT', hi⟩
        simp [ViewGroup.tests] at hT'
        subst hT'; exact hi
      · rintro ⟨i, hi⟩; exact ⟨T, by simp [ViewGroup.tests], i, hi⟩
    obtain ⟨T', hT', hu⟩ := ha' ρ (by
      unfold RefOn
      simp only [hga]
      constructor
      · intro ℓ ℓ' h1 h2 e
        obtain ⟨i, rfl⟩ := (hU _).1 h1
        obtain ⟨j, rfl⟩ := (hU _).1 h2
        rw [hρ, hρ] at e
        rw [hζ.1 e]
      · intro ℓ ℓ' h1 h2 e
        obtain ⟨i, rfl⟩ := (hU _).1 h1
        obtain ⟨j, rfl⟩ := (hU _).1 h2
        rw [hρ, hρ]
        exact hζ.2 i j e)
    simp [ViewGroup.tests] at hT'
    subst hT'
    convert hu using 1
    funext i; exact (hρ i).symm
  | edge u v w f1 r f2 =>
    rw [hga] at ha' hia hoa
    simp only [ViewGroup.Ordered] at hoa
    have hT1 : LabTest.quad u v f1 r f2 ∈ (ViewGroup.edge u v w f1 r f2).tests := List.mem_cons_self
    have hT2 : LabTest.quad u w f1 r f2 ∈ (ViewGroup.edge u v w f1 r f2).tests :=
      List.mem_cons_of_mem _ List.mem_cons_self
    have hia1 := hia _ hT1
    have hia2 := hia _ hT2
    have n1 : ∀ i j : ZMod 4, i ≠ j → ![v, f1, r, f2] i ≠ ![v, f1, r, f2] j :=
      fun i j hij e => hij (hia1 e)
    have n2 : ∀ i j : ZMod 4, i ≠ j → ![w, f1, r, f2] i ≠ ![w, f1, r, f2] j :=
      fun i j hij e => hij (hia2 e)
    have d_vf1 : v ≠ f1 := n1 0 1 (by decide)
    have d_vr : v ≠ r := n1 0 2 (by decide)
    have d_vf2 : v ≠ f2 := n1 0 3 (by decide)
    have d_f1r : f1 ≠ r := n1 1 2 (by decide)
    have d_f1f2 : f1 ≠ f2 := n1 1 3 (by decide)
    have d_rf2 : r ≠ f2 := n1 2 3 (by decide)
    have d_wf1 : w ≠ f1 := n2 0 1 (by decide)
    have d_wr : w ≠ r := n2 0 2 (by decide)
    have d_wf2 : w ≠ f2 := n2 0 3 (by decide)
    have d_vw : v ≠ w := fun e => by rw [e] at hoa; exact lt_irrefl _ hoa
    have plab_inj : Function.Injective (![v, w, f1, r, f2] : Fin 5 → Fin n) := by
      intro i j h
      have := d_vf1.symm; have := d_vr.symm; have := d_vf2.symm; have := d_f1r.symm
      have := d_f1f2.symm; have := d_rf2.symm; have := d_wf1.symm; have := d_wr.symm
      have := d_wf2.symm; have := d_vw.symm
      fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at h; contradiction)
    set plab : Fin 5 → Fin n := ![v, w, f1, r, f2] with hplab
    set ζ : Fin 5 → ℝ := fun i => ⟪y (plab i), u y⟫ with hζdef
    have hUp : ∀ i, (ViewGroup.edge u v w f1 r f2).Used (plab i) := by
      intro i
      rw [ViewGroup.used_edge]
      fin_cases i <;> simp [plab]
    -- the far-triple count
    have hcard : 3 ≤ (univ.image ζ).card := by
      obtain ⟨ψ, hψ, hψc⟩ := exists_collapse (List.ofFn fun t : Fin q => ((ties t).2.1, (ties t).2.2))
      have hinv : ∀ x x', Relation.EqvGen
          (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) x x' → ψ x = ψ x' := by
        intro x x' h
        induction h with
        | rel x x' hr =>
          obtain ⟨t, -, h2⟩ := hr
          have e1 : (ties t).2.1 = x := by rw [h2]
          have e2 : (ties t).2.2 = x' := by rw [h2]
          have := hψ ((ties t).2.1, (ties t).2.2) (by simp [List.mem_ofFn])
          simpa [e1, e2] using this
        | refl x => rfl
        | symm x x' _ ih => exact ih.symm
        | trans x x' x'' _ _ ih1 ih2 => exact ih1.trans ih2
      have hfac : ∀ i j : Fin 5, ζ i = ζ j → ψ (plab i) = ψ (plab j) := by
        intro i j hij
        obtain ⟨T, hT, ⟨i', hi'⟩, ⟨j', hj'⟩⟩ := ViewGroup.common_test y (ViewGroup.edge u v w f1 r f2)
          (by simpa [ViewGroup.Ordered] using hoa) (hUp i) (hUp j) (by simpa [ζ, ViewGroup.view] using hij)
        have hd : T.depth y i' = T.depth y j' := by
          have hv : T.view = u := by simpa [ViewGroup.view] using ViewGroup.view_of_mem hT
          simp only [LabTest.depth, hv, hi', hj']
          simpa [ζ] using hij
        have := hcover a T (by rw [hga]; exact hT) i' j' hd
        rw [hi', hj'] at this
        exact hinv _ _ this
      have h5 : (univ.image plab).card = 5 := by
        rw [card_image_of_injective _ plab_inj]; simp
      have h1 := hψc (univ.image plab)
      rw [h5, Finset.image_image, List.length_ofFn] at h1
      let h : ℝ → Fin n := fun r => if hr : ∃ i, ζ i = r then ψ (plab hr.choose) else ψ (plab 0)
      have hh : ∀ i, ψ (plab i) = h (ζ i) := by
        intro i
        have hr : ∃ j, ζ j = ζ i := ⟨i, rfl⟩
        simp only [h, dif_pos hr]
        exact (hfac _ _ hr.choose_spec).symm
      have h2 : (univ.image (ψ ∘ plab)).card ≤ (univ.image ζ).card := by
        have : univ.image (ψ ∘ plab) = (univ.image ζ).image h := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro i _
          exact hh i
        rw [this]
        exact card_image_le
      omega
    have hvw : ζ 1 < ζ 0 := by simpa [ζ, plab, ViewGroup.view] using hoa
    have hUi : ∀ ℓ, (ViewGroup.edge u v w f1 r f2).Used ℓ → ∃ i, plab i = ℓ := by
      intro ℓ h
      rw [ViewGroup.used_edge] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    have key := lemma292 ζ hvw hcard (by
      intro ζ' hζ'
      obtain ⟨ρ, hρ⟩ := exists_label_extension plab plab_inj ζ'
      obtain ⟨T', hT', hu⟩ := ha' ρ (by
        unfold RefOn
        simp only [hga]
        constructor
        · intro ℓ ℓ' h1 h2 e
          obtain ⟨i, rfl⟩ := hUi _ h1
          obtain ⟨j, rfl⟩ := hUi _ h2
          rw [hρ, hρ] at e
          rw [hζ'.1 e]
        · intro ℓ ℓ' h1 h2 e
          obtain ⟨i, rfl⟩ := hUi _ h1
          obtain ⟨j, rfl⟩ := hUi _ h2
          rw [hρ, hρ]
          exact hζ'.2 i j e)
      simp only [ViewGroup.tests, List.mem_cons, List.not_mem_nil, or_false] at hT'
      rcases hT' with rfl | rfl
      · left
        have e : (fun i : ZMod 4 => ρ (![v, f1, r, f2] i)) = edgeRim ζ' 0 := by
          funext i
          fin_cases i <;> first | exact (hρ 0) | exact (hρ 2) | exact (hρ 3) | exact (hρ 4)
        exact Eq.mp (congrArg IsCyclicUnimodal e) hu
      · right
        have e : (fun i : ZMod 4 => ρ (![w, f1, r, f2] i)) = edgeRim ζ' 1 := by
          funext i
          fin_cases i <;> first | exact (hρ 1) | exact (hρ 2) | exact (hρ 3) | exact (hρ 4)
        exact Eq.mp (congrArg IsCyclicUnimodal e) hu)
    rcases key with h | h | h
    · left
      refine ⟨a, LabTest.quad u v f1 r f2, by rw [hga]; exact hT1, ?_⟩
      have : (LabTest.quad u v f1 r f2).depth y = edgeRim ζ 0 := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact h
    · left
      refine ⟨a, LabTest.quad u w f1 r f2, by rw [hga]; exact hT2, ?_⟩
      have : (LabTest.quad u w f1 r f2).depth y = edgeRim ζ 1 := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact h
    · right
      exact ⟨a, by rw [hga]; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩


end Minimality
