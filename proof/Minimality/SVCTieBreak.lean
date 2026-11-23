module

public import Minimality.SVCLex

@[expose] public section

/-!
# SVCTieBreak: per-scenario tie breaks for the single-view closure (Task TB24)

`svc_local_tb` is `svc_local_lex` with the rule "exists rim, for all linear extensions" replaced
(for the weak orders that fail it) by "exists rim and ONE extension `L*` realised by a tilt `d1`
constructed from the scenario".  The weak orders are enumerated with all tie pairs allowed; every
weak order is closed by the old rule, vacuous (three tied points that cannot tie), or has a
certificate `(W, rim index, L*)`.  The geometric realisation of a certificate is the hypothesis
`hreal` (a statement `TBReal` about reals), discharged per cell.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.LexCell Minimality.H21

namespace Minimality.SVC

private theorem mem_addCliques_nil {p : ℕ} (T : List (Fin p × Fin p))
    (cur : List (Fin p)) (hne : cur ≠ []) (rem : List (Fin p)) :
    cur.reverse ∈ addCliques T cur rem := by
  induction rem generalizing cur with
  | nil => simp [addCliques, List.isEmpty_iff.not.mpr hne]
  | cons r rs ih =>
    simp only [addCliques]
    split_ifs
    · exact List.mem_append.mpr (Or.inr (ih cur hne))
    · exact ih cur hne

private theorem mem_addCliques {p : ℕ} {T : List (Fin p × Fin p)}
    {cur rem B : List (Fin p)} (hsub : B.Sublist rem) (hnd : rem.Nodup) (hne : B ≠ [])
    (hT : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → allowPair T x y = true)
    (hcurT : ∀ x ∈ cur, ∀ y ∈ B, allowPair T x y = true) :
    cur.reverse ++ B ∈ addCliques T cur rem := by
  induction rem generalizing cur B with
  | nil =>
    rw [List.sublist_nil] at hsub
    exact absurd hsub hne
  | cons r rs ih =>
    have hr_not : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hrs_nd : rs.Nodup := (List.nodup_cons.mp hnd).2
    simp only [addCliques]
    cases hsub with
    | cons _ hsub' =>
      have hr_not_B : r ∉ B := fun hm => hr_not (hsub'.subset hm)
      split_ifs
      · exact List.mem_append.mpr (Or.inr (ih hsub' hrs_nd hne hT hcurT))
      · exact ih hsub' hrs_nd hne hT hcurT
    | cons_cons _ hsub' =>
      rename_i bs
      have hc : cur.all (fun x => allowPair T x r) = true :=
        List.all_eq_true.mpr (fun x hx => hcurT x hx r List.mem_cons_self)
      simp only [hc, ↓reduceIte]
      refine List.mem_append.mpr (Or.inl ?_)
      by_cases hbs : bs = []
      · subst hbs
        simpa using mem_addCliques_nil T (r :: cur) (List.cons_ne_nil _ _) rs
      · have hT' : ∀ x ∈ bs, ∀ y ∈ bs, x ≠ y → allowPair T x y = true :=
          fun x hx y hy hxy => hT x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
        have hcurT' : ∀ x ∈ r :: cur, ∀ y ∈ bs, allowPair T x y = true := by
          intro x hx y hy
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hT x List.mem_cons_self y (List.mem_cons_of_mem _ hy)
              (fun e => hr_not (hsub'.subset (e ▸ hy)))
          · exact hcurT x hx' y (List.mem_cons_of_mem _ hy)
        simpa [List.reverse_cons, List.append_assoc] using ih hsub' hrs_nd hbs hT' hcurT'

private theorem mem_weakOrdersAux {p : ℕ} {T : List (Fin p × Fin p)}
    {fuel : ℕ} {rem : List (Fin p)} (hfuel : rem.length ≤ fuel) (hnd : rem.Nodup)
    {W : List (List (Fin p))}
    (hW_ne : ∀ B ∈ W, B ≠ [])
    (hW_T : ∀ B ∈ W, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → allowPair T x y = true)
    (hW_sub : ∀ B ∈ W, B.Sublist (rem.filter (fun x => x ∈ B)))
    (hW_part : ∀ x, x ∈ rem ↔ ∃ B ∈ W, x ∈ B)
    (hW_disj : W.Pairwise (fun B₁ B₂ => ∀ x ∈ B₁, x ∉ B₂)) :
    W ∈ weakOrdersAux T fuel rem := by
  induction fuel generalizing rem W with
  | zero =>
    have hrem : rem = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hfuel)
    subst hrem
    have hWe : W = [] := by
      cases W with
      | nil => rfl
      | cons B Bs =>
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil B (hW_ne B (by simp))
        have := (hW_part x).mpr ⟨B, by simp, hx⟩
        simp at this
    subst hWe
    simp [weakOrdersAux]
  | succ fuel ih =>
    simp only [weakOrdersAux]
    by_cases hrem : rem.isEmpty
    · simp only [hrem, ↓reduceIte]
      have hrem0 : rem = [] := List.isEmpty_iff.mp hrem
      subst hrem0
      have hWe : W = [] := by
        cases W with
        | nil => rfl
        | cons B Bs =>
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil B (hW_ne B (by simp))
          have := (hW_part x).mpr ⟨B, by simp, hx⟩
          simp at this
      subst hWe
      simp
    · simp only [hrem, ↓reduceIte, Bool.false_eq_true]
      have hrem_ne : rem ≠ [] := List.isEmpty_iff.not.mp hrem
      cases W with
      | nil =>
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil rem hrem_ne
        obtain ⟨B, hB, _⟩ := (hW_part x).mp hx
        simp at hB
      | cons B Bs =>
        refine List.mem_flatMap.mpr ⟨B, ?_, ?_⟩
        · have hB_sub : B.Sublist rem := (hW_sub B (by simp)).trans (List.filter_sublist)
          exact mem_addCliques hB_sub hnd (hW_ne B (by simp))
            (hW_T B (by simp)) (fun x hx => by simp at hx)
        · refine List.mem_map.mpr ⟨Bs, ih ?_ (hnd.filter _) ?_ ?_ ?_ ?_ ?_, rfl⟩
          · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil B (hW_ne B (by simp))
            have hxr : x ∈ rem := ((hW_part x).mpr ⟨B, by simp, hx⟩)
            have hlen : (rem.filter fun y => !B.contains y).length < rem.length := by
              refine List.length_filter_lt_length_iff_exists.mpr ⟨x, hxr, ?_⟩
              simp [hx]
            omega
          · exact fun B' hB' => hW_ne B' (by simp [hB'])
          · exact fun B' hB' => hW_T B' (by simp [hB'])
          · intro B' hB'
            have hdisj := (List.pairwise_cons.mp hW_disj).1 B' hB'
            have hsub' := hW_sub B' (by simp [hB'])
            have heq : rem.filter (fun x => x ∈ B') =
                (rem.filter (fun x => !B.contains x)).filter (fun x => x ∈ B') := by
              rw [List.filter_filter]
              refine List.filter_congr fun x _ => ?_
              by_cases hxB' : x ∈ B'
              · have hxB : x ∉ B := fun h => hdisj x h hxB'
                simp [hxB', hxB]
              · simp [hxB']
            rw [← heq]
            exact hsub'
          · intro x
            simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
              decide_eq_false_iff_not]
            constructor
            · rintro ⟨hxr, hxB⟩
              obtain ⟨B', hB', hxB'⟩ := (hW_part x).mp hxr
              rcases List.mem_cons.mp hB' with rfl | hBs
              · exact absurd hxB' hxB
              · exact ⟨B', hBs, hxB'⟩
            · rintro ⟨B', hB', hxB'⟩
              have hdisj := (List.pairwise_cons.mp hW_disj).1 B' hB'
              refine ⟨(hW_part x).mpr ⟨B', by simp [hB'], hxB'⟩, fun hxB => hdisj x hxB hxB'⟩
          · exact (List.pairwise_cons.mp hW_disj).2

private theorem mem_linExts {p : ℕ} {W : List (List (Fin p))} {L : List (Fin p)}
    (hL : ∃ f : (B : List (Fin p)) → B ∈ W → List (Fin p),
      (∀ B hB, f B hB ∈ B.permutations') ∧
      L = (W.attach.map (fun ⟨B, hB⟩ => f B hB)).flatten) :
    L ∈ linExts W := by
  induction W generalizing L with
  | nil =>
    obtain ⟨f, _, rfl⟩ := hL
    simp [linExts]
  | cons B Bs ih =>
    obtain ⟨f, hf, rfl⟩ := hL
    simp only [linExts, List.mem_flatMap, List.mem_map]
    refine ⟨f B (by simp), hf B (by simp), _, ih ⟨fun B' hB' => f B' (by simp [hB']),
      fun B' hB' => hf B' (by simp [hB']), rfl⟩, ?_⟩
    simp [List.attach_cons, Function.comp_def]

theorem weakOrders_level {p : ℕ} (z : Fin p → ℝ) (T : List (Fin p × Fin p))
    (hT : ∀ i j, i ≠ j → z i = z j → (i, j) ∈ T ∨ (j, i) ∈ T) :
    ∃ W ∈ weakOrders p T, (∀ B ∈ W, ∀ i ∈ B, ∀ j ∈ B, z i = z j) ∧
      W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, z i < z j) ∧ (∀ i, ∃ B ∈ W, i ∈ B) ∧
      ∀ {α : Type*} [LinearOrder α] (key : Fin p → α),
      (∀ i j, z i < z j → key i < key j) → Function.Injective key →
      ∃ L ∈ linExts W, L ∈ (List.finRange p).permutations' ∧
        ∀ i j, rk L i < rk L j → key i < key j := by
  classical
  let vals : List ℝ := ((List.finRange p).map z).dedup.mergeSort (· ≤ ·)
  let mkBlk : ℝ → List (Fin p) := fun v => (List.finRange p).filter (fun i => decide (z i = v))
  let W : List (List (Fin p)) := vals.map mkBlk
  have hvals_nd : vals.Nodup := by
    refine (List.Perm.nodup_iff (List.mergeSort_perm _ _)).mpr ?_
    exact List.nodup_dedup _
  have hvals_sort : vals.Pairwise (· < ·) := by
    have hs := List.pairwise_mergeSort (le := fun a b : ℝ => decide (a ≤ b))
      (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun a b => by simp [le_total]) ((List.finRange p).map z).dedup
    exact List.pairwise_iff_forall_sublist.mpr fun {a b} hab => by
      have hle : a ≤ b := of_decide_eq_true (List.pairwise_iff_forall_sublist.mp hs hab)
      have hne := List.pairwise_iff_forall_sublist.mp hvals_nd hab
      exact lt_of_le_of_ne hle hne
  have hvals_mem : ∀ i : Fin p, z i ∈ vals := fun i => by
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_dedup]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have hW_mem : W ∈ weakOrders p T := by
    refine mem_weakOrdersAux (by simp) (List.nodup_finRange p) ?_ ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hB
      have hv' : v ∈ ((List.finRange p).map z).dedup :=
        (List.mergeSort_perm _ _).mem_iff.mp hv
      obtain ⟨i, _, hi⟩ := List.mem_map.mp (List.mem_dedup.mp hv')
      exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i, by simp [hi]⟩)
    · intro B hB x hx y hy hxy
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
      have hzx : z x = v := by simpa [mkBlk] using (List.mem_filter.mp hx).2
      have hzy : z y = v := by simpa [mkBlk] using (List.mem_filter.mp hy).2
      rcases hT x y hxy (hzx.trans hzy.symm) with h | h
      · simp [allowPair, h]
      · simp [allowPair, h]
    · intro B hB
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
      have : (List.finRange p).filter (fun x => x ∈ mkBlk v) = mkBlk v := by
        refine List.filter_congr fun x _ => ?_
        simp [mkBlk]
      rw [this]
    · intro x
      simp only [List.mem_finRange, true_iff]
      exact ⟨mkBlk (z x), List.mem_map.mpr ⟨z x, hvals_mem x, rfl⟩,
        List.mem_filter.mpr ⟨List.mem_finRange x, by simp⟩⟩
    · refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt x hx₁ hx₂ => ?_)
      have h1 : z x = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hx₁).2
      have h2 : z x = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hx₂).2
      linarith
  have hblk : ∀ B ∈ W, ∀ i ∈ B, ∀ j ∈ B, z i = z j := by
    intro B hB i hi j hj
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
    have h1 : z i = v := by simpa [mkBlk] using (List.mem_filter.mp hi).2
    have h2 : z j = v := by simpa [mkBlk] using (List.mem_filter.mp hj).2
    rw [h1, h2]
  have hpw0 : W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, z i < z j) := by
    refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt x hx₁ y hy₂ => ?_)
    have h1 : z x = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hx₁).2
    have h2 : z y = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hy₂).2
    rw [h1, h2]; exact hlt
  have hcov : ∀ i, ∃ B ∈ W, i ∈ B := fun x =>
    ⟨mkBlk (z x), List.mem_map.mpr ⟨z x, hvals_mem x, rfl⟩,
        List.mem_filter.mpr ⟨List.mem_finRange x, by simp⟩⟩
  refine ⟨W, hW_mem, hblk, hpw0, hcov, fun {α} _ key hmono hinj => ?_⟩
  -- For each block `mkBlk v`, sort it by `key`
  let sortBlk : List (Fin p) → List (Fin p) := fun B =>
    B.mergeSort (fun i j => decide (key i ≤ key j))
  let L : List (Fin p) := (W.map sortBlk).flatten
  have hperm_blk : ∀ B ∈ W, sortBlk B ∈ B.permutations' := fun B _ => by
    rw [List.mem_permutations']
    exact List.mergeSort_perm _ _
  have hL_ext : L ∈ linExts W := by
    refine mem_linExts ⟨fun B _ => sortBlk B, hperm_blk, ?_⟩
    simp [L]
  have hL_perm : L ∈ (List.finRange p).permutations' := by
    rw [List.mem_permutations']
    have h1 : List.Perm L W.flatten := by
      refine List.Perm.flatten_congr ?_
      simp only [List.forall₂_map_left_iff, List.forall₂_same]
      intro B _
      exact List.mergeSort_perm _ _
    have hW_nd : W.flatten.Nodup := by
      refine List.nodup_flatten.mpr ⟨?_, ?_⟩
      · intro B hB
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
        exact (List.nodup_finRange p).filter _
      · refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt x hx₁ hx₂ => ?_)
        have h1 : z x = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hx₁).2
        have h2 : z x = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hx₂).2
        linarith
    have hW_perm : List.Perm W.flatten (List.finRange p) := by
      refine (List.perm_ext_iff_of_nodup hW_nd (List.nodup_finRange p)).mpr fun x => ?_
      simp only [List.mem_flatten, List.mem_finRange, iff_true]
      exact ⟨mkBlk (z x), List.mem_map.mpr ⟨z x, hvals_mem x, rfl⟩,
        List.mem_filter.mpr ⟨List.mem_finRange x, by simp⟩⟩
    exact h1.trans hW_perm
  have hL_nd : L.Nodup :=
    ((List.mem_permutations'.mp hL_perm).nodup_iff).mpr (List.nodup_finRange p)
  have hL_sorted : L.Pairwise (fun i j => key i < key j) := by
    have hsort_pw : ∀ B ∈ W, (sortBlk B).Pairwise (fun i j => key i < key j) := by
      intro B hB
      have hB_nd : B.Nodup := by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hB
        exact (List.nodup_finRange p).filter _
      have hs_nd : (sortBlk B).Nodup :=
        ((List.mergeSort_perm _ _).nodup_iff).mpr hB_nd
      have hs := List.pairwise_mergeSort (le := fun i j => decide (key i ≤ key j))
        (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        (fun a b => by simp [le_total]) B
      exact List.pairwise_iff_forall_sublist.mpr fun {a b} hab => by
        have hle : key a ≤ key b := of_decide_eq_true (List.pairwise_iff_forall_sublist.mp hs hab)
        have hne : a ≠ b := List.pairwise_iff_forall_sublist.mp hs_nd hab
        exact lt_of_le_of_ne hle (fun e => hne (hinj e))
    rw [List.pairwise_flatten]
    refine ⟨fun B' hB' => ?_, ?_⟩
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hB'
      exact hsort_pw B hB
    · have hpw : W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, key i < key j) := by
        refine List.pairwise_map.mpr (hvals_sort.imp fun {v₁ v₂} hlt i hi₁ j hj₂ => ?_)
        have h1 : z i = v₁ := by simpa [mkBlk] using (List.mem_filter.mp hi₁).2
        have h2 : z j = v₂ := by simpa [mkBlk] using (List.mem_filter.mp hj₂).2
        exact hmono i j (h1 ▸ h2 ▸ hlt)
      refine List.pairwise_map.mpr (hpw.imp fun {B₁ B₂} h i hi j hj => ?_)
      exact h i ((List.mergeSort_perm _ _).mem_iff.mp hi) j
        ((List.mergeSort_perm _ _).mem_iff.mp hj)
  refine ⟨L, hL_ext, hL_perm, fun i j hrk => ?_⟩
  have hi : i ∈ L := (List.mem_permutations'.mp hL_perm).mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ L := (List.mem_permutations'.mp hL_perm).mem_iff.mpr (List.mem_finRange j)
  have hlt := (List.pairwise_iff_getElem.mp hL_sorted) (L.idxOf i) (L.idxOf j)
    (List.idxOf_lt_length_of_mem hi) (List.idxOf_lt_length_of_mem hj) hrk
  simpa [List.getElem_idxOf] using hlt

private theorem allWeakOrdersAux_sound {p : ℕ} {T : List (Fin p × Fin p)}
    {f : List (List (Fin p)) → Bool} {fuel : ℕ} {rem : List (Fin p)} {acc : List (List (Fin p))}
    (h : allWeakOrdersAux T f fuel rem acc = true) :
    ∀ W ∈ weakOrdersAux T fuel rem, f (acc.reverse ++ W) = true := by
  induction fuel generalizing rem acc with
  | zero =>
    intro W hW
    simp only [weakOrdersAux, List.mem_singleton] at hW
    subst hW
    simpa [allWeakOrdersAux] using h
  | succ fuel ih =>
    intro W hW
    simp only [allWeakOrdersAux] at h
    simp only [weakOrdersAux] at hW
    by_cases hrem : rem.isEmpty
    · simp only [hrem, ↓reduceIte, List.mem_singleton] at h hW
      subst hW
      simpa using h
    · simp only [hrem, ↓reduceIte, Bool.false_eq_true, List.all_eq_true,
        List.mem_flatMap, List.mem_map] at h hW
      obtain ⟨B, hB, W', hW', rfl⟩ := hW
      have := ih (h B hB) W' hW'
      simpa [List.reverse_cons, List.append_assoc] using this

private theorem testBit_foldl_or {α : Type*} (f : α → ℕ) (init : ℕ) (l : List α)
    {x : α} (hx : x ∈ l) :
    Nat.testBit (l.foldl (fun acc a => acc ||| (1 <<< f a)) init) (f x) = true := by
  have hmono : ∀ (l' : List α) (i : ℕ) (k : ℕ), Nat.testBit i k = true →
      Nat.testBit (l'.foldl (fun acc a => acc ||| (1 <<< f a)) i) k = true := by
    intro l'
    induction l' with
    | nil => intro i k hk; exact hk
    | cons y ys ih =>
      intro i k hk
      apply ih
      simp [Nat.testBit_or, hk]
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [List.foldl_cons]
      apply hmono
      simp [Nat.testBit_or, Nat.testBit_shiftLeft]
    · exact ih _ hx'

private theorem testBit_and_eq {a b k : ℕ} (ha : Nat.testBit a k = true)
    (heq : (a &&& b) == a) : Nat.testBit b k = true := by
  have h := congrArg (fun n => Nat.testBit n k) (beq_iff_eq.mp heq)
  simp only [Nat.testBit_and, ha, Bool.true_and] at h
  exact h

private theorem buildMasks_fold_inv {m p : ℕ} (forced : List (Fin p × Fin p))
    (deps : List (Fin p → SignType)) (R : List (Rim m p))
    (hinj : ∀ L₁ ∈ (List.finRange p).permutations', ∀ L₂ ∈ (List.finRange p).permutations',
      lehmerAux L₁ = lehmerAux L₂ → L₁ = L₂)
    (L : List (Fin p)) (hL : L ∈ (List.finRange p).permutations')
    (l : List (List (Fin p))) (hl : ∀ L' ∈ l, L' ∈ (List.finRange p).permutations')
    (ex₀ : ℕ) (r₀ : List ℕ) (hr₀ : r₀.length = R.length)
    (hex₀ : Nat.testBit ex₀ (lehmerAux L) = true → exclOK_svc forced deps L = true)
    (hr₀_ok : ∀ (ri : ℕ) (hri : ri < R.length), Nat.testBit (r₀.getD ri 0) (lehmerAux L) = true →
      rimOK (R[ri]) L = true) :
    let res := l.foldl (fun (exM, rMs) L' =>
      let idx := lehmerAux L'
      let bit := 1 <<< idx
      if exclOK_svc forced deps L' then (exM ||| bit, rMs)
      else
        let rMs' := List.zipWith (fun ρ msk => if rimOK ρ L' then msk ||| bit else msk) R rMs
        (exM, rMs')) (ex₀, r₀)
    res.2.length = R.length ∧
      (Nat.testBit res.1 (lehmerAux L) = true → exclOK_svc forced deps L = true) ∧
      (∀ ri (hri : ri < R.length), Nat.testBit (res.2.getD ri 0) (lehmerAux L) = true →
        rimOK (R[ri]) L = true) := by
  induction l generalizing ex₀ r₀ with
  | nil => exact ⟨hr₀, hex₀, hr₀_ok⟩
  | cons L' ls ih =>
    have hL' : L' ∈ (List.finRange p).permutations' := hl L' List.mem_cons_self
    have hls : ∀ x ∈ ls, x ∈ (List.finRange p).permutations' :=
      fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons]
    by_cases he : exclOK_svc forced deps L' = true
    · simp only [he, ↓reduceIte]
      refine ih hls (ex₀ ||| (1 <<< lehmerAux L')) r₀ hr₀ (fun h => ?_) hr₀_ok
      simp only [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact hex₀ h
      · have heq : lehmerAux L' = lehmerAux L := by
          by_contra hne
          simp only [Nat.testBit_shiftLeft, Nat.testBit_one_eq_true_iff_self_eq_zero,
            Bool.and_eq_true, decide_eq_true_eq] at h
          exact hne (by omega)
        rw [← hinj L' hL' L hL heq]
        exact he
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      have hlen' : (List.zipWith (fun ρ msk => if rimOK ρ L' then msk ||| (1 <<< lehmerAux L') else msk) R r₀).length = R.length := by
        simp [hr₀]
      refine ih hls ex₀ _ hlen' hex₀ (fun ri hri h => ?_)
      have hri0 : ri < r₀.length := hr₀ ▸ hri
      have hget : (List.zipWith (fun ρ msk => if rimOK ρ L' then msk ||| (1 <<< lehmerAux L') else msk) R r₀).getD ri 0 =
          if rimOK (R[ri]) L' then r₀.getD ri 0 ||| (1 <<< lehmerAux L') else r₀.getD ri 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
          List.getElem?_eq_getElem hri, List.getElem?_eq_getElem hri0]
        rfl
      rw [hget] at h
      split_ifs at h with hr_ok
      · simp only [Nat.testBit_or, Bool.or_eq_true] at h
        rcases h with h | h
        · exact hr₀_ok ri hri h
        · have heq : lehmerAux L' = lehmerAux L := by
            by_contra hne
            simp only [Nat.testBit_shiftLeft, Nat.testBit_one_eq_true_iff_self_eq_zero,
              Bool.and_eq_true, decide_eq_true_eq] at h
            exact hne (by omega)
          rw [← hinj L' hL' L hL heq]
          exact hr_ok
      · exact hr₀_ok ri hri h

private theorem buildMasks_sound {m p : ℕ} {forced : List (Fin p × Fin p)}
    {deps : List (Fin p → SignType)} {R : List (Rim m p)}
    (hinj : ∀ L₁ ∈ (List.finRange p).permutations', ∀ L₂ ∈ (List.finRange p).permutations',
      lehmerAux L₁ = lehmerAux L₂ → L₁ = L₂)
    {L : List (Fin p)} (hL : L ∈ (List.finRange p).permutations') :
    (buildMasks forced deps R).2.length = R.length ∧
      (Nat.testBit (buildMasks forced deps R).1 (lehmerAux L) = true →
        exclOK_svc forced deps L = true) ∧
      (∀ ri (hri : ri < R.length),
        Nat.testBit ((buildMasks forced deps R).2.getD ri 0) (lehmerAux L) = true →
          rimOK (R[ri]) L = true) :=
  buildMasks_fold_inv forced deps R hinj L hL (List.finRange p).permutations'
    (fun _ h => h) 0 (R.map fun _ => 0) (by simp)
    (fun h => by simp at h) (fun ri hri h => by
      have : (R.map (fun _ => (0 : ℕ))).getD ri 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, hri]
      rw [this] at h
      simp at h)
private theorem testBit_foldl_or_mem {l : List ℕ} {init k : ℕ}
    (hinit : Nat.testBit init k = false) (hk : k ∉ l) :
    Nat.testBit (l.foldl (fun acc a => acc ||| (1 <<< a)) init) k = false := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih
    · have hne : a ≠ k := fun h => hk (h ▸ List.mem_cons_self)
      simp only [Nat.testBit_or, hinit, Nat.testBit_shiftLeft, Bool.false_or,
        Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hle : a ≤ k
      · right
        have hpos : 1 ≤ k - a := by omega
        exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) hpos))
      · exact Or.inl hle
    · exact fun h => hk (List.mem_cons_of_mem _ h)

private theorem nodup_of_checkBijection {p : ℕ} (h : checkBijection p = true) :
    ((List.finRange p).permutations'.map lehmerAux).Nodup := by
  classical
  simp only [checkBijection, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hm, hlen⟩ := h
  set idxs := (List.finRange p).permutations'.map lehmerAux
  have hmem : ∀ k ∈ List.range (fact p), k ∈ idxs := by
    intro k hk
    rw [List.mem_range] at hk
    by_contra hnot
    have hf := testBit_foldl_or_mem (init := 0) (k := k) (by simp) hnot
    rw [hm] at hf
    have ht : Nat.testBit ((1 <<< fact p) - 1) k = true := by
      rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hk
    rw [ht] at hf
    cases hf
  have hsub : (List.range (fact p)).toFinset ⊆ idxs.toFinset :=
    fun k hk => List.mem_toFinset.mpr (hmem k (List.mem_toFinset.mp hk))
  have hcard : fact p ≤ idxs.toFinset.card := by
    have hr : (List.range (fact p)).toFinset.card = fact p := by
      rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]
    rw [← hr]
    exact Finset.card_le_card hsub
  have hle := List.toFinset_card_le idxs
  have heq : idxs.dedup.length = idxs.length := by
    rw [← List.card_toFinset]
    omega
  rw [← (List.dedup_sublist idxs).eq_of_length heq]
  exact List.nodup_dedup idxs

theorem tb_lexKey_lt_of_tie {y z w d1 d2 : ℝ³} (h : ⟪y, w⟫ = ⟪z, w⟫) (h1 : ⟪y, d1⟫ < ⟪z, d1⟫) :
    lexKey y w d1 d2 < lexKey z w d1 d2 := by
  unfold lexKey
  refine Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨h, ?_⟩)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h1)

/-- A linear extension of a level-structured weak order respects the strict depth order. -/
theorem tb_rank_lt {p : ℕ} (z : Fin p → ℝ) :
    ∀ (W : List (List (Fin p))) (L : List (Fin p)),
    (∀ B ∈ W, ∀ i ∈ B, ∀ j ∈ B, z i = z j) →
    W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, z i < z j) →
    L ∈ linExts W → ∀ i j, (∃ B ∈ W, i ∈ B) → (∃ B ∈ W, j ∈ B) → z i < z j → rk L i < rk L j := by
  intro W
  induction W with
  | nil => intro L _ _ _ i j hi; obtain ⟨B, hB, _⟩ := hi; simp at hB
  | cons B Bs ih =>
    intro L hblk hpw hL i j hi hj hij
    simp only [linExts, List.mem_flatMap, List.mem_map] at hL
    obtain ⟨perm, hperm, L', hL', rfl⟩ := hL
    have hpm : perm.Perm B := List.mem_permutations'.mp hperm
    have hpw' := List.pairwise_cons.mp hpw
    have hblk' : ∀ B' ∈ Bs, ∀ i ∈ B', ∀ j ∈ B', z i = z j := fun B' hB' => hblk B' (by simp [hB'])
    have hiB : i ∈ B ∨ ∃ B' ∈ Bs, i ∈ B' := by
      obtain ⟨B', hB', hiB'⟩ := hi
      rcases List.mem_cons.mp hB' with rfl | h
      · exact Or.inl hiB'
      · exact Or.inr ⟨B', h, hiB'⟩
    have hjB : j ∈ B ∨ ∃ B' ∈ Bs, j ∈ B' := by
      obtain ⟨B', hB', hjB'⟩ := hj
      rcases List.mem_cons.mp hB' with rfl | h
      · exact Or.inl hjB'
      · exact Or.inr ⟨B', h, hjB'⟩
    have hBB : ∀ k ∈ B, ∀ B' ∈ Bs, ∀ l ∈ B', z k < z l := fun k hk B' hB' l hl => hpw'.1 B' hB' k hk l hl
    rcases hiB with hiB | ⟨Bi, hBi, hiBi⟩
    · rcases hjB with hjB | ⟨Bj, hBj, hjBj⟩
      · have := hblk B (by simp) i hiB j hjB
        rw [this] at hij; exact absurd hij (lt_irrefl _)
      · have hjnp : j ∉ perm := fun hjp => by
          have hjB' := hpm.mem_iff.mp hjp
          have := hBB j hjB' Bj hBj j hjBj
          exact lt_irrefl _ this
        have hip : i ∈ perm := hpm.mem_iff.mpr hiB
        unfold rk
        rw [List.idxOf_append_of_mem hip, List.idxOf_append_of_notMem hjnp]
        have := List.idxOf_lt_length_of_mem hip
        omega
    · rcases hjB with hjB | ⟨Bj, hBj, hjBj⟩
      · have := hBB j hjB Bi hBi i hiBi
        linarith
      · have hinp : i ∉ perm := fun hip => by
          have hiB' := hpm.mem_iff.mp hip
          have := hBB i hiB' Bi hBi i hiBi
          exact lt_irrefl _ this
        have hjnp : j ∉ perm := fun hjp => by
          have hjB' := hpm.mem_iff.mp hjp
          have := hBB j hjB' Bj hBj j hjBj
          exact lt_irrefl _ this
        unfold rk
        rw [List.idxOf_append_of_notMem hinp, List.idxOf_append_of_notMem hjnp]
        have := ih L' hblk' hpw'.2 hL' i j ⟨Bi, hBi, hiBi⟩ ⟨Bj, hBj, hjBj⟩ hij
        unfold rk at this
        omega

/-- All unordered pairs (as `(i, j)` with `i < j`). -/
def tbAllPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.finRange p).flatMap fun i => (List.finRange p).filterMap fun j =>
    if i < j then some (i, j) else none

theorem tb_mem_allPairs {p : ℕ} (i j : Fin p) (h : i ≠ j) :
    (i, j) ∈ tbAllPairs p ∨ (j, i) ∈ tbAllPairs p := by
  rcases lt_or_gt_of_ne h with h | h
  · left; simp [tbAllPairs, List.mem_flatMap, List.mem_filterMap, h]
  · right; simp [tbAllPairs, List.mem_flatMap, List.mem_filterMap, h]

/-- A certificate: weak order `W`, rim index and the chosen linear extension `L`. -/
structure TBCert (p : ℕ) where
  W : List (List (Fin p))
  ri : ℕ
  L : List (Fin p)
  deriving DecidableEq

def tbVac {p : ℕ} (vacs : List (Fin p × Fin p × Fin p)) (W : List (List (Fin p))) : Bool :=
  W.any fun B => vacs.any fun tr => B.contains tr.1 && B.contains tr.2.1 && B.contains tr.2.2

def tbCertOK {m p : ℕ} (R : List (Rim m p)) (forced : List (Fin p × Fin p))
    (deps : List (Fin p → SignType)) (c : TBCert p) : Bool :=
  decide (c.L ∈ linExts c.W) &&
    ((R[c.ri]?).any fun ρ => exclOK_svc forced deps c.L || rimOK ρ c.L)

def tbCertCase {m p : ℕ} (R : List (Rim m p)) (forced : List (Fin p × Fin p))
    (deps : List (Fin p → SignType)) (certs : List (TBCert p)) (W : List (List (Fin p))) : Bool :=
  certs.any (fun c => decide (c.W = W)) &&
    certs.all fun c => decide (c.W ≠ W) || tbCertOK R forced deps c

/-- The check: rims valid, and every weak order (all tie pairs allowed) is closed by the old rule
(bitmask form of `checkW`), vacuous, or certified. -/
def tbCheck {m n p : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin p → Fin n) (sw : Fin m → SignType)
    (forced : List (Fin p × Fin p)) (deps : List (Fin p → SignType)) (R : List (Rim m p))
    (vacs : List (Fin p × Fin p × Fin p)) (certs : List (TBCert p)) : Bool :=
  R.all (rimValid S P sw) && checkBijection p &&
    let pM := buildMasks forced deps R
    allWeakOrdersAux (tbAllPairs p) (fun W =>
      let wMask := (linExts W).foldl (fun acc L => acc ||| (1 <<< lehmerAux L)) 0
      (wMask &&& pM.1) == wMask || pM.2.any (fun rM => (wMask &&& (pM.1 ||| rM)) == wMask) ||
        tbVac vacs W || tbCertCase R forced deps certs W) p (List.finRange p) []

/-- Level structure of a weak order with respect to depths `z`. -/
def TBLevel {p : ℕ} (z : Fin p → ℝ) (W : List (List (Fin p))) : Prop :=
  (∀ B ∈ W, ∀ i ∈ B, ∀ j ∈ B, z i = z j) ∧
    W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, z i < z j) ∧ (∀ i, ∃ B ∈ W, i ∈ B)

/-- Realisation of a certificate: a tilt `d1` with the rim's signs on the zero facets, a basis
`(w, d1, d2)`, and `d1` orders every tie as the extension `L` does. -/
def TBReal {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : S0xFac m S x)
    (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType) (R : List (Rim m p))
    (c : TBCert p) : Prop :=
  ∃ ρ, R[c.ri]? = some ρ ∧ ∃ d1 d2 : ℝ³,
    (∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t) ∧ Split.det3 w d1 d2 ≠ 0 ∧
    ∀ i j, ⟪x (P i), w⟫ = ⟪x (P j), w⟫ → rk c.L i < rk c.L j → ⟪x (P i), d1⟫ < ⟪x (P j), d1⟫

theorem svc_local_tb {m n p : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (P : Fin p → Fin n) (w : ℝ³) (sw : Fin m → SignType)
    (R : List (Rim m p)) (hne : R ≠ [])
    (hsw : ∀ ρ ∈ R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = sw t)
    (hR : ∀ ρ ∈ R, ∃ d1 d2 : ℝ³,
      (∀ t, sw t = 0 → SignType.sign ⟪F.N t, d1⟫ = ρ.sd t) ∧ Split.det3 w d1 d2 ≠ 0)
    (forced : List (Fin p × Fin p))
    (hforced : ∀ ij ∈ forced, ⟪x (P ij.2), w⟫ < ⟪x (P ij.1), w⟫)
    (deps : List (Fin p → SignType))
    (hdeps : ∀ s ∈ deps, ∃ mu : Fin p → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = s i)
    (hP : Function.Injective (fun i => x (P i)))
    (vacs : List (Fin p × Fin p × Fin p))
    (hvac : ∀ tr ∈ vacs, ¬ (⟪x (P tr.1), w⟫ = ⟪x (P tr.2.1), w⟫ ∧
      ⟪x (P tr.2.1), w⟫ = ⟪x (P tr.2.2), w⟫))
    (certs : List (TBCert p))
    (hreal : ∀ W, TBLevel (fun i => ⟪x (P i), w⟫) W → (∃ c ∈ certs, c.W = W) →
      ∃ c ∈ certs, c.W = W ∧ TBReal F P w sw R c)
    (hcheck : tbCheck S P sw forced deps R vacs certs = true) : Minimality.Gen.LexAny F := by
  classical
  obtain ⟨W, hW, hblk, hpw, hcov, hW_ext⟩ :=
    weakOrders_level (fun i => ⟪x (P i), w⟫) (tbAllPairs p)
      (fun i j hij heq => tb_mem_allPairs i j hij)
  simp only [tbCheck, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨⟨hval, hbij⟩, hclosed⟩ := hcheck
  have hnd : ((List.finRange p).permutations'.map lehmerAux).Nodup :=
    nodup_of_checkBijection hbij
  have hinj : ∀ L₁ ∈ (List.finRange p).permutations', ∀ L₂ ∈ (List.finRange p).permutations',
      lehmerAux L₁ = lehmerAux L₂ → L₁ = L₂ := by
    intro L₁ h1 L₂ h2 heq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h1
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
    have hij : i = j := by
      have hfin : (⟨i, by simpa using hi⟩ : Fin ((List.finRange p).permutations'.map lehmerAux).length) =
          ⟨j, by simpa using hj⟩ :=
        List.nodup_iff_injective_getElem.mp hnd (by simpa using heq)
      exact congrArg Fin.val hfin
    subst hij
    rfl
  have hWc := allWeakOrdersAux_sound hclosed W hW
  simp only [List.reverse_nil, List.nil_append, Bool.or_eq_true, List.any_eq_true, tbVac,
    tbCertCase, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem] at hWc
  rcases hWc with ((hexcl | ⟨rM, hrM, hrim⟩) | ⟨B, hB, tr, htr, ⟨h1, h2⟩, h3⟩) |
      ⟨⟨c0, hc0, hc0W⟩, hallc⟩
  · obtain ⟨ρ0, hρ0⟩ := List.exists_mem_of_ne_nil R hne
    obtain ⟨d1, d2, _, hdet⟩ := hR ρ0 hρ0
    obtain ⟨L, hL, hLp, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (hP e)) h)
    have hbit := testBit_and_eq (testBit_foldl_or lehmerAux 0 (linExts W) hL) hexcl
    have hex := (buildMasks_sound hinj hLp).2.1 hbit
    exact (exclOK_svc_lex_false hforced hdeps hrk hex).elim
  · have hL0 : List.finRange p ∈ (List.finRange p).permutations' :=
      List.mem_permutations'.mpr (List.Perm.refl _)
    have hlen := (buildMasks_sound (forced := forced) (deps := deps) (R := R) hinj hL0).1
    have ⟨ri, hri_len, hri_eq⟩ : ∃ ri, ∃ hri : ri < (buildMasks forced deps R).2.length,
        (buildMasks forced deps R).2[ri] = rM := List.mem_iff_getElem.mp hrM
    have hri : ri < R.length := hlen ▸ hri_len
    let ρ := R[ri]
    have hρ : ρ ∈ R := List.getElem_mem hri
    obtain ⟨d1, d2, hd1, hdet⟩ := hR ρ hρ
    obtain ⟨L, hL, hLp, hrk⟩ := hW_ext (fun i => lexKey (x (P i)) w d1 d2)
      (fun _ _ h => lexKey_lt_of_lt h)
      (fun i j h => by by_contra hne'; exact lexKey_ne hdet (fun e => hne' (hP e)) h)
    have hbit := testBit_and_eq (testBit_foldl_or lehmerAux 0 (linExts W) hL) hrim
    rw [Nat.testBit_or, Bool.or_eq_true] at hbit
    rcases hbit with hex_bit | hrim_bit
    · exact (exclOK_svc_lex_false hforced hdeps hrk
        ((buildMasks_sound hinj hLp).2.1 hex_bit)).elim
    · have hrM_get : (buildMasks forced deps R).2.getD ri 0 = rM := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hri_len, hri_eq]
      rw [← hrM_get] at hrim_bit
      have hok := (buildMasks_sound hinj hLp).2.2 ri hri hrim_bit
      exact lexAny_of_rimOK_lex F P w d1 d2 sw ρ (hsw ρ hρ) hd1 (hval ρ hρ) hrk hok
  · exact absurd ⟨(hblk B hB _ h1 _ h2), (hblk B hB _ h2 _ h3)⟩ (hvac tr htr)
  · obtain ⟨c, hc, hcW, ρ, hρ, d1, d2, hd1, hdet, hties⟩ :=
      hreal W ⟨hblk, hpw, hcov⟩ ⟨c0, hc0, of_decide_eq_true hc0W⟩
    have hok := hallc c hc
    simp only [decide_eq_true_eq, tbCertOK, Bool.and_eq_true, ne_eq] at hok
    have hcW' : c.W = W := hcW
    rcases hok with hne' | ⟨hext, hrim⟩
    · simp [hcW'] at hne'
    · have hext' : c.L ∈ linExts W := by rw [← hcW']; simpa using hext
      have hρR : ρ ∈ R := List.mem_of_getElem? hρ
      have hrk : ∀ i j, rk c.L i < rk c.L j →
          lexKey (x (P i)) w d1 d2 < lexKey (x (P j)) w d1 d2 := by
        intro i j hij
        rcases lt_trichotomy ⟪x (P i), w⟫ ⟪x (P j), w⟫ with h | h | h
        · exact lexKey_lt_of_lt h
        · exact tb_lexKey_lt_of_tie h (hties i j h hij)
        · exfalso
          have := tb_rank_lt (fun i => ⟪x (P i), w⟫) W c.L hblk hpw hext' j i (hcov j) (hcov i) h
          omega
      simp only [hρ, Option.any_some, Bool.or_eq_true] at hrim
      rcases hrim with hex | hok'
      · exact (exclOK_svc_lex_false hforced hdeps hrk hex).elim
      · exact lexAny_of_rimOK_lex F P w d1 d2 sw ρ (hsw ρ hρR) hd1 (hval ρ hρR) hrk hok'

end Minimality.SVC
