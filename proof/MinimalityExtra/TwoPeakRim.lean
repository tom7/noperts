module

public import Mathlib
public import MinimalityExtra
public import MinimalityExtra.MetricUniform

@[expose] public section

/-!
# Theorem U for a rim of any length

Proof of `TwoPeakedRimOpenSetOfMetrics`.  Four non-coplanar corners, taken in cyclic order, have
skew diagonals; a linear functional puts one diagonal above the other; two arcs of the cycle then
each carry a peak.  The functional is perturbed (sign, `ℓ v > 0`, genericity) inside a nonempty
open set, and realised as `G v` by Theorem F (`thmF`).
-/

open Matrix

namespace MinimalityExtra


lemma lin_eq_dot (ℓ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) : ∃ n : Fin 3 → ℝ, ∀ y, ℓ y = n ⬝ᵥ y := by
  refine ⟨fun i => ℓ (Pi.single i 1), fun y => ?_⟩
  have : y = y 0 • (Pi.single 0 1 : Fin 3 → ℝ) + y 1 • (Pi.single 1 1 : Fin 3 → ℝ)
      + y 2 • (Pi.single 2 1 : Fin 3 → ℝ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul, dotProduct, Fin.sum_univ_three]
  ring

/-- prescribed values on four affinely independent points -/
lemma prescribe {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (p : Fin 3 → ZMod k)
    (hli : LinearIndependent ℝ (fun j => x (p j) - x 0)) (g : ZMod k → ℝ) :
    ∃ (n : Fin 3 → ℝ) (c0 : ℝ), n ⬝ᵥ x 0 = g 0 + c0 ∧ ∀ j, n ⬝ᵥ x (p j) = g (p j) + c0 := by
  let b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ∀ j, b j = x (p j) - x 0 := fun j => by simp [b]
  let ℓ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := b.constr ℝ (fun j => g (p j) - g 0)
  have hℓ : ∀ j, ℓ (x (p j) - x 0) = g (p j) - g 0 := fun j => by
    rw [← hb]; simp [ℓ]
  obtain ⟨n, hn⟩ := lin_eq_dot ℓ
  refine ⟨n, n ⬝ᵥ x 0 - g 0, by ring, fun j => ?_⟩
  have := hℓ j
  rw [hn, dotProduct_sub] at this
  linarith

lemma exists_dual_of_not_span_top {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ)
    (h : Submodule.span ℝ (Set.range fun i => x i - x 0) ≠ ⊤) :
    ∃ n : Fin 3 → ℝ, n ≠ 0 ∧ ∀ i, n ⬝ᵥ x i = n ⬝ᵥ x 0 := by
  have hlt : Submodule.span ℝ (Set.range fun i => x i - x 0) < ⊤ := lt_top_iff_ne_top.2 h
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  obtain ⟨n, hn⟩ := lin_eq_dot f
  refine ⟨n, ?_, fun i => ?_⟩
  · rintro rfl
    apply hf0
    ext y
    simp [hn]
  · have : f (x i - x 0) = 0 := by
      have hmem : f (x i - x 0) ∈ (Submodule.span ℝ (Set.range fun i => x i - x 0)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
      rw [hf] at hmem; simpa using hmem
    rw [hn, dotProduct_sub] at this
    linarith



lemma exists_sep {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ)
    (hnc : ¬ ∃ n : Fin 3 → ℝ, n ≠ 0 ∧ ∀ i, n ⬝ᵥ x i = n ⬝ᵥ x 0) :
    ∃ a b c d : ℕ, a < b ∧ b < c ∧ c < d ∧ d < k ∧ ∃ l : Fin 3 → ℝ,
      l ⬝ᵥ x (b : ZMod k) < l ⬝ᵥ x (a : ZMod k) ∧ l ⬝ᵥ x (b : ZMod k) < l ⬝ᵥ x (c : ZMod k) ∧
      l ⬝ᵥ x (d : ZMod k) < l ⬝ᵥ x (a : ZMod k) ∧ l ⬝ᵥ x (d : ZMod k) < l ⬝ᵥ x (c : ZMod k) := by
  have hspan : Submodule.span ℝ (Set.range fun i => x i - x 0) = ⊤ := by
    by_contra h
    exact hnc (exists_dual_of_not_span_top x h)
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => x i - x 0)) = 3 := by
    rw [hspan]; simp
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range fun i => x i - x 0)
  obtain ⟨f0, hfs0, -, hli0⟩ := hex
  let f : Fin 3 → Fin 3 → ℝ := fun j => f0 (Fin.cast h3.symm j)
  have hfs : ∀ j, f j ∈ Set.range fun i => x i - x 0 := fun j => hfs0 _
  have hli : LinearIndependent ℝ f := hli0.comp _ (Fin.cast_injective _)
  choose p hp using hfs
  have hli' : LinearIndependent ℝ (fun j => x (p j) - x 0) := by
    have : (fun j => x (p j) - x 0) = f := funext hp
    rw [this]; exact hli
  have hpinj : Function.Injective p := by
    intro i j hij
    apply hli.injective
    rw [← hp i, ← hp j, hij]
  have hp0 : ∀ j, p j ≠ 0 := by
    intro j h
    have : f j = 0 := by rw [← hp j, h]; simp
    exact hli.ne_zero j this
  let q : Fin 4 → ZMod k := Fin.cons 0 p
  have hq : Function.Injective q := by
    rw [Fin.cons_injective_iff]
    refine ⟨?_, hpinj⟩
    rintro ⟨j, hj⟩; exact hp0 j hj
  let S : Finset ℕ := Finset.univ.image (fun j : Fin 4 => (q j).val)
  have hS : S.card = 4 := by
    have hinj : Function.Injective (fun j : Fin 4 => (q j).val) := (ZMod.val_injective k).comp hq
    show (Finset.univ.image (fun j : Fin 4 => (q j).val)).card = 4
    rw [Finset.card_image_of_injective _ hinj]; simp
  let emb := S.orderEmbOfFin hS
  have hmem : ∀ i : Fin 4, ∃ j, ((q j).val = emb i) := fun i => by
    have := Finset.orderEmbOfFin_mem S hS i
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 this
    exact ⟨j, hj⟩
  have hlt : ∀ i : Fin 4, emb i < k := fun i => by
    obtain ⟨j, hj⟩ := hmem i
    rw [← hj]; exact ZMod.val_lt _
  have hcast : ∀ i : Fin 4, ∃ j, ((emb i : ℕ) : ZMod k) = q j := fun i => by
    obtain ⟨j, hj⟩ := hmem i
    exact ⟨j, by rw [← hj]; simp⟩
  have hmono : StrictMono emb := emb.strictMono
  set a := emb 0 with ha
  set b := emb 1 with hb
  set c := emb 2 with hc
  set d := emb 3 with hd
  have hab : a < b := hmono (by decide)
  have hbc : b < c := hmono (by decide)
  have hcd : c < d := hmono (by decide)
  have hdk : d < k := hlt 3
  let g : ZMod k → ℝ := fun s => if s.val = a ∨ s.val = c then 1 else 0
  obtain ⟨n, c0, h0, hj⟩ := prescribe x p hli' g
  have hall : ∀ j : Fin 4, n ⬝ᵥ x (q j) = g (q j) + c0 := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [q] using h0
    · simpa [q] using hj j
  have key : ∀ i : Fin 4, n ⬝ᵥ x ((emb i : ℕ) : ZMod k) = g ((emb i : ℕ) : ZMod k) + c0 := by
    intro i
    obtain ⟨j, hj⟩ := hcast i
    rw [hj]; exact hall j
  have gv : ∀ i : Fin 4, g ((emb i : ℕ) : ZMod k) = if emb i = a ∨ emb i = c then 1 else 0 := by
    intro i
    simp only [g, ZMod.val_natCast_of_lt (hlt i)]
  have ga : g (a : ZMod k) = 1 := by rw [gv 0]; exact ite_eq_left (Or.inl rfl)
  have gc : g (c : ZMod k) = 1 := by rw [gv 2]; exact ite_eq_left (Or.inr rfl)
  have gb : g (b : ZMod k) = 0 := by
    rw [gv 1]; exact ite_eq_right (by show ¬(b = a ∨ b = c); omega)
  have gd : g (d : ZMod k) = 0 := by
    rw [gv 3]; exact ite_eq_right (by show ¬(d = a ∨ d = c); omega)
  refine ⟨a, b, c, d, hab, hbc, hcd, hdk, n, ?_, ?_, ?_, ?_⟩
  · rw [key 1, key 0, gb, ga]; linarith
  · rw [key 1, key 2, gb, gc]; linarith
  · rw [key 3, key 0, gd, ga]; linarith
  · rw [key 3, key 2, gd, gc]; linarith



lemma not_unimodal_of_two_peaks {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (i j : ZMod k) (hij : i ≠ j)
    (hi : IsCyclicPeak z i) (hj : IsCyclicPeak z j) : ¬ IsCyclicUnimodal z := by
  rintro ⟨-, h⟩
  have : 1 < (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card :=
    Finset.one_lt_card.2 ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi, j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hj, hij⟩
  omega

/-- an interior maximum of an arc is a cyclic peak -/
lemma arc_peak {k : ℕ} [NeZero k] (hk : 2 ≤ k) (z : ZMod k → ℝ) (hz : Function.Injective z)
    (p q r : ℕ) (hpr : p < r) (hrq : r < q) (h1 : z p < z r) (h2 : z q < z r) :
    ∃ j : ℕ, p < j ∧ j < q ∧ IsCyclicPeak z (j : ZMod k) := by
  have : Fact (1 < k) := ⟨by omega⟩
  have h10 : (1 : ZMod k) ≠ 0 := one_ne_zero
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.Icc p q) (fun n : ℕ => z (n : ZMod k))
    ⟨r, Finset.mem_Icc.2 ⟨hpr.le, hrq.le⟩⟩
  rw [Finset.mem_Icc] at hj
  have hrj : z (r : ZMod k) ≤ z (j : ZMod k) :=
    hmax r (Finset.mem_Icc.2 ⟨hpr.le, hrq.le⟩)
  have hjp : p < j := by
    rcases eq_or_lt_of_le hj.1 with h | h
    · subst h; linarith
    · exact h
  have hjq : j < q := by
    rcases eq_or_lt_of_le hj.2 with h | h
    · subst h; linarith
    · exact h
  refine ⟨j, hjp, hjq, ?_, ?_⟩
  · have e : ((j : ZMod k) - 1) = ((j - 1 : ℕ) : ZMod k) := by
      rw [Nat.cast_sub (by omega)]; simp
    show z ((j : ZMod k) - 1) < z (j : ZMod k)
    rw [e]
    refine lt_of_le_of_ne (hmax _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)) ?_
    intro h
    have := hz h
    rw [← e] at this
    have h2 : (1 : ZMod k) = 0 := by
      have := congrArg (fun t => (j : ZMod k) - t) this
      simpa using this
    exact h10 h2
  · have e : ((j : ZMod k) + 1) = ((j + 1 : ℕ) : ZMod k) := by simp
    show z ((j : ZMod k) + 1) < z (j : ZMod k)
    rw [e]
    refine lt_of_le_of_ne (hmax _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)) ?_
    intro h
    have := hz h
    rw [← e] at this
    have h2 : (1 : ZMod k) = 0 := by
      have := congrArg (fun t => t - (j : ZMod k)) this
      simpa using this
    exact h10 h2

/-- two interleaved high/low pairs on a cycle give two peaks -/
lemma two_peaks_of_interleaved {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (hz : Function.Injective z)
    (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + k)
    (h1 : z b < z a ∧ z b < z c ∧ z d < z a ∧ z d < z c) :
    ∃ i j : ZMod k, i ≠ j ∧ IsCyclicPeak z i ∧ IsCyclicPeak z j := by
  have hk : 2 ≤ k := by omega
  obtain ⟨hba, hbc', hda', hdc⟩ := h1
  obtain ⟨j1, hj1a, hj1b, hp1⟩ := arc_peak hk z hz b d c hbc hcd hbc' hdc
  have ca : ((a + k : ℕ) : ZMod k) = (a : ZMod k) := by simp
  have cb : ((b + k : ℕ) : ZMod k) = (b : ZMod k) := by simp
  obtain ⟨j2, hj2a, hj2b, hp2⟩ := arc_peak hk z hz d (b + k) (a + k) hda (by omega)
    (by rw [ca]; exact hda')
    (by rw [cb, ca]; exact hba)
  refine ⟨(j1 : ZMod k), (j2 : ZMod k), ?_, hp1, hp2⟩
  intro h
  have h' : Nat.ModEq k j1 j2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h
  have := (Nat.modEq_iff_dvd' (by omega)).1 h'
  have := Nat.le_of_dvd (by omega) this
  omega



lemma cont_dot (w : Fin 3 → ℝ) : Continuous fun l : Fin 3 → ℝ => l ⬝ᵥ w := by
  simp only [dotProduct]; fun_prop

lemma dense_ne (d : Fin 3 → ℝ) (hd : d ≠ 0) : Dense {l : Fin 3 → ℝ | l ⬝ᵥ d ≠ 0} := by
  let P : Submodule ℝ (Fin 3 → ℝ) :=
    { carrier := {l | l ⬝ᵥ d = 0}
      add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq, add_dotProduct] at *; rw [ha, hb]; simp
      zero_mem' := by simp
      smul_mem' := by intro c a ha; simp only [Set.mem_ofPred_eq, smul_dotProduct] at *; rw [ha]; simp }
  have hP : P ≠ ⊤ := by
    intro h
    have : d ∈ P := by rw [h]; trivial
    have h2 : d ⬝ᵥ d = 0 := this
    exact hd (dotProduct_self_eq_zero.1 h2)
  have hint : interior (P : Set (Fin 3 → ℝ)) = ∅ := by
    by_contra hne
    exact hP (P.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 hne))
  have := interior_eq_empty_iff_dense_compl.1 hint
  convert this using 1
  ext l
  simp [P]

lemma dense_generic {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (hx : Function.Injective x) :
    Dense {l : Fin 3 → ℝ | ∀ m m' : ZMod k, m ≠ m' → l ⬝ᵥ x m ≠ l ⬝ᵥ x m'} := by
  have : {l : Fin 3 → ℝ | ∀ m m' : ZMod k, m ≠ m' → l ⬝ᵥ x m ≠ l ⬝ᵥ x m'} =
      ⋂ p : ZMod k × ZMod k, {l : Fin 3 → ℝ | p.1 ≠ p.2 → l ⬝ᵥ x p.1 ≠ l ⬝ᵥ x p.2} := by
    ext l; simp
  rw [this]
  apply dense_iInter_of_isOpen
  · intro p
    by_cases h : p.1 = p.2
    · simp [h]
    · have : {l : Fin 3 → ℝ | p.1 ≠ p.2 → l ⬝ᵥ x p.1 ≠ l ⬝ᵥ x p.2} =
          {l | l ⬝ᵥ x p.1 ≠ l ⬝ᵥ x p.2} := by ext l; simp [h]
      rw [this]
      exact isOpen_ne_fun (cont_dot _) (cont_dot _)
  · intro p
    by_cases h : p.1 = p.2
    · simp [h]
    · have hd : x p.1 - x p.2 ≠ 0 := sub_ne_zero.2 (fun e => h (hx e))
      have := dense_ne _ hd
      convert this using 1
      ext l
      simp [h, dotProduct_sub, sub_eq_zero]



lemma cont_depth {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (v : Fin 3 → ℝ) (m : ZMod k) :
    Continuous fun G : {G : Matrix (Fin 3) (Fin 3) ℝ // G.PosDef} => depth G.1 v (x m) := by
  have hc : ∀ i j, Continuous fun G : {G : Matrix (Fin 3) (Fin 3) ℝ // G.PosDef} => G.1 i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  simp only [depth, dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => (continuous_finsetSum _ fun j _ =>
    (hc i j).mul continuous_const).mul continuous_const

lemma isOpen_twoPeakMetrics {k : ℕ} [NeZero k] (x : ZMod k → Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    IsOpen (twoPeakMetrics x v) := by
  have : twoPeakMetrics x v = ⋃ i : ZMod k, ⋃ j : ZMod k, ⋃ _ : i ≠ j,
      ({G | IsCyclicPeak (fun m => depth G.1 v (x m)) i} ∩
        {G | IsCyclicPeak (fun m => depth G.1 v (x m)) j}) := by
    ext G
    simp only [twoPeakMetrics, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨i, j, h, a, b⟩; exact ⟨i, j, h, a, b⟩
    · rintro ⟨i, j, h, a, b⟩; exact ⟨i, j, h, a, b⟩
  rw [this]
  refine isOpen_iUnion fun i => isOpen_iUnion fun j => isOpen_iUnion fun _ => ?_
  have hp : ∀ i : ZMod k, IsOpen {G : {G : Matrix (Fin 3) (Fin 3) ℝ // G.PosDef} |
      IsCyclicPeak (fun m => depth G.1 v (x m)) i} := by
    intro i
    exact (isOpen_lt (cont_depth x v _) (cont_depth x v _)).inter
      (isOpen_lt (cont_depth x v _) (cont_depth x v _))
  exact (hp i).inter (hp j)

theorem twoPeakedRimOpenSetOfMetrics : TwoPeakedRimOpenSetOfMetrics := by
  intro k _ x v hinj hnc hv
  refine ⟨isOpen_twoPeakMetrics x v, ?_, fun G hG => ?_⟩
  · obtain ⟨a, b, c, d, hab, hbc, hcd, hdk, l, h1, h2, h3, h4⟩ := exists_sep x hnc
    let Hi : (Fin 3 → ℝ) → Prop := fun l => l ⬝ᵥ x (b : ZMod k) < l ⬝ᵥ x (a : ZMod k) ∧
      l ⬝ᵥ x (b : ZMod k) < l ⬝ᵥ x (c : ZMod k) ∧ l ⬝ᵥ x (d : ZMod k) < l ⬝ᵥ x (a : ZMod k) ∧
      l ⬝ᵥ x (d : ZMod k) < l ⬝ᵥ x (c : ZMod k)
    let Hi' : (Fin 3 → ℝ) → Prop := fun l => l ⬝ᵥ x (a : ZMod k) < l ⬝ᵥ x (b : ZMod k) ∧
      l ⬝ᵥ x (c : ZMod k) < l ⬝ᵥ x (b : ZMod k) ∧ l ⬝ᵥ x (a : ZMod k) < l ⬝ᵥ x (d : ZMod k) ∧
      l ⬝ᵥ x (c : ZMod k) < l ⬝ᵥ x (d : ZMod k)
    have oHi : IsOpen {l | Hi l} := by
      refine (isOpen_lt (cont_dot _) (cont_dot _)).inter ((isOpen_lt (cont_dot _) (cont_dot _)).inter
        ((isOpen_lt (cont_dot _) (cont_dot _)).inter (isOpen_lt (cont_dot _) (cont_dot _))))
    have oHi' : IsOpen {l | Hi' l} := by
      refine (isOpen_lt (cont_dot _) (cont_dot _)).inter ((isOpen_lt (cont_dot _) (cont_dot _)).inter
        ((isOpen_lt (cont_dot _) (cont_dot _)).inter (isOpen_lt (cont_dot _) (cont_dot _))))
    have opos : IsOpen {l : Fin 3 → ℝ | 0 < l ⬝ᵥ v} := isOpen_lt continuous_const (cont_dot _)
    have hl : Hi l := ⟨h1, h2, h3, h4⟩
    -- a nonempty open set among the two
    have hne : ({l | Hi l} ∩ {l | 0 < l ⬝ᵥ v}).Nonempty ∨
        ({l | Hi' l} ∩ {l | 0 < l ⬝ᵥ v}).Nonempty := by
      rcases lt_trichotomy (l ⬝ᵥ v) 0 with h | h | h
      · right
        refine ⟨-l, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Set.mem_ofPred_eq, neg_dotProduct] <;>
          linarith [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2]
      · left
        have hmap : Continuous fun t : ℝ => l + t • v := by fun_prop
        have ho : IsOpen {t : ℝ | Hi (l + t • v)} := oHi.preimage hmap
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho 0 (by simpa using hl)
        have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
          rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith
        refine ⟨l + (ε / 2) • v, hball ht, ?_⟩
        show 0 < (l + (ε / 2) • v) ⬝ᵥ v
        rw [add_dotProduct, smul_dotProduct, h, zero_add]
        have : 0 < v ⬝ᵥ v := by
          rcases (dotProduct_self_star_nonneg v).lt_or_eq with h' | h'
          · simpa using h'
          · exact absurd (dotProduct_self_eq_zero.1 (by simpa using h'.symm)) hv
        simpa using mul_pos (by linarith : (0:ℝ) < ε / 2) this
      · left; exact ⟨l, hl, h⟩
    have hdense := dense_generic x hinj
    have finish : ∀ ℓ : Fin 3 → ℝ, 0 < ℓ ⬝ᵥ v →
        (∀ m m' : ZMod k, m ≠ m' → ℓ ⬝ᵥ x m ≠ ℓ ⬝ᵥ x m') → (Hi ℓ ∨ Hi' ℓ) →
        (twoPeakMetrics x v).Nonempty := by
      intro ℓ hpos hgen hH
      obtain ⟨G, hG, hGv⟩ := thmF v ℓ hpos
      have hz : ∀ m, depth G v (x m) = ℓ ⬝ᵥ x m := fun m => by simp [depth, hGv]
      have hzi : Function.Injective (fun m => depth G v (x m)) := by
        intro m m' h
        by_contra hne
        exact hgen m m' hne (by rw [← hz, ← hz]; exact h)
      refine ⟨⟨G, hG⟩, ?_⟩
      show ∃ i j : ZMod k, i ≠ j ∧ IsCyclicPeak (fun m => depth G v (x m)) i ∧
        IsCyclicPeak (fun m => depth G v (x m)) j
      rcases hH with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
      · exact two_peaks_of_interleaved _ hzi a b c d hab hbc hcd (by omega)
          ⟨by rw [hz, hz]; exact e1, by rw [hz, hz]; exact e2, by rw [hz, hz]; exact e3,
           by rw [hz, hz]; exact e4⟩
      · have ca : ((a + k : ℕ) : ZMod k) = (a : ZMod k) := by simp
        exact two_peaks_of_interleaved _ hzi b c d (a + k) hbc hcd (by omega) (by omega)
          ⟨by rw [hz, hz]; exact e2, by rw [hz, hz]; exact e4, by rw [ca, hz, hz]; exact e1,
           by rw [ca, hz, hz]; exact e3⟩
    rcases hne with hne | hne
    · obtain ⟨ℓ, ⟨hH, hpos⟩, hgen⟩ := hdense.inter_open_nonempty _ (oHi.inter opos) hne
      exact finish ℓ hpos hgen (Or.inl hH)
    · obtain ⟨ℓ, ⟨hH, hpos⟩, hgen⟩ := hdense.inter_open_nonempty _ (oHi'.inter opos) hne
      exact finish ℓ hpos hgen (Or.inr hH)
  · obtain ⟨i, j, hij, hi, hj⟩ := hG
    exact not_unimodal_of_two_peaks _ i j hij hi hj


end MinimalityExtra

#print axioms MinimalityExtra.twoPeakedRimOpenSetOfMetrics
