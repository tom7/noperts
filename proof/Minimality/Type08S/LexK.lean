module

public import Minimality.Type08S.P2RKT1
public import Minimality.OctaTools

@[expose] public section

/-!
# k-level lexicographic lex cells (scratch package `lexk`)

A lex cell at the base view `u₀` from a LIST of tilts `v₁, …, v_m`: every tilt test and every depth comparison is a
lex-positive vector of reals `(f u₀, f v₁, …, f v_m)` (`lexkPos`).  The single tilt of `LexCell` is
`v = v₁ + δ v₂ + … + δ^{m-1} v_m` (`lexkVec`) for a small `δ > 0`.
Depths: a lex-sorted list `s` of the cycle indices (consecutive steps lex-positive, `lexkChain`) and a decidable
peak count `lexkPeak s`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Lex positivity of a vector of reals: first nonzero entry positive (the empty vector is not positive). -/
def lexkPos : List ℝ → Prop
  | [] => False
  | b :: l => 0 < b ∨ (b = 0 ∧ lexkPos l)

@[simp] theorem lexkPos_cons (b : ℝ) (l : List ℝ) : lexkPos (b :: l) ↔ 0 < b ∨ (b = 0 ∧ lexkPos l) := Iff.rfl

theorem lexkPos_head {b : ℝ} {l : List ℝ} (h : 0 < b) : lexkPos (b :: l) := Or.inl h
theorem lexkPos_tail {b : ℝ} {l : List ℝ} (h0 : b = 0) (h : lexkPos l) : lexkPos (b :: l) := Or.inr ⟨h0, h⟩

/-- Closes one row `lexkPos [e₀, e₁, …]`: the first entry that `nlinarith` proves positive, all earlier ones `ring1`
zeros (`ring1`, else `linarith`).  Hint facts must be in the context. -/
syntax "lexk_row" : tactic
macro_rules
  | `(tactic| lexk_row) =>
    `(tactic| first
      | exact lexkPos_head (by nlinarith)
      | (refine lexkPos_tail (by first | ring1 | linarith) ?_; lexk_row))

/-- Positive rescaling of the entries. -/
theorem lexkPos_map_of {α : Type*} (f g : α → ℝ) (c : ℝ) (hc : 0 < c) (hfg : ∀ a, f a = c * g a) :
    ∀ l : List α, lexkPos (l.map g) → lexkPos (l.map f)
  | [], h => h
  | a :: l, h => by
    simp only [List.map_cons, lexkPos_cons] at h ⊢
    rw [hfg]
    rcases h with h | ⟨h0, h⟩
    · exact Or.inl (mul_pos hc h)
    · exact Or.inr ⟨by rw [h0, mul_zero], lexkPos_map_of f g c hc hfg l h⟩

/-- `b₀ + δ b₁ + δ² b₂ + …`. -/
def lexkEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | b :: l, δ => b + δ * lexkEval l δ

/-- `v₁ + δ v₂ + δ² v₃ + …`. -/
noncomputable def lexkVec : List ℝ³ → ℝ → ℝ³
  | [], _ => 0
  | v :: vs, δ => v + δ • lexkVec vs δ

theorem lexk_eval_cont : ∀ l : List ℝ, Continuous (lexkEval l)
  | [] => continuous_const
  | b :: l => by
    show Continuous fun δ => b + δ * lexkEval l δ
    exact continuous_const.add (continuous_id.mul (lexk_eval_cont l))

theorem lexk_eval_pos : ∀ l : List ℝ, lexkPos l → ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < lexkEval l δ
  | [], h => h.elim
  | b :: l, h => by
    rcases h with h | ⟨h0, h⟩
    · have hc := (lexk_eval_cont (b :: l)).continuousAt (x := 0)
      have h0' : 0 < lexkEval (b :: l) 0 := by simp only [lexkEval, zero_mul, add_zero]; exact h
      exact nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds h0'))
    · have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
      refine ((lexk_eval_pos l h).and hpos).mono fun δ hδ => ?_
      simp only [lexkEval, h0, zero_add]
      exact mul_pos hδ.2 hδ.1

theorem lexk_inner_vec (w : ℝ³) : ∀ (vs : List ℝ³) (δ : ℝ),
    ⟪w, lexkVec vs δ⟫ = lexkEval (vs.map (fun v => ⟪w, v⟫)) δ
  | [], δ => by simp [lexkVec, lexkEval]
  | v :: vs, δ => by
    simp only [lexkVec, lexkEval, List.map_cons, inner_add_right, real_inner_smul_right, lexk_inner_vec w vs δ]

/-- One lex row gives the 2-level sign at `(u₀, lexkVec vs δ)` for all small `δ > 0`. -/
theorem lexk_ev (w u₀ : ℝ³) (vs : List ℝ³) (h : lexkPos ((u₀ :: vs).map (fun u => ⟪w, u⟫))) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < ⟪w, u₀⟫ ∨ (⟪w, u₀⟫ = 0 ∧ 0 < ⟪w, lexkVec vs δ⟫) := by
  simp only [List.map_cons, lexkPos_cons] at h
  rcases h with h | ⟨h0, h⟩
  · exact Eventually.of_forall fun _ => Or.inl h
  · exact (lexk_eval_pos _ h).mono fun δ hδ => Or.inr ⟨h0, by rw [lexk_inner_vec]; exact hδ⟩

theorem lexk_ts_ev {a b u₀ : ℝ³} {vs : List ℝ³} (h : lexkPos ((u₀ :: vs).map (det3 a b))) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), TiltSign a b u₀ (lexkVec vs δ) :=
  lexk_ev (cross a b) u₀ vs h

/-- Depth step `y <lex z`: the vector `(⟪z - y, u₀⟫, ⟪z - y, v₁⟫, …)` is lex-positive. -/
def LexkDep (u₀ : ℝ³) (vs : List ℝ³) (y z : ℝ³) : Prop := lexkPos ((u₀ :: vs).map (fun u => ⟪z - y, u⟫))

theorem lexk_dep_ev {u₀ y z : ℝ³} {vs : List ℝ³} (h : LexkDep u₀ vs y z) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), LexLt (⟪y, u₀⟫, ⟪y, lexkVec vs δ⟫) (⟪z, u₀⟫, ⟪z, lexkVec vs δ⟫) := by
  refine (lexk_ev (z - y) u₀ vs h).mono fun δ hδ => ?_
  simp only [inner_sub_left] at hδ
  unfold LexLt
  rcases hδ with h | ⟨h0, h⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem lexk_lt_trans {p q s : ℝ × ℝ} (h1 : LexLt p q) (h2 : LexLt q s) : LexLt p s := by
  unfold LexLt at *
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem lexk_lt_irrefl (p : ℝ × ℝ) : ¬ LexLt p p := by
  unfold LexLt; rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

/-- Consecutive relation along a list. -/
def lexkChain {α : Type*} (R : α → α → Prop) : List α → Prop
  | a :: b :: l => R a b ∧ lexkChain R (b :: l)
  | _ => True

@[simp] theorem lexkChain_one {α : Type*} (R : α → α → Prop) (a : α) : lexkChain R [a] ↔ True := Iff.rfl
@[simp] theorem lexkChain_cons2 {α : Type*} (R : α → α → Prop) (a b : α) (l : List α) :
    lexkChain R (a :: b :: l) ↔ R a b ∧ lexkChain R (b :: l) := Iff.rfl

theorem lexk_chain_ev {α : Type*} {F : Filter ℝ} {P : α → α → Prop} {Q : ℝ → α → α → Prop}
    (hPQ : ∀ a b, P a b → ∀ᶠ δ in F, Q δ a b) : ∀ l : List α, lexkChain P l → ∀ᶠ δ in F, lexkChain (Q δ) l
  | [], _ => Eventually.of_forall fun _ => trivial
  | [_], _ => Eventually.of_forall fun _ => trivial
  | a :: b :: l, h => ((hPQ a b h.1).and (lexk_chain_ev hPQ (b :: l) h.2)).mono fun _ hδ => ⟨hδ.1, hδ.2⟩

theorem lexk_chain_mono {α : Type*} {P Q : α → α → Prop} (hPQ : ∀ a b, P a b → Q a b) :
    ∀ l : List α, lexkChain P l → lexkChain Q l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, h => ⟨hPQ a b h.1, lexk_chain_mono hPQ (b :: l) h.2⟩

theorem lexk_pairwise {α : Type*} {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c) :
    ∀ l : List α, lexkChain R l → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have ih := lexk_pairwise htr (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact htr _ _ _ h.1 (List.rel_of_pairwise_cons ih hc)

theorem lexk_idx_rel {α : Type*} [DecidableEq α] {R : α → α → Prop} {s : List α} (hs : ∀ a, a ∈ s)
    (hpw : s.Pairwise R) (a b : α) (hab : s.idxOf a < s.idxOf b) : R a b := by
  rw [List.pairwise_iff_getElem] at hpw
  have := hpw (s.idxOf a) (s.idxOf b) (List.idxOf_lt_length_of_mem (hs a))
    (List.idxOf_lt_length_of_mem (hs b)) hab
  simpa only [List.getElem_idxOf] using this

/-- The decidable peak check on a lex-sorted index list `s`: exactly one cycle index is above both neighbours
(positions in `s` = lex rank). -/
def lexkPeak {k : ℕ} [NeZero k] (s : List (ZMod k)) : Prop :=
  (univ.filter fun i : ZMod k => s.idxOf (i - 1) < s.idxOf i ∧ s.idxOf (i + 1) < s.idxOf i).card = 1

instance {k : ℕ} [NeZero k] (s : List (ZMod k)) : Decidable (lexkPeak s) := by
  unfold lexkPeak; infer_instance

/-- **Core (rank form, ccw).** -/
theorem lexk_core (V : Finset ℝ³) (u₀ : ℝ³) (vs : List ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (x : ZMod k → ℝ³) (hmem : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → lexkPos ((u₀ :: vs).map (det3 (x (i + 1) - x i) (x j - x i))))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, lexkPos ((u₀ :: vs).map (det3 (x (i + 1) - x i) (y - x i))))
    (r : ZMod k → ℕ) (hrinj : ∀ i j, r i = r j → i = j)
    (hdep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ a b, r a < r b →
      LexLt (⟪x a, u₀⟫, ⟪x a, lexkVec vs δ⟫) (⟪x b, u₀⟫, ⟪x b, lexkVec vs δ⟫))
    (hpeak : (univ.filter fun i : ZMod k => r (i - 1) < r i ∧ r (i + 1) < r i).card = 1) :
    HasLexCellAt V u₀ := by
  have E1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p : ZMod k × ZMod k, p.2 ≠ p.1 → p.2 ≠ p.1 + 1 →
      TiltSign (x (p.1 + 1) - x p.1) (x p.2 - x p.1) u₀ (lexkVec vs δ) := by
    refine Filter.eventually_all.2 fun p => ?_
    by_cases h : p.2 ≠ p.1 ∧ p.2 ≠ p.1 + 1
    · exact (lexk_ts_ev (hcyc p.1 p.2 h.1 h.2)).mono fun δ hδ _ _ => hδ
    · exact Eventually.of_forall fun δ h1 h2 => absurd ⟨h1, h2⟩ h
  have E2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) u₀ (lexkVec vs δ) := by
    refine (Filter.eventually_all_finset V).2 fun y hy => ?_
    by_cases h : ∀ j, y ≠ x j
    · exact (Filter.eventually_all.2 fun i => lexk_ts_ev (hrest y hy h i)).mono fun δ hδ _ => hδ
    · exact Eventually.of_forall fun δ h' => absurd h' h
  obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := ((E1.and E2).and hdep).exists
  have key : ∀ a b, LexLt (⟪x a, u₀⟫, ⟪x a, lexkVec vs δ⟫) (⟪x b, u₀⟫, ⟪x b, lexkVec vs δ⟫) ↔ r a < r b := by
    intro a b
    refine ⟨fun h => ?_, h3 a b⟩
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with hlt | heq
    · exact lexk_lt_irrefl _ (lexk_lt_trans h (h3 b a hlt))
    · rw [hrinj b a heq] at h; exact lexk_lt_irrefl _ h
  refine ⟨k, inferInstance, x, lexkVec vs δ, hk, hmem, fun i j a b => h1 (i, j) a b, h2, ?_, ?_⟩
  · intro i j hz hw
    change ⟪x i, u₀⟫ = ⟪x j, u₀⟫ at hz
    change ⟪x i, lexkVec vs δ⟫ = ⟪x j, lexkVec vs δ⟫ at hw
    by_contra hne
    have hr : r i ≠ r j := fun e => hne (hrinj i j e)
    rcases lt_or_gt_of_ne hr with hlt | hlt
    · have := h3 i j hlt; rw [hz, hw] at this; exact lexk_lt_irrefl _ this
    · have := h3 j i hlt; rw [hz, hw] at this; exact lexk_lt_irrefl _ this
  · rw [← hpeak]; congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (key _ _).and (key _ _)

theorem lexk_det3_rev (A B y u : ℝ³) : det3 (A - B) (y - B) u = -det3 (B - A) (y - A) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- **Core, reversed orientation**: rows lex-NEGATIVE (as for a cw cycle); the cell uses the reversed cycle. -/
theorem lexk_core_rev (V : Finset ℝ³) (u₀ : ℝ³) (vs : List ℝ³) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (x : ZMod k → ℝ³) (hmem : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      lexkPos ((u₀ :: vs).map (fun u => -det3 (x (i + 1) - x i) (x j - x i) u)))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      lexkPos ((u₀ :: vs).map (fun u => -det3 (x (i + 1) - x i) (y - x i) u)))
    (r : ZMod k → ℕ) (hrinj : ∀ i j, r i = r j → i = j)
    (hdep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ a b, r a < r b →
      LexLt (⟪x a, u₀⟫, ⟪x a, lexkVec vs δ⟫) (⟪x b, u₀⟫, ⟪x b, lexkVec vs δ⟫))
    (hpeak : (univ.filter fun i : ZMod k => r (i - 1) < r i ∧ r (i + 1) < r i).card = 1) :
    HasLexCellAt V u₀ := by
  refine lexk_core V u₀ vs hk (fun i => x (-i)) (fun i => hmem _) ?_ ?_ (fun i => r (-i))
    (fun i j h => neg_injective (hrinj _ _ h)) (hdep.mono fun δ h a b hab => h (-a) (-b) hab) ?_
  · intro i j h1 h2
    have := hcyc (-i - 1) (-j) (fun e => h2 (by linear_combination -e)) (fun e => h1 (by linear_combination -e))
    have e1 : -i - 1 + 1 = -i := by ring
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e1] at this
    refine lexkPos_map_of _ _ 1 one_pos (fun u => ?_) _ this
    rw [one_mul, e2, lexk_det3_rev]
  · intro y hy hyx i
    have := hrest y hy (fun j => by simpa using hyx (-j)) (-i - 1)
    have e1 : -i - 1 + 1 = -i := by ring
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e1] at this
    refine lexkPos_map_of _ _ 1 one_pos (fun u => ?_) _ this
    rw [one_mul, e2, lexk_det3_rev]
  · rw [← hpeak]
    refine Finset.card_nbij' (fun i => -i) (fun i => -i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
      have e1 : -(i - 1) = -i + 1 := by ring
      have e2 : -(i + 1) = -i - 1 := by ring
      rw [e1, e2] at hi; exact ⟨hi.2, hi.1⟩
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
      have e1 : -(-i - 1) = i + 1 := by ring
      have e2 : -(-i + 1) = i - 1 := by ring
      rw [neg_neg, e1, e2]; exact ⟨hi.2, hi.1⟩
    · intro i _; simp
    · intro i _; simp

/-- Depth hypotheses from a lex-sorted list `s` (ascending; consecutive steps lex-positive). -/
theorem lexk_dep_of_chain (u₀ : ℝ³) (vs : List ℝ³) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³)
    (s : List (ZMod k)) (hs : ∀ i, i ∈ s) (hchain : lexkChain (fun i j => LexkDep u₀ vs (x i) (x j)) s) :
    (∀ i j, s.idxOf i = s.idxOf j → i = j) ∧
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ a b, s.idxOf a < s.idxOf b →
      LexLt (⟪x a, u₀⟫, ⟪x a, lexkVec vs δ⟫) (⟪x b, u₀⟫, ⟪x b, lexkVec vs δ⟫) := by
  refine ⟨fun i j h => (List.idxOf_inj (hs i)).1 h, ?_⟩
  refine (lexk_chain_ev (fun a b h => lexk_dep_ev h) s hchain).mono fun δ hδ a b hab => ?_
  exact lexk_idx_rel hs (lexk_pairwise (R := fun a b => LexLt (⟪x a, u₀⟫, ⟪x a, lexkVec vs δ⟫)
    (⟪x b, u₀⟫, ⟪x b, lexkVec vs δ⟫)) (fun _ _ _ h1 h2 => lexk_lt_trans h1 h2) s hδ) a b hab

/-- Frame row: `d3 e f v` as a function of the frame vector `v`. -/
def lexkD3 (e f v : ℝ × ℝ × ℝ) : ℝ := d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 v.1 v.2.1 v.2.2

/-- Frame tilt. -/
noncomputable def lexkF (p q r : ℝ³) (v : ℝ × ℝ × ℝ) : ℝ³ := fcomb p q r v.1 v.2.1 v.2.2

theorem lexk_inner_F (w p q r : ℝ³) (v : ℝ × ℝ × ℝ) :
    ⟪w, lexkF p q r v⟫ = v.1 * ⟪w, p⟫ + v.2.1 * ⟪w, q⟫ + v.2.2 * ⟪w, r⟫ := by
  simp only [lexkF, fcomb, inner_add_right, real_inner_smul_right]

theorem lexk_det3_frame (p q r d : ℝ³) (s t w v : ℝ × ℝ × ℝ) :
    det3 (fpoint p q r d s - fpoint p q r d t) (fpoint p q r d w - fpoint p q r d t) (lexkF p q r v) =
      det3 p q r * lexkD3 (s - t) (w - t) v := by
  rw [fpoint_sub, fpoint_sub, lexkF, det3_coord]; rfl

/-- **k-level lex cell, frame form.**  Frame `(p, q, r)` over `d` with `det3 p q r ≠ 0` (either sign), base view `r`,
cycle `X` and rest points in frame coordinates, tilts `T` in frame coordinates.  TS rows are lex-positive vectors
`(d3 e f (0,0,1), d3 e f T₁, …)` (no `det3` factor: they describe a ccw cycle in frame coordinates); depth steps
along the lex-sorted list `s` are lex-positive vectors `(⟪Δx, r⟫, ⟪Δx, T₁⟫, …)`. -/
theorem lexk_cell_frame (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (X : ZMod k → ℝ × ℝ × ℝ) (T : List (ℝ × ℝ × ℝ)) (hmem : ∀ i, fpoint p q r d (X i) ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (X j - X i))))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (X j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ i, lexkPos (((0, 0, 1) :: T).map (lexkD3 (X (i + 1) - X i) (t - X i))))
    (s : List (ZMod k)) (hs : ∀ i, i ∈ s)
    (hchain : lexkChain (fun i j => lexkPos (((0, 0, 1) :: T).map
      (fun v => ⟪fpoint p q r d (X j) - fpoint p q r d (X i), lexkF p q r v⟫))) s)
    (hpeak : lexkPeak s) : HasLexCellAt V r := by
  have hr : lexkF p q r (0, 0, 1) = r := by simp [lexkF, fcomb]
  set vs := T.map (lexkF p q r) with hvs
  have hL : ∀ (g : ℝ³ → ℝ), (r :: vs).map g = ((0, 0, 1) :: T).map (fun v => g (lexkF p q r v)) := by
    intro g; simp only [hvs, List.map_cons, List.map_map, hr]; rfl
  have hch : lexkChain (fun i j => LexkDep r vs (fpoint p q r d (X i)) (fpoint p q r d (X j))) s := by
    refine lexk_chain_mono (fun a b h => ?_) s hchain
    unfold LexkDep; rw [hL]; exact h
  have h := lexk_dep_of_chain r vs (fun i => fpoint p q r d (X i)) s hs hch
  rcases lt_or_gt_of_ne hΔ with hneg | hpos
  · refine lexk_core_rev V r vs hk _ hmem (fun i j h1 h2 => ?_) (fun y hy hyx i => ?_) (fun i => s.idxOf i)
      h.1 h.2 hpeak
    · rw [hL]
      exact lexkPos_map_of _ _ (-det3 p q r) (by linarith) (fun v => by rw [lexk_det3_frame]; ring) _
        (hcyc i j h1 h2)
    · obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
      rw [hL]
      exact lexkPos_map_of _ _ (-det3 p q r) (by linarith) (fun v => by rw [lexk_det3_frame]; ring) _ (ht i)
  · refine lexk_core V r vs hk _ hmem (fun i j h1 h2 => ?_) (fun y hy hyx i => ?_) (fun i => s.idxOf i)
      h.1 h.2 hpeak
    · rw [hL]
      exact lexkPos_map_of _ _ (det3 p q r) hpos (fun v => by rw [lexk_det3_frame]) _ (hcyc i j h1 h2)
    · obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
      rw [hL]
      exact lexkPos_map_of _ _ (det3 p q r) hpos (fun v => by rw [lexk_det3_frame]) _ (ht i)

end Type08Sp
end Minimality
