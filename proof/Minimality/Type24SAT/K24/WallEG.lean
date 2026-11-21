module

public import Minimality.WallSil
public import Minimality.Type24SAT.Facets24
public import Minimality.Type24SAT.Geo.Top
public import Minimality.SilS0XB

@[expose] public section

/-!
# Type 24: Lemma WV on `E ∥ G`, acute at the floor edge `06`

`Minimality.T24.isRupert_wallEG_acute`: if the facet `E` is parallel to the segments `23`, `25` (so `E ∥ G`), the dihedral
angle at `06` is acute (`⟪N_B, N_E⟫ < 0`) and no lateral facet is edge-on at the view `-N_E`, the shape is Rupert.  The levels
`⟪x i, -N_E⟫` have three classes (floor `0 4 6`, vertex `1`, ceiling `2 3 5`; `eg_par`, `eg_lev`), and the facings of the
six lateral facets give a 16-leaf decision tree whose leaves are rim cycles (`CycOK24`) with wall-shaped levels (`wsN`,
`eg_leaf_wall`, from `isRupert_of_wallSil`) or triangles (`eg_leaf_k3`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT

namespace Minimality.H24K.SAT

/-- Three-element cycles have robustly unimodal depths. -/
theorem robUni_three (z : ZMod 3 → ℝ) : H21.RobUni z := by
  intro B b c d hb hbc hcd hd3
  omega

theorem wallEG_par_aux (a b e P R : ℝ³) (hPa : ⟪P, a⟫ = 0) (hPb : ⟪P, b⟫ = 0) (hRa : ⟪R, a⟫ = 0)
    (hRb : ⟪R, b⟫ = 0) (hQ : cross a b ≠ 0) (hPe : 0 < ⟪P, e⟫) : ⟪P, e⟫ • R = ⟪R, e⟫ • P := by
  have key : ∀ T : ℝ³, ⟪T, a⟫ = 0 → ⟪T, b⟫ = 0 → ⟪T, e⟫ • cross a b = ⟪cross a b, e⟫ • T := by
    intro T hTa hTb
    simp only [wsil_inn3] at hTa hTb ⊢
    ext i; fin_cases i
    · simp [cross]
      linear_combination (e 1 * b 2 - e 2 * b 1) * hTa + (e 2 * a 1 - e 1 * a 2) * hTb
    · simp [cross]
      linear_combination (e 2 * b 0 - e 0 * b 2) * hTa + (e 0 * a 2 - e 2 * a 0) * hTb
    · simp [cross]
      linear_combination (e 0 * b 1 - e 1 * b 0) * hTa + (e 1 * a 0 - e 0 * a 1) * hTb
  have h1 := key P hPa hPb
  have h2 := key R hRa hRb
  set d := ⟪cross a b, e⟫ with hd
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    exact hQ ((smul_eq_zero.1 h1).resolve_left hPe.ne')
  refine smul_right_injective (ℝ³) hd0 ?_
  simp only
  calc d • (⟪P, e⟫ • R) = ⟪P, e⟫ • (d • R) := by rw [smul_comm]
    _ = ⟪P, e⟫ • (⟪R, e⟫ • cross a b) := by rw [h2]
    _ = ⟪R, e⟫ • (⟪P, e⟫ • cross a b) := by rw [smul_comm]
    _ = ⟪R, e⟫ • (d • P) := by rw [h1]
    _ = d • (⟪R, e⟫ • P) := by rw [smul_comm]

theorem wallEG_cross_zero (a b w : ℝ³) (hQ : cross a b = 0) : ⟪a, w⟫ • b = ⟪b, w⟫ • a := by
  have h0 : a 1 * b 2 - a 2 * b 1 = 0 := by simpa [cross] using congrArg (fun v : ℝ³ => v 0) hQ
  have h1 : a 2 * b 0 - a 0 * b 2 = 0 := by simpa [cross] using congrArg (fun v : ℝ³ => v 1) hQ
  have h2 : a 0 * b 1 - a 1 * b 0 = 0 := by simpa [cross] using congrArg (fun v : ℝ³ => v 2) hQ
  ext i; fin_cases i
  · simp [wsil_inn3]
    linear_combination (-w 1) * h2 + (w 2) * h1
  · simp [wsil_inn3]
    linear_combination (-w 2) * h0 + (w 0) * h2
  · simp [wsil_inn3]
    linear_combination (-w 0) * h1 + (w 1) * h0




/-- A cyclic list as a function on `ZMod k` (position `i.val`). -/
def cycL {α : Type} (d : α) {k : ℕ} (L : List α) : ZMod k → α := fun i => L.getD i.val d

theorem cycL_natCast {α : Type} (d : α) {k : ℕ} [NeZero k] (L : List α) (a : ℕ) :
    cycL d L (a : ZMod k) = L.getD (a % k) d := by
  simp [cycL, ZMod.val_natCast]


/-- Wall shape of a `ℕ`-valued class sequence (decidable), mirroring `WallShape`. -/
def wsN (g : ℕ → ℕ) (k s r r' : ℕ) : Prop :=
  s < r ∧ r ≤ r' ∧ r' < k ∧ ∀ t, t < k → (t < s → g t = g (t + 1)) ∧ (s ≤ t → t < r → g t < g (t + 1)) ∧
    (r ≤ t → t < r' → g t = g (t + 1)) ∧ (r' ≤ t → g (t + 1) < g t)

instance (g : ℕ → ℕ) (k s r r' : ℕ) : Decidable (wsN g k s r r') := by
  unfold wsN; infer_instance

theorem wallShape_of_wsN {k : ℕ} [NeZero k] {l : ZMod k → ℝ} {g : ℕ → ℕ} {s r r' : ℕ}
    (hlt : ∀ a b : ℕ, g a < g b → l a < l b) (heq : ∀ a b : ℕ, g a = g b → l a = l b)
    (h : wsN g k s r r') : WallShape l s r r' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c : ∀ t : ℕ, ((t + 1 : ℕ) : ZMod k) = (t : ZMod k) + 1 := fun t => by push_cast; rfl
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have := heq t (t + 1) ((h4 t (by omega)).1 ht)
    rwa [c] at this
  · intro t ht1 ht2
    have := hlt t (t + 1) ((h4 t (by omega)).2.1 ht1 ht2)
    rwa [c] at this
  · intro t ht1 ht2
    have := heq t (t + 1) ((h4 t (by omega)).2.2.1 ht1 ht2)
    rwa [c] at this
  · intro t ht1 ht2
    have := hlt (t + 1) t ((h4 t ht2).2.2.2 ht1)
    rwa [c] at this






set_option hygiene false in
/-- Prove `hU` / `hD` of a leaf from the facing hypotheses in context. -/
local macro "eg_face" : tactic =>
  `(tactic| (intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
             rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption))

set_option hygiene false in
local macro "eg_w" k:num L:term:max U:term:max Dn:term:max s:num r:num r':num : tactic =>
  `(tactic| exact eg_leaf_wall F hEG0 (k := $k) (by norm_num) $L $U $Dn (by decide) (by decide) (by eg_face)
      (by eg_face) (s := $s) (r := $r) (r' := $r') (by decide))

set_option hygiene false in
local macro "eg_t" L:term:max U:term:max Dn:term:max : tactic =>
  `(tactic| exact eg_leaf_k3 F $L $U $Dn (by decide) (by decide) (by eg_face) (by eg_face))


end Minimality.H24K.SAT
