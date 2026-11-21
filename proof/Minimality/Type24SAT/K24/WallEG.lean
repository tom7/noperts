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

/-- **Parallel normals**: if the facet `E` (`046`) is parallel to the segments `23`, `25` (so to the plane of `G`),
then `N_G` and `N_E` point in opposite directions, and vertex `1` lies strictly between the two planes. -/
theorem eg_par {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hEG0 : ⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0) :
    ⟪F.N 6, F.N 4⟫ < 0 ∧ 0 < ⟪F.N 4, x 1 - x 2⟫ := by
  have hPa : ⟪F.N 4, x 3 - x 2⟫ = 0 := by
    rw [← neg_sub, inner_neg_right, hEG0.1, neg_zero]
  have hPb : ⟪F.N 4, x 5 - x 2⟫ = 0 := by
    rw [← neg_sub, inner_neg_right, hEG0.2, neg_zero]
  have hRa := perp24 F 6 3 2 (by decide) (by decide)
  have hRb := perp24 F 6 5 2 (by decide) (by decide)
  have hPe := off24 F 4 0 2 (by decide) (by decide)
  have hRe := off24 F 6 2 0 (by decide) (by decide)
  have hR1 := off24 F 6 2 1 (by decide) (by decide)
  have hQ : cross (x 3 - x 2) (x 5 - x 2) ≠ 0 := by
    intro hQ
    have h := wallEG_cross_zero _ _ (F.N 2) hQ
    have hCa := off24 F 2 2 3 (by decide) (by decide)
    have hCa' : ⟪F.N 2, x 3 - x 2⟫ < 0 := by
      rw [← neg_sub, inner_neg_right]; linarith
    rw [real_inner_comm (F.N 2) (x 3 - x 2), real_inner_comm (F.N 2) (x 5 - x 2)] at h
    have hCb' : ⟪F.N 2, x 5 - x 2⟫ = 0 := perp24 F 2 5 2 (by decide) (by decide)
    rw [hCb', zero_smul] at h
    have : x 5 - x 2 = 0 := (smul_eq_zero.1 h).resolve_left hCa'.ne
    exact absurd (Minimality.H24.SAT.inj_of_fac F (sub_eq_zero.1 this)) (by decide)
  have W := wallEG_par_aux _ _ (x 0 - x 2) (F.N 4) (F.N 6) hPa hPb hRa hRb hQ hPe
  have n4 := nn24 F 4
  have hRe' : ⟪F.N 6, x 0 - x 2⟫ < 0 := by
    rw [← neg_sub, inner_neg_right]; linarith
  have hR1' : ⟪F.N 6, x 1 - x 2⟫ < 0 := by
    rw [← neg_sub, inner_neg_right]; linarith
  have e1 := congrArg (fun v => ⟪v, F.N 4⟫) W
  have e2 := congrArg (fun v => ⟪v, x 1 - x 2⟫) W
  simp only [real_inner_smul_left] at e1 e2
  constructor
  · by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hPe.le hc, mul_pos_of_neg_of_neg hRe' (neg_neg_of_pos n4)]
  · by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_pos_of_neg hPe hR1', mul_nonneg_of_nonpos_of_nonpos hRe'.le hc]

/-- Class of a vertex by level: floor `0, 4, 6`, middle `1`, ceiling `2, 3, 5`. -/
def lvCl : Fin 7 → ℕ := ![0, 1, 2, 2, 0, 2, 0]

/-- The levels of the vertices along the view `-N_E`, in the order floor < vertex 1 < ceiling. -/
theorem eg_lev {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hEG0 : ⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0) (p q : Fin 7) :
    (lvCl p < lvCl q → ⟪x p, -F.N 4⟫ < ⟪x q, -F.N 4⟫) ∧ (lvCl p = lvCl q → ⟪x p, -F.N 4⟫ = ⟪x q, -F.N 4⟫) := by
  have m : ∀ p : Fin 7, ⟪x p, -F.N 4⟫ = - ⟪F.N 4, x p⟫ := fun p => by
    rw [inner_neg_right, real_inner_comm]
  have d : ∀ p q : Fin 7, ⟪F.N 4, x p - x q⟫ = ⟪F.N 4, x p⟫ - ⟪F.N 4, x q⟫ := fun p q => inner_sub_right _ _ _
  have f04 := perp24 F 4 0 4 (by decide) (by decide)
  have f06 := perp24 F 4 0 6 (by decide) (by decide)
  have f01 := off24 F 4 0 1 (by decide) (by decide)
  have f12 := (eg_par F hEG0).2
  have h23 := hEG0.1
  have h25 := hEG0.2
  rw [d] at f04 f06 f01 f12 h23 h25
  simp only [m]
  fin_cases p <;> fin_cases q <;> simp [lvCl] <;> linarith

/-- A cyclic list as a function on `ZMod k` (position `i.val`). -/
def cycL {α : Type} (d : α) {k : ℕ} (L : List α) : ZMod k → α := fun i => L.getD i.val d

theorem cycL_natCast {α : Type} (d : α) {k : ℕ} [NeZero k] (L : List α) (a : ℕ) :
    cycL d L (a : ZMod k) = L.getD (a % k) d := by
  simp [cycL, ZMod.val_natCast]

/-- The level classes along the cycle `L` (of length `k`), as a `ℕ`-indexed periodic sequence. -/
def gN (L : List (Fin 7)) (k : ℕ) (t : ℕ) : ℕ := lvCl (L.getD (t % k) 0)

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

/-- The cycle `c` is a silhouette of the facets `U` (up) and `Dn` (down): each edge lies in one of each, every other
vertex is off one of them. -/
def CycOK24 {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) : Prop :=
  ∀ i, ∃ a ∈ U, ∃ b ∈ Dn, c i ∈ s0x_S24 a ∧ c i ∈ s0x_S24 b ∧ c (i + 1) ∈ s0x_S24 a ∧ c (i + 1) ∈ s0x_S24 b ∧
    ∀ q : Fin 7, q ≠ c i → q ≠ c (i + 1) → q ∉ s0x_S24 a ∨ q ∉ s0x_S24 b

instance {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) : Decidable (CycOK24 c U Dn) := by
  unfold CycOK24; infer_instance

/-- Silhouette data at the view `-N_E` from a cycle with up facets `U` (`⟪N, N_E⟫ < 0`) and down facets `Dn`. -/
theorem silL24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] {c : ZMod k → Fin 7}
    {U Dn : Finset (Fin 9)} (hcyc : CycOK24 c U Dn) (hU : ∀ t ∈ U, ⟪F.N t, F.N 4⟫ < 0)
    (hD : ∀ t ∈ Dn, 0 < ⟪F.N t, F.N 4⟫) : Nonempty (h21b_SilDataL k x c (-F.N 4) 0) := by
  choose ea hea eb heb h0a h0b h1a h1b hs using hcyc
  exact ⟨{
    A := fun i => F.N (ea i)
    B := fun i => F.N (eb i)
    fA := fun i => F.f (ea i)
    fB := fun i => F.f (eb i)
    hA := fun i => F.hN (ea i)
    hB := fun i => F.hN (eb i)
    zA0 := fun i => F.zero _ _ (h0a i)
    zA1 := fun i => F.zero _ _ (h1a i)
    zB0 := fun i => F.zero _ _ (h0b i)
    zB1 := fun i => F.zero _ _ (h1b i)
    nA := fun i q => F.le _ q
    nB := fun i q => F.le _ q
    strict := fun i q a b => by
      rcases hs i q a b with h | h
      · exact Or.inl (F.neg _ _ h)
      · exact Or.inr (F.neg _ _ h)
    up := fun i => Or.inl (by rw [inner_neg_right]; linarith [hU _ (hea i)])
    dn := fun i => Or.inl (by rw [inner_neg_right, neg_neg]; linarith [hD _ (heb i)]) }⟩

theorem eg_leaf_wall {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hEG0 : ⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k) (L : List (Fin 7))
    (U Dn : Finset (Fin 9)) (hc : Function.Injective (cycL 0 L : ZMod k → Fin 7))
    (hcyc : CycOK24 (cycL 0 L : ZMod k → Fin 7) U Dn) (hU : ∀ t ∈ U, ⟪F.N t, F.N 4⟫ < 0)
    (hD : ∀ t ∈ Dn, 0 < ⟪F.N t, F.N 4⟫) {s r r' : ℕ} (hws : wsN (gN L k) k s r r') :
    IsRupert (univ.image x) := by
  obtain ⟨D⟩ := silL24 F hcyc hU hD
  have hu : -F.N 4 ≠ 0 := neg_ne_zero.2 (fun h => by have := nn24 F 4; rw [h] at this; simp at this)
  refine isRupert_of_wallSil hk (Minimality.H24.SAT.inj_of_fac F) hc hu D (wallShape_of_wsN ?_ ?_ hws)
  · intro a b h
    simp only [cycL_natCast]
    exact (eg_lev F hEG0 _ _).1 h
  · intro a b h
    simp only [cycL_natCast]
    exact (eg_lev F hEG0 _ _).2 h

theorem eg_leaf_k3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (L : List (Fin 7))
    (U Dn : Finset (Fin 9)) (hc : Function.Injective (cycL 0 L : ZMod 3 → Fin 7))
    (hcyc : CycOK24 (cycL 0 L : ZMod 3 → Fin 7) U Dn) (hU : ∀ t ∈ U, ⟪F.N t, F.N 4⟫ < 0)
    (hD : ∀ t ∈ Dn, 0 < ⟪F.N t, F.N 4⟫) : IsRupert (univ.image x) := by
  obtain ⟨D⟩ := silL24 F hcyc hU hD
  have hu : -F.N 4 ≠ 0 := neg_ne_zero.2 (fun h => by have := nn24 F 4; rw [h] at this; simp at this)
  exact s0x_sil_isRupert_lex (by norm_num) (Minimality.H24.SAT.inj_of_fac F) hc hu D (robUni_three _)

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

/-- **Lemma WV on type 24, `E ∥ G`, acute at `06`.**  If the facet `E` is parallel to the segments `23`, `25` (so
`E ∥ G`), the dihedral angle at the edge `06` between `B` and `E` is acute (`⟪N_B, N_E⟫ < 0`) and no lateral facet
(`A C D F H I`) is edge-on at the view `-N_E`, then the shape is Rupert.  Sixteen leaves, one rim cycle each. -/
theorem _root_.Minimality.T24.isRupert_wallEG_acute {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hEG0 : ⟪F.N 4, x 2 - x 3⟫ = 0 ∧ ⟪F.N 4, x 2 - x 5⟫ = 0)
    (hB : ⟪F.N 1, F.N 4⟫ < 0)
    (hgen : ∀ t ∈ ({0, 2, 3, 5, 7, 8} : Finset (Fin 9)), ⟪F.N t, F.N 4⟫ ≠ 0) :
    IsRupert (Finset.univ.image x) := by
  have hG : ⟪F.N 6, F.N 4⟫ < 0 := (eg_par F hEG0).1
  have hE : 0 < ⟪F.N 4, F.N 4⟫ := nn24 F 4
  have gA := lt_or_gt_of_ne (hgen 0 (by decide))
  have gC := lt_or_gt_of_ne (hgen 2 (by decide))
  have gD := lt_or_gt_of_ne (hgen 3 (by decide))
  have gF := lt_or_gt_of_ne (hgen 5 (by decide))
  have gH := lt_or_gt_of_ne (hgen 7 (by decide))
  have gI := lt_or_gt_of_ne (hgen 8 (by decide))
  rcases gD with hD | hD
  · rcases gI with hI | hI
    · eg_t [4, 0, 6] {1, 8, 3} {4}
    · rcases gH with hH | hH
      · eg_w 4 [4, 0, 6, 3] {3, 1, 7} {4, 8} 2 3 3
      · rcases gF with hF | hF
        · eg_w 5 [4, 0, 6, 2, 3] {3, 1, 5, 6} {4, 7, 8} 2 3 4
        · rcases gA with hA | hA
          · eg_w 6 [4, 0, 6, 1, 2, 3] {3, 1, 0, 6} {4, 5, 7, 8} 2 4 5
          · eg_t [0, 6, 1] {1} {4, 5, 0}
  · rcases gC with hC | hC
    · rcases gH with hH | hH
      · rcases gI with hI | hI
        · eg_w 5 [0, 6, 4, 3, 5] {1, 8, 6, 2} {4, 3} 2 3 4
        · eg_w 4 [0, 6, 3, 5] {1, 7, 6, 2} {4, 8, 3} 1 2 3
      · rcases gA with hA | hA
        · rcases gF with hF | hF
          · eg_w 5 [0, 6, 2, 3, 5] {1, 5, 6, 2} {4, 7, 3} 1 2 4
          · eg_w 6 [0, 6, 1, 2, 3, 5] {1, 0, 6, 2} {4, 5, 7, 3} 1 3 5
        · eg_w 4 [0, 2, 3, 5] {2, 6} {0, 7, 3} 0 1 3
    · rcases gH with hH | hH
      · rcases gA with hA | hA
        · rcases gI with hI | hI
          · eg_w 6 [0, 6, 4, 3, 5, 2] {1, 8, 6, 0} {4, 3, 2} 2 3 5
          · eg_w 5 [0, 6, 3, 5, 2] {1, 7, 6, 0} {4, 8, 3, 2} 1 2 4
        · rcases gF with hF | hF
          · rcases gI with hI | hI
            · eg_w 7 [0, 6, 4, 3, 5, 2, 1] {1, 8, 6, 5} {4, 3, 2, 0} 2 3 5
            · eg_w 6 [0, 6, 3, 5, 2, 1] {1, 7, 6, 5} {4, 8, 3, 2, 0} 1 2 4
          · eg_t [0, 6, 1] {1} {4, 5, 0}
      · eg_t [2, 3, 5] {6} {7, 3, 2}

end Minimality.H24K.SAT
