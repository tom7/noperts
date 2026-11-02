module

public import Minimality.Type21Sl2D

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-- **The leaf core**: a facing pattern whose silhouette is the cycle `c`, a view `u ≠ 0` with
exactly two edge-on facets `X`, `Y` (with a dual pair `v1`, `v2` witnessing independence), strict
facings of the others, and strictly unimodal depths: a lex cell, hence `IsRupert`. -/
theorem h21b_leaf_core (T : Facets21 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin 7}
    (hc : Function.Injective c) {pat : Fin 8 → Bool} (hcyc : h21b_CycOK c pat) {X Y : Fin 8}
    {u v1 v2 : ℝ³} (hu : u ≠ 0)
    (h1 : ⟪(fac8 T).N X, v1⟫ < 0) (h1' : ⟪(fac8 T).N Y, v1⟫ = 0)
    (h2 : ⟪(fac8 T).N X, v2⟫ = 0) (h2' : ⟪(fac8 T).N Y, v2⟫ < 0)
    (hX : ⟪(fac8 T).N X, u⟫ = 0) (hY : ⟪(fac8 T).N Y, u⟫ = 0)
    (hstr : ∀ t, t ≠ X → t ≠ Y →
      (pat t = true → 0 < ⟪(fac8 T).N t, u⟫) ∧ (pat t = false → ⟪(fac8 T).N t, u⟫ < 0))
    (hU : Uni (fun a : ZMod k => ⟪x (c a), u⟫)) : IsRupert (univ.image x) := by
  obtain ⟨v, hfac, hv⟩ := h21b_exists_v (fac8 T) T.inj hc h1 h1' h2 h2' hX hY hstr
  obtain ⟨D⟩ := h21b_silL (fac8 T) hcyc hfac
  exact isRupert_of_hasLexCell _ ⟨u, hu, h21b_sil_cell hk T.inj hc D hv hU⟩

/-! ### Segment views -/

/-- A segment-view leaf at `r = x j - x i`: the two edge-on facets `X`, `Y` (through both), the facing
pattern `pat` (true = up; forced for facets through exactly one of `i`, `j`, a literal for the
facets through neither, tilt-chosen for `X`, `Y`) and the silhouette cycle `c`. -/
structure h21b_SegSpec (k : ℕ) where
  i : Fin 7
  j : Fin 7
  X : Fin 8
  Y : Fin 8
  pat : Fin 8 → Bool
  c : ZMod k → Fin 7

/-- The decidable side conditions of a segment leaf. -/
def h21b_SegSpec.Good {k : ℕ} [NeZero k] (s : h21b_SegSpec k) : Prop :=
  s.i ≠ s.j ∧ s.X ≠ s.Y ∧ s.i ∈ h21S s.X ∧ s.j ∈ h21S s.X ∧ s.i ∈ h21S s.Y ∧ s.j ∈ h21S s.Y ∧
  (∀ t, s.i ∈ h21S t → s.j ∈ h21S t → t = s.X ∨ t = s.Y) ∧
  (∀ t, s.j ∈ h21S t → s.i ∉ h21S t → s.pat t = true) ∧
  (∀ t, s.i ∈ h21S t → s.j ∉ h21S t → s.pat t = false) ∧
  (∃ m, m ∈ h21S s.X ∧ m ∉ h21S s.Y) ∧ (∃ m, m ∈ h21S s.Y ∧ m ∉ h21S s.X) ∧
  Function.Injective s.c ∧ 3 ≤ k ∧ h21b_CycOK s.c s.pat

instance {k : ℕ} [NeZero k] (s : h21b_SegSpec k) : Decidable s.Good := by
  unfold h21b_SegSpec.Good; infer_instance

/-- The failing-condition of a segment leaf: the facing literals of the facets through neither
endpoint (`φ_t(i,j) = f_t(x j) - f_t(x i)`) and strict unimodality of the depths along the cycle. -/
def h21b_SegCond {k : ℕ} [NeZero k] (T : Facets21 x) (s : h21b_SegSpec k) : Prop :=
  (∀ t, s.i ∉ h21S t → s.j ∉ h21S t →
    (s.pat t = true → 0 < (fac8 T).f t (x s.j) - (fac8 T).f t (x s.i)) ∧
    (s.pat t = false → (fac8 T).f t (x s.j) - (fac8 T).f t (x s.i) < 0)) ∧
  Uni (fun a : ZMod k => ⟪x (s.c a), x s.j - x s.i⟫)

theorem h21b_seg_rupert (T : Facets21 x) {k : ℕ} [NeZero k] (s : h21b_SegSpec k) (hg : s.Good)
    (hC : h21b_SegCond T s) : IsRupert (univ.image x) := by
  obtain ⟨hij, hXY, hiX, hjX, hiY, hjY, hboth, hup, hdn, ⟨m, hmX, hmY⟩, ⟨m', hmY', hmX'⟩, hc, hk, hcyc⟩ := hg
  obtain ⟨hlit, hU⟩ := hC
  set F := fac8 T with hF
  have hN : ∀ t (a b : Fin 7), ⟪F.N t, x a - x b⟫ = F.f t (x a) - F.f t (x b) :=
    fun t a b => (F.hN t _ _).symm
  have hu : x s.j - x s.i ≠ 0 := by
    intro h
    exact hij (T.inj (sub_eq_zero.1 h)).symm
  refine h21b_leaf_core T hk hc hcyc (X := s.X) (Y := s.Y) (u := x s.j - x s.i)
    (v1 := x m' - x s.i) (v2 := x m - x s.i) hu ?_ ?_ ?_ ?_ ?_ ?_ ?_ hU
  · rw [hN, F.zero _ _ hiX]; linarith [F.neg s.X m' hmX']
  · rw [hN, F.zero _ _ hiY, F.zero _ _ hmY']; ring
  · rw [hN, F.zero _ _ hiX, F.zero _ _ hmX]; ring
  · rw [hN, F.zero _ _ hiY]; linarith [F.neg s.Y m hmY]
  · rw [hN, F.zero _ _ hiX, F.zero _ _ hjX]; ring
  · rw [hN, F.zero _ _ hiY, F.zero _ _ hjY]; ring
  · intro t htX htY
    rw [hN]
    by_cases hi : s.i ∈ h21S t <;> by_cases hj : s.j ∈ h21S t
    · rcases hboth t hi hj with h | h
      · exact absurd h htX
      · exact absurd h htY
    · have hp := hdn t hi hj
      exact ⟨fun h => by rw [hp] at h; exact absurd h (by decide),
        fun _ => F.dn t hi hj⟩
    · have hp := hup t hj hi
      exact ⟨fun _ => F.up t hj hi, fun h => by rw [hp] at h; exact absurd h (by decide)⟩
    · exact hlit t hi hj

/-! ### Line views -/

/-- A line-view leaf: the view `u = N_X × N_Y`, the facing pattern of the other six facets (true =
up, the sign of `⟪N_t, u⟫`), the tilt-chosen facings of `X`, `Y`, and the silhouette cycle. -/
structure h21b_LinSpec (k : ℕ) where
  X : Fin 8
  Y : Fin 8
  pat : Fin 8 → Bool
  c : ZMod k → Fin 7

def h21b_LinSpec.Good {k : ℕ} [NeZero k] (s : h21b_LinSpec k) : Prop :=
  s.X ≠ s.Y ∧ Function.Injective s.c ∧ 3 ≤ k ∧ h21b_CycOK s.c s.pat

instance {k : ℕ} [NeZero k] (s : h21b_LinSpec k) : Decidable s.Good := by
  unfold h21b_LinSpec.Good; infer_instance

/-- The failing-condition of a line leaf: with `u = N_X × N_Y`, the facings of the other facets
(signs of `det3 N_t N_X N_Y`) and strict unimodality of the depths `⟪x (c a), u⟫`. -/
def h21b_LinCond {k : ℕ} [NeZero k] (T : Facets21 x) (s : h21b_LinSpec k) : Prop :=
  (∀ t, t ≠ s.X → t ≠ s.Y →
    (s.pat t = true → 0 < ⟪(fac8 T).N t, cross ((fac8 T).N s.X) ((fac8 T).N s.Y)⟫) ∧
    (s.pat t = false → ⟪(fac8 T).N t, cross ((fac8 T).N s.X) ((fac8 T).N s.Y)⟫ < 0)) ∧
  Uni (fun a : ZMod k => ⟪x (s.c a), cross ((fac8 T).N s.X) ((fac8 T).N s.Y)⟫)

theorem h21b_dual {n1 n2 : ℝ³} (h : cross n1 n2 ≠ 0) :
    ∃ v1 v2 : ℝ³, ⟪n1, v1⟫ < 0 ∧ ⟪n2, v1⟫ = 0 ∧ ⟪n1, v2⟫ = 0 ∧ ⟪n2, v2⟫ < 0 := by
  have hn : 0 < ⟪cross n1 n2, cross n1 n2⟫ := real_inner_self_pos.2 h
  refine ⟨-cross n2 (cross n1 n2), -cross (cross n1 n2) n1, ?_, ?_, ?_, ?_⟩
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply] at hn ⊢
    nlinarith
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply]; ring
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply]; ring
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply] at hn ⊢
    nlinarith

theorem h21b_lin_rupert (T : Facets21 x) {k : ℕ} [NeZero k] (s : h21b_LinSpec k) (hg : s.Good)
    (hC : h21b_LinCond T s) : IsRupert (univ.image x) := by
  obtain ⟨hXY, hc, hk, hcyc⟩ := hg
  obtain ⟨hstr, hU⟩ := hC
  set F := fac8 T with hF
  obtain ⟨t, htX, htY⟩ : ∃ t : Fin 8, t ≠ s.X ∧ t ≠ s.Y := by
    have : ∀ X Y : Fin 8, ∃ t : Fin 8, t ≠ X ∧ t ≠ Y := by decide
    exact this s.X s.Y
  have hu : cross (F.N s.X) (F.N s.Y) ≠ 0 := by
    intro h0
    obtain ⟨a, b⟩ := hstr t htX htY
    rw [h0] at a b
    cases hp : s.pat t
    · have := b hp; simp at this
    · have := a hp; simp at this
  obtain ⟨v1, v2, h1, h1', h2, h2'⟩ := h21b_dual hu
  refine h21b_leaf_core T hk hc hcyc (X := s.X) (Y := s.Y) hu h1 h1' h2 h2' ?_ ?_ hstr hU
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

end H21
end Minimality
