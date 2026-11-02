module

public import Minimality.Type21Sl2G
public import Minimality.SilS0XB

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-! ### Split/apex leaves with `RobUni` -/

theorem h21r_leaf_gen {k : ℕ} [NeZero k] (T : Facets21 x) (hk : 3 ≤ k) (c : ZMod k → Fin 7)
    (hc : Function.Injective c) (ea eb : ZMod k → Fin 8) (i0 j0 : Fin 7)
    (h0 : ∀ i, c i ∈ h21S (ea i) ∧ c i ∈ h21S (eb i))
    (h1 : ∀ i, c (i + 1) ∈ h21S (ea i) ∧ c (i + 1) ∈ h21S (eb i))
    (hs : ∀ i m, m ≠ c i → m ≠ c (i + 1) → m ∉ h21S (ea i) ∨ m ∉ h21S (eb i))
    (hup : ∀ i, 0 < (fac8 T).f (ea i) (x j0) - (fac8 T).f (ea i) (x i0))
    (hdn : ∀ i, (fac8 T).f (eb i) (x j0) - (fac8 T).f (eb i) (x i0) < 0)
    (hU : RobUni (fun i => ⟪x (c i), x j0 - x i0⟫)) :
    IsRupert (univ.image x) :=
  s0x_sil_isRupert_rob hk T.inj hc ((fac8 T).sil c ea eb i0 j0 h0 h1 hs hup hdn) hU

theorem h21r_W1 (T : Facets21 x)
    (hU : RobUni (fun i : ZMod 5 => ⟪x (cW1 i), x 3 - x 0⟫)) : IsRupert (univ.image x) :=
  h21r_leaf_gen T (by norm_num) cW1 (by decide) ![4, 6, 6, 7, 5] ![0, 3, 2, 2, 1] 0 3
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

theorem h21r_W2 (T : Facets21 x)
    (hU : RobUni (fun i : ZMod 5 => ⟪x (cW2 i), x 5 - x 4⟫)) : IsRupert (univ.image x) :=
  h21r_leaf_gen T (by norm_num) cW2 (by decide) ![1, 5, 7, 2, 2] ![0, 4, 6, 6, 3] 4 5
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

theorem h21r_W3 (T : Facets21 x) (hD : 0 < T.f046.f (x 2) - T.f046.f (x 1))
    (hU : RobUni (fun i : ZMod 4 => ⟪x (cW3 i), x 2 - x 1⟫)) : IsRupert (univ.image x) :=
  h21r_leaf_gen T (by norm_num) cW3 (by decide) ![3, 6, 7, 2] ![0, 4, 5, 1] 1 2
    (by decide) (by decide) (by decide)
    (fun i => by
      fin_cases i
      · exact hD
      all_goals exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

theorem h21r_W4 (T : Facets21 x) (hD : T.f046.f (x 2) - T.f046.f (x 1) < 0)
    (hU : RobUni (fun i : ZMod 5 => ⟪x (cW4 i), x 2 - x 1⟫)) : IsRupert (univ.image x) :=
  h21r_leaf_gen T (by norm_num) cW4 (by decide) ![2, 7, 6, 6, 2] ![1, 5, 4, 3, 3] 1 2
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by
      fin_cases i
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact hD
      · exact hD) hU

theorem h21r_W5 (T : Facets21 x) (hH : 0 < T.f235.f (x 6) - T.f235.f (x 1))
    (hU : RobUni (fun i : ZMod 4 => ⟪x (cW3 i), x 6 - x 1⟫)) : IsRupert (univ.image x) :=
  h21r_leaf_gen T (by norm_num) cW3 (by decide) ![3, 6, 7, 2] ![0, 4, 5, 1] 1 6
    (by decide) (by decide) (by decide)
    (fun i => by
      fin_cases i
      · exact Fac8.up _ _ (by decide) (by decide)
      · exact Fac8.up _ _ (by decide) (by decide)
      · exact hH
      · exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by fin_cases i <;> exact Fac8.dn _ _ (by decide) (by decide)) hU

theorem h21r_W6 (T : Facets21 x) (hH : T.f235.f (x 6) - T.f235.f (x 1) < 0)
    (hU : RobUni (fun i : ZMod 5 => ⟪x (cW6 i), x 6 - x 1⟫)) : IsRupert (univ.image x) :=
  h21r_leaf_gen T (by norm_num) cW6 (by decide) ![3, 6, 6, 2, 2] ![0, 4, 7, 7, 1] 1 6
    (by decide) (by decide) (by decide)
    (fun i => by fin_cases i <;> exact Fac8.up _ _ (by decide) (by decide))
    (fun i => by
      fin_cases i
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact Fac8.dn _ _ (by decide) (by decide)
      · exact hH
      · exact hH
      · exact Fac8.dn _ _ (by decide) (by decide)) hU

def h21rL1 (x : Fin 7 → ℝ³) : Prop := RobUni (fun i : ZMod 5 => ⟪x (cW1 i), x 3 - x 0⟫)
def h21rL2 (x : Fin 7 → ℝ³) : Prop := RobUni (fun i : ZMod 5 => ⟪x (cW2 i), x 5 - x 4⟫)
def h21rL3 (T : Facets21 x) : Prop :=
  0 < T.f046.f (x 2) - T.f046.f (x 1) ∧ RobUni (fun i : ZMod 4 => ⟪x (cW3 i), x 2 - x 1⟫)
def h21rL4 (T : Facets21 x) : Prop :=
  T.f046.f (x 2) - T.f046.f (x 1) < 0 ∧ RobUni (fun i : ZMod 5 => ⟪x (cW4 i), x 2 - x 1⟫)
def h21rL5 (T : Facets21 x) : Prop :=
  0 < T.f235.f (x 6) - T.f235.f (x 1) ∧ RobUni (fun i : ZMod 4 => ⟪x (cW3 i), x 6 - x 1⟫)
def h21rL6 (T : Facets21 x) : Prop :=
  T.f235.f (x 6) - T.f235.f (x 1) < 0 ∧ RobUni (fun i : ZMod 5 => ⟪x (cW6 i), x 6 - x 1⟫)

/-- Robust version of `H21Resid`. -/
def h21rResid (T : Facets21 x) : Prop :=
  ¬ h21rL1 x ∧ ¬ h21rL2 x ∧ ¬ h21rL3 T ∧ ¬ h21rL4 T ∧ ¬ h21rL5 T ∧ ¬ h21rL6 T

theorem h21r_resid_imp (T : Facets21 x) (h : h21rResid T) : H21Resid T := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨fun e => a1 (s0x_robUni_of_uni e), fun e => a2 (s0x_robUni_of_uni e),
    fun e => a3 ⟨e.1, s0x_robUni_of_uni e.2⟩, fun e => a4 ⟨e.1, s0x_robUni_of_uni e.2⟩,
    fun e => a5 ⟨e.1, s0x_robUni_of_uni e.2⟩, fun e => a6 ⟨e.1, s0x_robUni_of_uni e.2⟩⟩

/-! ### Edge and line views with `RobUni` -/

theorem h21r_leaf_core (T : Facets21 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k) {c : ZMod k → Fin 7}
    (hc : Function.Injective c) {pat : Fin 8 → Bool} (hcyc : h21b_CycOK c pat) {X Y : Fin 8}
    {u v1 v2 : ℝ³} (hu : u ≠ 0)
    (h1 : ⟪(fac8 T).N X, v1⟫ < 0) (h1' : ⟪(fac8 T).N Y, v1⟫ = 0)
    (h2 : ⟪(fac8 T).N X, v2⟫ = 0) (h2' : ⟪(fac8 T).N Y, v2⟫ < 0)
    (hX : ⟪(fac8 T).N X, u⟫ = 0) (hY : ⟪(fac8 T).N Y, u⟫ = 0)
    (hstr : ∀ t, t ≠ X → t ≠ Y →
      (pat t = true → 0 < ⟪(fac8 T).N t, u⟫) ∧ (pat t = false → ⟪(fac8 T).N t, u⟫ < 0))
    (hU : RobUni (fun a : ZMod k => ⟪x (c a), u⟫)) : IsRupert (univ.image x) := by
  obtain ⟨v, hfac, hv⟩ := h21b_exists_v (fac8 T) T.inj hc h1 h1' h2 h2' hX hY hstr
  obtain ⟨D⟩ := h21b_silL (fac8 T) hcyc hfac
  exact s0x_sil_isRupert_lex hk T.inj hc hu D hU

def h21rSegCond {k : ℕ} [NeZero k] (T : Facets21 x) (s : h21b_SegSpec k) : Prop :=
  (∀ t, s.i ∉ h21S t → s.j ∉ h21S t →
    (s.pat t = true → 0 < (fac8 T).f t (x s.j) - (fac8 T).f t (x s.i)) ∧
    (s.pat t = false → (fac8 T).f t (x s.j) - (fac8 T).f t (x s.i) < 0)) ∧
  RobUni (fun a : ZMod k => ⟪x (s.c a), x s.j - x s.i⟫)

theorem h21rSegCond_of {k : ℕ} [NeZero k] {T : Facets21 x} {s : h21b_SegSpec k}
    (h : h21b_SegCond T s) : h21rSegCond T s := ⟨h.1, s0x_robUni_of_uni h.2⟩

theorem h21r_seg_rupert (T : Facets21 x) {k : ℕ} [NeZero k] (s : h21b_SegSpec k) (hg : s.Good)
    (hC : h21rSegCond T s) : IsRupert (univ.image x) := by
  obtain ⟨hij, hXY, hiX, hjX, hiY, hjY, hboth, hup, hdn, ⟨m, hmX, hmY⟩, ⟨m', hmY', hmX'⟩, hc, hk, hcyc⟩ := hg
  obtain ⟨hlit, hU⟩ := hC
  set F := fac8 T with hF
  have hN : ∀ t (a b : Fin 7), ⟪F.N t, x a - x b⟫ = F.f t (x a) - F.f t (x b) :=
    fun t a b => (F.hN t _ _).symm
  have hu : x s.j - x s.i ≠ 0 := by
    intro h
    exact hij (T.inj (sub_eq_zero.1 h)).symm
  refine h21r_leaf_core T hk hc hcyc (X := s.X) (Y := s.Y) (u := x s.j - x s.i)
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

def h21rLinCond {k : ℕ} [NeZero k] (T : Facets21 x) (s : h21b_LinSpec k) : Prop :=
  (∀ t, t ≠ s.X → t ≠ s.Y →
    (s.pat t = true → 0 < ⟪(fac8 T).N t, cross ((fac8 T).N s.X) ((fac8 T).N s.Y)⟫) ∧
    (s.pat t = false → ⟪(fac8 T).N t, cross ((fac8 T).N s.X) ((fac8 T).N s.Y)⟫ < 0)) ∧
  RobUni (fun a : ZMod k => ⟪x (s.c a), cross ((fac8 T).N s.X) ((fac8 T).N s.Y)⟫)

theorem h21rLinCond_of {k : ℕ} [NeZero k] {T : Facets21 x} {s : h21b_LinSpec k}
    (h : h21b_LinCond T s) : h21rLinCond T s := ⟨h.1, s0x_robUni_of_uni h.2⟩

theorem h21r_lin_rupert (T : Facets21 x) {k : ℕ} [NeZero k] (s : h21b_LinSpec k) (hg : s.Good)
    (hC : h21rLinCond T s) : IsRupert (univ.image x) := by
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
  refine h21r_leaf_core T hk hc hcyc (X := s.X) (Y := s.Y) hu h1 h1' h2 h2' ?_ ?_ hstr hU
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-! ### The robust residual -/

def h21rNoSeg (T : Facets21 x) : Prop :=
  (∀ s ∈ h21b_seg4, ¬ h21rSegCond T s) ∧ (∀ s ∈ h21b_seg5, ¬ h21rSegCond T s) ∧
  (∀ s ∈ h21b_seg6, ¬ h21rSegCond T s)

def h21rNoLin (T : Facets21 x) : Prop :=
  (∀ s ∈ h21b_lin4, ¬ h21rLinCond T s) ∧ (∀ s ∈ h21b_lin5, ¬ h21rLinCond T s) ∧
  (∀ s ∈ h21b_lin6, ¬ h21rLinCond T s)

/-- **The robust residual**: no leaf applies even with `RobUni` in place of `Uni`. -/
def H21Resid3 (T : Facets21 x) : Prop := h21rResid T ∧ h21rNoSeg T ∧ h21rNoLin T

theorem h21r_resid3_imp_resid2 (T : Facets21 x) (h : H21Resid3 T) : H21Resid2 T := by
  obtain ⟨hr, ⟨s4, s5, s6⟩, ⟨l4, l5, l6⟩⟩ := h
  exact ⟨h21r_resid_imp T hr,
    ⟨fun s hs e => s4 s hs (h21rSegCond_of e), fun s hs e => s5 s hs (h21rSegCond_of e),
      fun s hs e => s6 s hs (h21rSegCond_of e)⟩,
    ⟨fun s hs e => l4 s hs (h21rLinCond_of e), fun s hs e => l5 s hs (h21rLinCond_of e),
      fun s hs e => l6 s hs (h21rLinCond_of e)⟩⟩

theorem h21r_rule_isRupert (T : Facets21 x) (h : ¬ H21Resid3 T) : IsRupert (univ.image x) := by
  by_contra hR
  apply h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact fun e => hR (h21r_W1 T e)
  · exact fun e => hR (h21r_W2 T e)
  · exact fun e => hR (h21r_W3 T e.1 e.2)
  · exact fun e => hR (h21r_W4 T e.1 e.2)
  · exact fun e => hR (h21r_W5 T e.1 e.2)
  · exact fun e => hR (h21r_W6 T e.1 e.2)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21b_seg4_good s hs) hc)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21b_seg5_good s hs) hc)
  · exact fun s hs hc => hR (h21r_seg_rupert T s (h21b_seg6_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21b_lin4_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21b_lin5_good s hs) hc)
  · exact fun s hs hc => hR (h21r_lin_rupert T s (h21b_lin6_good s hs) hc)

theorem h21r_rule_false (hN : IsNopert (Finset.univ.image x)) (T : Facets21 x)
    (h : ¬ H21Resid3 T) : False :=
  hN.2 (h21r_rule_isRupert T h)

end H21
end Minimality
