module

public import Minimality.SilS0XA
public import Minimality.Type21Sl2E

@[expose] public section


/-!
# S0X-B: S0-lex and S0-rob (type-free)

The lex form of `SilData` is the tree's `h21b_SilDataL k x c u₀ v` (Type21Sl2A): the same fields as
`SilData`, with `up : h21b_LP ⟪A i, u₀⟫ ⟪A i, v⟫` and `dn : h21b_LP (-⟪B i, u₀⟫) (-⟪B i, v⟫)`
(lex facings; only the up/down facets of the cycle edges enter, so only those must be lex-strict).
The tree's `h21b_sil_cell` needs a tilt `v` that also separates the cycle points and strict `Uni`.
Here:
* `s0x_sep_tilt`: any lex data at `(u₀, v)` stays lex data at `(u₀, v + η s)` for small `η > 0`, and
  for a separating `s` the new tilt separates the cycle points (so the user picks `v` only for the
  edge-on facings, e.g. by `s0x_exists_tilt_signs`);
* `s0x_sil_cell_lexUni`: the cell from any `LexUni` of the lex depths;
* `s0x_sil_cell_lex` (**S0-lex + rob**): lex data at any `(u₀, v)` and `RobUni` of `⟪x (c i), u₀⟫`;
* `s0x_sil_cell_rob` (**S0-rob**): `SilData` (strict facings) and `RobUni`;
* `s0x_exists_tilt_signs`, `s0x_exists_tilt_sign1`: tilts with prescribed `⟪n, v⟫` for one or two
  independent normals.
`Uni → RobUni` is `s0x_robUni_of_uni` (S0XA), so these subsume `h21_sil_cell` and `h21b_sil_cell`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}

/-- Strict facings are lex facings at any tilt. -/
def SilData.s0x_toL (D : SilData k x c u₀) (v : ℝ³) : h21b_SilDataL k x c u₀ v where
  A := D.A
  B := D.B
  fA := D.fA
  fB := D.fB
  hA := D.hA
  hB := D.hB
  zA0 := D.zA0
  zA1 := D.zA1
  zB0 := D.zB0
  zB1 := D.zB1
  nA := D.nA
  nB := D.nB
  strict := D.strict
  up i := Or.inl (D.up i)
  dn i := Or.inl (by linarith [D.dn i])

/-- A lex positive pair stays lex positive when the second entry moves by `η c`, `η > 0` small. -/
theorem s0x_lp_ev {a b c : ℝ} (h : h21b_LP a b) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), h21b_LP a (b + η * c) := by
  rcases h with h | ⟨h0, h1⟩
  · exact Eventually.of_forall fun _ => Or.inl h
  · exact (eventually_pos_affine (A := b) (B := c) (Or.inl h1)).mono fun η hη => Or.inr ⟨h0, hη⟩

theorem s0x_ne_ev {b c : ℝ} (h : c ≠ 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), b + η * c ≠ 0 := by
  have : h21b_LP b c ∨ h21b_LP (-b) (-c) := by
    unfold h21b_LP
    rcases lt_trichotomy b 0 with hb | rfl | hb
    · right; left; linarith
    · rcases lt_or_gt_of_ne h with hc | hc
      · right; right; exact ⟨by simp, by linarith⟩
      · left; right; exact ⟨rfl, hc⟩
    · left; left; exact hb
  rcases this with h' | h'
  · exact (eventually_pos_affine h').mono fun η hη => hη.ne'
  · exact (eventually_pos_affine h').mono fun η hη e => by linarith

/-- **The tilt can be made separating**: lex data at `(u₀, v)` gives lex data at some `(u₀, v')` whose
tilt separates the cycle points. -/
theorem s0x_sep_tilt (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v) :
    ∃ v' : ℝ³, Nonempty (h21b_SilDataL k x c u₀ v') ∧
      ∀ i j : ZMod k, i ≠ j → ⟪x (c i), v'⟫ ≠ ⟪x (c j), v'⟫ := by
  obtain ⟨s, hs⟩ := exists_tilt (k := k) hx hc
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (∀ i, h21b_LP ⟪D.A i, u₀⟫ (⟪D.A i, v⟫ + η * ⟪D.A i, s⟫)) ∧
      (∀ i, h21b_LP (-⟪D.B i, u₀⟫) (-⟪D.B i, v⟫ + η * (-⟪D.B i, s⟫))) ∧
      (∀ i j : ZMod k, i ≠ j →
        (⟪x (c i), v⟫ - ⟪x (c j), v⟫) + η * (⟪x (c i), s⟫ - ⟪x (c j), s⟫) ≠ 0) := by
    refine (eventually_all.2 fun i => s0x_lp_ev (D.up i)).and
      ((eventually_all.2 fun i => s0x_lp_ev (D.dn i)).and
        (eventually_all.2 fun i => eventually_all.2 fun j => ?_))
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · exact (s0x_ne_ev (sub_ne_zero.2 (hs i j hij))).mono fun _ h _ => h
  obtain ⟨η, h1, h2, h3⟩ := hev.exists
  have e : ∀ y : ℝ³, ⟪y, v + η • s⟫ = ⟪y, v⟫ + η * ⟪y, s⟫ := fun y => by
    rw [inner_add_right, real_inner_smul_right]
  refine ⟨v + η • s, ⟨{ D with
    up := fun i => by rw [e]; exact h1 i
    dn := fun i => by rw [e, neg_add, ← mul_neg]; exact h2 i }⟩, ?_⟩
  intro i j hij h
  rw [e, e] at h
  exact h3 i j hij (by linarith)

/-- **The lex silhouette cell, general depth form**: lex data at `(u₀, v)` and lex unimodal depths
`(⟪x (c i), u₀⟫, ⟪x (c i), v⟫)`. -/
theorem s0x_sil_cell_lexUni (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v)
    (hL : LexUni (fun i => ⟪x (c i), u₀⟫) (fun i => ⟪x (c i), v⟫)) :
    HasLexCellAt (univ.image x) u₀ := by
  choose μ hμ0 hd using h21b_exists_mu hk hx hc D
  rcases h21b_sign_agree hk hx hc D μ hμ0 hd with hp | hn
  · exact h21b_core_pos hc hk D μ hp hd hL
  · refine h21b_core_pos (c := fun i => c (-i)) (fun i j h => neg_injective (hc h)) hk D.rev
      (fun i => - μ (-i - 1)) (fun i => by linarith [hn (-i - 1)]) ?_ (Type08Sp.lexUni_neg hL)
    intro i
    have := hd (-i - 1)
    rw [sub_add_cancel] at this
    show x (c (-(i + 1))) - x (c (-i)) = (-μ (-i - 1)) • cross (D.A (-i - 1)) (D.B (-i - 1))
    rw [show -(i + 1) = -i - 1 by ring, neg_smul, ← this]
    abel

/-- **S0-lex with robust depths**: lex facings at any `(u₀, v)` (edge-on up/down facets allowed; the
tilt need not separate depth ties) and `RobUni` of the depths along the cycle. -/
theorem s0x_sil_cell_lex (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : h21b_SilDataL k x c u₀ v) (hU : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    HasLexCellAt (univ.image x) u₀ := by
  obtain ⟨v', ⟨D'⟩, hv⟩ := s0x_sep_tilt hx hc D
  exact s0x_sil_cell_lexUni hk hx hc D'
    (s0x_lexUni_of_robUni hk hU _ fun i j _ h => by_contra fun hij => hv i j hij h)

theorem s0x_sil_isRupert_lex (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (hu : u₀ ≠ 0) (D : h21b_SilDataL k x c u₀ v) (hU : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ ⟨u₀, hu, s0x_sil_cell_lex hk hx hc D hU⟩

/-- **S0-rob**: `h21_sil_cell` with `Uni` weakened to `RobUni` (no weak alternating quadruple). -/
theorem s0x_sil_cell_rob (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : SilData k x c u₀) (hU : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    HasLexCellAt (univ.image x) u₀ :=
  s0x_sil_cell_lex hk hx hc (D.s0x_toL 0) hU

theorem s0x_sil_isRupert_rob (hk : 3 ≤ k) (hx : Function.Injective x) (hc : Function.Injective c)
    (D : SilData k x c u₀) (hU : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    IsRupert (univ.image x) := by
  have hu : u₀ ≠ 0 := by
    intro h; have := D.up 0; subst h; simp at this
  exact isRupert_of_hasLexCell _ ⟨u₀, hu, s0x_sil_cell_rob hk hx hc D hU⟩

/-! ### Tilts with prescribed edge-on facings -/

/-- One normal: any value of `⟪n, v⟫`. -/
theorem s0x_exists_tilt_sign1 {n : ℝ³} (h : n ≠ 0) (t : ℝ) : ∃ v : ℝ³, ⟪n, v⟫ = t := by
  have hn : ⟪n, n⟫ ≠ 0 := (real_inner_self_pos.2 h).ne'
  exact ⟨(t / ⟪n, n⟫) • n, by rw [real_inner_smul_right]; field_simp⟩

/-- Two independent normals (`cross n₁ n₂ ≠ 0`, e.g. two facets edge-on at `u₀ ≠ 0`): any values of
`⟪n₁, v⟫`, `⟪n₂, v⟫`, so any lex sign pattern. -/
theorem s0x_exists_tilt_signs {n₁ n₂ : ℝ³} (h : cross n₁ n₂ ≠ 0) (t₁ t₂ : ℝ) :
    ∃ v : ℝ³, ⟪n₁, v⟫ = t₁ ∧ ⟪n₂, v⟫ = t₂ := by
  obtain ⟨v1, v2, h1, h1', h2, h2'⟩ := h21b_dual h
  refine ⟨(t₁ / ⟪n₁, v1⟫) • v1 + (t₂ / ⟪n₂, v2⟫) • v2, ?_, ?_⟩
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h2, mul_zero, add_zero,
      div_mul_cancel₀ _ h1.ne]
  · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h1', mul_zero, zero_add,
      div_mul_cancel₀ _ h2'.ne]

end H21
end Minimality

