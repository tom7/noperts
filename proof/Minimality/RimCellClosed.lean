module

public import Minimality.SilS0XC
public import Minimality.RimCell

@[expose] public section

/-!
# Closed-cell leaves (type-free)

A rim cell given by up facets `U` and down facets `Dn` (each rim edge lies in one of each) is the
open cone `CellAt F U Dn` of views with strict facings.  Its closure is reached by weak facings.

* `S0xCycUD S c U Dn`: the cycle `c` is a silhouette of `U` (up) and `Dn` (down); decidable.
* `silL_of_cell`: weak facings at `u₀` and strict facings at any `a` give lex silhouette data at
  `(u₀, a)` (the tilt is the cell point itself).
* `isRupert_of_closedCell` (**closed-cell vertex leaf**): a nonempty cell, a point `u₀` of its
  closure (weak facings) and robustly unimodal rim depths at `u₀` (`RobUni`, ties allowed) give
  Rupert.  `u₀` need not be an extreme ray, and facets edge-on at `u₀` may be any number (so two
  parallel facets edge-on together are fine, unlike `s0x_lin_rupert`).
* `robUni_four_iff`-style: for a 4-rim, `RobUni` is exactly "some diagonal form negative and some
  positive" (`robUni_four_of_mixed`).
* `isRupert_of_closedCell_q4` (**Lemma Q4, Euclidean, no coplanarity hypothesis**): a nonempty cell
  with a 4-rim, closure points `g`, `g'` with `D1` failing at `g` (a diagonal form `< 0`) and `D2`
  failing at `g'` (a form `> 0`): Rupert.  The rim non-coplanarity (`hspan`) of
  `RimCell.isRupert_of_rimCell_coords` is not needed: a cell view where all four rim depths are equal
  is moved off by a tilt built from the rim triangle `c 0, c 1, c 2`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- The cycle `c` is a silhouette of the up facets `U` and the down facets `Dn`: each edge
`c i → c (i+1)` lies in some `a ∈ U` and some `b ∈ Dn`, and every other vertex is off one of them. -/
def S0xCycUD {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (c : ZMod k → Fin n)
    (U Dn : Finset (Fin m)) : Prop :=
  ∀ i, ∃ a ∈ U, ∃ b ∈ Dn, c i ∈ S a ∧ c i ∈ S b ∧ c (i + 1) ∈ S a ∧ c (i + 1) ∈ S b ∧
    ∀ q : Fin n, q ≠ c i → q ≠ c (i + 1) → q ∉ S a ∨ q ∉ S b

instance {k : ℕ} [NeZero k] (S : Fin m → Finset (Fin n)) (c : ZMod k → Fin n)
    (U Dn : Finset (Fin m)) : Decidable (S0xCycUD S c U Dn) := by
  unfold S0xCycUD; infer_instance

/-- Strict facings: the view `u` is in the open cell. -/
def CellAt (F : S0xFac m S x) (U Dn : Finset (Fin m)) (u : ℝ³) : Prop :=
  (∀ t ∈ U, 0 < ⟪F.N t, u⟫) ∧ ∀ t ∈ Dn, ⟪F.N t, u⟫ < 0

/-- Weak facings: the view `u` is in the closed cell. -/
def CellLe (F : S0xFac m S x) (U Dn : Finset (Fin m)) (u : ℝ³) : Prop :=
  (∀ t ∈ U, 0 ≤ ⟪F.N t, u⟫) ∧ ∀ t ∈ Dn, ⟪F.N t, u⟫ ≤ 0

theorem CellAt.cellLe {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u : ℝ³} (h : CellAt F U Dn u) :
    CellLe F U Dn u :=
  ⟨fun t ht => (h.1 t ht).le, fun t ht => (h.2 t ht).le⟩

/-- Lex silhouette data at `(u₀, a)` from weak facings at `u₀` and strict facings at `a`. -/
theorem silL_of_cell {k : ℕ} [NeZero k] (F : S0xFac m S x) {c : ZMod k → Fin n}
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u₀ a : ℝ³} (hu : CellLe F U Dn u₀)
    (ha : CellAt F U Dn a) : Nonempty (h21b_SilDataL k x c u₀ a) := by
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
    up := fun i => by
      rcases (hu.1 _ (hea i)).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, ha.1 _ (hea i)⟩
    dn := fun i => by
      rcases (hu.2 _ (heb i)).lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [h]; simp, by linarith [ha.2 _ (heb i)]⟩ }⟩

/-- `RobUni` of `k ≥ 4` values forces them not all equal. -/
theorem not_robUni_const {k : ℕ} (hk : 4 ≤ k) (r : ℝ) : ¬ RobUni (fun _ : ZMod k => r) := by
  intro h
  exact h 0 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by omega)
    ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- **Closed-cell vertex leaf.**  A nonempty cell (`a`), a point `u₀` of its closure and robustly
unimodal rim depths at `u₀`: Rupert. -/
theorem isRupert_of_closedCell {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a u₀ : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨D⟩ := silL_of_cell F hcyc hu ha
  have hu0 : u₀ ≠ 0 := by
    rintro rfl
    exact not_robUni_const hk 0 (by simpa using hR)
  exact s0x_sil_isRupert_lex (by omega) hx hc hu0 D hR

open Minimality.RimCell in
/-- For a 4-cycle, a negative and a positive diagonal form give `RobUni`. -/
theorem robUni_four_of_mixed {z : ZMod 4 → ℝ}
    (hn : ∃ p ∈ diagPairs, z p.1 - z p.2 < 0) (hp : ∃ p ∈ diagPairs, 0 < z p.1 - z p.2) :
    RobUni z := by
  obtain ⟨p, hpm, hpn⟩ := hn
  obtain ⟨q, hqm, hqp⟩ := hp
  simp only [diagPairs, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hpm hqm
  intro B b c d hb hbc hcd hd
  have hb1 : b = 1 := by omega
  have hc2 : c = 2 := by omega
  have hd3 : d = 3 := by omega
  subst hb1 hc2 hd3
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only at hpm hqm hpn hqp
  have e : ((0 : ZMod 4) + 1 = 1 ∧ (0 : ZMod 4) + 2 = 2 ∧ (0 : ZMod 4) + 3 = 3) ∧
      ((1 : ZMod 4) + 1 = 2 ∧ (1 : ZMod 4) + 2 = 3 ∧ (1 : ZMod 4) + 3 = 0) ∧
      ((2 : ZMod 4) + 1 = 3 ∧ (2 : ZMod 4) + 2 = 0 ∧ (2 : ZMod 4) + 3 = 1) ∧
      ((3 : ZMod 4) + 1 = 0 ∧ (3 : ZMod 4) + 2 = 1 ∧ (3 : ZMod 4) + 3 = 2) := by decide
  obtain ⟨⟨e01, e02, e03⟩, ⟨e11, e12, e13⟩, ⟨e21, e22, e23⟩, ⟨e31, e32, e33⟩⟩ := e
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by revert B; decide
  rcases hB with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.cast_one, Nat.cast_ofNat]
    rintro ⟨h1, h2, h3, h4⟩
    simp only [e01, e02, e03, e11, e12, e13, e21, e22, e23, e31, e32, e33] at h1 h2 h3 h4
    clear e01 e02 e03 e11 e12 e13 e21 e22 e23 e31 e32 e33
    rcases hpm with ⟨rfl | rfl, rfl | rfl⟩ <;> rcases hqm with ⟨rfl | rfl, rfl | rfl⟩ <;>
      simp_all <;> linarith

/-- Moving from a closed-cell point `g` toward a cell point `a` enters the open cell. -/
theorem eventually_cellAt {F : S0xFac m S x} {U Dn : Finset (Fin m)} {a g : ℝ³}
    (ha : CellAt F U Dn a) (hg : CellLe F U Dn g) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (g + ε • (a - g)) := by
  have e : ∀ t ε, ⟪F.N t, g + ε • (a - g)⟫ = ⟪F.N t, g⟫ + ε * (⟪F.N t, a⟫ - ⟪F.N t, g⟫) := by
    intro t ε; rw [inner_add_right, inner_smul_right, inner_sub_right]
  refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
    (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
  · have h := eventually_pos_affine (A := ⟪F.N t, g⟫) (B := ⟪F.N t, a⟫ - ⟪F.N t, g⟫) (by
      rcases (hg.1 t ht).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, by rw [← h]; linarith [ha.1 t ht]⟩)
    exact h.mono fun ε hε => by rw [e]; exact hε
  · have h := eventually_pos_affine (A := -⟪F.N t, g⟫) (B := -(⟪F.N t, a⟫ - ⟪F.N t, g⟫)) (by
      rcases (hg.2 t ht).lt_or_eq with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by rw [h]; simp, by rw [h]; linarith [ha.2 t ht]⟩)
    exact h.mono fun ε hε => by rw [e]; linarith

/-- A closed-cell point is in the closure of the open cell (when the cell is nonempty). -/
theorem mem_closure_cell {F : S0xFac m S x} {U Dn : Finset (Fin m)} {a g : ℝ³}
    (ha : CellAt F U Dn a) (hg : CellLe F U Dn g) :
    g ∈ closure {u | CellAt F U Dn u} := by
  have ht : Tendsto (fun ε : ℝ => g + ε • (a - g)) (𝓝[>] 0) (𝓝 g) := by
    have hc : Continuous fun ε : ℝ => g + ε • (a - g) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht (eventually_cellAt ha hg)

/-- At a cell view `u`, the rim triangle `c 0, c 1, c 2` is not degenerate along `u`. -/
theorem det_ne_zero_of_cellAt {k : ℕ} [NeZero k] (hk : 3 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {u : ℝ³} (hu : CellAt F U Dn u) :
    ⟪x (c 0) - x (c 1), cross (x (c 2) - x (c 1)) u⟫ ≠ 0 := by
  obtain ⟨a, haU, b, hbD, h0a, h0b, h1a, h1b, hs⟩ := hcyc 0
  obtain ⟨n1, n2⟩ := zmod_ne hk
  have hc2 : c 2 ≠ c 0 := fun h => n2 (hc h)
  have hc21 : c 2 ≠ c (0 + 1) := fun h => by
    have := hc h
    rw [zero_add] at this
    have h1 : (1 : ZMod k) = 2 := this.symm
    have : (1 : ZMod k) = 0 := by linear_combination -h1
    exact n1 this
  set P := x (c 0) - x (c 1) with hP
  set Q := x (c 2) - x (c 1) with hQ
  have z1a := F.zero a _ h1a
  have z1b := F.zero b _ h1b
  rw [zero_add] at z1a z1b
  have hPa : ⟪F.N a, P⟫ = 0 := by
    rw [hP, F.inner_sub, F.zero a _ h0a, z1a, sub_zero]
  have hPb : ⟪F.N b, P⟫ = 0 := by
    rw [hP, F.inner_sub, F.zero b _ h0b, z1b, sub_zero]
  have hQa : ⟪F.N a, Q⟫ = F.f a (x (c 2)) := by rw [hQ, F.inner_sub, z1a, sub_zero]
  have hQb : ⟪F.N b, Q⟫ = F.f b (x (c 2)) := by rw [hQ, F.inner_sub, z1b, sub_zero]
  have hqa := F.le a (c 2)
  have hqb := F.le b (c 2)
  have hua := hu.1 a haU
  have hub := hu.2 b hbD
  have hQv : 0 < ⟪F.N a, Q⟫ * ⟪F.N b, u⟫ - ⟪F.N a, u⟫ * ⟪F.N b, Q⟫ := by
    rw [hQa, hQb]
    rcases hs (c 2) hc2 hc21 with h | h
    · have := F.neg a _ h
      nlinarith [mul_nonneg (neg_nonneg.2 hqb) hua.le]
    · have := F.neg b _ h
      nlinarith [mul_nonneg (neg_nonneg.2 hqa) (neg_nonneg.2 hub.le)]
  rw [h21_binet] at hQv
  have hcr : cross (F.N a) (F.N b) ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hQv; exact lt_irrefl _ hQv
  obtain ⟨μ, hμ⟩ := h21_mul_cross hcr hPa hPb
  rw [hμ, real_inner_smul_left]
  have hP0 : P ≠ 0 := by
    intro h
    have : x (c 0) = x (c 1) := sub_eq_zero.1 h
    have := hc (hx this)
    exact n1 this.symm
  have hμ0 : μ ≠ 0 := by
    rintro rfl; rw [zero_smul] at hμ; exact hP0 hμ
  exact mul_ne_zero hμ0 hQv.ne'

open Minimality.RimCell in
/-- **Lemma Q4 on a closed cell (Euclidean, no coplanarity hypothesis).**  A nonempty cell with a
4-rim, a closure point `g` where some diagonal form is negative (`D1` fails) and a closure point
`g'` where some diagonal form is positive (`D2` fails): Rupert. -/
theorem isRupert_of_closedCell_q4 (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a g g' : ℝ³} (ha : CellAt F U Dn a)
    (hg : CellLe F U Dn g) (hg' : CellLe F U Dn g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), g'⟫) :
    IsRupert (univ.image x) := by
  set A : Set ℝ³ := {u | CellAt F U Dn u} with hA
  let f : {p // p ∈ diagPairs} → ℝ³ →ₗ[ℝ] ℝ := fun p =>
    (innerSL ℝ (x (c p.1.1) - x (c p.1.2))).toLinearMap
  have hf : ∀ p u, f p u = ⟪x (c p.1.1) - x (c p.1.2), u⟫ := fun p u => rfl
  have hfc : ∀ p, Continuous (f p) := fun p => (innerSL ℝ _).continuous
  have hAc : Convex ℝ A := by
    intro u hu v hv s t hs ht hst
    have e : ∀ N : ℝ³, ⟪N, s • u + t • v⟫ = s * ⟪N, u⟫ + t * ⟪N, v⟫ := by
      intro N; rw [inner_add_right, inner_smul_right, inner_smul_right]
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [e]
      have := hu.1 r hr; have := hv.1 r hr
      rcases hs.lt_or_eq with h | h
      · nlinarith
      · subst h; simp at hst; subst hst; simpa
    · rw [e]
      have := hu.2 r hr; have := hv.2 r hr
      rcases hs.lt_or_eq with h | h
      · nlinarith
      · subst h; simp at hst; subst hst; simpa
  -- a mixed cell view
  have hmix : ∃ u ∈ A, (∃ p, f p u < 0) ∧ ∃ p, 0 < f p u := by
    by_contra H
    have hz : ∀ u ∈ A, ∃ p, f p u ≠ 0 := by
      intro u hu
      by_contra hall
      push Not at hall
      set P := x (c 0) - x (c 1)
      set Q := x (c 2) - x (c 1)
      set d : ℝ³ := cross Q u - cross u P with hd
      have hD := det_ne_zero_of_cellAt (by norm_num) F hx hc hcyc hu
      have ePd : ⟪P, d⟫ = ⟪P, cross Q u⟫ := by
        simp only [hd, inner3, cross_apply_zero, cross_apply_one, cross_apply_two,
          PiLp.sub_apply]; ring
      have eQd : ⟪Q, d⟫ = -⟪P, cross Q u⟫ := by
        simp only [hd, inner3, cross_apply_zero, cross_apply_one, cross_apply_two,
          PiLp.sub_apply]; ring
      -- move along d inside the cell
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u + ε • d) := by
        have e : ∀ t ε, ⟪F.N t, u + ε • d⟫ = ⟪F.N t, u⟫ + ε * ⟪F.N t, d⟫ := by
          intro t ε; rw [inner_add_right, inner_smul_right]
        refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
          (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
        · exact (eventually_pos_affine (Or.inl (hu.1 t ht))).mono fun ε hε => by rw [e]; exact hε
        · exact (eventually_pos_affine (B := -⟪F.N t, d⟫) (Or.inl (neg_pos.2 (hu.2 t ht)))).mono
            fun ε hε => by rw [e]; linarith
      obtain ⟨ε, hεA, hε⟩ := (hev.and self_mem_nhdsWithin).exists
      have hε0 : (0 : ℝ) < ε := hε
      have p01 : ((0 : ZMod 4), (1 : ZMod 4)) ∈ diagPairs := by decide
      have p21 : ((2 : ZMod 4), (1 : ZMod 4)) ∈ diagPairs := by decide
      have v01 : f ⟨_, p01⟩ (u + ε • d) = ε * ⟪P, cross Q u⟫ := by
        rw [map_add, map_smul, hall, hf, smul_eq_mul, zero_add]
        simp only; rw [ePd]
      have v21 : f ⟨_, p21⟩ (u + ε • d) = -(ε * ⟪P, cross Q u⟫) := by
        rw [map_add, map_smul, hall, hf, smul_eq_mul, zero_add]
        simp only; rw [eQd]; ring
      apply H
      refine ⟨u + ε • d, hεA, ?_⟩
      rcases lt_or_gt_of_ne hD with h | h
      · exact ⟨⟨_, by rw [v01]; nlinarith⟩, ⟨_, by rw [v21]; nlinarith⟩⟩
      · exact ⟨⟨_, by rw [v21]; nlinarith⟩, ⟨_, by rw [v01]; nlinarith⟩⟩
    obtain ⟨pn, hpn, hpnv⟩ := hn
    obtain ⟨pp, hpp, hppv⟩ := hp
    exact H (exists_mixed_sign_of_closure f hfc hAc hz (mem_closure_cell ha hg)
      (mem_closure_cell ha hg') ⟨⟨pn, hpn⟩, hpnv⟩ ⟨⟨pp, hpp⟩, hppv⟩)
  obtain ⟨u, hu, ⟨pn, hpn⟩, ⟨pp, hpp⟩⟩ := hmix
  refine isRupert_of_closedCell le_rfl F hx hc hcyc hu hu.cellLe (robUni_four_of_mixed ?_ ?_)
  · exact ⟨pn.1, pn.2, by rw [← inner_sub_left]; exact hpn⟩
  · exact ⟨pp.1, pp.2, by rw [← inner_sub_left]; exact hpp⟩

/-- A closed-cell point `u₀` with a tilt `v` deciding the edge-on facets (lex facings) gives a point of
the open cell (`u₀ + ε v`, `ε > 0` small). -/
theorem exists_cellAt_of_lex {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u₀ v : ℝ³}
    (hU : ∀ t ∈ U, h21b_LP ⟪F.N t, u₀⟫ ⟪F.N t, v⟫)
    (hD : ∀ t ∈ Dn, h21b_LP (-⟪F.N t, u₀⟫) (-⟪F.N t, v⟫)) : ∃ a, CellAt F U Dn a := by
  have e : ∀ t ε, ⟪F.N t, u₀ + ε • v⟫ = ⟪F.N t, u₀⟫ + ε * ⟪F.N t, v⟫ := by
    intro t ε; rw [inner_add_right, inner_smul_right]
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u₀ + ε • v) := by
    refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
      (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
    · exact (eventually_pos_affine (hU t ht)).mono fun ε hε => by rw [e]; exact hε
    · exact (eventually_pos_affine (hD t ht)).mono fun ε hε => by rw [e]; linarith
  obtain ⟨ε, hε⟩ := hev.exists
  exact ⟨_, hε⟩

end H21
end Minimality
