module

public import Minimality.Type24GapLemmas

/-!
# GAPT2OC: the `236` face of the `T_2` cell `A2` and a closed-face `B2` leaf on the `012` edge

The type-24 lemma-gap point `w6_15_0` (nopert229 `data/hard/holekit/lemmagap_new.lines`, found by the LRADV3
adversary; no earlier Lean region lemma holds on either side) carries strict apex certificates only on two
walls of the `T_2` cone (nopert229 FACENORM24.md "== GAPT2OC =="):

* side `x`: the face of cell `A2` (rim `cA2 = 0.5.3.6.1`) where facet `236` is edge-on, the views
  `t2e236 x s = x₃ - x₂ + s (x₆ - x₂)`, `s > 0` (base `5-3` apex `6`, order `1 < 5 < 0 < 6 < 3`, between the
  ties `z₀ = z₆` and `z₃ = z₆`; or base `6-1` apex `3`).  This is the face family `T2Edge236` that the WALLGEN
  design review (nopert229 notes/WALL-GENERALIZATION.md, item 1) proposed and predicted for this point.
* twin side: the `012` edge of `B2` (`t2e012`, as `T2Edge012B2`) with an apex certificate (base `0-5` apex `4`)
  instead of three monotone corners: `T2Edge012B2C` (RobUni or ApexCert; contains `T2Edge012B2`).

Generic step added here: `lexAny_of_wall_robUni` (any cell, any closed-face view carrying `RobUni`), the Lex twin of
`splitAny_of_wall_apexCert`; `robUni_eventually_add` is the persistence of `RobUni` under a small view change.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt
  Minimality.T24.M4

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic: `RobUni` at a closed-face view -/

/-- `RobUni` is open in the view: it persists from `u` to `u + t e` for `t` near `0` (public copy of the private
`GenPlus.robUni_eventually` of `WeakChord.lean`). -/
theorem robUni_eventually_add {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (u e : ℝ³)
    (hR : RobUni (fun i => ⟪X i, u⟫)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), RobUni (fun i => ⟪X i, u + t • e⟫) := by
  have hlin : ∀ i : ZMod k, ∀ t : ℝ, ⟪X i, u + t • e⟫ = ⟪X i, u⟫ + t * ⟪X i, e⟫ := fun i t => by
    rw [inner_add_right, real_inner_smul_right]
  have h4 : ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
      ∀ᶠ t in 𝓝 (0 : ℝ),
        ⟪X B, u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X B, u + t • e⟫ < ⟪X (B + d), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + d), u + t • e⟫ := by
    intro B b c d hb hbc hcd hd
    have hlt_ev : ∀ i j : ZMod k, ⟪X i, u⟫ < ⟪X j, u⟫ →
        ∀ᶠ t in 𝓝 (0 : ℝ), ⟪X i, u + t • e⟫ < ⟪X j, u + t • e⟫ := by
      intro i j hij
      have hc : Continuous fun t : ℝ => ⟪X j, u + t • e⟫ - ⟪X i, u + t • e⟫ := by
        simp_rw [hlin]; fun_prop
      have h0 : 0 < (fun t : ℝ => ⟪X j, u + t • e⟫ - ⟪X i, u + t • e⟫) 0 := by
        simp; linarith
      filter_upwards [(hc.tendsto 0).eventually_const_lt h0] with t ht
      linarith
    have h4' : ⟪X B, u⟫ < ⟪X (B + b), u⟫ ∨ ⟪X (B + c), u⟫ < ⟪X (B + b), u⟫ ∨
        ⟪X B, u⟫ < ⟪X (B + d), u⟫ ∨ ⟪X (B + c), u⟫ < ⟪X (B + d), u⟫ := by
      by_contra hnot
      push Not at hnot
      exact hR B b c d hb hbc hcd hd ⟨hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩
    rcases h4' with h | h | h | h
    · exact (hlt_ev _ _ h).mono fun _ => Or.inl
    · exact (hlt_ev _ _ h).mono fun _ ht => Or.inr (Or.inl ht)
    · exact (hlt_ev _ _ h).mono fun _ ht => Or.inr (Or.inr (Or.inl ht))
    · exact (hlt_ev _ _ h).mono fun _ ht => Or.inr (Or.inr (Or.inr ht))
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ (B : ZMod k) (b c d : ℕ),
      0 < b → b < c → c < d → d < k →
        ⟪X B, u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X B, u + t • e⟫ < ⟪X (B + d), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + d), u + t • e⟫ := by
    rw [eventually_all]
    intro B
    have hb_fin : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b c d : Fin k,
        0 < b.val → b.val < c.val → c.val < d.val → d.val < k →
          ⟪X B, u + t • e⟫ < ⟪X (B + b.val), u + t • e⟫ ∨
          ⟪X (B + c.val), u + t • e⟫ < ⟪X (B + b.val), u + t • e⟫ ∨
          ⟪X B, u + t • e⟫ < ⟪X (B + d.val), u + t • e⟫ ∨
          ⟪X (B + c.val), u + t • e⟫ < ⟪X (B + d.val), u + t • e⟫ := by
      refine eventually_all.mpr fun b => eventually_all.mpr fun c => eventually_all.mpr fun d => ?_
      by_cases hcond : 0 < b.val ∧ b.val < c.val ∧ c.val < d.val ∧ d.val < k
      · filter_upwards [h4 B b.val c.val d.val hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2] with t ht _ _ _ _
        exact ht
      · filter_upwards with t hb' hbc' hcd' hd'
        exact absurd ⟨hb', hbc', hcd', hd'⟩ hcond
    filter_upwards [hb_fin] with t ht b c d hb hbc hcd hd
    exact ht ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩ hb hbc hcd hd
  filter_upwards [hall] with t ht B b c d hb hbc hcd hd hnot
  rcases ht B b c d hb hbc hcd hd with h | h | h | h <;> linarith [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]

/-- **Wall view with a robustly unimodal rim** (G1): a view `r` on the closed face of a cell `c` (every facet strictly
of its side, or `= 0` with `v` pointing to its side) at which the rim depths are `RobUni` gives `Gen.LexAny F`. -/
theorem lexAny_of_wall_robUni (F : S0xFac 9 s0x_S24 x) (c : Cell24) {r v : ℝ³}
    (hU : ∀ t ∈ c.U, 0 < ⟪F.N t, r⟫ ∨ (⟪F.N t, r⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ c.U, ⟪F.N t, r⟫ < 0 ∨ (⟪F.N t, r⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (hR : RobUni (fun i => ⟪x (c.r i), r⟫)) : Gen.LexAny F := by
  have evC := cellAt_eventually_of_wall F c.U hU hD
  have evR : ∀ᶠ η : ℝ in 𝓝[>] 0, RobUni (fun i => ⟪x (c.r i), r + η • v⟫) :=
    (robUni_eventually_add (fun i => x (c.r i)) r v hR).filter_mono nhdsWithin_le_nhds
  obtain ⟨η, hcell, hR'⟩ := (evC.and evR).exists
  exact lexAny_of_cellRob F c hcell hR'

/-- **Wall view with a certificate**: `RobUni` or `ApexCert` at a closed-face view of a cell gives a leaf. -/
theorem leaf_of_wall_cert (F : S0xFac 9 s0x_S24 x) (c : Cell24) {r v : ℝ³}
    (hU : ∀ t ∈ c.U, 0 < ⟪F.N t, r⟫ ∨ (⟪F.N t, r⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ c.U, ⟪F.N t, r⟫ < 0 ∨ (⟪F.N t, r⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (h : RobUni (fun i => ⟪x (c.r i), r⟫) ∨ ApexCert (fun i => x (c.r i)) r) :
    Gen.LexAny F ∨ Gen.SplitAny F :=
  h.elim (fun hR => Or.inl (lexAny_of_wall_robUni F c hU hD hR))
    (fun hA => Or.inr (splitAny_of_wall_apexCert F c hU hD hA))

/-! ## `T2Edge236`: the `236` face of `A2` -/

/-- The `236` face view of `T_2`: `x₃ - x₂ + s (x₆ - x₂)` (facet `236` edge-on; `s → 0` is the corner ray `x₃ - x₂`,
`s → ∞` the corner ray `x₆ - x₂`). -/
noncomputable def t2e236 (x : Fin 7 → ℝ³) (s : ℝ) : ℝ³ := x 3 - x 2 + s • (x 6 - x 2)

/-- **T2Edge236:** some `s > 0` such that at the face view `r = x₃ - x₂ + s (x₆ - x₂)` (facet `236` edge-on) the
`A2` facets `016, 0345, 046, 346` are in front (`012, 025, 126, 235` are automatically behind) and the `A2` rim
`cA2 = 0.5.3.6.1` is `RobUni` or carries a strict apex certificate (at `w6_15_0`: base `5-3`, apex `6`). -/
def T2Edge236 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s : ℝ, 0 < s ∧ 0 < ⟪F.N 1, t2e236 x s⟫ ∧ 0 < ⟪F.N 3, t2e236 x s⟫ ∧ 0 < ⟪F.N 4, t2e236 x s⟫ ∧
    0 < ⟪F.N 8, t2e236 x s⟫ ∧
    (RobUni (fun i => ⟪x (TwoCone.cA2 i), t2e236 x s⟫) ∨ ApexCert (fun i => x (TwoCone.cA2 i)) (t2e236 x s))

/-- **T2Edge236 (leaf):** `T2Edge236 x F` gives `Gen.LexAny F ∨ Gen.SplitAny F` (push `x₁ - x₂` into the open
`A2`). -/
theorem leaf_of_t2Edge236 {F : S0xFac 9 s0x_S24 x} (h : T2Edge236 x F) : Gen.LexAny F ∨ Gen.SplitAny F := by
  obtain ⟨s, hs, h1, h3, h4, h8, hC⟩ := h
  have hNr : ∀ t : Fin 9, ⟪F.N t, t2e236 x s⟫ =
      (F.f t (x 3) - F.f t (x 2)) + s * (F.f t (x 6) - F.f t (x 2)) := by
    intro t
    rw [t2e236, inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
  refine leaf_of_wall_cert F cellA2 (v := x 1 - x 2) ?_ ?_ hC
  · intro t ht
    have ht' : t ∈ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    left
    rcases ht' with rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h4
    · exact h8
  · intro t ht
    have ht' : t ∉ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
    have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht'' with rfl | rfl | rfl | rfl | rfl
    · left
      rw [hNr, F.zero 0 2 (by decide)]
      have h3' := F.neg 0 3 (by decide)
      have h6' := F.neg 0 6 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 2 2 (by decide)]
      have h3' := F.neg 2 3 (by decide)
      have h6' := F.neg 2 6 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
      linarith [F.neg 5 3 (by decide)]
    · left
      rw [hNr, F.zero 6 2 (by decide), F.zero 6 3 (by decide)]
      have h6' := F.neg 6 6 (by decide)
      nlinarith
    · right
      rw [hNr, F.inner_sub, F.zero 7 2 (by decide), F.zero 7 3 (by decide), F.zero 7 6 (by decide)]
      exact ⟨by ring, by linarith [F.neg 7 1 (by decide)]⟩

/-- **T2Edge236, `π_24` twin.** -/
theorem leaf_of_t2Edge236_twin {F : S0xFac 9 s0x_S24 x}
    (h : T2Edge236 (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F ∨ Gen.SplitAny F :=
  (leaf_of_t2Edge236 h).elim (fun hL => Or.inl (Sym.lexAny_sym F hL))
    (fun hS => Or.inr (Sym.splitAny24_sym F hS))

/-- **T2Edge236 hole fact.** -/
theorem holeLeaf_not_t2Edge236 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ T2Edge236 x F :=
  fun h => (leaf_of_t2Edge236 h).elim hF.2.2.2.1 hF.2.2.2.2.1

/-- **T2Edge236 twin hole fact.** -/
theorem holeLeaf_not_t2Edge236_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ T2Edge236 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => (leaf_of_t2Edge236_twin h).elim hF.2.2.2.1 hF.2.2.2.2.1

/-! ## `T2Edge012B2C`: any certificate on the `012` edge of `B2` -/

/-- **T2Edge012B2C:** as `T2Edge012B2` (some `β > 1`, at `t2e012 x β` the `B2` facets `0345, 046` in front and
`235, 236, 346` behind), with the `B2` rim `cB2 = 0.5.3.4.6.1` `RobUni` or carrying a strict apex certificate (the
`w6_15_0` twin: base `0-5`, apex `4`). -/
def T2Edge012B2C (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ beta : ℝ, 1 < beta ∧ 0 < ⟪F.N 3, t2e012 x beta⟫ ∧ 0 < ⟪F.N 4, t2e012 x beta⟫ ∧
    ⟪F.N 6, t2e012 x beta⟫ < 0 ∧ ⟪F.N 7, t2e012 x beta⟫ < 0 ∧ ⟪F.N 8, t2e012 x beta⟫ < 0 ∧
    (RobUni (fun i => ⟪x (TwoCone.cB2 i), t2e012 x beta⟫) ∨
      ApexCert (fun i => x (TwoCone.cB2 i)) (t2e012 x beta))

/-- **T2Edge012B2C (leaf):** `T2Edge012B2C x F` gives `Gen.LexAny F ∨ Gen.SplitAny F` (push `x₆ - x₁`). -/
theorem leaf_of_t2Edge012B2C {F : S0xFac 9 s0x_S24 x} (h : T2Edge012B2C x F) :
    Gen.LexAny F ∨ Gen.SplitAny F := by
  obtain ⟨beta, hb, h3, h4, h6, h7, h8, hC⟩ := h
  have hNr : ∀ t : Fin 9, ⟪F.N t, t2e012 x beta⟫ =
      (F.f t (x 0) - F.f t (x 1)) - beta * (F.f t (x 2) - F.f t (x 1)) := by
    intro t
    rw [t2e012, inner_sub_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
  refine leaf_of_wall_cert F cellB2 (v := x 6 - x 1) ?_ ?_ hC
  · intro t ht
    have ht' : t ∈ ({1, 3, 4} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    left
    rcases ht' with rfl | rfl | rfl
    · rw [hNr, F.zero 1 0 (by decide), F.zero 1 1 (by decide)]
      have hf := F.neg 1 2 (by decide)
      nlinarith
    · exact h3
    · exact h4
  · intro t ht
    have ht' : t ∉ ({1, 3, 4} : Finset (Fin 9)) := ht
    have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by revert t; decide
    rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
    · right
      rw [hNr, F.inner_sub, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
      exact ⟨by ring, by linarith [F.neg 0 6 (by decide)]⟩
    · left
      rw [hNr, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
      have hf := F.neg 2 1 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 5 1 (by decide), F.zero 5 2 (by decide)]
      linarith [F.neg 5 0 (by decide)]
    · exact Or.inl h6
    · exact Or.inl h7
    · exact Or.inl h8

/-- `T2Edge012B2` (three monotone corners) is the `RobUni` case of `T2Edge012B2C`. -/
theorem t2Edge012B2C_of_t2Edge012B2 {F : S0xFac 9 s0x_S24 x} (h : T2Edge012B2 x F) : T2Edge012B2C x F := by
  obtain ⟨beta, hb, h3, h4, h6, h7, h8, S, hS, hm⟩ := h
  exact ⟨beta, hb, h3, h4, h6, h7, h8, Or.inl (GenPlus.robUni_of_monoCorners (k := 6) (by norm_num) S hS hm)⟩

/-- **T2Edge012B2C, `π_24` twin.** -/
theorem leaf_of_t2Edge012B2C_twin {F : S0xFac 9 s0x_S24 x}
    (h : T2Edge012B2C (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F ∨ Gen.SplitAny F :=
  (leaf_of_t2Edge012B2C h).elim (fun hL => Or.inl (Sym.lexAny_sym F hL))
    (fun hS => Or.inr (Sym.splitAny24_sym F hS))

/-- **T2Edge012B2C hole fact.** -/
theorem holeLeaf_not_t2Edge012B2C {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ T2Edge012B2C x F :=
  fun h => (leaf_of_t2Edge012B2C h).elim hF.2.2.2.1 hF.2.2.2.2.1

/-- **T2Edge012B2C twin hole fact.** -/
theorem holeLeaf_not_t2Edge012B2C_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ T2Edge012B2C (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => (leaf_of_t2Edge012B2C_twin h).elim hF.2.2.2.1 hF.2.2.2.2.1

/-! ## Four cells outside `cells24` (the GAPT2OC pocket residue)

At `t1_1e-2_nb548_k0_e1e-02` (nopert229 `data/hard/holekit/gapt2oc_resid.lines`, a crit=0 neighbour of `w6_15_0`
at scale `1e-2`) no cell of `cells24` (nor a `π_24` twin or an antipode) carries a strict `RobUni` or `ApexCert`
view, and no Lean region lemma holds; genleaves finds Lex and Split views only in the four cells below (side `x`),
on their walls (nopert229 FACENORM24.md "== GAPT2OC ==").  The leaves are the generic `lexAny_of_cellRob` /
`splitAny_of_cellApex` (or `leaf_of_wall_cert` at a wall view). -/

/-- Rim of `cell0164`. -/
def r0164 : ZMod 4 → Fin 7 := ![0, 1, 6, 4]

/-- Cell `0.1.6.4` (up facets `016, 046`; vertices `2, 3, 5` hidden). -/
def cell0164 : Cell24 where
  k := 4
  hk := le_rfl
  r := r0164
  U := {1, 4}
  inj := by cell24_rim_inj
  cyc := by decide

/-- Rim of `cell01634`. -/
def r01634 : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 4]

/-- Cell `0.1.6.3.4` (up facets `016, 046, 346`; vertices `2, 5` hidden). -/
def cell01634 : Cell24 where
  k := 5
  hk := by norm_num
  r := r01634
  U := {1, 4, 8}
  inj := by cell24_rim_inj
  cyc := by decide

/-- Rim of `cell05326`. -/
def r05326 : ZMod 5 → Fin 7 := ![0, 5, 3, 2, 6]

/-- Cell `0.5.3.2.6` (up facets `0345, 046, 236, 346`; vertices `1, 4` hidden). -/
def cell05326 : Cell24 where
  k := 5
  hk := by norm_num
  r := r05326
  U := {3, 4, 7, 8}
  inj := by cell24_rim_inj
  cyc := by decide

/-- Rim of `cell046125`. -/
def r046125 : ZMod 6 → Fin 7 := ![0, 4, 6, 1, 2, 5]

/-- Cell `0.4.6.1.2.5` (up facets `0345, 126, 235, 236, 346`; vertex `3` hidden). -/
def cell046125 : Cell24 where
  k := 6
  hk := by norm_num
  r := r046125
  U := {3, 5, 6, 7, 8}
  inj := by cell24_rim_inj
  cyc := by decide

end Minimality.T24.Cell
