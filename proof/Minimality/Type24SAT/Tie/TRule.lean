module

public import Minimality.Type24SAT.Tie.TSec
public import Minimality.Type24SAT.Tie.TPar

@[expose] public section

/-!
# L24T, T6: the tie rule (family 23), the `ty` / `tfail` defining rows (38, 39), and family 36 on `rhoW`

The leaf of `(t, f, sd)`: `u = wf = N_t x D_f`, tie-break `d = sigma dplus`, tilt `w = tau N_t`
(`tau = +1` iff `t` is up in the pattern).  The state literals of a tie rule give the lex facings `LP3` of every
facet (`tie_hfac`; the zero facet `zs` is antiparallel to `t` by T5's `zero_facet_antipar`), the failure literal
gives `RobUniL` along the rim (`robUniL_of_altT`), and `s0x_lex2_rupert` (Type21SAT/Lex2) makes the shape Rupert.
So a checked tie rule holds under `rhoW (geoF F)` of any shape that is not Rupert (`tieOK_sound`); under `Z0`
it holds by its guard literal.  The prefix of `tie_core` up to the facings and the cycle facts is `tie_ctx` (on the
context literals `tieCtxLits`: state and `Z0`, no `tfail`), for the tie split rule (SSplit, family 40 kind 1).

The `lineS` functional of `(t, s)` is read from the table `lsTab` (the vmap's `LS` lines), checked
once against T2's `lsOK` (`lsT_ok`), so the checkers need no `LS` data.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset

open Minimality.T24.SAT (s0x_S24)

namespace Minimality.H24T.SAT
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.H29.SAT

/-! ### The `lineS` table -/

/-- `lsTab[t][s] = (view, k)`: `lineS(t,s,x) = k T(view,x)` (the vmap's `LS` lines; diagonal unused). -/
def lsTab : List (List (Nat × Int)) := [
  [(0, 0), (0, -1), (1, 1), (21, 1), (22, 1), (6, -1), (23, 1), (24, 1), (25, 1)],
  [(0, 1), (0, 0), (26, 1), (27, 1), (5, -1), (10, 1), (28, 1), (29, 1), (30, 1)],
  [(1, -1), (26, -1), (0, 0), (4, 1), (31, 1), (32, 1), (13, -1), (33, 1), (34, 1)],
  [(21, -1), (27, -1), (4, -1), (0, 0), (3, 1), (35, 1), (16, 1), (36, 1), (15, -1)],
  [(22, -1), (5, 1), (31, -1), (3, -1), (0, 0), (37, 1), (38, 1), (39, 1), (19, -1)],
  [(6, 1), (10, -1), (32, -1), (35, -1), (37, -1), (0, 0), (40, 1), (14, 1), (41, 1)],
  [(23, -1), (28, -1), (13, 1), (16, -1), (38, -1), (40, -1), (0, 0), (11, -1), (42, 1)],
  [(24, -1), (29, -1), (33, -1), (36, -1), (39, -1), (14, -1), (11, 1), (0, 0), (17, 1)],
  [(25, -1), (30, -1), (34, -1), (15, 1), (19, 1), (41, -1), (42, -1), (17, -1), (0, 0)]
]

/-- The `LS` line `(view, k)` of the pair `(t, s)`. -/
def lsT (t s : Nat) : Nat × Int := (lsTab.getD t []).getD s (0, 0)

/-- Every off-diagonal entry of the table passes T2's check. -/
theorem lsT_ok : ∀ t < 9, ∀ s < 9, t ≠ s → lsOK t s (lsT t s).1 (lsT t s).2 = true := by decide +kernel

/-- The facing sign `Fp(s)` of the leaf `(t, f, sd)` with the table's `lineS`. -/
def FpT (t f sd s : Nat) : S3W := FpW t f sd (lsT t s).1 (lsT t s).2 s

/-- `Fp(s)` is the lex sign of `(-L(s,f), sigma Ktie(s))`. -/
theorem FpT_lex {g : Geo} (hG : GeoOK g) {t s f : Nat} (ht : t < 9) (hs : s < 9) (hts : t ≠ s) (hf : f < 21)
    (sd : Nat) : LexSg (rhoW g) (FpT t f sd s) (-Ls g t s f) (sdR sd * Ktie g t f s) :=
  FpW_lex hG (lsT_ok t ht s hs hts) hf sd

/-! ### Small facts -/

theorem lp3_of_lp {a b c : ℝ} (h : h21b_LP a b) : LP3 a b c := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Or.inl h2⟩

theorem lp3_of_zero {a b c : ℝ} (ha : a = 0) (hb : b = 0) (hc : 0 < c) : LP3 a b c :=
  Or.inr ⟨ha, Or.inr ⟨hb, hc⟩⟩

theorem sdR_ne (sd : Nat) : sdR sd ≠ 0 := by unfold sdR; split_ifs <;> norm_num

theorem sdR_pm (sd : Nat) : sdR sd = 1 ∨ sdR sd = -1 := by unfold sdR; split_ifs <;> simp

/-- The literals of `cl` that `s` asks for are all false when `cl` does not hold. -/
theorem false_of_covers {ρ : W → Bool} (hP : ProperW ρ) {cl s : List LitW} (hc : coversW cl s = true)
    (hn : ¬ HoldsW ρ cl) : ∀ l ∈ s, evalW ρ l = false := by
  intro l hl
  by_contra h'
  exact hn (HoldsW.of_covers hP hc ⟨l, hl, by simpa using h'⟩)

/-- The tilt sign `tau`: `+1` iff `t` is up in the pattern. -/
def tauR (pp t : Nat) : ℝ := if pp.testBit t then 1 else -1

/-! ### The tie rule clause -/

/-- The state literals of facet `s` (none for `t`; both literals of `Fp(s)` for the zero facet `zs1 - 1`). -/
def stLits (t f sd pp zs1 s : Nat) : List LitW :=
  if s = t then []
  else if s + 1 = zs1 then [(FpT t f sd s).1, (FpT t f sd s).2]
  else if pp.testBit s then [(FpT t f sd s).1.neg] else [(FpT t f sd s).2.neg]

/-- The context literals of the tie leaf `(t, f, sd, pp, zs1)`: the state of every facet and the guard `Z0(t,f)`, no failure
literal.  Shared by the tie rule (23) and the tie split rule (40, kind 1), as `ctxLits` of the menu rules (Rule2). -/
def tieCtxLits (t f sd pp zs1 : Nat) : List LitW :=
  ((List.range 9).flatMap fun s => stLits t f sd pp zs1 s) ++ [Z0L t f]

/-- The clause of the tie rule `(t, f, sd, pp, zs1)` (`zs1 = zs + 1`, `0` for no zero facet), with the cycle `cyc` of
its failure variable: the state, the guard `Z0(t,f)`, and `tfail` if the rim has more than three vertices. -/
def tieLits (t f sd pp zs1 : Nat) (cyc : List Nat) : List LitW :=
  tieCtxLits t f sd pp zs1 ++
  (if 3 < (patCyc.getD pp []).length then [(true, W.tfail t f sd cyc)] else [])

/-- The cycle of the clause's failure variable (first `tfail t f sd _` literal). -/
def tfailOf (cl : List LitW) (t f sd : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (true, .tfail t' f' sd' c) => if t' == t && f' == f && sd' == sd then some c else none
    | _ => none).getD []

/-- The parameter conditions of a tie rule: with a zero facet, it is not `t` and has the other sign than `t`. -/
def tieParOK (t f sd pp zs1 : Nat) : Prop :=
  t < 9 ∧ f < 21 ∧ (sd = 0 ∨ sd = 1) ∧
    (zs1 = 0 ∨ (zs1 ≤ 9 ∧ zs1 ≠ t + 1 ∧ pp.testBit t ≠ pp.testBit (zs1 - 1)))

instance (t f sd pp zs1 : Nat) : Decidable (tieParOK t f sd pp zs1) := by unfold tieParOK; infer_instance

/-- **The check of a tie rule row** (tag `23 t f sd pp mask zs fv`, here `zs1 = zs + 1`; `mask` and `fv` are not
needed: the failure variable is read off the clause). -/
def tieOK (t f sd pp zs1 : Nat) (cl : List LitW) : Bool :=
  let L := patCyc.getD pp []
  let cyc := tfailOf cl t f sd
  decide (tieParOK t f sd pp zs1) && cycChk pp L && (L.length == 3 || altChk L cyc) &&
    coversW cl (tieLits t f sd pp zs1 cyc)

theorem mem_tieCtx_st {t f sd pp zs1 s : Nat} {l : LitW} (hs : s < 9)
    (hl : l ∈ stLits t f sd pp zs1 s) : l ∈ tieCtxLits t f sd pp zs1 := by
  unfold tieCtxLits
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs, hl⟩)

theorem mem_tieCtx_z0 {t f sd pp zs1 : Nat} : Z0L t f ∈ tieCtxLits t f sd pp zs1 := by
  unfold tieCtxLits
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_tieLits_ctx {t f sd pp zs1 : Nat} {cyc : List Nat} {l : LitW} (hl : l ∈ tieCtxLits t f sd pp zs1) :
    l ∈ tieLits t f sd pp zs1 cyc := by
  unfold tieLits
  exact List.mem_append_left _ hl

theorem mem_tieLits_fail {t f sd pp zs1 : Nat} {cyc : List Nat} (h : 3 < (patCyc.getD pp []).length) :
    ((true, W.tfail t f sd cyc) : LitW) ∈ tieLits t f sd pp zs1 cyc := by
  unfold tieLits
  rw [ite_eq_left h]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-! ### The facings at the tie leaf -/

/-- **`tie_hfac`.**  Off `Z0`, all state literals false give the lex facings `LP3 (N.u, N.d, N.w)` of every facet at
`u = wf`, `d = sigma dplus`, `w = tau N_t`: `t` by the tilt, a strict facet by `Fp`, the zero facet `zs` because it is
antiparallel to `t` (T5) and has the opposite sign in the pattern. -/
theorem tie_hfac {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hG : GeoOK (geoF F)) {t f sd pp zs1 : Nat}
    (hp : tieParOK t f sd pp zs1) (hZ : ¬ Z0 (geoF F) t f)
    (hno : ∀ l ∈ tieCtxLits t f sd pp zs1, evalW (rhoW (geoF F)) l = false) (r : Fin 9) :
    (bits pp r = true → LP3 ⟪F.N r, wf (geoF F) t f⟫ ⟪F.N r, sdR sd • dplus (geoF F) t f⟫
        ⟪F.N r, tauR pp t • F.N ⟨t, hp.1⟩⟫) ∧
    (bits pp r = false → LP3 (-⟪F.N r, wf (geoF F) t f⟫) (-⟪F.N r, sdR sd • dplus (geoF F) t f⟫)
        (-⟪F.N r, tauR pp t • F.N ⟨t, hp.1⟩⟫)) := by
  obtain ⟨ht, hf, hsd, hzs⟩ := hp
  set g := geoF F with hg
  have eN : ∀ s : Fin 9, g.N s.val = F.N s := geoF_N F
  have ea : ⟪F.N r, wf g t f⟫ = -Ls g t r.val f := by rw [← eN r]; exact facing_wf g t r.val f
  have eb : ⟪F.N r, sdR sd • dplus g t f⟫ = sdR sd * Kk g t f r.val := by
    rw [real_inner_smul_right, ← eN r, real_inner_comm]; rfl
  have ec : ⟪F.N r, tauR pp t • F.N ⟨t, ht⟩⟫ = tauR pp t * ⟪F.N r, F.N ⟨t, ht⟩⟫ := real_inner_smul_right _ _ _
  have nn := nn24 F ⟨t, ht⟩
  by_cases hrt : r.val = t
  · have hr : r = ⟨t, ht⟩ := Fin.ext hrt
    subst hr
    have a0 : ⟪F.N ⟨t, ht⟩, wf g t f⟫ = 0 := by rw [← eN]; exact inner_N_wf g t f
    have b0 : ⟪F.N ⟨t, ht⟩, sdR sd • dplus g t f⟫ = 0 := by
      rw [real_inner_smul_right, ← eN]; simp [inner_N_dplus]
    constructor
    · intro hb
      have hb' : pp.testBit t = true := hb
      refine lp3_of_zero a0 b0 ?_
      rw [ec]; simp only [tauR, hb', ite_true, one_mul]; exact nn
    · intro hb
      have hb' : pp.testBit t = false := hb
      refine lp3_of_zero (by rw [a0]; ring) (by rw [b0]; ring) ?_
      rw [ec]; simp only [tauR, hb', Bool.false_eq_true, ite_false]; linarith
  · have hts : t ≠ r.val := fun e => hrt e.symm
    have hlex := FpT_lex hG ht r.isLt hts hf sd
    have hKt : Ktie g t f r.val = Kk g t f r.val := by simp [Ktie, hZ]
    rw [hKt] at hlex
    by_cases hz : r.val + 1 = zs1
    · -- the zero facet
      have hst : stLits t f sd pp zs1 r.val = [(FpT t f sd r.val).1, (FpT t f sd r.val).2] := by
        simp [stLits, hrt, hz]
      have a1 := hno (FpT t f sd r.val).1 (mem_tieCtx_st r.isLt (by rw [hst]; simp))
      have a2 := hno (FpT t f sd r.val).2 (mem_tieCtx_st r.isLt (by rw [hst]; simp))
      have n1 : ¬ h21b_LP (-Ls g t r.val f) (sdR sd * Kk g t f r.val) := fun h => by
        rw [hlex.1.mpr h] at a1; exact absurd a1 (by simp)
      have n2 : ¬ h21b_LP (-(-Ls g t r.val f)) (-(sdR sd * Kk g t f r.val)) := fun h => by
        rw [hlex.2.mpr h] at a2; exact absurd a2 (by simp)
      obtain ⟨h1, h2⟩ := lp_none n1 n2
      have hL : Ls g t r.val f = 0 := by linarith
      have hK : Kk g t f r.val = 0 := (mul_eq_zero.mp h2).resolve_left (sdR_ne sd)
      have hZ' : cross (F.N ⟨t, ht⟩) (g.dv f) ≠ 0 := by rw [← eN]; exact hZ
      have hne : (⟨t, ht⟩ : Fin 9) ≠ r := fun e => hrt (by rw [← e])
      have hLf : Lf (F.N ⟨t, ht⟩) (F.N r) (g.dv f) = 0 := by rw [← eN, ← eN]; exact hL
      have hKf : Kf (F.N ⟨t, ht⟩) (F.N r) (g.dv f) = 0 := by
        rw [← eN, ← eN]; unfold Kf; rw [← K_expand]; exact hK
      obtain ⟨ρ, hρ, hN⟩ := zero_facet_antipar F hZ' hne hLf hKf
      have a0 : ⟪F.N r, wf g t f⟫ = 0 := by rw [ea, hL]; ring
      have b0 : ⟪F.N r, sdR sd • dplus g t f⟫ = 0 := by rw [eb, hK]; ring
      have c0 : ⟪F.N r, tauR pp t • F.N ⟨t, ht⟩⟫ = tauR pp t * (ρ * ⟪F.N ⟨t, ht⟩, F.N ⟨t, ht⟩⟫) := by
        rw [ec, hN, real_inner_smul_left]
      have hbit : pp.testBit t ≠ pp.testBit r.val := by
        rcases hzs with h0 | ⟨_, _, hb⟩
        · omega
        · subst hz; simpa using hb
      have hm : 0 < -(ρ * ⟪F.N ⟨t, ht⟩, F.N ⟨t, ht⟩⟫) := by nlinarith
      constructor
      · intro hb
        have hb' : pp.testBit r.val = true := hb
        have ht' : pp.testBit t = false := by rw [hb'] at hbit; simpa using hbit
        refine lp3_of_zero a0 b0 ?_
        rw [c0]; simp only [tauR, ht', Bool.false_eq_true, ite_false]; linarith
      · intro hb
        have hb' : pp.testBit r.val = false := hb
        have ht' : pp.testBit t = true := by rw [hb'] at hbit; simpa using hbit
        refine lp3_of_zero (by rw [a0]; ring) (by rw [b0]; ring) ?_
        rw [c0]; simp only [tauR, ht', ite_true, one_mul]; linarith
    · -- a strict facet
      constructor
      · intro hb
        have hb' : pp.testBit r.val = true := hb
        have hst : stLits t f sd pp zs1 r.val = [(FpT t f sd r.val).1.neg] := by
          simp [stLits, hrt, hz, hb']
        have a1 := hno (FpT t f sd r.val).1.neg (mem_tieCtx_st r.isLt (by rw [hst]; simp))
        rw [evalW_neg] at a1
        have := hlex.1.mp (by simpa using a1)
        rw [ea, eb]; exact lp3_of_lp this
      · intro hb
        have hb' : pp.testBit r.val = false := hb
        have hst : stLits t f sd pp zs1 r.val = [(FpT t f sd r.val).2.neg] := by
          simp [stLits, hrt, hz, hb']
        have a1 := hno (FpT t f sd r.val).2.neg (mem_tieCtx_st r.isLt (by rw [hst]; simp))
        rw [evalW_neg] at a1
        have := hlex.2.mp (by simpa using a1)
        rw [ea, eb]; exact lp3_of_lp this

/-! ### The rim at the tie leaf -/

/-- If a matching alternation has the four lex inequalities, `tfail` is true (off `Z0`). -/
theorem rhoW_tfail_of (g : Geo) {t f sd : Nat} {cyc : List Nat} (hZ : ¬ Z0 g t f) {a : Nat × Nat × Nat × Nat}
    (ha : a ∈ alts cyc) {p1 p2 q1 q2 : Nat} (hm : Mt a p1 p2 q1 q2)
    (h11 : ¬ lexLtT g t f sd p1 q1) (h12 : ¬ lexLtT g t f sd p1 q2) (h21 : ¬ lexLtT g t f sd p2 q1)
    (h22 : ¬ lexLtT g t f sd p2 q2) : rhoW g (W.tfail t f sd cyc) = true := by
  rw [rhoW_tfail]
  simp only [hZ, decide_false, Bool.not_false, Bool.true_and, List.any_eq_true]
  refine ⟨a, ha, ?_⟩
  simp only [yT, decide_eq_true_eq]
  obtain ⟨h1, h2⟩ := hm
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    simp only [a1, a2, b1, b2] <;> tauto

/-- **`robUniL_of_altT`**: `tfail` false and `AltCover2` give `RobUniL` of the depths `<x, wf>` along the cycle
with the tie-break `<x, sigma dplus>`. -/
theorem robUniL_of_altT {k : ℕ} [NeZero k] (g : Geo) {x : Fin 7 → ℝ³} (hx : ∀ i : Fin 7, g.x i.val = x i)
    {t f sd : Nat} {c : ZMod k → Fin 7} {cyc : List Nat} (hA : AltCover2 c cyc) (hZ : ¬ Z0 g t f)
    (hf : rhoW g (W.tfail t f sd cyc) = false) :
    RobUniL (fun a : ZMod k => ⟪x (c a), wf g t f⟫) (fun a : ZMod k => ⟪x (c a), sdR sd • dplus g t f⟫) := by
  intro B b c' d' h0 h1 h2 h3 ⟨e1, e2, e3, e4⟩
  obtain ⟨a, ha, hm⟩ := hA B b (by omega) c' (by omega) d' h3 h0 h1 h2
  have key : ∀ p q : Fin 7, (⟪x q, wf g t f⟫ < ⟪x p, wf g t f⟫ ∨ (⟪x q, wf g t f⟫ = ⟪x p, wf g t f⟫ ∧
      ⟪x q, sdR sd • dplus g t f⟫ ≤ ⟪x p, sdR sd • dplus g t f⟫)) → ¬ lexLtT g t f sd p.val q.val := by
    intro p q hpq
    have z1 : ⟪wf g t f, g.x p.val - g.x q.val⟫ = ⟪x p, wf g t f⟫ - ⟪x q, wf g t f⟫ := by
      rw [hx, hx, inner_sub_right, real_inner_comm (x p), real_inner_comm (x q)]
    have z2 : sdR sd * ⟪dplus g t f, g.x p.val - g.x q.val⟫ =
        ⟪x p, sdR sd • dplus g t f⟫ - ⟪x q, sdR sd • dplus g t f⟫ := by
      rw [hx, hx, real_inner_smul_right, real_inner_smul_right, inner_sub_right, real_inner_comm (x p),
        real_inner_comm (x q)]; ring
    unfold lexLtT
    rw [z1, z2]
    rintro (h | ⟨h, h'⟩)
    · rcases hpq with h2 | ⟨h2, _⟩ <;> linarith
    · rcases hpq with h2 | ⟨h2, h3⟩ <;> linarith
  have := rhoW_tfail_of g hZ ha hm (key _ _ e1) (key _ _ e3) (key _ _ e2) (key _ _ e4)
  rw [hf] at this
  exact absurd this (by simp)

/-! ### Soundness of the tie rule -/

/-- **`tie_ctx`, the shared prefix of the tie leaves** (the tie rule 23 here, the tie split rule 40 kind 1 in SSplit):
all context literals false (state of every facet and the guard `Z0`) give the cycle facts of the pattern's silhouette,
`Z0` false (so `u = wf != 0`), and the lex facings `LP3` of every facet at `u = wf`, `d = sigma dplus`, `w = tau N_t`
(the `hfac` of `s0x_lex2_rupert` and `split_lex2_rupert`). -/
theorem tie_ctx {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hG : GeoOK (geoF F))
    {t f sd pp zs1 : Nat} (hp : tieParOK t f sd pp zs1)
    (hcyc : cycChk pp (patCyc.getD pp []) = true)
    (hno : ∀ l ∈ tieCtxLits t f sd pp zs1, evalW (rhoW (geoF F)) l = false) :
    ∃ _ : NeZero (patCyc.getD pp []).length, 3 ≤ (patCyc.getD pp []).length ∧
      Function.Injective (cOf (k := (patCyc.getD pp []).length) (patCyc.getD pp [])) ∧
      S0xCycOK s0x_S24 (cOf (k := (patCyc.getD pp []).length) (patCyc.getD pp [])) (bits pp) ∧
      ¬ Z0 (geoF F) t f ∧
      ∀ r : Fin 9,
        (bits pp r = true → LP3 ⟪F.N r, wf (geoF F) t f⟫ ⟪F.N r, sdR sd • dplus (geoF F) t f⟫
          ⟪F.N r, tauR pp t • F.N ⟨t, hp.1⟩⟫) ∧
        (bits pp r = false → LP3 (-⟪F.N r, wf (geoF F) t f⟫) (-⟪F.N r, sdR sd • dplus (geoF F) t f⟫)
          (-⟪F.N r, tauR pp t • F.N ⟨t, hp.1⟩⟫)) := by
  have hlen := cycChk_len hcyc
  haveI hne : NeZero (patCyc.getD pp []).length := ⟨by omega⟩
  obtain ⟨h3, hinj, hcycOK⟩ := cycFacts (k := (patCyc.getD pp []).length) rfl hcyc
  have hZ : ¬ Z0 (geoF F) t f := by
    intro hz
    have := hno _ mem_tieCtx_z0
    rw [(evalW_Z0L _ t f).mpr hz] at this
    exact absurd this (by simp)
  exact ⟨hne, h3, hinj, hcycOK, hZ, tie_hfac F hG hp hZ hno⟩

/-- **The core of the tie rule soundness**: all literals of the tie rule clause false gives a Rupert shape
(`tie_ctx`, the rim by `tfail`, then `s0x_lex2_rupert`). -/
theorem tie_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x) (hG : GeoOK (geoF F))
    {t f sd pp zs1 : Nat} {cyc : List Nat} (hp : tieParOK t f sd pp zs1)
    (hcyc : cycChk pp (patCyc.getD pp []) = true)
    (halt : ((patCyc.getD pp []).length == 3 || altChk (patCyc.getD pp []) cyc) = true)
    (hno : ∀ l ∈ tieLits t f sd pp zs1 cyc, evalW (rhoW (geoF F)) l = false) :
    IsRupert (univ.image x) := by
  obtain ⟨hne, h3, hinj, hcycOK, hZ, hfac⟩ :=
    tie_ctx F hG hp hcyc (fun l hl => hno l (mem_tieLits_ctx hl))
  have hune : wf (geoF F) t f ≠ 0 := hZ
  have hU : RobUniL (fun a : ZMod (patCyc.getD pp []).length => ⟪x (cOf (patCyc.getD pp []) a), wf (geoF F) t f⟫)
      (fun a => ⟪x (cOf (patCyc.getD pp []) a), sdR sd • dplus (geoF F) t f⟫) := by
    by_cases h3' : (patCyc.getD pp []).length = 3
    · intro B b c d h0 h1 h2 h3''; omega
    · have hf' : 3 < (patCyc.getD pp []).length := by omega
      have hrf : rhoW (geoF F) (W.tfail t f sd cyc) = false := by
        simpa [evalW] using hno _ (mem_tieLits_fail (zs1 := zs1) (t := t) (f := f) (sd := sd) (cyc := cyc) hf')
      have hk3 : ((patCyc.getD pp []).length == 3) = false := by simpa using h3'
      rw [hk3, Bool.false_or] at halt
      have hA : AltCover2 (cOf (k := (patCyc.getD pp []).length) (patCyc.getD pp [])) cyc := by
        refine altFacts rfl ?_ halt
        unfold cycChk at hcyc
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcyc
        exact fun v hv => hcyc.1.1.2 v hv
      exact robUniL_of_altT (geoF F) (geoF_x F) hA hZ hrf
  exact s0x_lex2_rupert F hx hinj h3 hcycOK hune hfac hU

/-- **A tie rule row that passes the check is true of the real data, if the shape is not Rupert.** -/
theorem tieOK_sound {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) {t f sd pp zs1 : Nat} {cl : List LitW}
    (h : tieOK t f sd pp zs1 cl = true) : HoldsW (rhoW (geoF F)) cl := by
  by_contra hn
  apply hNR
  unfold tieOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hcyc⟩, halt⟩, hcov⟩ := h
  exact tie_core F hx hG hp hcyc halt (false_of_covers (rhoW_proper _) hcov hn)

/-! ### Families 38 and 39: the defining rows of `ty` and `tfail` -/

/-- Off `Z0`, the second literal of `ordD(p,q)` ("lex negative") is true exactly when `lexLtT p q`. -/
theorem ordDW_neg_iff {g : Geo} {t f : Nat} (hv : g.dv f ≠ 0) (hZ : ¬ Z0 g t f) (sd : Nat) {p q : Nat}
    (hp : p < 7) (hq : q < 7) (hpq : p ≠ q) :
    evalW (rhoW g) (ordDW t f sd p q).2 = true ↔ lexLtT g t f sd p q := by
  have h := (ordDW_lex (t := t) hv sd hp hq hpq).2
  rw [h]
  have hG : Gv g t f = dplus g t f := by simp [Gv, hZ]
  rw [hG]
  have hR := inv_pos.mpr (Rff_pos (t := t) hv)
  unfold h21b_LP lexLtT
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by linarith, ?_⟩
      by_contra hc
      have : 0 ≤ (Rtie g t f f)⁻¹ * (sdR sd * ⟪dplus g t f, g.x p - g.x q⟫) := mul_nonneg hR.le (not_lt.mp hc)
      linarith
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨by linarith, ?_⟩
      have := mul_neg_of_pos_of_neg hR h2
      linarith

/-- The literal `-ordD(p,q).q` of a `ty` row: "the depth of `p` is not lex less than that of `q`". -/
def tyLit (t f sd p q : Nat) : LitW := (ordDW t f sd p q).2.neg

/-- The four defining rows `{-ty, l}` of `ty t f sd p1 p2 q1 q2`. -/
def tyRows (t f sd p1 p2 q1 q2 : Nat) : List (List LitW) :=
  [[(false, W.ty t f sd p1 p2 q1 q2), tyLit t f sd p1 q1], [(false, W.ty t f sd p1 p2 q1 q2), tyLit t f sd p1 q2],
   [(false, W.ty t f sd p1 p2 q1 q2), tyLit t f sd p2 q1], [(false, W.ty t f sd p1 p2 q1 q2), tyLit t f sd p2 q2]]

/-- The vertex conditions of an alternation `(p1, p2, q1, q2)`. -/
def altOK (p1 p2 q1 q2 : Nat) : Prop :=
  p1 < 7 ∧ p2 < 7 ∧ q1 < 7 ∧ q2 < 7 ∧ p1 ≠ q1 ∧ p1 ≠ q2 ∧ p2 ≠ q1 ∧ p2 ≠ q2

instance (p1 p2 q1 q2 : Nat) : Decidable (altOK p1 p2 q1 q2) := by unfold altOK; infer_instance

/-- **The check of a family 38 row** (tag `38 y t f sd p1 p2 q1 q2`; `y` must be the variable `ty t f sd p1 p2 q1 q2`,
which the coverage checks). -/
def chk38 (t f sd p1 p2 q1 q2 : Nat) (cl : List LitW) : Bool :=
  decide (f < 21 ∧ altOK p1 p2 q1 q2) && anyCovW cl (tyRows t f sd p1 p2 q1 q2)

theorem ty_row {g : Geo} (hG : GeoOK g) {t f sd p1 p2 q1 q2 p q : Nat} (hf : f < 21) (hp : p < 7) (hq : q < 7)
    (hpq : p ≠ q) (hsem : rhoW g (W.ty t f sd p1 p2 q1 q2) = true → ¬ lexLtT g t f sd p q) :
    HoldsW (rhoW g) [(false, W.ty t f sd p1 p2 q1 q2), tyLit t f sd p q] := by
  cases hy : rhoW g (W.ty t f sd p1 p2 q1 q2)
  · exact ⟨_, List.mem_cons_self .., by simp [evalW, hy]⟩
  · have hZ : ¬ Z0 g t f := fun hz => by rw [rhoW_ty_Z0 hz] at hy; exact absurd hy (by simp)
    have hn := hsem hy
    refine ⟨tyLit t f sd p q, by simp, ?_⟩
    unfold tyLit
    rw [evalW_neg]
    have : evalW (rhoW g) (ordDW t f sd p q).2 = false := by
      by_contra hc
      exact hn ((ordDW_neg_iff (dv_ne hG hf) hZ sd hp hq hpq).mp (by simpa using hc))
    rw [this]; rfl

/-- **Family 38 soundness.** -/
theorem fam38_sound {g : Geo} (hG : GeoOK g) {t f sd p1 p2 q1 q2 : Nat} {cl : List LitW}
    (h : chk38 t f sd p1 p2 q1 q2 cl = true) : HoldsW (rhoW g) cl := by
  unfold chk38 at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, a1, a2, a3, a4, n1, n2, n3, n4⟩, hcov⟩ := h
  refine anyCovW_holds (rhoW_proper g) hcov ?_
  have hy : rhoW g (W.ty t f sd p1 p2 q1 q2) = true →
      ¬ lexLtT g t f sd p1 q1 ∧ ¬ lexLtT g t f sd p1 q2 ∧ ¬ lexLtT g t f sd p2 q1 ∧ ¬ lexLtT g t f sd p2 q2 := by
    intro h; rw [rhoW_ty] at h
    simp only [Bool.and_eq_true, yT, decide_eq_true_eq] at h
    exact h.2
  intro s hs
  simp only [tyRows, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact ty_row hG hf a1 a3 n1 fun h => (hy h).1
  · exact ty_row hG hf a1 a4 n2 fun h => (hy h).2.1
  · exact ty_row hG hf a2 a3 n3 fun h => (hy h).2.2.1
  · exact ty_row hG hf a2 a4 n4 fun h => (hy h).2.2.2

/-- An alternation is dead when one of its four `ordD(p,q).q` literals is the constant true (the pair is `f`, lex
less by `Dp(f) = sigma`): the encoder gives it no `ty`. -/
def deadAlt (t f sd : Nat) (a : Nat × Nat × Nat × Nat) : Bool :=
  (ordDW t f sd a.1 a.2.2.1).2 == ltrueW || (ordDW t f sd a.1 a.2.2.2).2 == ltrueW ||
  (ordDW t f sd a.2.1 a.2.2.1).2 == ltrueW || (ordDW t f sd a.2.1 a.2.2.2).2 == ltrueW

/-- The big row `{-tfail, ty_1, .., ty_n}` over the live alternations of `c`. -/
def tfailRow (t f sd : Nat) (c : List Nat) : List LitW :=
  (false, W.tfail t f sd c) ::
    ((alts c).filter fun a => !deadAlt t f sd a).map fun a => (true, W.ty t f sd a.1 a.2.1 a.2.2.1 a.2.2.2)

/-- **The check of a family 39 row** (tag `39 v t f sd k : c`; `v` must be `tfail t f sd c`, checked by the coverage). -/
def chk39 (t f sd : Nat) (c : List Nat) (cl : List LitW) : Bool :=
  decide (f < 21) && (alts c).all (fun a => decide (altOK a.1 a.2.1 a.2.2.1 a.2.2.2)) &&
    coversW cl (tfailRow t f sd c)

theorem evalW_eq_ltrueW {g : Geo} {l : LitW} (h : (l == ltrueW) = true) : evalW (rhoW g) l = true := by
  have : l = ltrueW := by simpa using h
  subst this; exact evalW_ltrueW g

/-- **Family 39 soundness.** -/
theorem fam39_sound {g : Geo} (hG : GeoOK g) {t f sd : Nat} {c : List Nat} {cl : List LitW}
    (h : chk39 t f sd c cl = true) : HoldsW (rhoW g) cl := by
  unfold chk39 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hf, hA⟩, hcov⟩ := h
  refine HoldsW.of_covers (rhoW_proper g) hcov ?_
  cases hv : rhoW g (W.tfail t f sd c)
  · exact ⟨_, List.mem_cons_self .., by simp [evalW, hv]⟩
  · have hZ : ¬ Z0 g t f := fun hz => by rw [rhoW_tfail_Z0 hz] at hv; exact absurd hv (by simp)
    rw [rhoW_tfail] at hv
    simp only [hZ, decide_false, Bool.not_false, Bool.true_and, List.any_eq_true] at hv
    obtain ⟨a, ha, hy⟩ := hv
    have hy' := hy
    simp only [yT, decide_eq_true_eq] at hy'
    obtain ⟨b1, b2, b3, b4, n1, n2, n3, n4⟩ := hA a ha
    have hv' := dv_ne hG hf
    have hd : deadAlt t f sd a = false := by
      unfold deadAlt
      simp only [Bool.or_eq_false_iff]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (by_contra hc; simp only [Bool.not_eq_false] at hc)
      · exact hy'.1 ((ordDW_neg_iff hv' hZ sd b1 b3 n1).mp (evalW_eq_ltrueW hc))
      · exact hy'.2.1 ((ordDW_neg_iff hv' hZ sd b1 b4 n2).mp (evalW_eq_ltrueW hc))
      · exact hy'.2.2.1 ((ordDW_neg_iff hv' hZ sd b2 b3 n3).mp (evalW_eq_ltrueW hc))
      · exact hy'.2.2.2 ((ordDW_neg_iff hv' hZ sd b2 b4 n4).mp (evalW_eq_ltrueW hc))
    refine ⟨(true, W.ty t f sd a.1 a.2.1 a.2.2.1 a.2.2.2), ?_, ?_⟩
    · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp [hd]⟩, rfl⟩)
    · simp [evalW, rhoW_ty, hZ, hy]

/-! ### Family 36 on `rhoW` (glue of T5's `fam36_sound`) -/

/-- The literals of a family 36 row `36 t f sd kind s s2`. -/
def lits36 (t f sd kind s s2 : Nat) : List LitW :=
  [(FpT t f sd s).1, (FpT t f sd s).2] ++ (if kind = 1 then [(FpT t f sd s2).1, (FpT t f sd s2).2] else [])

/-- **The check of a family 36 row.** -/
def chk36 (t f sd kind s s2 : Nat) (cl : List LitW) : Bool :=
  decide (f < 21) && p36OK t kind s s2 && coversW cl (lits36 t f sd kind s s2)

/-- **Family 36 soundness on the real data** (`fam36_sound` of T5 with the literal values of `rhoW`). -/
theorem fam36_rhoW {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hG : GeoOK (geoF F)) {t f sd kind s s2 : Nat}
    {cl : List LitW} (h : chk36 t f sd kind s s2 cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold chk36 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hok⟩, hcov⟩ := h
  set g := geoF F with hg
  have ht : t < 9 := by
    simp only [p36OK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1
  let fp : Nat → Bool × Bool := fun r => (evalW (rhoW g) (FpT t f sd r).1, evalW (rhoW g) (FpT t f sd r).2)
  have hfp : ∀ r, r < 9 → r ≠ t → ∃ k : ℝ, KAsem (g.N t) (g.N r) (g.dv f) k ∧
      Lex2Sg (fp r).1 (fp r).2 (-Lf (g.N t) (g.N r) (g.dv f)) (sdR sd * k) := by
    intro r hr hrt
    refine ⟨Ktie g t f r, ⟨fun hz => ?_, fun hz => ?_⟩, FpT_lex hG ht hr (Ne.symm hrt) hf sd⟩
    · have : Z0 g t f := hz
      simp [Ktie, this]
    · have : ¬ Z0 g t f := hz
      simp only [Ktie, this, ite_false]; rw [K_expand]; rfl
  have hcl := fam36_sound F (sdR_pm sd) hok fp hfp
  refine HoldsW.of_covers (rhoW_proper g) hcov ?_
  simp only [cl36, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, fp] at hcl
  rcases hcl with (h1 | h1) | ⟨hk, h1 | h1⟩
  · exact ⟨_, by simp [lits36], h1⟩
  · exact ⟨_, by simp [lits36], h1⟩
  · exact ⟨_, by simp [lits36, hk], h1⟩
  · exact ⟨_, by simp [lits36, hk], h1⟩

end Minimality.H24T.SAT
