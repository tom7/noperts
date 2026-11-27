module

public import Minimality.Type24OffOB1Bs

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the e26 view on `s = 1` (job OSPEC12, nopert229 notes/OPENSPECIAL-STRATEGY.md)

The 3-level lex view `(x 2 - x 6, -N3, x 0 - x 4)` is a lex cell with rim `0 1 6 3 4` (`0345` up) or `0 1 6 3 5`
(`0345` down) once `126` and `236` (edge-on at level 1, decided at level 2 by `-N3`) are up and the rim is
`RobUniLex` (`lexAny_of_e26View`, mirror `lexAny_of_e26View_sym` = view `(x 6 - x 2, -N3, x 0 - x 5)`).  Facet signs:
`012 025 235` up and `016 046 346` down at level 1 (through `2` resp. `6`), `0345` by the sign of `f3(x 2) - f3(x 6)`
(down at level 2 on the S3 tie), all automatic.

On the branch `ResBs1` with the tie `TBs1` (`s = 1`, `⟪x 2 - x 6, e5⟫ = 0`) the whole face `0345` is edge-on in the
level-1 depth `⟪., x 2 - x 6⟫` along `e5` (`x 3 - x 4 = t e5`, `x 5 - x 0 = e5`) and flat at level 2, so the pairs
`3, 4` and `0, 5` are decided at level 3 by `⟪., x 0 - x 4⟫`.  The rim is `RobUniLex` from three inner-product signs
(`e26ViewOK_of`): `6` below `1` (`⟪x 6 - x 1, x 2 - x 6⟫ < 0`), the face below `0` (`⟪x 2 - x 6, e4⟫ < 0`) and the
acute face angle `0` (`0 < ⟪e4, e5⟫`); in both rims they give the facts `z2 < z1`, `z3 < z4 < z0`, `z3 < z0` of the
5-cycle lemma `robUniLex_five_e26`.  Not derived: `126`, `236` up (`⟪N5, N3⟫ < 0`, `⟪N7, N3⟫ < 0`) and the three signs.
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section E26
open Minimality.LexCell

/-- Rim `0 1 6 3 4` (facets `012 025 0345 126 235 236` up, `016 046 346` down). -/
def rimEA : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 4]
def UEA : Finset (Fin 9) := {0, 2, 3, 5, 6, 7}
def DnEA : Finset (Fin 9) := {1, 4, 8}
/-- Rim `0 1 6 3 5` (facets `012 025 126 235 236` up, `016 0345 046 346` down). -/
def rimEB : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
def UEB : Finset (Fin 9) := {0, 2, 5, 6, 7}
def DnEB : Finset (Fin 9) := {1, 3, 4, 8}

theorem rimEA_cyc : S0xCycUD s0x_S24 rimEA UEA DnEA := by decide
theorem rimEA_inj : Function.Injective rimEA := by decide
theorem rimEB_cyc : S0xCycUD s0x_S24 rimEB UEB DnEB := by decide
theorem rimEB_inj : Function.Injective rimEB := by decide

/-- Facet `t` is up in the e26 view `(x 2 - x 6, -N3, x 0 - x 4)`. -/
def E26Up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, x 2 - x 6⟫ ⟪F.N t, -F.N 3⟫ ⟪F.N t, x 0 - x 4⟫
/-- Facet `t` is down in the e26 view. -/
def E26Dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, x 2 - x 6⟫) (-⟪F.N t, -F.N 3⟫) (-⟪F.N t, x 0 - x 4⟫)

/-- The e26 view depth triple of a vertex. -/
noncomputable def e26P {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) : ℝ × ℝ × ℝ :=
  (⟪x v, x 2 - x 6⟫, ⟪x v, -F.N 3⟫, ⟪x v, x 0 - x 4⟫)

/-- Lex depth triples of a rim in the e26 view. -/
noncomputable def e26Z {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} (c : ZMod k → Fin 7) :
    ZMod k → ℝ × ℝ × ℝ :=
  fun i => e26P F (c i)

/-- **The e26 view condition**: `126` and `236` up, and `0345` up with the rim `0 1 6 3 4` `RobUniLex`, or `0345`
down with the rim `0 1 6 3 5` `RobUniLex` (the other facet signs are automatic). -/
def E26ViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  E26Up F 5 ∧ E26Up F 7 ∧ ((E26Up F 3 ∧ RobUniLex (e26Z F rimEA)) ∨ (E26Dn F 3 ∧ RobUniLex (e26Z F rimEB)))

/-- A facet through `2` but not `6` is up (level 1). -/
theorem e26_up_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h2 : (2 : Fin 7) ∈ s0x_S24 t)
    (h6 : (6 : Fin 7) ∉ s0x_S24 t) : E26Up F t := by
  left
  rw [F.inner_sub t 2 6, F.zero t 2 h2]
  linarith [F.neg t 6 h6]

/-- A facet through `6` but not `2` is down (level 1). -/
theorem e26_dn_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h6 : (6 : Fin 7) ∈ s0x_S24 t)
    (h2 : (2 : Fin 7) ∉ s0x_S24 t) : E26Dn F t := by
  left
  rw [F.inner_sub t 2 6, F.zero t 6 h6]
  linarith [F.neg t 2 h2]

/-- `0345` is up when `f3(x 6) < f3(x 2)` (level 1). -/
theorem e26_up3 (F : S0xFac 9 s0x_S24 x) (h : F.f 3 (x 6) < F.f 3 (x 2)) : E26Up F 3 := by
  left
  rw [F.inner_sub 3 2 6]; linarith

/-- `0345` is down when `f3(x 2) ≤ f3(x 6)` (level 1, or level 2 on the S3 tie: `|N3|² > 0`). -/
theorem e26_dn3 (F : S0xFac 9 s0x_S24 x) (h : F.f 3 (x 2) ≤ F.f 3 (x 6)) : E26Dn F 3 := by
  rw [E26Dn, F.inner_sub 3 2 6]
  rcases h.lt_or_eq with h | h
  · left; linarith
  · right
    refine ⟨by rw [h]; ring, Or.inl ?_⟩
    rw [inner_neg_right, neg_neg]; exact real_inner_self_pos.mpr (n3_ne_zero F)

/-- **The e26 view is a lex cell** (either rim). -/
theorem lexAny_of_e26View (F : S0xFac 9 s0x_S24 x) (h : E26ViewOK F) : Gen.LexAny F := by
  obtain ⟨h5, h7, ⟨h3, hR⟩ | ⟨h3, hR⟩⟩ := h
  · refine ⟨5, inferInstance, rimEA, UEA, DnEA, x 2 - x 6, -F.N 3, x 0 - x 4, by norm_num, rimEA_inj,
      rimEA_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UEA, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [e26_up_of_mem F 0 (by decide) (by decide), e26_up_of_mem F 2 (by decide) (by decide), h3, h5,
        e26_up_of_mem F 6 (by decide) (by decide), h7]
    · intro t ht
      simp only [DnEA, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [e26_dn_of_mem F 1 (by decide) (by decide), e26_dn_of_mem F 4 (by decide) (by decide),
        e26_dn_of_mem F 8 (by decide) (by decide)]
  · refine ⟨5, inferInstance, rimEB, UEB, DnEB, x 2 - x 6, -F.N 3, x 0 - x 4, by norm_num, rimEB_inj,
      rimEB_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UEB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [e26_up_of_mem F 0 (by decide) (by decide), e26_up_of_mem F 2 (by decide) (by decide), h5,
        e26_up_of_mem F 6 (by decide) (by decide), h7]
    · intro t ht
      simp only [DnEB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [e26_dn_of_mem F 1 (by decide) (by decide), h3, e26_dn_of_mem F 4 (by decide) (by decide),
        e26_dn_of_mem F 8 (by decide) (by decide)]

/-- **The mirror e26 view** (`π = (2 6)(4 5)`): the view `(x 6 - x 2, -N3, x 0 - x 5)` of `x`. -/
theorem lexAny_of_e26View_sym (F : S0xFac 9 s0x_S24 x) (h : E26ViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_e26View (Sym.sym24 F) h)

/-! ### The rim from three inner-product signs on `s = 1`, `TBs1` -/

/-- **A 5-cycle with `z2 < z1` and the chain `z3 < z4 < z0`, `z3 < z0` is `RobUniLex`** (every alternating
quadruple contains one of the four comparisons; `z0` and `z1` are the candidate peaks, `z2`, `z3` the valleys). -/
theorem robUniLex_five_e26 (z : ZMod 5 → ℝ × ℝ × ℝ) (h21 : LexLt3 (z 2) (z 1)) (h34 : LexLt3 (z 3) (z 4))
    (h40 : LexLt3 (z 4) (z 0)) (h30 : LexLt3 (z 3) (z 0)) : RobUniLex z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl]
  all_goals first
    | exact Or.inl ‹_›
    | exact Or.inr (Or.inl ‹_›)
    | exact Or.inr (Or.inr (Or.inl ‹_›))
    | exact Or.inr (Or.inr (Or.inr ‹_›))

/-- Level-1 strict comparison. -/
theorem lexLt3_of_fst {p q : ℝ × ℝ × ℝ} (h : p.1 < q.1) : LexLt3 p q := Or.inl (by linarith)

/-- Comparison decided at level 3. -/
theorem lexLt3_of_thd {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) (h3 : p.2.2 < q.2.2) :
    LexLt3 p q := Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

/-- The sign conditions of the e26 view on `s = 1`, `TBs1`: `126` and `236` up, `6` below `1` and the face below
`0` at level 1, and the acute face angle at `0`. -/
def E26Cond {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  E26Up F 5 ∧ E26Up F 7 ∧ ⟪x 6 - x 1, x 2 - x 6⟫ < 0 ∧ ⟪x 2 - x 6, x 4 - x 0⟫ < 0 ∧ 0 < ⟪x 4 - x 0, x 5 - x 0⟫

/-- **The e26 view from the sign conditions on `s = 1` and the tie `TBs1`** (`⟪x 2, e5⟫ = ⟪x 6, e5⟫`). -/
theorem e26ViewOK_of (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs : s = 1) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hT : Q45TieLocusBs1 x) (h : E26Cond F) :
    E26ViewOK F := by
  subst hs
  obtain ⟨h5, h7, h1, h2, hac⟩ := h
  have hT' : ⟪x 5 - x 0, x 2 - x 6⟫ = 0 := by
    unfold Q45TieLocusBs1 at hT
    rw [inner_sub_right, real_inner_comm, real_inner_comm (x 6)]; linarith
  have h34 : x 3 - x 4 = t • (x 5 - x 0) := by
    rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, hdec, one_smul]; abel
  -- level 1
  have l61 : ⟪x 6, x 2 - x 6⟫ < ⟪x 1, x 2 - x 6⟫ := by rw [inner_sub_left] at h1; linarith
  have l40 : ⟪x 4, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫ := by
    rw [real_inner_comm, inner_sub_left] at h2; linarith
  have l34 : ⟪x 3, x 2 - x 6⟫ = ⟪x 4, x 2 - x 6⟫ := by
    have : ⟪x 3 - x 4, x 2 - x 6⟫ = 0 := by rw [h34, inner_smul_left, hT']; simp
    rw [inner_sub_left] at this; linarith
  have l50 : ⟪x 5, x 2 - x 6⟫ = ⟪x 0, x 2 - x 6⟫ := by rw [inner_sub_left] at hT'; linarith
  -- level 2: the face `0345` is flat
  have f2 : ∀ v w : Fin 7, v ∈ s0x_S24 3 → w ∈ s0x_S24 3 → ⟪x v, -F.N 3⟫ = ⟪x w, -F.N 3⟫ := by
    intro v w hv hw
    have e := F.inner_sub 3 v w
    rw [F.zero 3 v hv, F.zero 3 w hw, real_inner_comm, inner_sub_left] at e
    rw [inner_neg_right, inner_neg_right]; linarith
  -- level 3
  have k34 : ⟪x 3, x 0 - x 4⟫ < ⟪x 4, x 0 - x 4⟫ := by
    have : ⟪x 3 - x 4, x 0 - x 4⟫ = -(t * ⟪x 4 - x 0, x 5 - x 0⟫) := by
      rw [h34, inner_smul_left, show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, real_inner_comm]
      simp
    rw [inner_sub_left] at this; nlinarith
  have k50 : ⟪x 5, x 0 - x 4⟫ < ⟪x 0, x 0 - x 4⟫ := by
    have : ⟪x 5 - x 0, x 0 - x 4⟫ = -⟪x 4 - x 0, x 5 - x 0⟫ := by
      rw [show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, real_inner_comm]
    rw [inner_sub_left] at this; linarith
  refine ⟨h5, h7, ?_⟩
  rcases lt_or_ge (F.f 3 (x 6)) (F.f 3 (x 2)) with h3 | h3
  · refine Or.inl ⟨e26_up3 F h3, ?_⟩
    exact robUniLex_five_e26 (e26Z F rimEA) (lexLt3_of_fst l61)
      (lexLt3_of_thd l34 (f2 3 4 (by decide) (by decide)) k34) (lexLt3_of_fst l40)
      (lexLt3_of_fst (by show ⟪x 3, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫; linarith))
  · refine Or.inr ⟨e26_dn3 F h3, ?_⟩
    exact robUniLex_five_e26 (e26Z F rimEB) (lexLt3_of_fst l61)
      (lexLt3_of_fst (by show ⟪x 3, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫; linarith))
      (lexLt3_of_thd l50 (f2 5 0 (by decide) (by decide)) k50)
      (lexLt3_of_fst (by show ⟪x 3, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫; linarith))

/-- **The mirror form** (the e26 view of `π24 x` on `t = 1` and the mirror tie `⟪x 6 - x 2, e4⟫ = 0`). -/
theorem e26ViewOK_sym_of (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (ht : t = 1) (hs0 : 0 < s)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hT : Q45TieLocusBs1 (x ∘ Sym.pi24))
    (h : E26Cond (Sym.sym24 F)) : E26ViewOK (Sym.sym24 F) := by
  refine e26ViewOK_of (Sym.sym24 F) (s := t) (t := s) ht hs0 ?_ hT h
  simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
  rw [hdec]; abel

/-! ### The residue after the e26 views -/

/-- `Q45ResSTD` where neither e26 view applies. -/
def Q45ResSTS {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTD F s t ∧ ¬ E26ViewOK F ∧ ¬ E26ViewOK (Sym.sym24 F)

/-- The branch-tagged residue after the e26 views. -/
def Q45ResWS {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTS F s t

/-- **The e26 views cut the residue**: a point of `Q45ResSTD` is `LexAny` or in `Q45ResSTS`. -/
theorem q45_resS_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : Q45ResSTD F s t) :
    Gen.LexAny F ∨ Q45ResSTS F s t := by
  by_cases hA : E26ViewOK F
  · exact Or.inl (lexAny_of_e26View F hA)
  by_cases hB : E26ViewOK (Sym.sym24 F)
  · exact Or.inl (lexAny_of_e26View_sym F hB)
  exact Or.inr ⟨h, hA, hB⟩

/-- **What is left on `s = 1`, `TBs1`**: a residue point there fails one of the e26 sign conditions (`e26ViewOK_of`);
mirror: on `t = 1` and the mirror tie, the mirror conditions fail. -/
theorem not_e26Cond_of_resS (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : Q45ResSTS F s t) :
    (s = 1 → Q45TieLocusBs1 x → ¬ E26Cond F) ∧
      (t = 1 → Q45TieLocusBs1 (x ∘ Sym.pi24) → ¬ E26Cond (Sym.sym24 F)) :=
  ⟨fun hs hT hC => h.2.1 (e26ViewOK_of F hs ht0 hdec hT hC),
    fun ht hT hC => h.2.2 (e26ViewOK_sym_of F ht hs0 hdec hT hC)⟩

/-- `Q45ResWS ⊆ Q45ResWD`. -/
theorem q45ResWD_of_S {F : S0xFac 9 s0x_S24 x} (h : Q45ResWS F) : Q45ResWD F := by
  obtain ⟨s, t, hs, ht, hst, hd, h⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h.1⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWS`. -/
theorem q45_resS (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWS F := by
  rcases q45_resD F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resS_local F h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the e26 views, Rupert form**: `OpenSpecialD` with `Q45ResWS` in place of
`Q45ResWD`. -/
def OpenSpecialS : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWS F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialD → OpenSpecialS` (`q45ResWD_of_S`). -/
theorem openSpecialS_of_openSpecialD (h : OpenSpecialD) : OpenSpecialS :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWD_of_S hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialS`. -/
theorem hole24_offOB1_S {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialS) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resS F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the e26 views) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_S (h1 : OpenOB1) (h2 : OpenSpecialS) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_S hH hO h2

end E26

end Minimality.T24.OSpec
