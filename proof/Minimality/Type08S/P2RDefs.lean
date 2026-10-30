module

public import Minimality.Type08S.P2QFinalI

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / PRDefs2 (R5a copy of R4a/PRDefs2 with the added P3Tpii leftover): definitions for the endgame of type 08 (the special-position residual).  No sorry.
Compile with `leanchk PRDefs.lean -o`.

**Mechanism (map.md §2).**  Theorem 24.1 in lexicographic form (`LexCell`): at a base view `u₀` and a tilt `v`,
a cycle `x` of the points whose first-order tilt tests (`TiltSign`, Lemma 8.0) all pass and whose lexicographic depths
`(⟪x i, u₀⟫, ⟪x i, v⟫)` are distinct with one peak.  It is HDN-blind (no hypothesis at `u₀` about horizontal double
normals) and robustness-free (ties at `u₀` are broken by the tilt).  Package R0 proves
`HasLexCell V → IsRupert V` from `isRupert_of_tilted_unimodal'`.

**Residual.**  `Resid08FinalJ` keeps, of `Resid08FinalI`, only the items that no package closes outright, each with
the conjunct `¬ HasLexCell` (no lex cell at any view).  Codimensions as plan2/map.md (`T`, `T'`, planar, a tie, an
HDN at a fixed view: 1 each); the `¬ HasLexCell` conjunct is an open condition (numerically empty, map.md §3).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

/-! ## The lexicographic cell certificate (generic) -/

/-- Strict lexicographic order on (depth at the base view, depth along the tilt). -/
def LexLt (p q : ℝ × ℝ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

open Classical in
/-- **Lexicographic cyclic unimodality**: the pairs `(z i, w i)` are distinct and exactly one is a lex peak. -/
noncomputable def LexUni {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) : Prop :=
  (∀ i j, z i = z j → w i = w j → i = j) ∧
    (Finset.univ.filter (fun i : ZMod k => LexLt (z (i - 1), w (i - 1)) (z i, w i) ∧
      LexLt (z (i + 1), w (i + 1)) (z i, w i))).card = 1

/-- **Lex cell** at the base view `u₀` with tilt `v`: the cycle `x` (points of `V`) passes every first-order tilt test
of Lemma 8.0 (convex, ccw, every other point strictly inside, for all small `ε > 0` at `u₀ + ε v`), and its
lexicographic depths are cyclically unimodal. -/
def LexCell (V : Finset ℝ³) (u₀ v : ℝ³) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) : Prop :=
  3 ≤ k ∧ (∀ i, x i ∈ V) ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v) ∧
    (∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v) ∧
    LexUni (fun i => ⟪x i, u₀⟫) (fun i => ⟪x i, v⟫)

/-- Some lex cell at the base view `u₀`. -/
def HasLexCellAt (V : Finset ℝ³) (u₀ : ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (x : ZMod k → ℝ³) (v : ℝ³), LexCell V u₀ v x

/-- Some lex cell at some base view (numerically: at `ℓ`, at an edge direction `x - y` or at a face normal). -/
def HasLexCell (V : Finset ℝ³) : Prop := ∃ u₀ : ℝ³, u₀ ≠ 0 ∧ HasLexCellAt V u₀

namespace Type08Sp

/-- The seven points. -/
noncomputable abbrev V8 (a a' b b' c c' d : ℝ³) : Finset ℝ³ := insert d ({a, a', b, b', c, c'} : Finset ℝ³)

/-! ## Strata closed outright (packages R2–R5) -/

/-- Case B at `T` on N2's weak far triple (with `AngBig`: S4TB's (B1) and P1's L3, package R2; without: (B2)). -/
def StN2WS (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧ ¬ RobKb a a' b b' c c' d ∧ N2WST a' b b' c c' d

/-- `b'` in the plane of `Q_ac` with `α4 > 1` / `α4 < 1` (`b' = d + α4 (a - d) + γ4 (c - d)`). -/
def Al4Gt (a b' c d : ℝ³) : Prop := ∃ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) ∧ 1 < α4
def Al4Lt (a b' c d : ℝ³) : Prop := ∃ α4 γ4 : ℝ, b' = d + α4 • (a - d) + γ4 • (c - d) ∧ α4 < 1

/-- `α4 = 1` at `T'` (the `det` item of `S4TpG2`). -/
def Al4One (a b b' c d : ℝ³) : Prop := det3 (b' - a) (c - d) (b - d) = 0

/-- `T'`, level face of `Q_ac` (all `α4`; `α4 < 1` is the tree's `Tp_level_sep`). -/
def StLevTp (a b c' c d : ℝ³) : Prop := IsT' a b c' d ∧ LevelQac a b c d

/-- `T'`, `QacTop` through the tie `D_a = D_d` (tpq's P3), off the level face. -/
def StP3Tp (a b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧ ⟪a, b - d⟫ = ⟪d, b - d⟫ ∧ ¬ LevelQac a b c d

/-! ## The items left (each with `¬ HasLexCell`) -/

/-- **At `T`**: P1's L2, case B's (B2) and (B3) (codim 4 each), the valve L5.  L1 is empty under `Norm08` (package
R1); case B's (B1) and P1's L3 close (N2's weak far triple with `AngBig`: package R2); P1's L4 lands in (B2), (B3) or
the tree's `cellXba2_rupert`. -/
def S4TR (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧
    ((TouchT b b' c c' d ∧ ⟪c, b - d⟫ < ⟪b, b - d⟫ ∧ ¬ AngBig a b b' c d ∧
        ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d)) ∨
     -- case B's (B2): N2's weak far triple with `∠q + ∠q' ≤ π` and an HDN of `K_2` (codim 4)
     (¬ RobKb a a' b b' c c' d ∧ N2WST a' b b' c c' d ∧ ¬ AngBig a b b' c d ∧
        ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d)) ∨
     (¬ RobKb a a' b b' c c' d ∧ RobXba a' b b' c' d ∧ ¬ AngBig a b b' c d ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫ ∧
        ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d) ∧ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d)) ∨
     -- P1's valve L5 (level face of `Q_ac` at `T`, HDN of `R1`): never produced by the tree's route (`close_T_sig4`
     -- uses `close_hdn_pers_KbT`, which is Rupert outright); kept because `S4T'` contains it.  Package W removes it.
     (LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)))

/-- **R4 leftover** (`α4 = 1` at `T'` with `QacTop`, `0 ≤ C := ⟪c - d, b - d⟫`, i.e. case (ii) of R4a/HANDOFF.md; includes the
level face `C = 0`).  Carries the `X_2a`-HDN and `¬ CaseATp` conjuncts of the branch of `S4TpG2` it comes from, so that it
lands in `S4TpG2` (`TpA1ii_imp`). -/
def TpA1ii (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧ Al4One a b b' c d ∧ 0 ≤ ⟪c - d, b - d⟫ ∧
    ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧ ¬ CaseATp a b b' c d

/-- **R5 leftover**: tpq's P3 tie at `T'` (`D_a = D_d`, `QacTop`, off the level face, `α4 ≠ 1`) with `0 ≤ ⟪c - d, b - d⟫`.
Off the level face `QacTop` then forces `⟪c-d,b-d⟫ > 0` and `γ4 = 1` (the maximum is attained by the pair `(c, b')`).  Carries
`X_2a`-HDN, `TpHDN2` (the `Al4One` alternative of `S4TpG2` is excluded by `¬ Al4One`) and `¬ CaseATp`, so that it lands in
`S4TpG2` (`P3Tpii_imp`).  Codim 5: `T'`, the tie `D_a = D_d`, `γ4 = 1`, two HDNs. -/
def P3Tpii (a a' b b' c c' d : ℝ³) : Prop :=
  StP3Tp a b b' c c' d ∧ ¬ Al4One a b b' c d ∧ 0 ≤ ⟪c - d, b - d⟫ ∧
    ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧ TpHDN2 a b b' c c' d ∧ ¬ CaseATp a b b' c d

/-- **At `T'`** (codim 4: `T'`, the tie `D_c = D_b'` (tpq's P1), `α4 < 1`, an HDN of `X_2a`, a second HDN). -/
def S4TpR (a a' b b' c c' d : ℝ³) : Prop :=
  IsT' a b c' d ∧ QacTop a b b' c d ∧ ⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ¬ LevelQac a b c d ∧ Al4Lt a b' c d ∧
    ¬ NoHDNAt ({d, a, b', c} : Finset ℝ³) (b - d) ∧ TpHDN2 a b b' c c' d ∧ ¬ CaseATp a b b' c d

/-- The residual in the labelling of `N` (J). -/
def ResNJ {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) : Prop :=
  ResNC' N ∧ (S4TR a a' b b' c c' d ∨ S4TpR a a' b b' c c' d ∨ TpA1ii a a' b b' c c' d ∨
    P3Tpii a a' b b' c c' d) ∧ ¬ HasLexCell (V8 a a' b b' c c' d)

def ResidNJ (a a' b b' c c' d : ℝ³) : Prop := ∃ N : Norm08 a a' b b' c c' d, ResNJ N

/-- **`Resid08FinalJ`**: the planar items keep `ResidP6` (codim 3; `LeftTT`, `κ_a = 0 ∧ ParEnd`) with
`¬ HasLexCell`; the non-planar items are `S4TR ∨ S4TpR ∨ TpA1ii ∨ P3Tpii` with `¬ HasLexCell`. -/
def Resid08FinalJ (a a' b b' c c' d : ℝ³) : Prop :=
  ((PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ ResidP6 a a' b b' c c' d ∧
      ¬ HasLexCell (V8 a a' b b' c c' d)) ∨
  ResidNJ a a' b b' c c' d ∨ ResidNJ b b' a a' c c' d ∨ ResidNJ a a' c c' b b' d ∨
  ResidNJ c c' a a' b b' d ∨ ResidNJ b b' c c' a a' d ∨ ResidNJ c c' b b' a a' d

/-! ## `J ⊆ I` (proved) -/

theorem S4TR_imp {a a' b b' c c' d : ℝ³} (h : S4TR a a' b b' c c' d) : S4T2 a a' b b' c c' d := by
  obtain ⟨hT, ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩⟩ := h
  · exact Or.inl ⟨hT, Or.inr (Or.inl ⟨h1, h3, h4⟩)⟩
  · exact Or.inr ⟨hT, h1, Or.inr (Or.inl ⟨h2, h3, h4⟩)⟩
  · exact Or.inr ⟨hT, h1, Or.inr (Or.inr ⟨h2, h3, h4, h5, h6⟩)⟩
  · exact Or.inl ⟨hT, Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))⟩

theorem S4TpR_imp {a a' b b' c c' d : ℝ³} (h : S4TpR a a' b b' c c' d) : S4TpG2 a a' b b' c c' d := by
  obtain ⟨hT', hq, -, -, -, hX, h2, hA⟩ := h
  exact ⟨hT', hq, Or.inr ⟨hX, Or.inl h2, hA⟩⟩

theorem TpA1ii_imp {a a' b b' c c' d : ℝ³} (h : TpA1ii a a' b b' c c' d) : S4TpG2 a a' b b' c c' d := by
  obtain ⟨hT', hq, h1, -, hX, hA⟩ := h
  exact ⟨hT', hq, Or.inr ⟨hX, Or.inr h1, hA⟩⟩

theorem P3Tpii_imp {a a' b b' c c' d : ℝ³} (h : P3Tpii a a' b b' c c' d) : S4TpG2 a a' b b' c c' d := by
  obtain ⟨⟨hT', hq, -, -⟩, -, -, hX, h2, hA⟩ := h
  exact ⟨hT', hq, Or.inr ⟨hX, Or.inl h2, hA⟩⟩

theorem resid08FinalJ_imp_I {a a' b b' c c' d : ℝ³} (h : Resid08FinalJ a a' b b' c c' d) :
    Resid08FinalI a a' b b' c c' d := by
  have g : ∀ {p p' q q' r r' : ℝ³}, ResidNJ p p' q q' r r' d → ResidNH p p' q q' r r' d :=
    fun ⟨N, h1, h2, _⟩ => ⟨N, h1, h2.imp S4TR_imp (fun h => h.elim S4TpR_imp (fun h => h.elim TpA1ii_imp P3Tpii_imp))⟩
  rcases h with ⟨hp, hr, -⟩ | h | h | h | h | h | h
  · exact Or.inl ⟨hp, hr⟩
  · exact Or.inr (Or.inl (g h))
  · exact Or.inr (Or.inr (Or.inl (g h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (g h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (g h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (g h))))))

end Type08Sp
end Minimality
