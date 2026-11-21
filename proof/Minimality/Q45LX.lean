module

public import Minimality.Q45
public import Minimality.RDispatch24
public import Minimality.EdgeViewLink
public import Minimality.LexCell
public import Minimality.RCell24

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.T24.Q45
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.EdgeViewLink
open Minimality.LexCell Minimality.T24.RCell

lemma zero_pair {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {t : Fin 9} {i j : Fin 7}
    (hi : i ∈ s0x_S24 t) (hj : j ∈ s0x_S24 t) : ⟪F.N t, x i - x j⟫ = 0 := by
  rw [F.inner_sub, F.zero t i hi, F.zero t j hj]; simp

/-- Hypotheses of a lex corner leaf (all of them are conditions on the lex point
`b + ε d1 + ε² d2`, `d1 = α p + β q`, `d2 = γ p + δ q`): the facets `U` (resp. `Dn`) other than the
two edge-on facets `a`, `S` are lex positive (resp. negative), the edge-on ones are decided by
`d1`, `d2`, and the rim depths are `RobUniLex`. -/
def LxCellHyp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (a S : Fin 9)
    (b p q : ℝ³) (U Dn : Finset (Fin 9)) (c : ZMod k → Fin 7) (α β γ δ : ℝ) : Prop :=
  (∀ t ∈ U, t ≠ a → t ≠ S →
      LexPos3 ⟪F.N t, b⟫ ⟪F.N t, α • p + β • q⟫ ⟪F.N t, γ • p + δ • q⟫) ∧
  (∀ t ∈ Dn, t ≠ a → t ≠ S →
      LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, α • p + β • q⟫) (-⟪F.N t, γ • p + δ • q⟫)) ∧
  (a ∈ U → LexPos3 0 (β * ⟪F.N a, q⟫) (δ * ⟪F.N a, q⟫)) ∧
  (a ∈ Dn → LexPos3 0 (-(β * ⟪F.N a, q⟫)) (-(δ * ⟪F.N a, q⟫))) ∧
  (S ∈ U → LexPos3 0 (α * ⟪F.N S, p⟫) (γ * ⟪F.N S, p⟫)) ∧
  (S ∈ Dn → LexPos3 0 (-(α * ⟪F.N S, p⟫)) (-(γ * ⟪F.N S, p⟫))) ∧
  RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), α • p + β • q⟫, ⟪x (c i), γ • p + δ • q⟫))

/-- Generic lex corner leaf packed into `LexAny F`. -/
theorem lx_corner_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    {c : ZMod k → Fin 7} (hc : Function.Injective c) {U Dn : Finset (Fin 9)}
    (hcyc : S0xCycUD s0x_S24 c U Dn) (a S : Fin 9) (b p q : ℝ³) (α β γ δ : ℝ)
    (hab : ⟪F.N a, b⟫ = 0) (hap : ⟪F.N a, p⟫ = 0)
    (hSb : ⟪F.N S, b⟫ = 0) (hSq : ⟪F.N S, q⟫ = 0)
    (H : LxCellHyp F a S b p q U Dn c α β γ δ) :
    LexAny F := by
  obtain ⟨hU1, hD1, haU, haD, hSU, hSD, hR⟩ := H
  have ha1 : ⟪F.N a, α • p + β • q⟫ = β * ⟪F.N a, q⟫ := by
    simp only [inner_add_right, inner_smul_right, hap]; ring
  have ha2 : ⟪F.N a, γ • p + δ • q⟫ = δ * ⟪F.N a, q⟫ := by
    simp only [inner_add_right, inner_smul_right, hap]; ring
  have hS1 : ⟪F.N S, α • p + β • q⟫ = α * ⟪F.N S, p⟫ := by
    simp only [inner_add_right, inner_smul_right, hSq]; ring
  have hS2 : ⟪F.N S, γ • p + δ • q⟫ = γ * ⟪F.N S, p⟫ := by
    simp only [inner_add_right, inner_smul_right, hSq]; ring
  refine ⟨k, inferInstance, c, U, Dn, b, α • p + β • q, γ • p + δ • q, hk, hc, hcyc, ?_, ?_, hR⟩
  · intro t ht
    by_cases h1 : t = a
    · subst h1; rw [hab, ha1, ha2]; exact haU ht
    by_cases h2 : t = S
    · subst h2; rw [hSb, hS1, hS2]; exact hSU ht
    exact hU1 t ht h1 h2
  · intro t ht
    by_cases h1 : t = a
    · subst h1; rw [hab, ha1, ha2]; simpa using haD ht
    by_cases h2 : t = S
    · subst h2; rw [hSb, hS1, hS2]; simpa using hSD ht
    exact hD1 t ht h1 h2

/-- Generic lex corner leaf: view `b` with two facets `a`, `S` edge-on, `p` a direction in the facet
`a`, `q` a direction in the facet `S`. -/
theorem lx_corner {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    {c : ZMod k → Fin 7} (hc : Function.Injective c) {U Dn : Finset (Fin 9)}
    (hcyc : S0xCycUD s0x_S24 c U Dn) (a S : Fin 9) (b p q : ℝ³) (α β γ δ : ℝ)
    (hab : ⟪F.N a, b⟫ = 0) (hap : ⟪F.N a, p⟫ = 0)
    (hSb : ⟪F.N S, b⟫ = 0) (hSq : ⟪F.N S, q⟫ = 0)
    (H : LxCellHyp F a S b p q U Dn c α β γ δ) :
    IsRupert (univ.image x) :=
  lexAny_isRupert F (lx_corner_lexAny F hk hc hcyc a S b p q α β γ δ hab hap hSb hSq H)

def lxr_e4_0526 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]

/-- Lex corner leaf `e4_0526` (corner view `x 4 - x 0`, edge-on facets 3, 4; rim 0526;
up facets {3, 4, 6, 7}, down facets {1, 2, 5}). -/
def Lx_e4_0526 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 4 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0)
    {3, 4, 6, 7} {1, 2, 5} lxr_e4_0526 α β γ δ

theorem q45_lx_e4_0526 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e4_0526 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 4 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e35_2346 : ZMod 4 → Fin 7 := ![2, 3, 4, 6]

/-- Lex corner leaf `e35_2346` (corner view `x 3 - x 5`, edge-on facets 3, 6; rim 2346;
up facets {7, 8}, down facets {3, 4, 5, 6}). -/
def Lx_e35_2346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 6 (x 3 - x 5) (x 4 - x 0) (x 2 - x 5)
    {7, 8} {3, 4, 5, 6} lxr_e35_2346 α β γ δ

theorem q45_lx_e35_2346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e35_2346 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 6 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e5_0264 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]

/-- Lex corner leaf `e5_0264` (corner view `x 5 - x 0`, edge-on facets 3, 2; rim 0264;
up facets {2, 3, 7, 8}, down facets {0, 4, 5}). -/
def Lx_e5_0264 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 2 (x 5 - x 0) (x 4 - x 0) (x 2 - x 0)
    {2, 3, 7, 8} {0, 4, 5} lxr_e5_0264 α β γ δ

theorem q45_lx_e5_0264 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e5_0264 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 2 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e34_2536 : ZMod 4 → Fin 7 := ![2, 5, 3, 6]

/-- Lex corner leaf `e34_2536` (corner view `x 3 - x 4`, edge-on facets 3, 8; rim 2536;
up facets {6, 7}, down facets {2, 3, 5, 8}). -/
def Lx_e34_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 8 (x 3 - x 4) (x 5 - x 0) (x 6 - x 4)
    {6, 7} {2, 3, 5, 8} lxr_e34_2536 α β γ δ

theorem q45_lx_e34_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e34_2536 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 8 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e4_2346 : ZMod 4 → Fin 7 := ![2, 3, 4, 6]

/-- Lex corner leaf `e4_2346` (corner view `x 4 - x 0`, edge-on facets 3, 4; rim 2346;
up facets {7, 8}, down facets {3, 4, 5, 6}). -/
def Lx_e4_2346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 4 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0)
    {7, 8} {3, 4, 5, 6} lxr_e4_2346 α β γ δ

theorem q45_lx_e4_2346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e4_2346 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 4 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e35_04625 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]

/-- Lex corner leaf `e35_04625` (corner view `x 3 - x 5`, edge-on facets 3, 6; rim 04625;
up facets {3, 6, 7, 8}, down facets {2, 4, 5}). -/
def Lx_e35_04625 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 6 (x 3 - x 5) (x 4 - x 0) (x 2 - x 5)
    {3, 6, 7, 8} {2, 4, 5} lxr_e35_04625 α β γ δ

theorem q45_lx_e35_04625 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e35_04625 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 6 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e5_12536 : ZMod 5 → Fin 7 := ![1, 2, 5, 3, 6]

/-- Lex corner leaf `e5_12536` (corner view `x 5 - x 0`, edge-on facets 3, 2; rim 12536;
up facets {5, 6, 7}, down facets {0, 1, 2, 3, 8}). -/
def Lx_e5_12536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 2 (x 5 - x 0) (x 4 - x 0) (x 2 - x 0)
    {5, 6, 7} {0, 1, 2, 3, 8} lxr_e5_12536 α β γ δ

theorem q45_lx_e5_12536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e5_12536 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 2 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e4_25346 : ZMod 5 → Fin 7 := ![2, 5, 3, 4, 6]

/-- Lex corner leaf `e4_25346` (corner view `x 4 - x 0`, edge-on facets 3, 4; rim 25346;
up facets {6, 7, 8}, down facets {2, 3, 4, 5}). -/
def Lx_e4_25346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 4 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0)
    {6, 7, 8} {2, 3, 4, 5} lxr_e4_25346 α β γ δ

theorem q45_lx_e4_25346 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e4_25346 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 4 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e34_0264 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]

/-- Lex corner leaf `e34_0264` (corner view `x 3 - x 4`, edge-on facets 3, 8; rim 0264;
up facets {2, 3, 7, 8}, down facets {0, 4, 5}). -/
def Lx_e34_0264 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 8 (x 3 - x 4) (x 5 - x 0) (x 6 - x 4)
    {2, 3, 7, 8} {0, 4, 5} lxr_e34_0264 α β γ δ

theorem q45_lx_e34_0264 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e34_0264 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 8 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e35_04326 : ZMod 5 → Fin 7 := ![0, 4, 3, 2, 6]

/-- Lex corner leaf `e35_04326` (corner view `x 3 - x 5`, edge-on facets 3, 6; rim 04326;
up facets {4, 7, 8}, down facets {1, 3, 5, 6}). -/
def Lx_e35_04326 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 6 (x 3 - x 5) (x 4 - x 0) (x 2 - x 5)
    {4, 7, 8} {1, 3, 5, 6} lxr_e35_04326 α β γ δ

theorem q45_lx_e35_04326 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e35_04326 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 6 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e34_04625 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]

/-- Lex corner leaf `e34_04625` (corner view `x 3 - x 4`, edge-on facets 3, 8; rim 04625;
up facets {3, 6, 7, 8}, down facets {2, 4, 5}). -/
def Lx_e34_04625 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 8 (x 3 - x 4) (x 5 - x 0) (x 6 - x 4)
    {3, 6, 7, 8} {2, 4, 5} lxr_e34_04625 α β γ δ

theorem q45_lx_e34_04625 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e34_04625 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 8 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

def lxr_e5_2536 : ZMod 4 → Fin 7 := ![2, 5, 3, 6]

/-- Lex corner leaf `e5_2536` (corner view `x 5 - x 0`, edge-on facets 3, 2; rim 2536;
up facets {6, 7}, down facets {2, 3, 5, 8}). -/
def Lx_e5_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ α β γ δ : ℝ, LxCellHyp F 3 2 (x 5 - x 0) (x 4 - x 0) (x 2 - x 0)
    {6, 7} {2, 3, 5, 8} lxr_e5_2536 α β γ δ

theorem q45_lx_e5_2536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : Lx_e5_2536 F) :
    IsRupert (univ.image x) := by
  obtain ⟨α, β, γ, δ, H⟩ := h
  exact lx_corner F (by norm_num) (by decide) (by decide) 3 2 _ _ _ α β γ δ
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
    (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

/-- The menu: any of the twelve lex corner leaves applies. -/
def LxMenu {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Lx_e4_0526 F ∨
  Lx_e35_2346 F ∨
  Lx_e5_0264 F ∨
  Lx_e34_2536 F ∨
  Lx_e4_2346 F ∨
  Lx_e35_04625 F ∨
  Lx_e5_12536 F ∨
  Lx_e4_25346 F ∨
  Lx_e34_0264 F ∨
  Lx_e35_04326 F ∨
  Lx_e34_04625 F ∨
  Lx_e5_2536 F

/-- Every leaf in `LxMenu` is an instance of `LexAny`. -/
theorem lxMenu_imp_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : LxMenu F) :
    LexAny F := by
  rcases h with ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ |
      ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ |
      ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩ | ⟨α, β, γ, δ, H⟩
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 4 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 6 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 2 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 8 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 4 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 6 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 2 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 4 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 8 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 6 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 8 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H
  · exact lx_corner_lexAny F (by norm_num) (by decide) (by decide) 3 2 _ _ _ α β γ δ
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide))
      (zero_pair F (by decide) (by decide)) (zero_pair F (by decide) (by decide)) H

theorem q45_lx_menu {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : LxMenu F) :
    IsRupert (univ.image x) :=
  lexAny_isRupert F (lxMenu_imp_lexAny F h)

/-- Residual of the cell-first Q45 dispatcher after `LexAny`. -/
def Q45Resid {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45Special' F ∧ ¬ LexAny F

/-- **Q45 dispatcher with `LexAny`**: `Q45Special'` is refined to `Q45Special' ∧ ¬ LexAny`. -/
theorem q45_half_cell2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hsign : Minimality.T24.Q45HalfPred F) :
    IsRupert (univ.image x) ∨ Q45Resid F := by
  rcases q45_half_cell F hsign with h | h
  · exact Or.inl h
  · by_cases hl : LexAny F
    · exact Or.inl (lexAny_isRupert F hl)
    · exact Or.inr ⟨h, hl⟩

end Minimality.T24.Q45
