module

public import Mathlib

@[expose] public section

/-!
# Lemma TQ (type 24, obtuse corner OB1), chart layer

Pure real algebra in the chart of the corner at vertex 1 (TQPROOF24.md, fourth pass and "Shape facts").
A view is `g = (g_a, g_b, g_c)`, the coordinates along the edges `x0 - x1`, `x2 - x1`, `x6 - x1`; chart
points of the lemmas have `g_a + g_b + g_c = 1`.  The six facets not through vertex 1 have normalized
chart normals (end rows: an end on the facet gives `1`, an end off it gives `< 1`):
`025 = (1, 1, p)`, `4350 = (1, m1, m2)`, `046 = (1, q, 1)`, `235 = (s0, 1, s2)`, `236 = (r, 1, 1)`,
`346 = (w0, w1, 1)`; the facets `012`, `016`, `126` are back exactly when `g_c`, `g_b`, `g_a > 0`.
`y3 = (a3, b3, c3)` lies on `235`, `236`, `4350`, `346`; `θ`, `θb`, `γ` are the levels of the lines
`L_236 = {g_a = θ}`, `L_046 = {g_b = θb}`, `L_025 = {g_c = γ}`.  `k1..k4` is the vertex-figure relation
V3 at vertex 3.  The region `R = 04325` has front set `{4350, 235}`, the cell `0234` front set
`{025, 4350, 235}`, the cell `0536` front set `{046, 4350, 346}`.

The metric enters through the Gram entries `Gij` of the three edges, `G t = h2 (1,1,1)` at the
orthocentre chart point `t`, and the values `(G g)_i`.
-/

set_option autoImplicit false

open Filter Topology

namespace Minimality.T24.TQ

/-- A linear form in chart coordinates. -/
def L3 (α β γ a b c : ℝ) : ℝ := α * a + β * b + γ * c

theorem L3_pert (α β γ a b c x y z ε : ℝ) :
    L3 α β γ (a + ε * x) (b + ε * y) (c + ε * z) = L3 α β γ a b c + ε * L3 α β γ x y z := by
  unfold L3; ring

/-- Eventual positivity of an affine function of `ε` near `0⁺`. -/
theorem ev_pos {A B : ℝ} (h : 0 < A ∨ (0 ≤ A ∧ 0 < B)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < A + ε * B := by
  rcases h with h | ⟨h0, h1⟩
  · have hc : Continuous fun ε : ℝ => A + ε * B := by fun_prop
    have := (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using h))
    exact this.filter_mono nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    nlinarith

theorem ev_neg {A B : ℝ} (h : A < 0 ∨ (A ≤ 0 ∧ B < 0)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), A + ε * B < 0 := by
  have := ev_pos (A := -A) (B := -B) (by
    rcases h with h | ⟨h0, h1⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩)
  filter_upwards [this] with ε hε
  linarith

theorem ev_L3_pos {α β γ a b c x y z : ℝ}
    (h : 0 < L3 α β γ a b c ∨ (0 ≤ L3 α β γ a b c ∧ 0 < L3 α β γ x y z)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < L3 α β γ (a + ε * x) (b + ε * y) (c + ε * z) := by
  filter_upwards [ev_pos h] with ε hε
  rwa [L3_pert]

theorem ev_L3_neg {α β γ a b c x y z : ℝ}
    (h : L3 α β γ a b c < 0 ∨ (L3 α β γ a b c ≤ 0 ∧ L3 α β γ x y z < 0)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), L3 α β γ (a + ε * x) (b + ε * y) (c + ε * z) < 0 := by
  filter_upwards [ev_neg h] with ε hε
  rwa [L3_pert]

/-- Segment form: from `A ≤ 0` at the start and `A1 < 0` at the end, negative just after the start. -/
theorem seg_neg {A A1 : ℝ} (h0 : A ≤ 0) (h1 : A1 < 0) : A < 0 ∨ (A ≤ 0 ∧ A1 - A < 0) := by
  rcases h0.lt_or_eq with h | h
  · exact Or.inl h
  · right; constructor <;> linarith

/-- Chart data of a type-24 shape at the corner 1, frame `04325` (see the module docstring). -/
structure Ch24 where
  p : ℝ
  q : ℝ
  r : ℝ
  m1 : ℝ
  m2 : ℝ
  s0 : ℝ
  s2 : ℝ
  w0 : ℝ
  w1 : ℝ
  a3 : ℝ
  b3 : ℝ
  c3 : ℝ
  th : ℝ
  thb : ℝ
  ga : ℝ
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ
  k4 : ℝ
  hp : p < 1
  hq : q < 1
  hr : r < 1
  hm1 : m1 < 1
  hm2 : m2 < 1
  hs0 : s0 < 1
  hs2 : s2 < 1
  hw1 : w1 < 1
  hth : th * (1 - r) = 1
  hthb : thb * (1 - q) = 1
  hga : ga * (1 - p) = 1
  ha3 : 0 < a3
  hb3 : 0 < b3
  hc3 : 0 < c3
  i235 : s0 * a3 + b3 + s2 * c3 = 1
  i236 : r * a3 + b3 + c3 = 1
  i4350 : a3 + m1 * b3 + m2 * c3 = 1
  i346 : w0 * a3 + w1 * b3 + c3 = 1
  o025 : a3 + b3 + p * c3 < 1
  o046 : a3 + q * b3 + c3 < 1
  hqm : q < m1
  hk1 : 0 < k1
  hk2 : 0 < k2
  hk3 : 0 < k3
  hk4 : 0 < k4
  v0 : k1 + k3 * r = k2 * s0 + k4 * w0
  v1 : k1 * m1 + k3 = k2 + k4 * w1
  v2 : k1 * m2 + k3 = k2 * s2 + k4

namespace Ch24
variable (S : Ch24)

/-- Facings (front `> 0`). -/
def f025 (a b c : ℝ) : ℝ := L3 1 1 S.p a b c
def f4350 (a b c : ℝ) : ℝ := L3 1 S.m1 S.m2 a b c
def f046 (a b c : ℝ) : ℝ := L3 1 S.q 1 a b c
def f235 (a b c : ℝ) : ℝ := L3 S.s0 1 S.s2 a b c
def f236 (a b c : ℝ) : ℝ := L3 S.r 1 1 a b c
def f346 (a b c : ℝ) : ℝ := L3 S.w0 S.w1 1 a b c

/-- The region `04325` (front `{4350, 235}`), open. -/
def InR (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < S.f4350 a b c ∧ 0 < S.f235 a b c ∧ S.f025 a b c < 0 ∧
    S.f046 a b c < 0 ∧ S.f236 a b c < 0 ∧ S.f346 a b c < 0

/-- The weak region: `025`, `046`, `236` back (no condition on `4350`, `235`, `346`).  It contains the
region `04325` and the hexagon `046325`; Lemmas A2, B (case `c3 ≥ 1`) only use these facings of `t`. -/
def InW (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ S.f025 a b c < 0 ∧ S.f046 a b c < 0 ∧ S.f236 a b c < 0

theorem InR.toW {S : Ch24} {a b c : ℝ} (h : S.InR a b c) : S.InW a b c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-- The open cell `0234` (front `{025, 4350, 235}`). -/
def Op0234 (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < S.f025 a b c ∧ 0 < S.f4350 a b c ∧ 0 < S.f235 a b c ∧
    S.f046 a b c < 0 ∧ S.f236 a b c < 0 ∧ S.f346 a b c < 0

/-- The closed cell `0234`. -/
def Cl0234 (a b c : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ S.f025 a b c ∧ 0 ≤ S.f4350 a b c ∧ 0 ≤ S.f235 a b c ∧
    S.f046 a b c ≤ 0 ∧ S.f236 a b c ≤ 0 ∧ S.f346 a b c ≤ 0

/-- The open cell `0536` (front `{046, 4350, 346}`). -/
def Op0536 (a b c : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < S.f046 a b c ∧ 0 < S.f4350 a b c ∧ 0 < S.f346 a b c ∧
    S.f025 a b c < 0 ∧ S.f235 a b c < 0 ∧ S.f236 a b c < 0

/-- The closed cell `0536`. -/
def Cl0536 (a b c : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ S.f046 a b c ∧ 0 ≤ S.f4350 a b c ∧ 0 ≤ S.f346 a b c ∧
    S.f025 a b c ≤ 0 ∧ S.f235 a b c ≤ 0 ∧ S.f236 a b c ≤ 0

/-- The 3-rim cell with front set `{235}` is empty. -/
def No235 : Prop := ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → 0 < S.f235 a b c → S.f4350 a b c < 0 →
  S.f025 a b c < 0 → S.f046 a b c < 0 → S.f236 a b c < 0 → S.f346 a b c < 0 → False

/-- The 3-rim cell with front set `{346}` is empty. -/
def No346 : Prop := ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → 0 < S.f346 a b c → S.f4350 a b c < 0 →
  S.f235 a b c < 0 → S.f025 a b c < 0 → S.f046 a b c < 0 → S.f236 a b c < 0 → False

/-- The 3-rim cell with front set `{025}` is empty. -/
def No025 : Prop := ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → 0 < S.f025 a b c → S.f4350 a b c < 0 →
  S.f235 a b c < 0 → S.f046 a b c < 0 → S.f236 a b c < 0 → S.f346 a b c < 0 → False

/-- Lemma V3' (vertex figure at 3) at every view. -/
theorem v3 (a b c : ℝ) :
    S.k1 * S.f4350 a b c + S.k3 * S.f236 a b c = S.k2 * S.f235 a b c + S.k4 * S.f346 a b c := by
  simp only [f4350, f236, f235, f346, L3]
  linear_combination a * S.v0 + b * S.v1 + c * S.v2

theorem th_pos : 0 < S.th := by nlinarith [S.hth, S.hr]
theorem thb_pos : 0 < S.thb := by nlinarith [S.hthb, S.hq]
theorem ga_pos : 0 < S.ga := by nlinarith [S.hga, S.hp]

/-- On chart points, `f236 = (1 - r)(θ - g_a)`, `f025 = (1 - p)(γ - g_c)`, `f046 = (1 - q)(θb - g_b)`. -/
theorem f236_eq {a b c : ℝ} (h : a + b + c = 1) : S.f236 a b c = (1 - S.r) * (S.th - a) := by
  simp only [f236, L3]; linear_combination h - S.hth
theorem f025_eq {a b c : ℝ} (h : a + b + c = 1) : S.f025 a b c = (1 - S.p) * (S.ga - c) := by
  simp only [f025, L3]; linear_combination h - S.hga
theorem f046_eq {a b c : ℝ} (h : a + b + c = 1) : S.f046 a b c = (1 - S.q) * (S.thb - b) := by
  simp only [f046, L3]; linear_combination h - S.hthb

/-- `s3 = a3 + b3 + c3 - 1 = a3 (1 - r)` and `θ s3 = a3`. -/
theorem s3_eq : S.a3 + S.b3 + S.c3 - 1 = S.a3 * (1 - S.r) := by linear_combination S.i236
theorem s3_pos : 0 < S.a3 + S.b3 + S.c3 - 1 := by
  rw [s3_eq]; exact mul_pos S.ha3 (by linarith [S.hr])
theorem th_s3 : S.th * (S.a3 + S.b3 + S.c3 - 1) = S.a3 := by
  rw [s3_eq]; linear_combination S.a3 * S.hth

/-- `a3 (f235 - f236) = (1 - s2) (c3 g_a - a3 g_c)` (Lemma E23 in one line). -/
theorem e23 (a b c : ℝ) :
    S.a3 * (S.f235 a b c - S.f236 a b c) = (1 - S.s2) * (S.c3 * a - S.a3 * c) := by
  simp only [f235, f236, L3]
  linear_combination a * (S.i235 - S.i236)

/-- Perturbation conditions at `ε = 0⁺` for `A + ε B` (positive / negative). -/
abbrev Pos (A B : ℝ) : Prop := 0 < A ∨ (0 ≤ A ∧ 0 < B)
abbrev Neg (A B : ℝ) : Prop := A < 0 ∨ (A ≤ 0 ∧ B < 0)

theorem op0234_pert {a b c x y z : ℝ} (h0 : Pos a x) (h1 : Pos b y) (h2 : Pos c z)
    (h025 : Pos (S.f025 a b c) (S.f025 x y z)) (h4350 : Pos (S.f4350 a b c) (S.f4350 x y z))
    (h235 : Pos (S.f235 a b c) (S.f235 x y z)) (h046 : Neg (S.f046 a b c) (S.f046 x y z))
    (h236 : Neg (S.f236 a b c) (S.f236 x y z)) (h346 : Neg (S.f346 a b c) (S.f346 x y z)) :
    ∃ a b c, S.Op0234 a b c := by
  obtain ⟨ε, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ((ev_pos h0).and ((ev_pos h1).and
    ((ev_pos h2).and ((ev_L3_pos h025).and ((ev_L3_pos h4350).and ((ev_L3_pos h235).and
    ((ev_L3_neg h046).and ((ev_L3_neg h236).and (ev_L3_neg h346))))))))).exists
  exact ⟨_, _, _, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩

theorem op0536_pert {a b c x y z : ℝ} (h0 : Pos a x) (h1 : Pos b y) (h2 : Pos c z)
    (h046 : Pos (S.f046 a b c) (S.f046 x y z)) (h4350 : Pos (S.f4350 a b c) (S.f4350 x y z))
    (h346 : Pos (S.f346 a b c) (S.f346 x y z)) (h025 : Neg (S.f025 a b c) (S.f025 x y z))
    (h235 : Neg (S.f235 a b c) (S.f235 x y z)) (h236 : Neg (S.f236 a b c) (S.f236 x y z)) :
    ∃ a b c, S.Op0536 a b c := by
  obtain ⟨ε, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ((ev_pos h0).and ((ev_pos h1).and
    ((ev_pos h2).and ((ev_L3_pos h046).and ((ev_L3_pos h4350).and ((ev_L3_pos h346).and
    ((ev_L3_neg h025).and ((ev_L3_neg h235).and (ev_L3_neg h236))))))))).exists
  exact ⟨_, _, _, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩

theorem no235_pert (hNo : S.No235) {a b c x y z : ℝ} (h0 : Pos a x) (h1 : Pos b y) (h2 : Pos c z)
    (h235 : Pos (S.f235 a b c) (S.f235 x y z)) (h4350 : Neg (S.f4350 a b c) (S.f4350 x y z))
    (h025 : Neg (S.f025 a b c) (S.f025 x y z)) (h046 : Neg (S.f046 a b c) (S.f046 x y z))
    (h236 : Neg (S.f236 a b c) (S.f236 x y z)) (h346 : Neg (S.f346 a b c) (S.f346 x y z)) :
    False := by
  obtain ⟨ε, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ((ev_pos h0).and ((ev_pos h1).and
    ((ev_pos h2).and ((ev_L3_pos h235).and ((ev_L3_neg h4350).and ((ev_L3_neg h025).and
    ((ev_L3_neg h046).and ((ev_L3_neg h236).and (ev_L3_neg h346))))))))).exists
  exact hNo _ _ _ e0 e1 e2 e3 e4 e5 e6 e7 e8

theorem no346_pert (hNo : S.No346) {a b c x y z : ℝ} (h0 : Pos a x) (h1 : Pos b y) (h2 : Pos c z)
    (h346 : Pos (S.f346 a b c) (S.f346 x y z)) (h4350 : Neg (S.f4350 a b c) (S.f4350 x y z))
    (h235 : Neg (S.f235 a b c) (S.f235 x y z)) (h025 : Neg (S.f025 a b c) (S.f025 x y z))
    (h046 : Neg (S.f046 a b c) (S.f046 x y z)) (h236 : Neg (S.f236 a b c) (S.f236 x y z)) :
    False := by
  obtain ⟨ε, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ((ev_pos h0).and ((ev_pos h1).and
    ((ev_pos h2).and ((ev_L3_pos h346).and ((ev_L3_neg h4350).and ((ev_L3_neg h235).and
    ((ev_L3_neg h025).and ((ev_L3_neg h046).and (ev_L3_neg h236))))))))).exists
  exact hNo _ _ _ e0 e1 e2 e3 e4 e5 e6 e7 e8

theorem no025_pert (hNo : S.No025) {a b c x y z : ℝ} (h0 : Pos a x) (h1 : Pos b y) (h2 : Pos c z)
    (h025 : Pos (S.f025 a b c) (S.f025 x y z)) (h4350 : Neg (S.f4350 a b c) (S.f4350 x y z))
    (h235 : Neg (S.f235 a b c) (S.f235 x y z)) (h046 : Neg (S.f046 a b c) (S.f046 x y z))
    (h236 : Neg (S.f236 a b c) (S.f236 x y z)) (h346 : Neg (S.f346 a b c) (S.f346 x y z)) :
    False := by
  obtain ⟨ε, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ((ev_pos h0).and ((ev_pos h1).and
    ((ev_pos h2).and ((ev_L3_pos h025).and ((ev_L3_neg h4350).and ((ev_L3_neg h235).and
    ((ev_L3_neg h046).and ((ev_L3_neg h236).and (ev_L3_neg h346))))))))).exists
  exact hNo _ _ _ e0 e1 e2 e3 e4 e5 e6 e7 e8

theorem L3_cvx (α β γ a b c a' b' c' l : ℝ) :
    L3 α β γ ((1 - l) * a + l * a') ((1 - l) * b + l * b') ((1 - l) * c + l * c') =
      (1 - l) * L3 α β γ a b c + l * L3 α β γ a' b' c' := by
  unfold L3; ring

theorem Cl0234_congr {a b c a' b' c' : ℝ} (h : S.Cl0234 a b c) (ha : a = a') (hb : b = b')
    (hc : c = c') : S.Cl0234 a' b' c' := by subst ha hb hc; exact h

/-- The chart point `t` of the region: `θ < t_a`, `θb < t_b`, `γ < t_c`. -/
theorem R_lt {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) :
    S.th < t0 ∧ S.thb < t1 ∧ S.ga < t2 := by
  obtain ⟨-, -, -, h025, h046, h236⟩ := hW
  rw [S.f025_eq hts] at h025
  rw [S.f046_eq hts] at h046
  rw [S.f236_eq hts] at h236
  have := S.hp; have := S.hq; have := S.hr
  refine ⟨?_, ?_, ?_⟩ <;> by_contra h <;> push Not at h
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - S.r by linarith) (show 0 ≤ S.th - t0 by linarith)]
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - S.q by linarith) (show 0 ≤ S.thb - t1 by linarith)]
  · nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - S.p by linarith) (show 0 ≤ S.ga - t2 by linarith)]

/-- Facings at the wall point `w = (t_a, t_b + t_c - γ, γ)` (wall ray from `t` along `(0, 1, -1)`). -/
theorem wall_facts {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1) :
    0 < t1 + t2 - S.ga ∧ S.f025 t0 (t1 + t2 - S.ga) S.ga = 0 ∧
      0 < S.f235 t0 (t1 + t2 - S.ga) S.ga ∧ S.f046 t0 (t1 + t2 - S.ga) S.ga < 0 ∧
      S.f236 t0 (t1 + t2 - S.ga) S.ga < 0 ∧ S.f346 t0 (t1 + t2 - S.ga) S.ga < 0 := by
  obtain ⟨θ, θb, γ⟩ := S.R_lt hR.toW hts
  obtain ⟨_, h1, _, _, h235, _, h046, h236, h346⟩ := hR
  have hc : 0 < t2 - S.ga := by linarith
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S.f025_eq (by linarith)]; ring
  · simp only [f235, L3] at h235 ⊢
    nlinarith [mul_pos hc (show (0:ℝ) < 1 - S.s2 by linarith [S.hs2])]
  · simp only [f046, L3] at h046 ⊢
    nlinarith [mul_pos hc (show (0:ℝ) < 1 - S.q by linarith [S.hq])]
  · simp only [f236, L3] at h236 ⊢; linarith
  · simp only [f346, L3] at h346 ⊢
    nlinarith [mul_pos hc (show (0:ℝ) < 1 - S.w1 by linarith [S.hw1])]

/-- **The cell 0234 is open** (from `R` and the empty cell `{235}`, via the wall ray). -/
theorem wall_open {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No235) :
    ∃ a b c, S.Op0234 a b c := by
  obtain ⟨θ, θb, γ⟩ := S.R_lt hR.toW hts
  obtain ⟨hwb, hw025, hw235, hw046, hw236, hw346⟩ := S.wall_facts hR hts
  have ht0 := hR.1
  have hga := S.ga_pos
  by_cases h4 : 0 ≤ S.f4350 t0 (t1 + t2 - S.ga) S.ga
  · obtain ⟨μ, hμ, hμ0⟩ := ((ev_pos (A := 1 - S.m1) (B := S.m1 - S.m2)
      (Or.inl (by linarith [S.hm1]))).and self_mem_nhdsWithin).exists
    have hμ0' : (0:ℝ) < μ := hμ0
    refine S.op0234_pert (x := 1) (y := μ - 1) (z := -μ) (Or.inl ht0) (Or.inl hwb) (Or.inl hga)
      (Or.inr ⟨hw025.ge, ?_⟩) (Or.inr ⟨h4, ?_⟩) (Or.inl hw235) (Or.inl hw046) (Or.inl hw236)
      (Or.inl hw346)
    · simp only [f025, L3]; nlinarith [mul_pos hμ0' (show (0:ℝ) < 1 - S.p by linarith [S.hp])]
    · simp only [f4350, L3]; linarith
  · push Not at h4
    exact (S.no235_pert hNo (x := 0) (y := S.ga - t2) (z := t2 - S.ga) (Or.inl ht0) (Or.inl hwb)
      (Or.inl hga) (Or.inl hw235) (Or.inl h4) (Or.inr ⟨hw025.le, by
        simp only [f025, L3]
        nlinarith [mul_pos (show (0:ℝ) < t2 - S.ga by linarith) (show (0:ℝ) < 1 - S.p by linarith [S.hp])]⟩)
      (Or.inl hw046) (Or.inl hw236) (Or.inl hw346)).elim

/-- `u = θ / a3 = 1 / s3`: the scale of `E23 = u (y3 - e_b)` and `E36 = u (y3 - e_c)`. -/
theorem u_facts : S.th / S.a3 * S.a3 = S.th ∧ S.th / S.a3 * (S.a3 + S.b3 + S.c3 - 1) = 1 ∧
    0 < S.th / S.a3 := by
  have ha := S.ha3
  refine ⟨div_mul_cancel₀ _ ha.ne', ?_, div_pos S.th_pos ha⟩
  rw [div_mul_eq_mul_div, S.th_s3, div_self ha.ne']

/-- `f346 (T_b) = (γ - u (c3 - 1)) (1 - w1)`, so `T_b` is `346`-front when `c3 ≤ 1`. -/
theorem f346_Tb : S.f346 S.th (1 - S.th - S.ga) S.ga =
    (S.ga - S.th / S.a3 * (S.c3 - 1)) * (1 - S.w1) := by
  obtain ⟨hua, hus, -⟩ := S.u_facts
  simp only [f346, L3]
  linear_combination S.th / S.a3 * S.i346 - S.w1 * hus - (S.w0 - S.w1) * hua

theorem tb346_pos (hc3 : S.c3 ≤ 1) : 0 < S.f346 S.th (1 - S.th - S.ga) S.ga := by
  rw [f346_Tb]
  obtain ⟨-, -, hu⟩ := S.u_facts
  apply mul_pos _ (by linarith [S.hw1])
  nlinarith [mul_nonneg hu.le (show 0 ≤ 1 - S.c3 by linarith), S.ga_pos]

/-- **Lemma A1** (wall end `025 × 346`, `T_b` `346`-front). -/
theorem a1 {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1)
    (hTb : 0 < S.f346 S.th (1 - S.th - S.ga) S.ga) :
    ∃ τ, S.th < τ ∧ τ < t0 ∧ 0 < 1 - τ - S.ga ∧ S.w0 < S.w1 ∧
      S.f025 τ (1 - τ - S.ga) S.ga = 0 ∧ S.f346 τ (1 - τ - S.ga) S.ga = 0 ∧
      0 < S.f4350 τ (1 - τ - S.ga) S.ga ∧ 0 < S.f235 τ (1 - τ - S.ga) S.ga ∧
      S.f236 τ (1 - τ - S.ga) S.ga < 0 ∧ S.f046 τ (1 - τ - S.ga) S.ga < 0 := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hR.toW hts
  obtain ⟨hwb, hw025, hw235, hw046, hw236, hw346⟩ := S.wall_facts hR hts
  have hwb' : t1 + t2 - S.ga = 1 - t0 - S.ga := by linarith
  rw [hwb'] at hw235 hw046 hw346
  have e346 : S.f346 t0 (1 - t0 - S.ga) S.ga =
      S.f346 S.th (1 - S.th - S.ga) S.ga - (t0 - S.th) * (S.w1 - S.w0) := by
    simp only [f346, L3]; ring
  have hD : 0 < S.w1 - S.w0 := by
    have : 0 < (t0 - S.th) * (S.w1 - S.w0) := by linarith
    exact pos_of_mul_pos_right this (by linarith)
  set F := S.f346 S.th (1 - S.th - S.ga) S.ga with hF
  set τ := S.th + F / (S.w1 - S.w0) with hτ
  have hτθ : S.th < τ := by have := div_pos hTb hD; linarith
  have hτt : τ < t0 := by
    have : F / (S.w1 - S.w0) < t0 - S.th := by rw [div_lt_iff₀ hD]; linarith
    linarith
  have hT346 : S.f346 τ (1 - τ - S.ga) S.ga = 0 := by
    have e : S.f346 τ (1 - τ - S.ga) S.ga = F - (τ - S.th) * (S.w1 - S.w0) := by
      rw [hF]; simp only [f346, L3]; ring
    rw [e, hτ]; field_simp; ring
  have hT235 : 0 < S.f235 τ (1 - τ - S.ga) S.ga := by
    have e : S.f235 τ (1 - τ - S.ga) S.ga = S.f235 t0 (1 - t0 - S.ga) S.ga + (t0 - τ) * (1 - S.s0) := by
      simp only [f235, L3]; ring
    rw [e]; nlinarith [mul_pos (show 0 < t0 - τ by linarith) (show (0:ℝ) < 1 - S.s0 by linarith [S.hs0])]
  have hT046 : S.f046 τ (1 - τ - S.ga) S.ga < 0 := by
    have e : S.f046 τ (1 - τ - S.ga) S.ga = S.f046 t0 (1 - t0 - S.ga) S.ga - (t0 - τ) * (1 - S.q) := by
      simp only [f046, L3]; ring
    rw [e]; nlinarith [mul_pos (show 0 < t0 - τ by linarith) (show (0:ℝ) < 1 - S.q by linarith [S.hq])]
  have hT236 : S.f236 τ (1 - τ - S.ga) S.ga < 0 := by
    rw [S.f236_eq (by ring)]
    exact mul_neg_of_pos_of_neg (by linarith [S.hr]) (by linarith)
  have hT4350 : 0 < S.f4350 τ (1 - τ - S.ga) S.ga := by
    have h := S.v3 τ (1 - τ - S.ga) S.ga
    rw [hT346] at h
    have : 0 < S.k1 * S.f4350 τ (1 - τ - S.ga) S.ga := by
      nlinarith [mul_pos S.hk2 hT235, mul_pos S.hk3 (neg_pos.2 hT236)]
    exact pos_of_mul_pos_right this S.hk1.le
  refine ⟨τ, hτθ, hτt, by linarith, by linarith, ?_, hT346, hT4350, hT235, hT236, hT046⟩
  rw [S.f025_eq (by ring)]; ring

/-- **Lemma A1'** (wall end `T_b`, when `T_b` is not `346`-front; uses the empty cell `{235}`). -/
theorem a1' {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No235)
    (hTb : S.f346 S.th (1 - S.th - S.ga) S.ga ≤ 0) :
    0 ≤ S.f4350 S.th (1 - S.th - S.ga) S.ga ∧ 0 < S.f235 S.th (1 - S.th - S.ga) S.ga ∧
      S.f046 S.th (1 - S.th - S.ga) S.ga < 0 := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hR.toW hts
  obtain ⟨hwb, hw025, hw235, hw046, hw236, hw346⟩ := S.wall_facts hR hts
  have hwb' : t1 + t2 - S.ga = 1 - t0 - S.ga := by linarith
  rw [hwb'] at hw235 hw046
  have h235 : 0 < S.f235 S.th (1 - S.th - S.ga) S.ga := by
    have e : S.f235 S.th (1 - S.th - S.ga) S.ga = S.f235 t0 (1 - t0 - S.ga) S.ga + (t0 - S.th) * (1 - S.s0) := by
      simp only [f235, L3]; ring
    rw [e]; nlinarith [mul_pos (show 0 < t0 - S.th by linarith) (show (0:ℝ) < 1 - S.s0 by linarith [S.hs0])]
  have h046 : S.f046 S.th (1 - S.th - S.ga) S.ga < 0 := by
    have e : S.f046 S.th (1 - S.th - S.ga) S.ga = S.f046 t0 (1 - t0 - S.ga) S.ga - (t0 - S.th) * (1 - S.q) := by
      simp only [f046, L3]; ring
    rw [e]; nlinarith [mul_pos (show 0 < t0 - S.th by linarith) (show (0:ℝ) < 1 - S.q by linarith [S.hq])]
  refine ⟨?_, h235, h046⟩
  by_contra h4
  push Not at h4
  obtain ⟨ht0, ht1, ht2, -, -, h025t, -, h236t, h346t⟩ := hR
  have h025T : S.f025 S.th (1 - S.th - S.ga) S.ga = 0 := by rw [S.f025_eq (by ring)]; ring
  have h236T : S.f236 S.th (1 - S.th - S.ga) S.ga = 0 := by rw [S.f236_eq (by ring)]; ring
  refine S.no235_pert hNo (x := t0 - S.th) (y := t1 - (1 - S.th - S.ga)) (z := t2 - S.ga)
    (Or.inl S.th_pos) (Or.inl (by linarith)) (Or.inl S.ga_pos) (Or.inl h235) (Or.inl h4)
    (Or.inr ⟨h025T.le, ?_⟩) (Or.inl h046) (Or.inr ⟨h236T.le, ?_⟩) ?_
  · have : S.f025 (t0 - S.th) (t1 - (1 - S.th - S.ga)) (t2 - S.ga) = S.f025 t0 t1 t2 - S.f025 S.th (1 - S.th - S.ga) S.ga := by
      simp only [f025, L3]; ring
    rw [this, h025T]; linarith
  · have : S.f236 (t0 - S.th) (t1 - (1 - S.th - S.ga)) (t2 - S.ga) = S.f236 t0 t1 t2 - S.f236 S.th (1 - S.th - S.ga) S.ga := by
      simp only [f236, L3]; ring
    rw [this, h236T]; linarith
  · have : S.f346 (t0 - S.th) (t1 - (1 - S.th - S.ga)) (t2 - S.ga) = S.f346 t0 t1 t2 - S.f346 S.th (1 - S.th - S.ga) S.ga := by
      simp only [f346, L3]; ring
    rw [this]; exact seg_neg hTb h346t

/-- Facings at `T_c = 046 × 236` in case C (`u (b3 - 1) > θb`); `f4350 ≥ 0` uses the empty cell `{346}`. -/
theorem tc_facts {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No346)
    (hC : S.thb < S.th / S.a3 * (S.b3 - 1)) :
    0 < 1 - S.th - S.thb ∧ S.f046 S.th S.thb (1 - S.th - S.thb) = 0 ∧
      S.f236 S.th S.thb (1 - S.th - S.thb) = 0 ∧ S.f235 S.th S.thb (1 - S.th - S.thb) < 0 ∧
      0 < S.f346 S.th S.thb (1 - S.th - S.thb) ∧ S.f025 S.th S.thb (1 - S.th - S.thb) < 0 ∧
      0 ≤ S.f4350 S.th S.thb (1 - S.th - S.thb) := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hW hts
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  set u := S.th / S.a3
  have hc : 0 < 1 - S.th - S.thb := by linarith [hW.2.2.1]
  have h046 : S.f046 S.th S.thb (1 - S.th - S.thb) = 0 := by rw [S.f046_eq (by ring)]; ring
  have h236 : S.f236 S.th S.thb (1 - S.th - S.thb) = 0 := by rw [S.f236_eq (by ring)]; ring
  have h235 : S.f235 S.th S.thb (1 - S.th - S.thb) < 0 := by
    have e : S.f235 S.th S.thb (1 - S.th - S.thb) = (S.thb - u * (S.b3 - 1)) * (1 - S.s2) := by
      simp only [f235, L3]
      linear_combination u * S.i235 - S.s2 * hus - (S.s0 - S.s2) * hua
    rw [e]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith [S.hs2])
  have h346 : 0 < S.f346 S.th S.thb (1 - S.th - S.thb) := by
    have e : S.f346 S.th S.thb (1 - S.th - S.thb) = (1 - S.w1) * (u - (S.thb - u * (S.b3 - 1))) := by
      simp only [f346, L3]
      linear_combination u * S.i346 - hus - (S.w0 - 1) * hua
    rw [e]; exact mul_pos (by linarith [S.hw1]) (by linarith)
  have h025 : S.f025 S.th S.thb (1 - S.th - S.thb) < 0 := by
    rw [S.f025_eq (by ring)]; exact mul_neg_of_pos_of_neg (by linarith [S.hp]) (by linarith)
  refine ⟨hc, h046, h236, h235, h346, h025, ?_⟩
  by_contra h4
  push Not at h4
  obtain ⟨ht0, ht1, ht2, -, h046t, h236t⟩ := hW
  refine S.no346_pert hNo (x := t0 - S.th) (y := t1 - S.thb) (z := t2 - (1 - S.th - S.thb))
    (Or.inl S.th_pos) (Or.inl S.thb_pos) (Or.inl hc) (Or.inl h346) (Or.inl h4) (Or.inl h235)
    (Or.inl h025) (Or.inr ⟨h046.le, ?_⟩) (Or.inr ⟨h236.le, ?_⟩)
  · have : S.f046 (t0 - S.th) (t1 - S.thb) (t2 - (1 - S.th - S.thb)) =
        S.f046 t0 t1 t2 - S.f046 S.th S.thb (1 - S.th - S.thb) := by simp only [f046, L3]; ring
    rw [this, h046]; linarith
  · have : S.f236 (t0 - S.th) (t1 - S.thb) (t2 - (1 - S.th - S.thb)) =
        S.f236 t0 t1 t2 - S.f236 S.th S.thb (1 - S.th - S.thb) := by simp only [f236, L3]; ring
    rw [this, h236]; linarith

/-- Facings at `E23 = u (y3 - e_b) = (θ, u (b3 - 1), u c3)` (on `L_236`, edge `23`). -/
theorem e23_facts :
    S.th + S.th / S.a3 * (S.b3 - 1) + S.th / S.a3 * S.c3 = 1 ∧
      S.f235 S.th (S.th / S.a3 * (S.b3 - 1)) (S.th / S.a3 * S.c3) = 0 ∧
      S.f236 S.th (S.th / S.a3 * (S.b3 - 1)) (S.th / S.a3 * S.c3) = 0 ∧
      0 < S.f4350 S.th (S.th / S.a3 * (S.b3 - 1)) (S.th / S.a3 * S.c3) ∧
      0 < S.f346 S.th (S.th / S.a3 * (S.b3 - 1)) (S.th / S.a3 * S.c3) ∧
      S.f025 S.th (S.th / S.a3 * (S.b3 - 1)) (S.th / S.a3 * S.c3) < 0 := by
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  set u := S.th / S.a3
  refine ⟨by linear_combination hus - hua, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [f235, L3]; linear_combination u * S.i235 - S.s0 * hua
  · simp only [f236, L3]; linear_combination u * S.i236 - S.r * hua
  · have e : S.f4350 S.th (u * (S.b3 - 1)) (u * S.c3) = u * (1 - S.m1) := by
      simp only [f4350, L3]; linear_combination u * S.i4350 - hua
    rw [e]; exact mul_pos hu (by linarith [S.hm1])
  · have e : S.f346 S.th (u * (S.b3 - 1)) (u * S.c3) = u * (1 - S.w1) := by
      simp only [f346, L3]; linear_combination u * S.i346 - S.w0 * hua
    rw [e]; exact mul_pos hu (by linarith [S.hw1])
  · have e : S.f025 S.th (u * (S.b3 - 1)) (u * S.c3) = u * (S.a3 + S.b3 + S.p * S.c3 - 1) := by
      simp only [f025, L3]; linear_combination -hua
    rw [e]; exact mul_neg_of_pos_of_neg hu (by linarith [S.o025])

/-- **Lemma A2, closed part**: for `b3 ≥ 1`, `cl 0536` meets `L_236` (at `E23` or `T_c`). -/
theorem a2_closed {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No346)
    (hb3 : 1 ≤ S.b3) : ∃ y z, S.th + y + z = 1 ∧ S.Cl0536 S.th y z := by
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  by_cases hC : S.thb < S.th / S.a3 * (S.b3 - 1)
  · obtain ⟨hc, h046, h236, h235, h346, h025, h4350⟩ := S.tc_facts hW hts hNo hC
    exact ⟨S.thb, 1 - S.th - S.thb, by ring, S.th_pos.le, S.thb_pos.le, hc.le, h046.ge, h4350,
      h346.le, h025.le, h235.le, h236.le⟩
  · push Not at hC
    obtain ⟨hsum, h235, h236, h4350, h346, h025⟩ := S.e23_facts
    refine ⟨_, _, hsum, S.th_pos.le, mul_nonneg hu.le (by linarith), mul_nonneg hu.le S.hc3.le, ?_,
      h4350.le, h346.le, h025.le, h235.le, h236.le⟩
    rw [S.f046_eq hsum]; exact mul_nonneg (by linarith [S.hq]) (by linarith)

/-- **Lemma A2, open part**: for `b3 > 1` the cell `0536` is open.  In case C the point is
`T_c + ε (1, -L, L - 1)` with `L > 0` small: `046` turns front, `236` back and `4350` front.  This
covers the special position `f4350 (T_c) = 0` (the lines `L_046`, `L_236`, `L_4350` meet at `T_c`):
the end rows `m2 < 1`, `r < 1` rule out an empty wedge there. -/
theorem a2_open {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No346)
    (hb3 : 1 < S.b3) : ∃ a b c, S.Op0536 a b c := by
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  have hs2 : 0 < 1 - S.s2 := by linarith [S.hs2]
  set K := (|S.s0 - S.s2| + 1) / (1 - S.s2) with hK
  have hK1 : K * (1 - S.s2) = |S.s0 - S.s2| + 1 := by rw [hK]; field_simp
  have hK0 : 0 < K := div_pos (by positivity) hs2
  have hab := le_abs_self (S.s0 - S.s2)
  have d046 : 0 < S.f046 1 (-K) (K - 1) := by
    simp only [f046, L3]; nlinarith [mul_pos hK0 (show (0:ℝ) < 1 - S.q by linarith [S.hq])]
  have d235 : S.f235 1 (-K) (K - 1) < 0 := by simp only [f235, L3]; nlinarith
  have d236 : S.f236 1 (-K) (K - 1) < 0 := by simp only [f236, L3]; linarith [S.hr]
  by_cases hC : S.thb < S.th / S.a3 * (S.b3 - 1)
  · obtain ⟨hc, h046, h236, h235, h346, h025, h4350⟩ := S.tc_facts hW hts hNo hC
    have hm2 : 0 < 1 - S.m2 := by linarith [S.hm2]
    set L := (1 - S.m2) / (|S.m1 - S.m2| + 1) with hL
    have hL1 : L * (|S.m1 - S.m2| + 1) = 1 - S.m2 := by rw [hL]; field_simp
    have hL0 : 0 < L := div_pos hm2 (by positivity)
    have hm := le_abs_self (S.m1 - S.m2)
    have e046 : 0 < S.f046 1 (-L) (L - 1) := by
      simp only [f046, L3]; nlinarith [mul_pos hL0 (show (0:ℝ) < 1 - S.q by linarith [S.hq])]
    have e4350 : 0 < S.f4350 1 (-L) (L - 1) := by
      simp only [f4350, L3]; nlinarith [mul_nonneg hL0.le (abs_nonneg (S.m1 - S.m2))]
    have e236 : S.f236 1 (-L) (L - 1) < 0 := by simp only [f236, L3]; linarith [S.hr]
    exact S.op0536_pert (x := 1) (y := -L) (z := L - 1) (Or.inl S.th_pos) (Or.inl S.thb_pos)
      (Or.inl hc) (Or.inr ⟨h046.ge, e046⟩) (Or.inr ⟨h4350, e4350⟩) (Or.inl h346) (Or.inl h025)
      (Or.inl h235) (Or.inr ⟨h236.le, e236⟩)
  · push Not at hC
    obtain ⟨hsum, h235, h236, h4350, h346, h025⟩ := S.e23_facts
    have h046 : 0 ≤ S.f046 S.th (S.th / S.a3 * (S.b3 - 1)) (S.th / S.a3 * S.c3) := by
      rw [S.f046_eq hsum]; exact mul_nonneg (by linarith [S.hq]) (by linarith)
    exact S.op0536_pert (x := 1) (y := -K) (z := K - 1) (Or.inl S.th_pos)
      (Or.inl (mul_pos hu (by linarith))) (Or.inl (mul_pos hu S.hc3)) (Or.inr ⟨h046, d046⟩)
      (Or.inl h4350) (Or.inl h346) (Or.inl h025) (Or.inr ⟨h235.le, d235⟩) (Or.inr ⟨h236.le, d236⟩)

/-- **Mirror of Lemma A2, closed part**: for `c3 ≥ 1`, `cl 0234` meets `L_236` (at `E36` or `T_b`). -/
theorem a2m_closed {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No235)
    (hc3 : 1 ≤ S.c3) : ∃ y z, S.th + y + z = 1 ∧ S.Cl0234 S.th y z := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hR.toW hts
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  set u := S.th / S.a3
  by_cases hC : S.ga < u * (S.c3 - 1)
  · have h346 : S.f346 S.th (1 - S.th - S.ga) S.ga ≤ 0 := by
      rw [S.f346_Tb]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [S.hw1])
    obtain ⟨h4350, h235, h046⟩ := S.a1' hR hts hNo h346
    refine ⟨1 - S.th - S.ga, S.ga, by ring, S.th_pos.le, by linarith [hR.2.1], S.ga_pos.le, ?_, h4350,
      h235.le, h046.le, ?_, h346⟩
    · rw [S.f025_eq (by ring)]; simp
    · rw [S.f236_eq (by ring)]; simp
  · push Not at hC
    have hsum : S.th + u * S.b3 + u * (S.c3 - 1) = 1 := by linear_combination hus - hua
    refine ⟨u * S.b3, u * (S.c3 - 1), hsum, S.th_pos.le, mul_nonneg hu.le S.hb3.le,
      mul_nonneg hu.le (by linarith), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [S.f025_eq hsum]; exact mul_nonneg (by linarith [S.hp]) (by linarith)
    · have e : S.f4350 S.th (u * S.b3) (u * (S.c3 - 1)) = u * (1 - S.m2) := by
        simp only [f4350, L3]; linear_combination u * S.i4350 - hua
      rw [e]; exact mul_nonneg hu.le (by linarith [S.hm2])
    · have e : S.f235 S.th (u * S.b3) (u * (S.c3 - 1)) = u * (1 - S.s2) := by
        simp only [f235, L3]; linear_combination u * S.i235 - S.s0 * hua
      rw [e]; exact mul_nonneg hu.le (by linarith [S.hs2])
    · have e : S.f046 S.th (u * S.b3) (u * (S.c3 - 1)) = u * (S.a3 + S.q * S.b3 + S.c3 - 1) := by
        simp only [f046, L3]; linear_combination -hua
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith [S.o046])
    · rw [S.f236_eq hsum]; simp
    · have e : S.f346 S.th (u * S.b3) (u * (S.c3 - 1)) = 0 := by
        simp only [f346, L3]; linear_combination u * S.i346 - S.w0 * hua
      rw [e]

theorem L3_side (α β γ x1 x2 l : ℝ) :
    L3 α β γ ((1 - l) * x1 + l * x2) (1 - ((1 - l) * x1 + l * x2)) 0 =
      (1 - l) * L3 α β γ x1 (1 - x1) 0 + l * L3 α β γ x2 (1 - x2) 0 := by
  unfold L3; ring

/-- Facings at `E36 = u (y3 - e_c) = (θ, u b3, u (c3 - 1))` (on `L_236` and `L_346`, edge `36`). -/
theorem e36_facts :
    S.th + S.th / S.a3 * S.b3 + S.th / S.a3 * (S.c3 - 1) = 1 ∧
      S.f236 S.th (S.th / S.a3 * S.b3) (S.th / S.a3 * (S.c3 - 1)) = 0 ∧
      S.f346 S.th (S.th / S.a3 * S.b3) (S.th / S.a3 * (S.c3 - 1)) = 0 ∧
      0 < S.f4350 S.th (S.th / S.a3 * S.b3) (S.th / S.a3 * (S.c3 - 1)) ∧
      0 < S.f235 S.th (S.th / S.a3 * S.b3) (S.th / S.a3 * (S.c3 - 1)) ∧
      S.f046 S.th (S.th / S.a3 * S.b3) (S.th / S.a3 * (S.c3 - 1)) < 0 := by
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  set u := S.th / S.a3
  refine ⟨by linear_combination hus - hua, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [f236, L3]; linear_combination u * S.i236 - S.r * hua
  · simp only [f346, L3]; linear_combination u * S.i346 - S.w0 * hua
  · have e : S.f4350 S.th (u * S.b3) (u * (S.c3 - 1)) = u * (1 - S.m2) := by
      simp only [f4350, L3]; linear_combination u * S.i4350 - hua
    rw [e]; exact mul_pos hu (by linarith [S.hm2])
  · have e : S.f235 S.th (u * S.b3) (u * (S.c3 - 1)) = u * (1 - S.s2) := by
      simp only [f235, L3]; linear_combination u * S.i235 - S.s0 * hua
    rw [e]; exact mul_pos hu (by linarith [S.hs2])
  · have e : S.f046 S.th (u * S.b3) (u * (S.c3 - 1)) = u * (S.a3 + S.q * S.b3 + S.c3 - 1) := by
      simp only [f046, L3]; linear_combination -hua
    rw [e]; exact mul_neg_of_pos_of_neg hu (by linarith [S.o046])

/-- **Lemma B, cases B1, B2** (`cl 0234` meets the side `L_012` when `f4350 (X) < 0` or `c3 ≥ 1`):
a point `P = (x, 1 - x, 0)` of `cl 0234` with `0 < x < 1`, at `X = 012 × 236` or `012 × 4350`
(uses the empty cell `{025}`).  Only the weak region `InW` of `t` is used. -/
theorem lemB_w {t0 t1 t2 : ℝ} (hW : S.InW t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No025)
    (hX : S.f4350 S.th (1 - S.th) 0 < 0 ∨ 1 ≤ S.c3) :
    ∃ x, 0 < x ∧ x < 1 ∧ S.Cl0234 x (1 - x) 0 := by
  obtain ⟨hθ, hθb, -⟩ := S.R_lt hW hts
  obtain ⟨hua, hus, hu⟩ := S.u_facts
  have hθ0 := S.th_pos
  have hθb0 := S.thb_pos
  have hsum : S.th + S.thb < 1 := by linarith [hW.2.2.1]
  -- facings at X = (θ, 1 - θ, 0) and Y = (1 - θb, θb, 0)
  have X025 : S.f025 S.th (1 - S.th) 0 = 1 := by simp only [f025, L3]; ring
  have X236 : S.f236 S.th (1 - S.th) 0 = 0 := by rw [S.f236_eq (by ring)]; ring
  have X046 : S.f046 S.th (1 - S.th) 0 < 0 := by
    rw [S.f046_eq (by ring)]; exact mul_neg_of_pos_of_neg (by linarith [S.hq]) (by linarith)
  have X235 : 0 < S.f235 S.th (1 - S.th) 0 := by
    have h := S.e23 S.th (1 - S.th) 0
    rw [X236] at h
    have : 0 < S.a3 * (S.f235 S.th (1 - S.th) 0 - 0) := by
      rw [h]; exact mul_pos (by linarith [S.hs2]) (by nlinarith [mul_pos S.hc3 hθ0])
    have := pos_of_mul_pos_right this S.ha3.le
    linarith
  have X346 : S.f346 S.th (1 - S.th) 0 = S.th / S.a3 * (S.c3 - 1) * (S.w1 - 1) := by
    simp only [f346, L3]
    linear_combination S.th / S.a3 * S.i346 - S.w1 * hus - (S.w0 - S.w1) * hua
  have Y4350 : S.f4350 (1 - S.thb) (1 - (1 - S.thb)) 0 = S.thb * (S.m1 - S.q) := by
    simp only [f4350, L3]; linear_combination -S.hthb
  have Y046 : S.f046 (1 - S.thb) (1 - (1 - S.thb)) 0 = 0 := by rw [S.f046_eq (by ring)]; ring
  have Y236 : S.f236 (1 - S.thb) (1 - (1 - S.thb)) 0 < 0 := by
    rw [S.f236_eq (by ring)]; exact mul_neg_of_pos_of_neg (by linarith [S.hr]) (by linarith)
  have Y4350p : 0 < S.f4350 (1 - S.thb) (1 - (1 - S.thb)) 0 := by
    rw [Y4350]; exact mul_pos hθb0 (by linarith [S.hqm])
  by_cases h4X : S.f4350 S.th (1 - S.th) 0 < 0
  · -- B2: the zero `P'` of `f4350` on `[X, Y]`
    set A := S.f4350 S.th (1 - S.th) 0
    set B := S.f4350 (1 - S.thb) (1 - (1 - S.thb)) 0
    set μ := A / (A - B) with hμ
    have hAB : A - B < 0 := by linarith
    have hμ0 : 0 < μ := div_pos_of_neg_of_neg h4X hAB
    have hμ1 : μ < 1 := by rw [hμ, div_lt_one_of_neg hAB]; linarith
    have hμe : μ * (A - B) = A := by rw [hμ, div_mul_cancel₀ _ hAB.ne]
    set x' := (1 - μ) * S.th + μ * (1 - S.thb) with hx'
    have hx'0 : S.th < x' := by
      linarith [mul_pos hμ0 (show 0 < 1 - S.thb - S.th by linarith)]
    have hx'1 : x' < 1 - S.thb := by
      linarith [mul_pos (show 0 < 1 - μ by linarith) (show 0 < 1 - S.thb - S.th by linarith)]
    have P4350 : S.f4350 x' (1 - x') 0 = 0 := by
      have e : S.f4350 x' (1 - x') 0 = (1 - μ) * A + μ * B := L3_side 1 S.m1 S.m2 S.th (1 - S.thb) μ
      rw [e]; linarith
    have P236 : S.f236 x' (1 - x') 0 < 0 := by
      have e : S.f236 x' (1 - x') 0 = (1 - μ) * S.f236 S.th (1 - S.th) 0 +
          μ * S.f236 (1 - S.thb) (1 - (1 - S.thb)) 0 := L3_side S.r 1 1 S.th (1 - S.thb) μ
      rw [e, X236]; linarith [mul_neg_of_pos_of_neg hμ0 Y236]
    have P046 : S.f046 x' (1 - x') 0 < 0 := by
      have e : S.f046 x' (1 - x') 0 = (1 - μ) * S.f046 S.th (1 - S.th) 0 +
          μ * S.f046 (1 - S.thb) (1 - (1 - S.thb)) 0 := L3_side 1 S.q 1 S.th (1 - S.thb) μ
      rw [e, Y046]; linarith [mul_neg_of_pos_of_neg (show 0 < 1 - μ by linarith) X046]
    have P025 : S.f025 x' (1 - x') 0 = 1 := by simp only [f025, L3]; ring
    have P235 : 0 ≤ S.f235 x' (1 - x') 0 := by
      by_contra h5
      push Not at h5
      set C := S.f235 S.th (1 - S.th) 0
      set D := S.f235 x' (1 - x') 0
      set ν := C / (C - D) with hν
      have hCD : 0 < C - D := by linarith
      have hν0 : 0 < ν := div_pos X235 hCD
      have hν1 : ν < 1 := by rw [hν, div_lt_one hCD]; linarith
      have hνe : ν * (C - D) = C := by rw [hν, div_mul_cancel₀ _ hCD.ne']
      set z := (1 - ν) * S.th + ν * x' with hz
      have Z235 : S.f235 z (1 - z) 0 = 0 := by
        have e : S.f235 z (1 - z) 0 = (1 - ν) * C + ν * D := L3_side S.s0 1 S.s2 S.th x' ν
        rw [e]; linarith
      have Z4350 : S.f4350 z (1 - z) 0 < 0 := by
        have e : S.f4350 z (1 - z) 0 = (1 - ν) * A + ν * S.f4350 x' (1 - x') 0 :=
          L3_side 1 S.m1 S.m2 S.th x' ν
        rw [e, P4350]; linarith [mul_neg_of_pos_of_neg (show 0 < 1 - ν by linarith) h4X]
      have Z236 : S.f236 z (1 - z) 0 < 0 := by
        have e : S.f236 z (1 - z) 0 = (1 - ν) * S.f236 S.th (1 - S.th) 0 + ν * S.f236 x' (1 - x') 0 :=
          L3_side S.r 1 1 S.th x' ν
        rw [e, X236]; linarith [mul_neg_of_pos_of_neg hν0 P236]
      have Z046 : S.f046 z (1 - z) 0 < 0 := by
        have e : S.f046 z (1 - z) 0 = (1 - ν) * S.f046 S.th (1 - S.th) 0 + ν * S.f046 x' (1 - x') 0 :=
          L3_side 1 S.q 1 S.th x' ν
        rw [e]; linarith [mul_neg_of_pos_of_neg hν0 P046,
          mul_neg_of_pos_of_neg (show 0 < 1 - ν by linarith) X046]
      have Z346 : S.f346 z (1 - z) 0 < 0 := by
        have h := S.v3 z (1 - z) 0
        rw [Z235] at h
        have : S.k4 * S.f346 z (1 - z) 0 < 0 := by
          linarith [mul_neg_of_pos_of_neg S.hk1 Z4350, mul_neg_of_pos_of_neg S.hk3 Z236]
        exact neg_of_mul_neg_right this S.hk4.le
      have Z025 : S.f025 z (1 - z) 0 = 1 := by simp only [f025, L3]; ring
      have hz0 : S.th < z := by linarith [mul_pos hν0 (show 0 < x' - S.th by linarith)]
      have hz1 : z < x' := by
        linarith [mul_pos (show 0 < 1 - ν by linarith) (show 0 < x' - S.th by linarith)]
      obtain ⟨μ', hμ', hμ'0⟩ := ((ev_neg (A := S.s0 - 1) (B := S.s2)
        (Or.inl (by linarith [S.hs0]))).and self_mem_nhdsWithin).exists
      have hμ'0' : (0:ℝ) < μ' := hμ'0
      exact S.no025_pert hNo (x := 1) (y := -1) (z := μ') (Or.inl (by linarith))
        (Or.inl (by linarith)) (Or.inr ⟨le_refl _, hμ'0'⟩) (Or.inl (by rw [Z025]; norm_num))
        (Or.inl Z4350) (Or.inr ⟨Z235.le, by simp only [f235, L3]; linarith⟩) (Or.inl Z046)
        (Or.inl Z236) (Or.inl Z346)
    have P346 : S.f346 x' (1 - x') 0 < 0 := by
      have h := S.v3 x' (1 - x') 0
      rw [P4350] at h
      have : S.k4 * S.f346 x' (1 - x') 0 < 0 := by
        linarith [mul_neg_of_pos_of_neg S.hk3 P236, mul_nonneg S.hk2.le P235]
      exact neg_of_mul_neg_right this S.hk4.le
    exact ⟨x', by linarith, by linarith, by linarith, by linarith, le_refl _, by rw [P025]; norm_num,
      P4350.ge, P235, P046.le, P236.le, P346.le⟩
  · push Not at h4X
    have hc3 : 1 ≤ S.c3 := hX.resolve_left (not_lt.2 h4X)
    -- B1: `P = X`
    refine ⟨S.th, hθ0, by linarith, hθ0.le, by linarith, le_refl _, by rw [X025]; norm_num, h4X,
      X235.le, X046.le, X236.le, ?_⟩
    rw [X346]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu.le (by linarith)) (by linarith [S.hw1])

/-- **Lemma B** (`cl 0234` meets the side `L_012`, every class): a point `P = (x, 1 - x, 0)` of
`cl 0234` with `0 < x < 1` (at `X = 012 × 236`, `012 × 4350` (uses the empty cell `{025}`) or
`012 × 346`). -/
theorem lemB {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1) (hNo : S.No025) :
    ∃ x, 0 < x ∧ x < 1 ∧ S.Cl0234 x (1 - x) 0 := by
  by_cases hX : S.f4350 S.th (1 - S.th) 0 < 0 ∨ 1 ≤ S.c3
  · exact S.lemB_w hR.toW hts hNo hX
  push Not at hX
  have hc3 := hX.2
  obtain ⟨hθ, -, -⟩ := S.R_lt hR.toW hts
  obtain ⟨-, -, hu⟩ := S.u_facts
  have hθ0 := S.th_pos
  have hθ1 : S.th < 1 := by linarith [hR.2.1, hR.2.2.1]
  -- B3: `P = 012 × 346`, between `E36` and the wall end `T` of Lemma A1
  obtain ⟨τ, hτθ, hτt, hτb, -, hT025, hT346, hT4350, hT235, hT236, hT046⟩ :=
    S.a1 hR hts (S.tb346_pos hc3.le)
  obtain ⟨hEs, hE236, hE346, hE4350, hE235, hE046⟩ := S.e36_facts
  set u := S.th / S.a3
  have hk : 0 < S.ga + u * (1 - S.c3) := by
    have h1 := mul_pos hu (show 0 < 1 - S.c3 by linarith)
    linarith [S.ga_pos]
  set l := u * (1 - S.c3) / (S.ga + u * (1 - S.c3)) with hl
  have hl0 : 0 < l := div_pos (mul_pos hu (by linarith)) hk
  have hl1 : l < 1 := by rw [hl, div_lt_one hk]; linarith [S.ga_pos]
  have hle : l * (S.ga + u * (1 - S.c3)) = u * (1 - S.c3) := by rw [hl, div_mul_cancel₀ _ hk.ne']
  have c3z : (1 - l) * (u * (S.c3 - 1)) + l * S.ga = 0 := by linear_combination hle
  have hl1' : 0 < 1 - l := by linarith
  have hE025 : 0 < S.f025 S.th (u * S.b3) (u * (S.c3 - 1)) := by
    have h1 := mul_pos hu (show 0 < 1 - S.c3 by linarith)
    rw [S.f025_eq hEs]
    exact mul_pos (by linarith [S.hp]) (by linarith [S.ga_pos])
  have hA0p : 0 < (1 - l) * S.th + l * τ := by
    linarith [mul_pos hl1' S.th_pos, mul_pos hl0 (show 0 < τ by linarith)]
  have hA0q : (1 - l) * S.th + l * τ < 1 := by
    linarith [mul_pos hl1' (show 0 < 1 - S.th by linarith), mul_pos hl0 (show 0 < 1 - τ by linarith [hR.2.1, hR.2.2.1])]
  have hA1 : (1 - l) * (u * S.b3) + l * (1 - τ - S.ga) = 1 - ((1 - l) * S.th + l * τ) := by
    linear_combination (1 - l) * hEs - c3z
  set A0 := (1 - l) * S.th + l * τ with hA0
  have q : ∀ α β γ' : ℝ, L3 α β γ' A0 (1 - A0) 0 =
      (1 - l) * L3 α β γ' S.th (u * S.b3) (u * (S.c3 - 1)) + l * L3 α β γ' τ (1 - τ - S.ga) S.ga := by
    intro α β γ'
    rw [← L3_cvx, ← hA1, ← c3z]
  refine ⟨A0, hA0p, hA0q, hA0p.le, by linarith, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := q 1 1 S.p
    simp only [f025] at hE025 hT025 ⊢
    rw [this, hT025]; linarith [mul_pos hl1' hE025]
  · have := q 1 S.m1 S.m2
    simp only [f4350] at hE4350 hT4350 ⊢
    rw [this]; linarith [mul_pos hl1' hE4350, mul_pos hl0 hT4350]
  · have := q S.s0 1 S.s2
    simp only [f235] at hE235 hT235 ⊢
    rw [this]; linarith [mul_pos hl1' hE235, mul_pos hl0 hT235]
  · have := q 1 S.q 1
    simp only [f046] at hE046 hT046 ⊢
    rw [this]; linarith [mul_neg_of_pos_of_neg hl1' hE046, mul_neg_of_pos_of_neg hl0 hT046]
  · have := q S.r 1 1
    simp only [f236] at hE236 hT236 ⊢
    rw [this, hE236]; linarith [mul_neg_of_pos_of_neg hl0 hT236]
  · have := q S.w0 S.w1 1
    simp only [f346] at hE346 hT346 ⊢
    rw [this, hE346, hT346]; simp

end Ch24

/-! ## Metric lemmas -/

/-- **Lemma WT, general wall end** (fourth pass, sections B, C; WTg): `T = (τ, 1 - τ - γ, γ)` with
`θ ≤ τ < t_a`, `0 ≤ γ < t_c`, `P = (p, 1 - p, 0)`.  Only `G_ab, G_bc ≤ 0` are used; `b3 ≤ 1` (so the class
boundary `b3 = 1` is included, the strictness comes from `p α_T (t_a - τ) > 0`).  Conclusion:
`z0 < z2` at `T` or `z3 < z2` at `P`. -/
theorem wt_gen (G00 G01 G02 G11 G12 h2 t0 t1 t2 a3 b3 c3 θ s3 τ γ p : ℝ)
    (hh2 : 0 < h2) (r0 : G00 * t0 + G01 * t1 + G02 * t2 = h2)
    (r1 : G01 * t0 + G11 * t1 + G12 * t2 = h2)
    (ht1 : 0 < t1) (ht2 : 0 < t2) (hts : t0 + t1 + t2 = 1)
    (hab : G01 ≤ 0) (hbc : G12 ≤ 0) (hd : 0 < G00 + G11 - 2 * G01)
    (hc3 : 0 < c3) (hb3 : b3 ≤ 1) (hs3 : 0 < s3) (ha3e : a3 = θ * s3)
    (hb3e : b3 = s3 + 1 - θ * s3 - c3) (hθ0 : 0 < θ)
    (hθτ : θ ≤ τ) (hτ : τ < t0) (hγ : 0 ≤ γ) (hγt : γ < t2)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hal : 0 ≤ c3 * t0 - a3 * t2) (halT : 0 < c3 * τ - a3 * γ) :
    (G00 * τ + G01 * (1 - τ - γ) + G02 * γ) - (G01 * τ + G11 * (1 - τ - γ) + G12 * γ) < 0 ∨
      a3 * (G00 * p + G01 * (1 - p)) + (b3 - 1) * (G01 * p + G11 * (1 - p)) +
        c3 * (G02 * p + G12 * (1 - p)) < 0 := by
  have ht1e : t1 = 1 - t0 - t2 := by linarith
  subst ht1e ha3e hb3e
  set ω := τ * t2 - γ * t0 with hω
  by_cases hom : ω ≤ 0
  · left
    have hG11 : 0 < G11 := by
      have h1 : G01 * t0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hab (by linarith)
      have h2' : G12 * t2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hbc ht2.le
      have : 0 < G11 * (1 - t0 - t2) := by linarith
      exact pos_of_mul_pos_left this ht1.le
    have hid : t2 * ((G00 * τ + G01 * (1 - τ - γ) + G02 * γ) - (G01 * τ + G11 * (1 - τ - γ) + G12 * γ))
        = (t2 - γ) * (G01 - G11) + ω * (G00 + G11 - 2 * G01) := by
      rw [hω]; linear_combination γ * (r0 - r1)
    have h1 : (t2 - γ) * (G01 - G11) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have h2' : ω * (G00 + G11 - 2 * G01) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hom hd.le
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg ht2.le hc]
  · push Not at hom
    by_contra hc
    push Not at hc
    obtain ⟨hT, hP⟩ := hc
    have hid : τ * ((1 - t0 - t2) * ((c3 * t0 - θ * s3 * t2) * p *
        ((G00 * τ + G01 * (1 - τ - γ) + G02 * γ) - (G01 * τ + G11 * (1 - τ - γ) + G12 * γ)) +
        ω * (θ * s3 * (G00 * p + G01 * (1 - p)) + (s3 + 1 - θ * s3 - c3 - 1) * (G01 * p + G11 * (1 - p)) +
          c3 * (G02 * p + G12 * (1 - p))))) =
      h2 * (-p * (c3 * τ - θ * s3 * γ) * (t0 - τ) +
          ω * (p * s3 * (θ - τ) - τ * (1 - (s3 + 1 - θ * s3 - c3))))
      + τ * G01 * ((t0 + (1 - t0 - t2)) * p * ((t0 - τ) * (c3 - γ * s3) - (t2 - γ) * s3 * (θ - τ)) +
          ω * (θ * s3 * (1 - t0 - t2) + (1 - (s3 + 1 - θ * s3 - c3)) * t0))
      + τ * G12 * ((c3 * t0 - θ * s3 * t2) * p * (t2 * (1 - τ - γ) - (1 - t0 - t2) * γ) +
          ω * (1 - p) * ((1 - (s3 + 1 - θ * s3 - c3)) * t2 + c3 * (1 - t0 - t2))) := by
      rw [hω]
      linear_combination (τ * ((1 - t0 - t2) * p * (c3 * τ - θ * s3 * γ))) * r0 +
        (τ * (-(c3 * t0 - θ * s3 * t2) * p * (1 - τ - γ) +
          (τ * t2 - γ * t0) * ((s3 + 1 - θ * s3 - c3) - 1) * (1 - p))) * r1
    have hτ0 : 0 < τ := by linarith
    have hb : 0 ≤ 1 - (s3 + 1 - θ * s3 - c3) := by linarith
    have hC : 0 < c3 - γ * s3 := by
      have : c3 - γ * s3 = s3 * (1 - θ - γ) + (1 - (s3 + 1 - θ * s3 - c3)) := by ring
      rw [this]; linarith [mul_pos hs3 (show (0:ℝ) < 1 - θ - γ by linarith)]
    have hΦ : -p * (c3 * τ - θ * s3 * γ) * (t0 - τ) +
        ω * (p * s3 * (θ - τ) - τ * (1 - (s3 + 1 - θ * s3 - c3))) < 0 := by
      have e1 : 0 < p * (c3 * τ - θ * s3 * γ) * (t0 - τ) :=
        mul_pos (mul_pos hp0 halT) (by linarith)
      have e2 : p * s3 * (θ - τ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_pos hp0 hs3).le (by linarith)
      have e3 : 0 ≤ τ * (1 - (s3 + 1 - θ * s3 - c3)) := mul_nonneg hτ0.le hb
      have e4 := mul_nonpos_of_nonneg_of_nonpos hom.le
        (show p * s3 * (θ - τ) - τ * (1 - (s3 + 1 - θ * s3 - c3)) ≤ 0 by linarith)
      linarith
    have hK1 : 0 ≤ (t0 + (1 - t0 - t2)) * p * ((t0 - τ) * (c3 - γ * s3) - (t2 - γ) * s3 * (θ - τ)) +
        ω * (θ * s3 * (1 - t0 - t2) + (1 - (s3 + 1 - θ * s3 - c3)) * t0) := by
      have e1 : 0 ≤ (t0 - τ) * (c3 - γ * s3) := mul_nonneg (by linarith) hC.le
      have e2 : 0 ≤ (t2 - γ) * s3 * (τ - θ) := mul_nonneg (mul_nonneg (by linarith) hs3.le) (by linarith)
      have e3 : 0 ≤ θ * s3 * (1 - t0 - t2) := mul_nonneg (mul_pos hθ0 hs3).le ht1.le
      have e4 : 0 ≤ (1 - (s3 + 1 - θ * s3 - c3)) * t0 := mul_nonneg hb (by linarith)
      have e5 : 0 ≤ (t0 + (1 - t0 - t2)) * p := mul_nonneg (by linarith) hp0.le
      have e6 : 0 ≤ (t0 + (1 - t0 - t2)) * p * ((t0 - τ) * (c3 - γ * s3) - (t2 - γ) * s3 * (θ - τ)) :=
        mul_nonneg e5 (by linarith [show (t2 - γ) * s3 * (θ - τ) = -((t2 - γ) * s3 * (τ - θ)) by ring])
      have e7 : 0 ≤ ω * (θ * s3 * (1 - t0 - t2) + (1 - (s3 + 1 - θ * s3 - c3)) * t0) :=
        mul_nonneg hom.le (by linarith)
      linarith
    have hK2 : 0 ≤ (c3 * t0 - θ * s3 * t2) * p * (t2 * (1 - τ - γ) - (1 - t0 - t2) * γ) +
        ω * (1 - p) * ((1 - (s3 + 1 - θ * s3 - c3)) * t2 + c3 * (1 - t0 - t2)) := by
      have hβ : 0 < t2 * (1 - τ - γ) - (1 - t0 - t2) * γ := by
        have : t2 * (1 - τ - γ) - (1 - t0 - t2) * γ = (t2 - γ) * (1 - τ - γ) + γ * ((t0 - τ) + (t2 - γ)) := by
          ring
        rw [this]; linarith [mul_pos (show (0:ℝ) < t2 - γ by linarith) (show (0:ℝ) < 1 - τ - γ by linarith),
          mul_nonneg hγ (show (0:ℝ) ≤ (t0 - τ) + (t2 - γ) by linarith)]
      have e1 : 0 ≤ (c3 * t0 - θ * s3 * t2) * p * (t2 * (1 - τ - γ) - (1 - t0 - t2) * γ) :=
        mul_nonneg (mul_nonneg hal hp0.le) hβ.le
      have e2 : 0 ≤ (1 - (s3 + 1 - θ * s3 - c3)) * t2 + c3 * (1 - t0 - t2) := by
        linarith [mul_nonneg hb ht2.le, mul_nonneg hc3.le ht1.le]
      have e3 : 0 ≤ ω * (1 - p) * ((1 - (s3 + 1 - θ * s3 - c3)) * t2 + c3 * (1 - t0 - t2)) :=
        mul_nonneg (mul_nonneg hom.le (by linarith)) e2
      linarith
    have hL : 0 ≤ τ * ((1 - t0 - t2) * ((c3 * t0 - θ * s3 * t2) * p *
        ((G00 * τ + G01 * (1 - τ - γ) + G02 * γ) - (G01 * τ + G11 * (1 - τ - γ) + G12 * γ)) +
        ω * (θ * s3 * (G00 * p + G01 * (1 - p)) + (s3 + 1 - θ * s3 - c3 - 1) * (G01 * p + G11 * (1 - p)) +
          c3 * (G02 * p + G12 * (1 - p))))) := by
      apply mul_nonneg hτ0.le
      apply mul_nonneg ht1.le
      exact add_nonneg (mul_nonneg (mul_nonneg hal hp0.le) hT) (mul_nonneg hom.le hP)
    rw [hid] at hL
    have := mul_neg_of_pos_of_neg hh2 hΦ
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hτ0.le hab) hK1
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hτ0.le hbc) hK2
    linarith

/-- Real core of Lemma CA (strict Cauchy-Schwarz `C² < A B`). -/
theorem ca_core {A B C db dc eb ec : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : C ^ 2 < A * B)
    (hdb : 0 ≤ db) (hdc : dc < 0) (heb : eb < 0) (hD : dc * eb ≤ db * ec) :
    0 < db * A + dc * C ∨ 0 < eb * C + ec * B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hpos : 0 < dc * eb := mul_pos_of_neg_of_neg hdc heb
  have hdbec : 0 < db * ec := lt_of_lt_of_le hpos hD
  have hdb' : 0 < db := lt_of_le_of_ne hdb (by rintro rfl; simp at hdbec)
  have hec : 0 < ec := by
    by_contra h; push Not at h; nlinarith
  have hc : 0 < C := by
    by_contra h; push Not at h; nlinarith [mul_pos hdb' hA]
  have e1 : db * A ≤ (-dc) * C := by linarith
  have e2 : ec * B ≤ (-eb) * C := by linarith
  have e3 : (db * A) * (ec * B) ≤ ((-dc) * C) * ((-eb) * C) :=
    mul_le_mul e1 e2 (by positivity) (by nlinarith)
  have e4 : (dc * eb) * C ^ 2 ≤ (db * ec) * C ^ 2 :=
    mul_le_mul_of_nonneg_right hD (by positivity)
  have : (db * ec) * (A * B - C ^ 2) ≤ 0 := by nlinarith
  have := mul_pos hdbec (sub_pos.2 hC)
  linarith

/-- **Lemma CA, chart form.**  `G t = h2 (1,1,1)`; `A = |x2 - x0|²`, `B = |x6 - x0|²`,
`C = <x2 - x0, x6 - x0>` in Gram entries; `P`, `P'` chart points (sum 1), `d = P - t`, `e = P' - t`.
Then `z0 < z2` at `P` or `z0 < z6` at `P'`. -/
theorem ca_chart (G00 G01 G02 G11 G12 G22 h2 t0 t1 t2 P0 P1 P2 Q0 Q1 Q2 : ℝ)
    (r0 : G00 * t0 + G01 * t1 + G02 * t2 = h2) (r1 : G01 * t0 + G11 * t1 + G12 * t2 = h2)
    (r2 : G02 * t0 + G12 * t1 + G22 * t2 = h2)
    (hA : 0 < G00 - 2 * G01 + G11) (hB : 0 < G00 - 2 * G02 + G22)
    (hC : (G00 - G01 - G02 + G12) ^ 2 < (G00 - 2 * G01 + G11) * (G00 - 2 * G02 + G22))
    (hts : t0 + t1 + t2 = 1) (hP : P0 + P1 + P2 = 1) (hQ : Q0 + Q1 + Q2 = 1)
    (hdb : t1 ≤ P1) (hdc : P2 < t2) (heb : Q1 < t1)
    (hD : (P2 - t2) * (Q1 - t1) ≤ (P1 - t1) * (Q2 - t2)) :
    G00 * P0 + G01 * P1 + G02 * P2 < G01 * P0 + G11 * P1 + G12 * P2 ∨
      G00 * Q0 + G01 * Q1 + G02 * Q2 < G02 * Q0 + G12 * Q1 + G22 * Q2 := by
  rcases ca_core hA hB hC (sub_nonneg.2 hdb) (sub_neg.2 hdc) (sub_neg.2 heb) hD with h | h
  · left
    have : (G01 * P0 + G11 * P1 + G12 * P2) - (G00 * P0 + G01 * P1 + G02 * P2) =
        (P1 - t1) * (G00 - 2 * G01 + G11) + (P2 - t2) * (G00 - G01 - G02 + G12) := by
      have hP0 : P0 = 1 - P1 - P2 := by linarith
      have ht0 : t0 = 1 - t1 - t2 := by linarith
      subst hP0 ht0
      linear_combination r1 - r0
    linarith
  · right
    have : (G02 * Q0 + G12 * Q1 + G22 * Q2) - (G00 * Q0 + G01 * Q1 + G02 * Q2) =
        (Q1 - t1) * (G00 - G01 - G02 + G12) + (Q2 - t2) * (G00 - 2 * G02 + G22) := by
      have hQ0 : Q0 = 1 - Q1 - Q2 := by linarith
      have ht0 : t0 = 1 - t1 - t2 := by linarith
      subst hQ0 ht0
      linear_combination r2 - r0
    linarith

/-! ## Assembly -/

/-- **Lemma TQ, chart form** (frame `04325`).  `t` is the orthocentre chart point, in the region
`R = 04325`; the 3-rim cells `{235}`, `{346}`, `{025}` are empty.  Metric: `G t = h2 (1,1,1)`, `G_ab, G_bc ≤ 0` (no condition on `G_ac`),
and the strict Cauchy-Schwarz inequality for the edges `x2 - x0`, `x6 - x0`.  Then one closed-cell
point of `0234` has `z0 < z2` or `z3 < z2` (and `0234` is open), or one closed-cell point of `0536`
has `z0 < z6` (and `0536` is open).  Depths relative to `x1`: `(G g)_0, (G g)_1, (G g)_2` for
`x0, x2, x6` and `a3 (G g)_0 + b3 (G g)_1 + c3 (G g)_2` for `x3`. -/
theorem tq_chart (S : Ch24) {t0 t1 t2 : ℝ} (hR : S.InR t0 t1 t2) (hts : t0 + t1 + t2 = 1)
    (hNo235 : S.No235) (hNo346 : S.No346) (hNo025 : S.No025)
    {G00 G01 G02 G11 G12 G22 h2 : ℝ} (hh2 : 0 < h2)
    (r0 : G00 * t0 + G01 * t1 + G02 * t2 = h2) (r1 : G01 * t0 + G11 * t1 + G12 * t2 = h2)
    (r2 : G02 * t0 + G12 * t1 + G22 * t2 = h2) (hab : G01 ≤ 0) (hbc : G12 ≤ 0)
    (hA : 0 < G00 - 2 * G01 + G11) (hB : 0 < G00 - 2 * G02 + G22)
    (hC : (G00 - G01 - G02 + G12) ^ 2 < (G00 - 2 * G01 + G11) * (G00 - 2 * G02 + G22)) :
    ((∃ a b c, S.Op0234 a b c) ∧ ∃ g0 g1 g2, S.Cl0234 g0 g1 g2 ∧
        (G00 * g0 + G01 * g1 + G02 * g2 < G01 * g0 + G11 * g1 + G12 * g2 ∨
          S.a3 * (G00 * g0 + G01 * g1 + G02 * g2) + S.b3 * (G01 * g0 + G11 * g1 + G12 * g2) +
            S.c3 * (G02 * g0 + G12 * g1 + G22 * g2) < G01 * g0 + G11 * g1 + G12 * g2)) ∨
      ((∃ a b c, S.Op0536 a b c) ∧ ∃ g0 g1 g2, S.Cl0536 g0 g1 g2 ∧
        G00 * g0 + G01 * g1 + G02 * g2 < G02 * g0 + G12 * g1 + G22 * g2) := by
  obtain ⟨hθ, hθb, hγ⟩ := S.R_lt hR.toW hts
  obtain ⟨ht0, ht1, ht2, h4350t, h235t, h025t, h046t, h236t, h346t⟩ := id hR
  have hop := S.wall_open hR hts hNo235
  rcases le_or_gt S.b3 1 with hb3 | hb3
  · -- class `b3 ≤ 1`: Lemma WT on `0234`
    left
    refine ⟨hop, ?_⟩
    obtain ⟨τ, hθτ, hτt, hTcl, hT235, hT236⟩ : ∃ τ, S.th ≤ τ ∧ τ < t0 ∧
        S.Cl0234 τ (1 - τ - S.ga) S.ga ∧ 0 < S.f235 τ (1 - τ - S.ga) S.ga ∧
        S.f236 τ (1 - τ - S.ga) S.ga ≤ 0 := by
      by_cases h : 0 < S.f346 S.th (1 - S.th - S.ga) S.ga
      · obtain ⟨τ, h1, h2, h3, -, h025, h346, h4350, h235, h236, h046⟩ := S.a1 hR hts h
        exact ⟨τ, h1.le, h2, ⟨by linarith [S.th_pos], h3.le, S.ga_pos.le, h025.ge, h4350.le,
          h235.le, h046.le, h236.le, h346.le⟩, h235, h236.le⟩
      · push Not at h
        obtain ⟨h4350, h235, h046⟩ := S.a1' hR hts hNo235 h
        have h025 : S.f025 S.th (1 - S.th - S.ga) S.ga = 0 := by rw [S.f025_eq (by ring)]; ring
        have h236 : S.f236 S.th (1 - S.th - S.ga) S.ga = 0 := by rw [S.f236_eq (by ring)]; ring
        exact ⟨S.th, le_refl _, hθ, ⟨S.th_pos.le, by linarith, S.ga_pos.le, h025.ge, h4350,
          h235.le, h046.le, h236.le, h⟩, h235, h236.le⟩
    obtain ⟨x, hx0, hx1, hPcl⟩ := S.lemB hR hts hNo025
    have hs2 : 0 < 1 - S.s2 := by linarith [S.hs2]
    have hal : 0 ≤ S.c3 * t0 - S.a3 * t2 := by
      have h := S.e23 t0 t1 t2
      have : 0 < S.a3 * (S.f235 t0 t1 t2 - S.f236 t0 t1 t2) := mul_pos S.ha3 (by linarith)
      rw [h] at this
      exact (pos_of_mul_pos_right this hs2.le).le
    have halT : 0 < S.c3 * τ - S.a3 * S.ga := by
      have h := S.e23 τ (1 - τ - S.ga) S.ga
      have : 0 < S.a3 * (S.f235 τ (1 - τ - S.ga) S.ga - S.f236 τ (1 - τ - S.ga) S.ga) :=
        mul_pos S.ha3 (by linarith)
      rw [h] at this
      exact pos_of_mul_pos_right this hs2.le
    rcases wt_gen G00 G01 G02 G11 G12 h2 t0 t1 t2 S.a3 S.b3 S.c3 S.th (S.a3 + S.b3 + S.c3 - 1) τ S.ga x
        hh2 r0 r1 ht1 ht2 hts hab hbc (by linarith) S.hc3 hb3 S.s3_pos S.th_s3.symm
        (by linarith [S.th_s3]) S.th_pos hθτ hτt S.ga_pos.le hγ hx0 hx1.le hal halT with h | h
    · exact ⟨τ, 1 - τ - S.ga, S.ga, hTcl, Or.inl (by linarith)⟩
    · exact ⟨x, 1 - x, 0, hPcl, Or.inr (by linarith)⟩
  · -- class `b3 > 1`: Lemma CA (TL or CX)
    obtain ⟨y', z', hs', hP'⟩ := S.a2_closed hR.toW hts hNo346 hb3.le
    have hop' := S.a2_open hR.toW hts hNo346 hb3
    have hy' : y' ≤ S.thb := by
      have h := hP'.2.2.2.1
      rw [S.f046_eq hs'] at h
      by_contra hc; push Not at hc
      nlinarith [mul_pos (show 0 < 1 - S.q by linarith [S.hq]) (show 0 < y' - S.thb by linarith)]
    have hz' : S.ga ≤ z' := by
      have h := hP'.2.2.2.2.2.2.1
      rw [S.f025_eq hs'] at h
      by_contra hc; push Not at hc
      nlinarith [mul_pos (show 0 < 1 - S.p by linarith [S.hp]) (show 0 < S.ga - z' by linarith)]
    rcases le_or_gt 1 S.c3 with hc3 | hc3
    · -- TL: both points on `L_236`
      obtain ⟨y, z, hs, hP⟩ := S.a2m_closed hR hts hNo235 hc3
      have hz : z ≤ S.ga := by
        have h := hP.2.2.2.1
        rw [S.f025_eq hs] at h
        by_contra hc; push Not at hc
        nlinarith [mul_pos (show 0 < 1 - S.p by linarith [S.hp]) (show 0 < z - S.ga by linarith)]
      have hD : (z - t2) * (y' - t1) ≤ (y - t1) * (z' - t2) := by
        have ey : y - t1 = (t0 - S.th) + (t2 - z) := by linarith
        have ez : z' - t2 = (t0 - S.th) + (t1 - y') := by linarith
        rw [ey, ez]
        nlinarith [mul_pos (show 0 < t0 - S.th by linarith) (show 0 < t0 - S.th by linarith),
          mul_pos (show 0 < t0 - S.th by linarith) (show 0 < t1 - y' by linarith),
          mul_pos (show 0 < t2 - z by linarith) (show 0 < t0 - S.th by linarith)]
      rcases ca_chart G00 G01 G02 G11 G12 G22 h2 t0 t1 t2 S.th y z S.th y' z' r0 r1 r2 hA hB hC hts
          hs hs' (by linarith) (by linarith) (by linarith) hD with h | h
      · exact Or.inl ⟨hop, S.th, y, z, hP, Or.inl h⟩
      · exact Or.inr ⟨hop', S.th, y', z', hP', h⟩
    · -- CX: the wall end `025 × 346` against `P'`
      obtain ⟨τ, hτθ, hτt, hτb, hw01, hT025, hT346, hT4350, hT235, hT236, hT046⟩ :=
        S.a1 hR hts (S.tb346_pos hc3.le)
      have hTcl : S.Cl0234 τ (1 - τ - S.ga) S.ga := ⟨by linarith [S.th_pos], hτb.le, S.ga_pos.le,
        hT025.ge, hT4350.le, hT235.le, hT046.le, hT236.le, hT346.le⟩
      have hU : (S.w1 - S.w0) * (t1 - (1 - τ - S.ga)) + (1 - S.w0) * (t2 - S.ga) =
          S.f346 t0 t1 t2 - S.f346 τ (1 - τ - S.ga) S.ga := by
        simp only [Ch24.f346, L3]; linear_combination (-S.w0) * hts
      have hV : (S.w1 - S.w0) * (y' - (1 - τ - S.ga)) + (1 - S.w0) * (z' - S.ga) =
          S.f346 S.th y' z' - S.f346 τ (1 - τ - S.ga) S.ga := by
        simp only [Ch24.f346, L3]; linear_combination (-S.w0) * hs'
      have hV0 := hP'.2.2.2.2.2.1
      rw [hT346] at hU hV
      have hWD : 0 ≤ (S.w1 - S.w0) * ((t2 - S.ga) * (y' - (1 - τ - S.ga)) -
          (t1 - (1 - τ - S.ga)) * (z' - S.ga)) := by
        linarith [mul_nonneg (show 0 ≤ t2 - S.ga by linarith) (show 0 ≤ (S.w1 - S.w0) * (y' - (1 - τ - S.ga)) +
          (1 - S.w0) * (z' - S.ga) by linarith), mul_nonneg (show 0 ≤ z' - S.ga by linarith)
          (show 0 ≤ -((S.w1 - S.w0) * (t1 - (1 - τ - S.ga)) + (1 - S.w0) * (t2 - S.ga)) by linarith)]
      have hD0 : 0 ≤ (t2 - S.ga) * (y' - (1 - τ - S.ga)) - (t1 - (1 - τ - S.ga)) * (z' - S.ga) := by
        exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hWD) (by linarith)
      have hD : (S.ga - t2) * (y' - t1) ≤ ((1 - τ - S.ga) - t1) * (z' - t2) := by linarith
      rcases ca_chart G00 G01 G02 G11 G12 G22 h2 t0 t1 t2 τ (1 - τ - S.ga) S.ga S.th y' z' r0 r1 r2
          hA hB hC hts (by ring) hs' (by linarith) hγ (by linarith) hD with h | h
      · exact Or.inl ⟨hop, τ, 1 - τ - S.ga, S.ga, hTcl, Or.inl h⟩
      · exact Or.inr ⟨hop', S.th, y', z', hP', h⟩

end Minimality.T24.TQ
