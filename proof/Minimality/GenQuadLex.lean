module

public import Minimality.GenQuadCross

@[expose] public section

/-!
# Lexicographic front lemma (edge-on facets)

`FrontOf p q r s v` (segment `p q` in front of `r s` along the direction `v`) gives the lex clause at any
`(b, d1, d2)` for which `v` is lex positive: `LexPos3 ⟪v,b⟫ ⟪v,d1⟫ ⟪v,d2⟫` (`frontOf_lex`).  With `v = b + ε d1` this
is the tilt `b → b + ε d1` that decides an edge-on facet.  `FrontDetLex` is `FrontDet` with every sign condition
read lexicographically on the pair (value at `b`, value at `d1`); `lexClause_of_frontDetLex` turns it into the clause.
Only the pair `(b, d1)` is ever used: a front needing `d2` is a quadruple whose `det3` values vanish at both `b`
and `d1` (see the report).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.LexCell Minimality.H21 Filter Topology

namespace Minimality.GenQuad

/-- A weighted lex-nonnegative triple stays lex-nonnegative (levelwise form). -/
theorem pair_lex {w d1 d2 d3 : ℝ} (hw : 0 ≤ w) (h1 : 0 ≤ d1) (h2 : d1 = 0 → 0 ≤ d2)
    (h3 : d1 = 0 → d2 = 0 → 0 ≤ d3) :
    0 ≤ w * d1 ∧ (w * d1 = 0 → 0 ≤ w * d2) ∧ (w * d1 = 0 → w * d2 = 0 → 0 ≤ w * d3) := by
  rcases hw.eq_or_lt with h | h
  · subst h; simp
  · refine ⟨mul_nonneg hw h1, fun e => ?_, fun e e' => ?_⟩
    · have : d1 = 0 := by
        rcases mul_eq_zero.1 e with h' | h'
        · exact absurd h' h.ne'
        · exact h'
      exact mul_nonneg hw (h2 this)
    · have : d1 = 0 := by
        rcases mul_eq_zero.1 e with h' | h'
        · exact absurd h' h.ne'
        · exact h'
      have : d2 = 0 := by
        rcases mul_eq_zero.1 e' with h' | h'
        · exact absurd h' h.ne'
        · exact h'
      exact mul_nonneg hw (h3 (by assumption) this)

/-- Four lex-nonnegative weighted triples cannot sum to `-η v` with `v` lex positive. -/
theorem sum4_lex {a1 a2 a3 b1 b2 b3 c1 c2 c3 e1 e2 e3 v1 v2 v3 eta : ℝ} (he : 0 < eta)
    (ha : 0 ≤ a1 ∧ (a1 = 0 → 0 ≤ a2) ∧ (a1 = 0 → a2 = 0 → 0 ≤ a3))
    (hb : 0 ≤ b1 ∧ (b1 = 0 → 0 ≤ b2) ∧ (b1 = 0 → b2 = 0 → 0 ≤ b3))
    (hc : 0 ≤ c1 ∧ (c1 = 0 → 0 ≤ c2) ∧ (c1 = 0 → c2 = 0 → 0 ≤ c3))
    (hd : 0 ≤ e1 ∧ (e1 = 0 → 0 ≤ e2) ∧ (e1 = 0 → e2 = 0 → 0 ≤ e3))
    (s1 : a1 + b1 + c1 + e1 = -(eta * v1)) (s2 : a2 + b2 + c2 + e2 = -(eta * v2))
    (s3 : a3 + b3 + c3 + e3 = -(eta * v3)) (hv : LexPos3 v1 v2 v3) : False := by
  obtain ⟨a1', a2', a3'⟩ := ha
  obtain ⟨b1', b2', b3'⟩ := hb
  obtain ⟨c1', c2', c3'⟩ := hc
  obtain ⟨e1', e2', e3'⟩ := hd
  rcases hv with hv1 | ⟨hv1, hv2 | ⟨hv2, hv3⟩⟩
  · nlinarith [mul_pos he hv1]
  · have h0 : eta * v1 = 0 := by rw [hv1]; ring
    have z : a1 = 0 ∧ b1 = 0 ∧ c1 = 0 ∧ e1 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    obtain ⟨z1, z2, z3, z4⟩ := z
    nlinarith [mul_pos he hv2, a2' z1, b2' z2, c2' z3, e2' z4]
  · have h0 : eta * v1 = 0 := by rw [hv1]; ring
    have h0' : eta * v2 = 0 := by rw [hv2]; ring
    have z : a1 = 0 ∧ b1 = 0 ∧ c1 = 0 ∧ e1 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    obtain ⟨z1, z2, z3, z4⟩ := z
    have y : a2 = 0 ∧ b2 = 0 ∧ c2 = 0 ∧ e2 = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [a2' z1, b2' z2, c2' z3, e2' z4]
    obtain ⟨y1, y2, y3, y4⟩ := y
    nlinarith [mul_pos he hv3, a3' z1 y1, b3' z2 y2, c3' z3 y3, e3' z4 y4]

/-- **Lex front lemma.** `p q` in front of `r s` along a direction `v` that is lex positive at `(b, d1, d2)` gives the
clause of the quadruple at `(b, d1, d2)`. -/
theorem frontOf_lex {p q r s v b d1 d2 : ℝ³} (h : FrontOf p q r s v)
    (hv : LexPos3 ⟪v, b⟫ ⟪v, d1⟫ ⟪v, d2⟫) : LexClause p q r s b d1 d2 := by
  obtain ⟨lam, mu, eta, hl0, hl1, hm0, hm1, he, hz⟩ := h
  by_contra hn
  unfold LexClause LexLt3 at hn
  simp only [not_or] at hn
  obtain ⟨n1, n2, n3, n4⟩ := hn
  obtain ⟨a1, a2, a3⟩ := neg_lexPos3 n1
  obtain ⟨b1, b2, b3⟩ := neg_lexPos3 n2
  obtain ⟨c1, c2, c3⟩ := neg_lexPos3 n3
  obtain ⟨e1, e2, e3⟩ := neg_lexPos3 n4
  have wpr : 0 ≤ lam * mu := mul_nonneg hl0 hm0
  have wps : 0 ≤ lam * (1 - mu) := mul_nonneg hl0 (sub_nonneg.2 hm1)
  have wqr : 0 ≤ (1 - lam) * mu := mul_nonneg (sub_nonneg.2 hl1) hm0
  have wqs : 0 ≤ (1 - lam) * (1 - mu) := mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hm1)
  have comp : ∀ w : ℝ³, lam * ⟪p, w⟫ + (1 - lam) * ⟪q, w⟫ =
      mu * ⟪r, w⟫ + (1 - mu) * ⟪s, w⟫ + eta * ⟪v, w⟫ := by
    intro w
    have := congrArg (fun y => ⟪y, w⟫) hz
    simpa only [inner_add_left, inner_smul_left, conj_trivial] using this
  have k0 := comp b
  have k1 := comp d1
  have k2 := comp d2
  refine sum4_lex (a1 := lam * mu * (⟪r, b⟫ - ⟪p, b⟫)) (a2 := lam * mu * (⟪r, d1⟫ - ⟪p, d1⟫))
    (a3 := lam * mu * (⟪r, d2⟫ - ⟪p, d2⟫))
    (b1 := lam * (1 - mu) * (⟪s, b⟫ - ⟪p, b⟫)) (b2 := lam * (1 - mu) * (⟪s, d1⟫ - ⟪p, d1⟫))
    (b3 := lam * (1 - mu) * (⟪s, d2⟫ - ⟪p, d2⟫))
    (c1 := (1 - lam) * mu * (⟪r, b⟫ - ⟪q, b⟫)) (c2 := (1 - lam) * mu * (⟪r, d1⟫ - ⟪q, d1⟫))
    (c3 := (1 - lam) * mu * (⟪r, d2⟫ - ⟪q, d2⟫))
    (e1 := (1 - lam) * (1 - mu) * (⟪s, b⟫ - ⟪q, b⟫)) (e2 := (1 - lam) * (1 - mu) * (⟪s, d1⟫ - ⟪q, d1⟫))
    (e3 := (1 - lam) * (1 - mu) * (⟪s, d2⟫ - ⟪q, d2⟫)) he
    (pair_lex wpr (by linarith) (fun h => by linarith [a2 (by linarith)])
      (fun h h' => by linarith [a3 (by linarith) (by linarith)]))
    (pair_lex wps (by linarith) (fun h => by linarith [b2 (by linarith)])
      (fun h h' => by linarith [b3 (by linarith) (by linarith)]))
    (pair_lex wqr (by linarith) (fun h => by linarith [c2 (by linarith)])
      (fun h h' => by linarith [c3 (by linarith) (by linarith)]))
    (pair_lex wqs (by linarith) (fun h => by linarith [e2 (by linarith)])
      (fun h h' => by linarith [e3 (by linarith) (by linarith)]))
    ?_ ?_ ?_ hv
  · linear_combination -k0
  · linear_combination -k1
  · linear_combination -k2


/-! ### Lexicographic sign conditions and the tilt `b + ε d1` -/

/-- `0 < A + ε B` for the small tilts `ε > 0`: `A > 0`, or `A = 0` and `B > 0`. -/
def Pos2 (A B : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ 0 < B)

/-- `0 ≤ A + ε B` for the small tilts `ε > 0`: `A > 0`, or `A = 0` and `B ≥ 0`. -/
def Nn2 (A B : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ 0 ≤ B)

theorem ev_pos {A B : ℝ} (h : Pos2 A B) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < A + ε * B := by
  rcases h with hA | ⟨hA, hB⟩
  · have hc : ContinuousAt (fun ε : ℝ => A + ε * B) 0 := by fun_prop
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < A + ε * B :=
      hc.eventually (lt_mem_nhds (show 0 < A + 0 * B by simpa using hA))
    exact this.filter_mono nhdsWithin_le_nhds
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have : 0 < ε := hε
    rw [hA]; positivity

theorem ev_nn {A B : ℝ} (h : Nn2 A B) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ A + ε * B := by
  rcases h with hA | ⟨hA, hB⟩
  · exact (ev_pos (Or.inl hA)).mono fun _ h => h.le
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have : 0 < ε := hε
    rw [hA]; positivity

theorem det3_tilt (u w b d : ℝ³) (ε : ℝ) :
    Split.det3 u w (b + ε • d) = Split.det3 u w b + ε * Split.det3 u w d := by
  simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- `FrontDet` read lexicographically on the pair (value at `b`, value at `d1`) for the four `det3` values that
involve the view; the volume `det3 (p-q) (r-s) (s-q)` is view independent and stays an honest sign. -/
def FrontDetLex (p q r s b d1 : ℝ³) : Prop :=
  (Pos2 (Split.det3 (p - q) (r - s) b) (Split.det3 (p - q) (r - s) d1) ∧
    Nn2 (Split.det3 (s - q) (r - s) b) (Split.det3 (s - q) (r - s) d1) ∧
    Nn2 (Split.det3 (p - q) (r - s) b - Split.det3 (s - q) (r - s) b)
      (Split.det3 (p - q) (r - s) d1 - Split.det3 (s - q) (r - s) d1) ∧
    Nn2 (-Split.det3 (p - q) (s - q) b) (-Split.det3 (p - q) (s - q) d1) ∧
    Nn2 (Split.det3 (p - q) (r - s) b + Split.det3 (p - q) (s - q) b)
      (Split.det3 (p - q) (r - s) d1 + Split.det3 (p - q) (s - q) d1) ∧
    Split.det3 (p - q) (r - s) (s - q) < 0) ∨
  (Pos2 (-Split.det3 (p - q) (r - s) b) (-Split.det3 (p - q) (r - s) d1) ∧
    Nn2 (-Split.det3 (s - q) (r - s) b) (-Split.det3 (s - q) (r - s) d1) ∧
    Nn2 (Split.det3 (s - q) (r - s) b - Split.det3 (p - q) (r - s) b)
      (Split.det3 (s - q) (r - s) d1 - Split.det3 (p - q) (r - s) d1) ∧
    Nn2 (Split.det3 (p - q) (s - q) b) (Split.det3 (p - q) (s - q) d1) ∧
    Nn2 (-Split.det3 (p - q) (s - q) b - Split.det3 (p - q) (r - s) b)
      (-Split.det3 (p - q) (s - q) d1 - Split.det3 (p - q) (r - s) d1) ∧
    0 < Split.det3 (p - q) (r - s) (s - q))

theorem frontDet_tilt {p q r s b d1 : ℝ³} (h : FrontDetLex p q r s b d1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), FrontDet p q r s (b + ε • d1) := by
  unfold FrontDet
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · filter_upwards [ev_pos h1, ev_nn h2, ev_nn h3, ev_nn h4, ev_nn h5] with ε e1 e2 e3 e4 e5
    left
    simp only [det3_tilt] at *
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, h6⟩
  · filter_upwards [ev_pos h1, ev_nn h2, ev_nn h3, ev_nn h4, ev_nn h5] with ε e1 e2 e3 e4 e5
    right
    simp only [det3_tilt] at *
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, h6⟩

/-- **Lex front lemma from determinant signs.** Lexicographic signs of the four `det3` values at `(b, d1)` give the
clause of the quadruple at `(b, d1, d2)` for every `d2` (no third level is used). -/
theorem lexClause_of_frontDetLex {p q r s b d1 : ℝ³} (d2 : ℝ³) (hb : b ≠ 0)
    (h : FrontDetLex p q r s b d1) : LexClause p q r s b d1 d2 := by
  have hbb : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hb
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪b, b⟫ + ε * ⟪d1, b⟫ := ev_pos (Or.inl hbb)
  obtain ⟨ε, h1, h2⟩ := ((frontDet_tilt h).and hpos).exists
  refine frontOf_lex (v := b + ε • d1) h1.frontOf (Or.inl ?_)
  simpa only [inner_add_left, inner_smul_left, conj_trivial] using h2

end Minimality.GenQuad
