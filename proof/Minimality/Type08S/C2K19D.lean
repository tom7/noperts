module

public import Minimality.Type08S.C2K19C

@[expose] public section


/-!
# K19 / D: the S1.7 tie `⟪a-d,c-d⟫ = 0` (L11): Pa(2), `β1 = 1`, `b' = c` at `d - b`, `pq = 0`

With `pq = pr = 0` the view `a - d` is the normal of the face `F = (d,b,a',c)` (bottom plateau at depth 0), and
`a, c'` tie at the top.  The tilt `v` restricted to `F` is the Euclidean direction `v` in the face plane.  With
`A = a'-c`, `B = a'-b` (edges at `a'`, `q = b-d`, `r = c-d`):
* pentagon `(a,d,b,a',b')` (`k17fPent`, frame `(b-d, c-d, a-d)`) needs `b` not a w-local max on `d,b,a'`:
  `⟪q,v⟫ < 0 ∨ ⟪B,v⟫ > 0`; its TS cone is `cone(A, -B)` (β6 < 1) / `cone(A, -r)` (β6 ≥ 1);
* hexagon `(a,b',c,a',b,c')` (`k17fHex`, frame `(c-d, b-d, a-d)`) needs `a'` not a w-local max on `c,a',b`:
  `⟪A,v⟫ < 0 ∨ ⟪B,v⟫ < 0`; its TS cone is `cone(q, r)` (β6 ≤ 1) / `cone(q, B)` (β6 > 1).
Rays: `⟪A,B⟫ > 0` ⟹ pentagon at ray `A`; `⟪A,B⟫ < 0 ∧ β6 ≥ 1` ⟹ hexagon at ray `B` (or `r`, β6 = 1);
`⟪A,B⟫ < 0 ∧ β6 < 1`: `⟪B,q⟫ > 0` ⟹ pentagon at ray `-B`, `⟪B,q⟫ < 0` ⟹ hexagon at ray `q`.
Leftovers: `⟪A,B⟫ = 0` (right angle at `a'`), and `⟪A,B⟫ < 0 ∧ ⟪B,q⟫ = 0` (with β6 < 1).
Numerics (gsec, K17F pabcb1 data, ties ζ(b',c) = 0, pr = 0): AB > 0 ⟹ pentagon 1140/1140; AB < 0, β6 > 1 ⟹ hexagon
1028/1028; AB < 0, β6 < 1: ⟪B,q⟫ > 0 ⟹ pentagon 280/280, ⟪B,q⟫ < 0 ⟹ hexagon 344/344.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k19_ip2 (P Q : ℝ³) (x y x' y' : ℝ) :
    ⟪x • P + y • Q, x' • P + y' • Q⟫ = x * x' * ⟪P, P⟫ + (x * y' + y * x') * ⟪P, Q⟫ + y * y' * ⟪Q, Q⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm Q P]
  ring

theorem k19_cone5 {x y u s t : ℝ × ℝ} {v1 v2 : ℝ} (h : k18Cone [x, y, u, s, t] v1 v2) :
    0 < x.1 * v1 + x.2 * v2 ∧ 0 < y.1 * v1 + y.2 * v2 ∧ 0 < u.1 * v1 + u.2 * v2 ∧ 0 < s.1 * v1 + s.2 * v2 ∧
      0 < t.1 * v1 + t.2 * v2 :=
  ⟨h x (by simp), h y (by simp), h u (by simp), h s (by simp), h t (by simp)⟩

set_option maxHeartbeats 12800000 in
/-- **S1.7 tie, pentagon** `(a,d,b,a',b')` at `a - d`: for `⟪A,B⟫ > 0`, or `β6 < 1 ∧ ⟪B,q⟫ > 0`. -/
theorem k19_s17_pent {a a' b b' c c' d : ℝ³} {α4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0)
    (hcase : 0 < ⟪a' - b, a' - c⟫ ∨ (β6 < 1 ∧ 0 < ⟪a' - b, b - d⟫)) : HasLexCell (V8 a a' b b' c c' d) := by
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by simp only [hP, hQ, hR, det3_expand]; ring
    rw [e, h]
  have Ea : fpoint P Q R d (0, 0, 1) = a := by rw [k17f_fp, hR]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17f_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17f_fp, hQ]; module
  have Ea' : fpoint P Q R d (β6, γ6, 0) = a' := by rw [k17f_fp, ha']; module
  have Eb' : fpoint P Q R d (0, 1, α4) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (1, 0, 1) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hPR : ⟪P, R⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hQR : ⟪Q, R⟫ = 0 := by rw [real_inner_comm]; exact hpr
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17f_r0 hΔ)
  have eB : a' - b = (β6 - 1) • P + γ6 • Q := by rw [ha', hP, hQ]; module
  have eA : a' - c = β6 • P + (γ6 - 1) • Q := by rw [ha', hP, hQ]; module
  have eq : b - d = (1 : ℝ) • P + (0 : ℝ) • Q := by rw [hP]; module
  have hAB : ⟪a' - b, a' - c⟫ = (β6 - 1) * β6 * ⟪P, P⟫ + ((β6 - 1) * (γ6 - 1) + γ6 * β6) * ⟪P, Q⟫ +
      γ6 * (γ6 - 1) * ⟪Q, Q⟫ := by rw [eB, eA, k19_ip2]
  have hBq : ⟪a' - b, b - d⟫ = (β6 - 1) * ⟪P, P⟫ + γ6 * ⟪P, Q⟫ := by rw [eB, eq, k19_ip2]; ring
  -- the cell on `cone ∧ (w(b) < w(d) ∨ w(b) < w(a'))`
  have C : K18Cell (V8 a a' b b' c c' d) P Q R d (fun v1 v2 => 0 < v1 ∧ v2 < 0 ∧ (1 - γ6) * v1 < β6 * (-v2) ∧
      (1 - β6) * (-v2) < γ6 * v1 ∧ (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ < 0 ∨
        0 < (β6 - 1) * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + γ6 * (v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫))) := by
    refine k18Cell_of (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17fPent α4 β6 γ6)
      (k17fPent_inj hα4 hβ6 hγ6) ?_ _ ?_ ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17fPent, pc5_0, Ea]; simp [V8]
      · simp only [k17fPent, pc5_1, Ed]; simp [V8]
      · simp only [k17fPent, pc5_2, Eb]; simp [V8]
      · simp only [k17fPent, pc5_3, Ea']; simp [V8]
      · simp only [k17fPent, pc5_4, Eb']; simp [V8]
    · rintro v1 v2 ⟨h1, h2, h3, h4, -⟩ D hD
      exact k17f_pent_tsc hD hα4 hβ6 hγ6 hs h1 h2 h3 h4
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
          y = fpoint P Q R d (β6, γ6, 0) ∨ y = fpoint P Q R d (0, 1, α4) ∨ y = fpoint P Q R d (0, 1, 0) ∨
          y = fpoint P Q R d (1, 0, 1) := by
        rw [Ea, Ed, Eb, Ea', Eb', Ec, Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17fPent, pc5_0])).elim
      · exact (hyx 1 (by simp only [k17fPent, pc5_1])).elim
      · exact (hyx 2 (by simp only [k17fPent, pc5_2])).elim
      · exact (hyx 3 (by simp only [k17fPent, pc5_3])).elim
      · exact (hyx 4 (by simp only [k17fPent, pc5_4])).elim
      · exact ⟨_, rfl, fun v1 v2 ⟨h1, h2, h3, h4, _⟩ D hD i => (k17f_pent_rest hD hα4 hβ6 hγ6 hs h1 h2 h3 h4).1 i⟩
      · exact ⟨_, rfl, fun v1 v2 ⟨h1, h2, h3, h4, _⟩ D hD i => (k17f_pent_rest hD hα4 hβ6 hγ6 hs h1 h2 h3 h4).2 i⟩
    · rintro v1 v2 ⟨h1, h2, h3, h4, hc⟩ hw
      obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
      refine k19_lexUni_nb _ _ hw 0 ?_ ?_ ?_
      · rw [e0]; left; simp only [k17fPent, pc5_4, pc5_0, hz, hPR, hQR]; nlinarith [mul_pos (sub_pos.2 hα41) hRR]
      · rw [f0]; left; simp only [k17fPent, pc5_0, pc5_1, hz, hPR, hQR]; nlinarith
      · intro i hi
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hi
        · left; rw [e1]; left; simp only [k17fPent, pc5_0, pc5_1, hz, hPR, hQR]; nlinarith
        · rcases hc with hc | hc
          · left; rw [e2]; right
            refine ⟨by simp only [k17fPent, pc5_1, pc5_2, hz, hPR, hQR]; ring, ?_⟩
            simp only [k17fPent, pc5_1, pc5_2, hwx, hPR, hQR]; nlinarith
          · right; rw [f2]; right
            refine ⟨by simp only [k17fPent, pc5_2, pc5_3, hz, hPR, hQR]; ring, ?_⟩
            simp only [k17fPent, pc5_2, pc5_3, hwx, hPR, hQR]; nlinarith
        · right; rw [f3]; left; simp only [k17fPent, pc5_3, pc5_4, hz, hPR, hQR]; nlinarith [mul_pos hα4 hRR]
        · right; rw [f4]; left; simp only [k17fPent, pc5_4, pc5_0, hz, hPR, hQR]
          nlinarith [mul_pos (sub_pos.2 hα41) hRR]
  refine ⟨R, k17f_r0 hΔ, ?_⟩
  rcases hcase with hc | ⟨hb, hc⟩
  · -- ray `A = (β6, γ6 - 1)`, direction `(0,-1)`; condition `w(a') > w(b)` (value `⟪A,B⟫`)
    refine C.cell (ρ1 := β6) (ρ2 := γ6 - 1) (δ1 := 0) (δ2 := -1)
      [(1, 0), (0, -1), (-(1 - γ6), -β6), (γ6, 1 - β6),
        ((β6 - 1) * ⟪P, P⟫ + γ6 * ⟪P, Q⟫, (β6 - 1) * ⟪P, Q⟫ + γ6 * ⟪Q, Q⟫)] ?_ (by simp) ?_
    · intro v1 v2 hC
      obtain ⟨h1, h2, h3, h4, h5⟩ := k19_cone5 hC
      simp only at h1 h2 h3 h4 h5
      exact ⟨by linarith, by linarith, by linarith, by linarith, Or.inr (by linarith)⟩
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl
      · left; simp only; linarith
      · left; simp only; linarith
      · right; constructor
        · simp only; ring
        · simp only; linarith
      · left; simp only; nlinarith
      · left; simp only; rw [hAB] at hc; linarith
  · -- ray `-B = (1 - β6, -γ6)`, direction `(1,0)`; condition `w(b) < w(d)` (value `⟪B,q⟫`)
    refine C.cell (ρ1 := 1 - β6) (ρ2 := -γ6) (δ1 := 1) (δ2 := 0)
      [(1, 0), (0, -1), (-(1 - γ6), -β6), (γ6, 1 - β6), (-⟪P, P⟫, -⟪P, Q⟫)] ?_ (by simp) ?_
    · intro v1 v2 hC
      obtain ⟨h1, h2, h3, h4, h5⟩ := k19_cone5 hC
      simp only at h1 h2 h3 h4 h5
      exact ⟨by linarith, by linarith, by linarith, by linarith, Or.inl (by linarith)⟩
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl
      · left; simp only; linarith
      · left; simp only; linarith
      · left; simp only; nlinarith
      · right; constructor
        · simp only; ring
        · simp only; linarith
      · left; simp only; rw [hBq] at hc; linarith

set_option maxHeartbeats 12800000 in
/-- **S1.7 tie, hexagon** `(a,b',c,a',b,c')` at `a - d`: for `⟪A,B⟫ < 0 ∧ (1 ≤ β6 ∨ ⟪B,q⟫ < 0)`. -/
theorem k19_s17_hex {a a' b b' c c' d : ℝ³} {α4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ = 0) (hpr : ⟪a - d, c - d⟫ = 0)
    (hAB0 : ⟪a' - b, a' - c⟫ < 0) (hcase : 1 ≤ β6 ∨ ⟪a' - b, b - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := c - d with hP
  set Q := b - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by simp only [hP, hQ, hR, det3_expand]; ring
    rw [e, h, neg_zero]
  have Ea : fpoint P Q R d (0, 0, 1) = a := by rw [k17f_fp, hR]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17f_fp, hQ]; module
  have Ec : fpoint P Q R d (1, 0, 0) = c := by rw [k17f_fp, hP]; module
  have Ea' : fpoint P Q R d (γ6, β6, 0) = a' := by rw [k17f_fp, ha']; module
  have Eb' : fpoint P Q R d (1, 0, α4) = b' := by rw [k17f_fp, hb']; module
  have Ec' : fpoint P Q R d (0, 1, 1) = c' := by rw [k17f_fp, hc']; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hwx : ∀ t : ℝ × ℝ × ℝ, ∀ v1 v2 : ℝ, ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫ =
      v1 * (⟪d, P⟫ + t.1 * ⟪P, P⟫ + t.2.1 * ⟪P, Q⟫ + t.2.2 * ⟪P, R⟫) +
      v2 * (⟪d, Q⟫ + t.1 * ⟪P, Q⟫ + t.2.1 * ⟪Q, Q⟫ + t.2.2 * ⟪Q, R⟫) := fun t v1 v2 => k17f_wexp P Q R d t v1 v2
  have hQR : ⟪Q, R⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have hPR : ⟪P, R⟫ = 0 := by rw [real_inner_comm]; exact hpr
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17f_r0 hΔ)
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have eB : a' - b = γ6 • P + (β6 - 1) • Q := by rw [ha', hP, hQ]; module
  have eA : a' - c = (γ6 - 1) • P + β6 • Q := by rw [ha', hP, hQ]; module
  have eq : b - d = (0 : ℝ) • P + (1 : ℝ) • Q := by rw [hQ]; module
  have hAB : ⟪a' - b, a' - c⟫ = γ6 * (γ6 - 1) * ⟪P, P⟫ + (γ6 * β6 + (β6 - 1) * (γ6 - 1)) * ⟪P, Q⟫ +
      (β6 - 1) * β6 * ⟪Q, Q⟫ := by rw [eB, eA, k19_ip2]
  have hBq : ⟪a' - b, b - d⟫ = γ6 * ⟪P, Q⟫ + (β6 - 1) * ⟪Q, Q⟫ := by rw [eB, eq, k19_ip2]; ring
  have C : K18Cell (V8 a a' b b' c c' d) P Q R d (fun v1 v2 => 0 < v1 ∧ 0 < v2 ∧ (β6 - 1) * v1 < γ6 * v2 ∧
      ((γ6 - 1) * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + β6 * (v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫) < 0 ∨
        γ6 * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + (β6 - 1) * (v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫) < 0)) := by
    refine k18Cell_of (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17fHex α4 β6 γ6)
      (k17fHex_inj hα4 hβ6 hγ6) ?_ _ ?_ ?_ ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k17fHex, pc6_0, Ea]; simp [V8]
      · simp only [k17fHex, pc6_1, Eb']; simp [V8]
      · simp only [k17fHex, pc6_2, Ec]; simp [V8]
      · simp only [k17fHex, pc6_3, Ea']; simp [V8]
      · simp only [k17fHex, pc6_4, Eb]; simp [V8]
      · simp only [k17fHex, pc6_5, Ec']; simp [V8]
    · rintro v1 v2 ⟨h1, h2, h3, -⟩ D hD
      exact k17f_hex_tsc hD hα4 hβ6 hγ6 hs hγ61 h1 h2 h3
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (1, 0, α4) ∨ y = fpoint P Q R d (1, 0, 0) ∨
          y = fpoint P Q R d (γ6, β6, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 1, 1) ∨
          y = fpoint P Q R d (0, 0, 0) := by
        rw [Ea, Eb', Ec, Ea', Eb, Ec', Ed]
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17fHex, pc6_0])).elim
      · exact (hyx 1 (by simp only [k17fHex, pc6_1])).elim
      · exact (hyx 2 (by simp only [k17fHex, pc6_2])).elim
      · exact (hyx 3 (by simp only [k17fHex, pc6_3])).elim
      · exact (hyx 4 (by simp only [k17fHex, pc6_4])).elim
      · exact (hyx 5 (by simp only [k17fHex, pc6_5])).elim
      · exact ⟨_, rfl, fun v1 v2 ⟨h1, h2, h3, _⟩ D hD i => k17f_hex_rest hD hα4 hβ6 hγ6 hs hγ61 h1 h2 h3 i⟩
    · rintro v1 v2 ⟨h1, h2, h3, hc⟩ hw
      obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5⟩ := k19_z6
      refine k19_lexUni_nb2 _ _ hw 5 (by decide) ?_ ?_ ?_
      · rw [e5]; left; simp only [k17fHex, pc6_4, pc6_5, hz, hPR, hQR]; nlinarith
      · rw [f5, f0]; left; simp only [k17fHex, pc6_0, pc6_1, hz, hPR, hQR]
        nlinarith [mul_pos (sub_pos.2 hα41) hRR]
      · intro i hi hi'
        rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd (by decide) hi'
        · left; rw [e1]; left; simp only [k17fHex, pc6_0, pc6_1, hz, hPR, hQR]
          nlinarith [mul_pos (sub_pos.2 hα41) hRR]
        · left; rw [e2]; left; simp only [k17fHex, pc6_1, pc6_2, hz, hPR, hQR]; nlinarith [mul_pos hα4 hRR]
        · rcases hc with hc | hc
          · left; rw [e3]; right
            refine ⟨by simp only [k17fHex, pc6_2, pc6_3, hz, hPR, hQR]; ring, ?_⟩
            simp only [k17fHex, pc6_2, pc6_3, hwx, hPR, hQR]; nlinarith
          · right; rw [f3]; right
            refine ⟨by simp only [k17fHex, pc6_3, pc6_4, hz, hPR, hQR]; ring, ?_⟩
            simp only [k17fHex, pc6_3, pc6_4, hwx, hPR, hQR]; nlinarith
        · right; rw [f4]; left; simp only [k17fHex, pc6_4, pc6_5, hz, hPR, hQR]; nlinarith
        · exact absurd rfl hi
  refine ⟨R, k17f_r0 hΔ, ?_⟩
  rcases hcase with hb | hc
  · -- ray `B = (γ6, β6 - 1)`, direction `(0,1)`; condition `w(a') < w(c)` (value `⟪A,B⟫`)
    refine C.cell (ρ1 := γ6) (ρ2 := β6 - 1) (δ1 := 0) (δ2 := 1)
      [(1, 0), (0, 1), (-(β6 - 1), γ6),
        (-((γ6 - 1) * ⟪P, P⟫ + β6 * ⟪P, Q⟫), -((γ6 - 1) * ⟪P, Q⟫ + β6 * ⟪Q, Q⟫))] ?_ (by simp) ?_
    · intro v1 v2 hC
      obtain ⟨h1, h2, h3, h4⟩ := k19_cone4' hC
      simp only at h1 h2 h3 h4
      exact ⟨by linarith, by linarith, by linarith, Or.inl (by linarith)⟩
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · left; simp only; linarith
      · rcases hb.lt_or_eq with hb | hb
        · left; simp only; linarith
        · right; constructor
          · simp only; rw [← hb]; ring
          · simp only; linarith
      · right; constructor
        · simp only; ring
        · simp only; linarith
      · left; simp only; rw [hAB] at hAB0; linarith
  · -- ray `q = (0,1)`, direction `(1,0)`; condition `w(a') < w(b)` (value `⟪B,q⟫`)
    refine C.cell (ρ1 := 0) (ρ2 := 1) (δ1 := 1) (δ2 := 0)
      [(1, 0), (0, 1), (-(β6 - 1), γ6),
        (-(γ6 * ⟪P, P⟫ + (β6 - 1) * ⟪P, Q⟫), -(γ6 * ⟪P, Q⟫ + (β6 - 1) * ⟪Q, Q⟫))] ?_ (by simp) ?_
    · intro v1 v2 hC
      obtain ⟨h1, h2, h3, h4⟩ := k19_cone4' hC
      simp only at h1 h2 h3 h4
      exact ⟨by linarith, by linarith, by linarith, Or.inr (by linarith)⟩
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · right; constructor
        · simp only; ring
        · simp only; linarith
      · left; simp only; linarith
      · left; simp only; linarith
      · left; simp only; rw [hBq] at hc; linarith

/-- **S1.7 tie** (`k17f_s17`'s leftover `⟪a-d,c-d⟫ = 0`): a cell, or the right angle `⟪a'-b,a'-c⟫ = 0`, or
(`β6 < 1`) `⟪a'-b,a'-c⟫ < 0 ∧ ⟪a'-b,b-d⟫ = 0`. -/
theorem k19_s17_tie {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h0 : ⟪b' - c, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) (hpr : ⟪a - d, c - d⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a' - b, a' - c⟫ = 0 ∨
      (⟪a' - b, a' - c⟫ < 0 ∧ ⟪a' - b, b - d⟫ = 0) := by
  obtain ⟨α4, β6, γ6, hdet, hc', hb', ha', hα4, hα41, hβ6, hγ6, hγ61, hs, hpq⟩ :=
    k17f_pa2_frame W hT' hκ hfar h0 hα hβ
  rcases lt_trichotomy ⟪a' - b, a' - c⟫ 0 with hn | hz | hp
  · rcases le_or_gt 1 β6 with hb | hb
    · exact Or.inl (k19_s17_hex hdet hc' hb' ha' hα4 hα41 hβ6 hγ6 hγ61 hs hpq hpr hn (Or.inl hb))
    · rcases lt_trichotomy ⟪a' - b, b - d⟫ 0 with hq | hq | hq
      · exact Or.inl (k19_s17_hex hdet hc' hb' ha' hα4 hα41 hβ6 hγ6 hγ61 hs hpq hpr hn (Or.inr hq))
      · exact Or.inr (Or.inr ⟨hn, hq⟩)
      · exact Or.inl (k19_s17_pent hdet hc' hb' ha' hα4 hα41 hβ6 hγ6 hγ61 hs hpq hpr (Or.inr ⟨hb, hq⟩))
  · exact Or.inr (Or.inl hz)
  · exact Or.inl (k19_s17_pent hdet hc' hb' ha' hα4 hα41 hβ6 hγ6 hγ61 hs hpq hpr (Or.inl hp))

end C2
end Type08Sp
end Minimality
