module

public import Minimality.Type08S.C2K17GC4

@[expose] public section


/-!
# K17GC / GC5: U3 (`K14LeftPa` 3rd disjunct, `β1 > 1` branch: `α4 = 1`, `ζ(b',c) = ⟪b'-c,d-b⟫ = 0`).

Frame: `γ4 = β1`, `b' = d + p + β1 r`, `c' = d + p + β1 q`; tie `pq + (β1-1) qr = 0`.  Literal `⟪a-d,a-c'⟫ = -β1 pq`.
* `pq < 0` (U3a): quadrilateral `(a,c',a',b')` at `b' - c`, frame `(a-d, b-d, b'-c)`, `κ = 1/(β1-1)`:
  `a (1,0,0)`, `c' (1,β1,0)`, `a' (-γ6κ,β6,γ6κ)`, `b' (-κ,0,β1κ)`, `c (-κ,0,κ)` (= `b'` on the screen), `d 0` (on the
  screen edge `b' a`), `b (0,1,0)`.  `z(a) = z(c')` (the tie); cone `v2 > 0 ∧ β6 v1 > κ(1-γ6) v2`; lex: `w(c') < w(a)`
  (`v1 pq + v2 qq < 0`, holds near the ray `(1,0)`), and `a'` cannot be a second peak (`|R|² > 0`);
  tilt `(β6 qq - κ(1-γ6) pq, -λ β6 pq)`.
* `pq > 0` (U3b): pentagon `(b',c',a,d,c)` at `d - b` (frame `(c-d,a-d,d-b)`); `z(b') = z(c)` (the tie) adjacent
  peaks, w-free (`lexUni5_top`); cone `v1, v2 > 0`.
* `pq = 0`: leftover (literal's tie; then `qr = 0` too: the 4-plateau `a,d,c,b'` at `d - b`, U1-like).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- 4-cycle: `1 < 0` and (`0 < 3` or `2 < 3` or `2 < 1`). -/
theorem k17gc_lexUni4_b (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0))
    (hor : LexLt (z 0, w 0) (z 3, w 3) ∨ LexLt (z 2, w 2) (z 3, w 3) ∨ LexLt (z 2, w 2) (z 1, w 1)) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have hne : ∀ i j : ZMod 4, i ≠ j → (z i, w i) ≠ (z j, w j) := fun i j h e =>
    h (hinj i j (congrArg Prod.fst e) (congrArg Prod.snd e))
  have h03 := hne 0 3 (by decide)
  have h23 := hne 2 3 (by decide)
  have h12 := hne 1 2 (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 4 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 := fun g => Fin.sum_univ_four (f := g)
  rw [hs]
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  have f0 : (0 : ZMod 4) + 1 = 1 := by decide
  have f1 : (1 : ZMod 4) + 1 = 2 := by decide
  have f2 : (2 : ZMod 4) + 1 = 3 := by decide
  have f3 : (3 : ZMod 4) + 1 = 0 := by decide
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) = 1
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  have a10 := lexLt_asymm h10
  have hno : LexLt (z 0, w 0) (z 3, w 3) → LexLt (z 3, w 3) (z 2, w 2) → LexLt (z 2, w 2) (z 1, w 1) → False :=
    fun x y u => by
      have := lexLt_trans_K2 (lexLt_trans_K2 (lexLt_trans_K2 x y) u) h10
      exact lexLt_asymm this this
  rcases lexLt_total h03 with x | x <;> have ax := lexLt_asymm x <;>
    rcases lexLt_total h23 with y | y <;> have ay := lexLt_asymm y <;>
    rcases lexLt_total h12 with u | u <;> have au := lexLt_asymm u <;>
    rcases hor with t | t | t <;>
    (try simp [x, ax, y, ay, u, au, h10, a10]) <;>
    first | exact (hno x y u).elim | exact (lexLt_asymm t ‹_›).elim

/-- **Relation lemma, U3**: `α4 = 1`, `γ4 = β1 > 1`, tie `⟪a-d,b-d⟫ + (β1-1) ⟪b-d,c-d⟫ = 0`. -/
theorem k17gc_u3_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (h0 : ⟪b' - c, d - b⟫ = 0) :
    ∃ β1 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + β1 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 1 < β1 ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧
      ⟪a - d, b - d⟫ + (β1 - 1) * ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_beta1 hc'] at hβ
  have hb1 : 1 < β1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  rw [det_alpha4 hb'] at hα
  have ha1 : α4 = 1 := by
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  subst ha1
  have hg4 : γ4 = β1 := by
    have := (planar_a_iff hdet hc' hb').1 hκ
    linarith
  subst hg4
  refine ⟨γ4, β6, γ6, hdet, hc', hb', ha', hb1, hβ6, hγ6, hfa hfar, hs, ?_⟩
  have e : b' - c = (1 : ℝ) • (a - d) + (γ4 - 1) • (c - d) := by rw [hb']; module
  have e2 : d - b = -(b - d) := by abel
  rw [e, e2, inner_neg_right, inner_add_left, inner_smul_left, inner_smul_left] at h0
  simp only [conj_trivial, one_mul] at h0
  rw [real_inner_comm (c - d) (b - d)]; linarith

/-! ## U3b: pentagon `(b',c',a,d,c)` at `d - b`, frame `(c-d, a-d, d-b)` -/

/-- ccw pentagon `b' (β1,1,0), c' (0,1,-β1), a (0,1,0), d 0, c (1,0,0)`. -/
def k17gcPentU3 (β1 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (β1, 1, 0) (0, 1, -β1) (0, 1, 0) (0, 0, 0) (1, 0, 0)

set_option maxHeartbeats 6400000 in
theorem k17gc_pentU3_tsc {β1 β6 γ6 v1 v2 : ℝ} (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcPentU3 β1 (i + 1) - k17gcPentU3 β1 i) (k17gcPentU3 β1 j - k17gcPentU3 β1 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (γ6, 0, -β6)], ∀ i : ZMod 5,
      TSc 1 (k17gcPentU3 β1 (i + 1) - k17gcPentU3 β1 i) (t - k17gcPentU3 β1 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have hb0 : 0 < β1 := by linarith
  have kb := mul_pos hb0 hv1
  have kb2 := mul_pos hb0 hv2
  have kg := mul_pos hγ6 hv2
  have kg1 := mul_pos hγ6 hv1
  have kbb := mul_pos hβ6 hv2
  have kbb1 := mul_pos hβ6 hv1
  have k61 := mul_pos (sub_pos.2 hγ61) hv2
  have kbg := mul_pos (mul_pos hb0 hβ6) hv2
  have kbg1 := mul_pos (mul_pos hb0 hγ6) hv2
  have kbb2 := mul_pos (mul_pos hb0 hb0) hv2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcPentU3, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcPentU3, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcPentU3_inj {β1 : ℝ} (hβ1 : 1 < β1) :
    ∀ i j, k17gcPentU3 β1 i = k17gcPentU3 β1 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcPentU3, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- **U3b cell** (`pq > 0`). -/
theorem k17gc_u3b_cell {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (htie : ⟪a - d, b - d⟫ + (β1 - 1) * ⟪b - d, c - d⟫ = 0) (hpq : 0 < ⟪a - d, b - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := c - d with hP
  set Q := a - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = -det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h, neg_zero]
  have Ea : fpoint P Q R d (0, 1, 0) = a := by rw [k17gc_fp, hQ]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gc_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17gc_fp, hR]; module
  have Ec : fpoint P Q R d (1, 0, 0) = c := by rw [k17gc_fp, hP]; module
  have Ea' : fpoint P Q R d (γ6, 0, -β6) = a' := by rw [k17gc_fp, ha', hP, hR]; module
  have Eb' : fpoint P Q R d (β1, 1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -β1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQR : ⟪Q, R⟫ = -⟪a - d, b - d⟫ := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right]
  have hPR : ⟪P, R⟫ = -⟪b - d, c - d⟫ := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm]
  have hQR0 : ⟪Q, R⟫ < 0 := by rw [hQR]; linarith
  have hPR0 : 0 < ⟪P, R⟫ := by rw [hPR]; nlinarith
  have htie' : (β1 - 1) * ⟪P, R⟫ + ⟪Q, R⟫ = 0 := by rw [hPR, hQR]; linarith
  refine ⟨R, hR0, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPentU3 β1)
    (k17gcPentU3_inj hβ1) (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (by norm_num) ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcPentU3, pc5_0, Eb']; simp [V8]
    · simp only [k17gcPentU3, pc5_1, Ec']; simp [V8]
    · simp only [k17gcPentU3, pc5_2, Ea]; simp [V8]
    · simp only [k17gcPentU3, pc5_3, Ed]; simp [V8]
    · simp only [k17gcPentU3, pc5_4, Ec]; simp [V8]
  · intro lam h0 h1 D hD i j hi hj
    exact tsc_scale hD ((k17gc_pentU3_tsc hβ1 hβ6 hγ6 hγ61 (by norm_num) (by linarith)).1 i j hi hj)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (β1, 1, 0) ∨ y = fpoint P Q R d (0, 1, -β1) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
        y = fpoint P Q R d (γ6, 0, -β6) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT := fun lam (h0 : (0:ℝ) < lam) (h1 : lam < 1) =>
      (k17gc_pentU3_tsc hβ1 hβ6 hγ6 hγ61 (v1 := 1 + lam * 0) (v2 := 1 + lam * 1) (by norm_num)
        (by linarith)).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gcPentU3, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gcPentU3, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gcPentU3, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gcPentU3, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gcPentU3, pc5_4])).elim
    · exact ⟨_, rfl, fun lam h0 h1 D hD i => tsc_scale hD (hT lam h0 h1 _ (by simp) i)⟩
    · exact ⟨_, rfl, fun lam h0 h1 D hD i => tsc_scale hD (hT lam h0 h1 _ (by simp) i)⟩
  · intro w hw
    refine lexUni5_top _ w hw ?_ ?_ ?_
    · left; simp only [k17gcPentU3, pc5_0, pc5_1, hz]; nlinarith [mul_pos (by linarith : (0:ℝ) < β1) hRR]
    · left; simp only [k17gcPentU3, pc5_2, pc5_3, hz]; nlinarith
    · left; simp only [k17gcPentU3, pc5_3, pc5_4, hz]; nlinarith

/-! ## U3a: quadrilateral `(a,c',a',b')` at `b' - c`, frame `(a-d, b-d, b'-c)` -/

/-- ccw quadrilateral `a (1,0,0), c' (1,β1,0), a' (-γ6κ,β6,γ6κ), b' (-κ,0,β1κ)`. -/
def k17gcQ4b (κ β1 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (1, β1, 0), (-(γ6 * κ), β6, γ6 * κ), (-κ, 0, β1 * κ)]

theorem k17gcQ4b_0 : k17gcQ4b κ β1 β6 γ6 0 = (1, 0, 0) := rfl
theorem k17gcQ4b_1 : k17gcQ4b κ β1 β6 γ6 1 = (1, β1, 0) := rfl
theorem k17gcQ4b_2 : k17gcQ4b κ β1 β6 γ6 2 = (-(γ6 * κ), β6, γ6 * κ) := rfl
theorem k17gcQ4b_3 : k17gcQ4b κ β1 β6 γ6 3 = (-κ, 0, β1 * κ) := rfl

set_option maxHeartbeats 6400000 in
theorem k17gc_q4b_tsc {κ β1 β6 γ6 v1 v2 : ℝ} (hκ : 0 < κ) (hβ1 : 1 < β1) (hκβ : κ * (β1 - 1) = 1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6)
    (hv2 : 0 < v2) (hc : 0 < β6 * v1 - κ * (1 - γ6) * v2) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcQ4b κ β1 β6 γ6 (i + 1) - k17gcQ4b κ β1 β6 γ6 i)
        (k17gcQ4b κ β1 β6 γ6 j - k17gcQ4b κ β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (-κ, 0, κ)], ∀ i : ZMod 4,
      TSc 1 (k17gcQ4b κ β1 β6 γ6 (i + 1) - k17gcQ4b κ β1 β6 γ6 i) (t - k17gcQ4b κ β1 β6 γ6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := k17gc_z4
  have hb0 : 0 < β1 := by linarith
  have ks := sub_pos.2 hs
  have kb := sub_pos.2 hβ1
  have k1 := mul_pos hκ ks
  have k2 := mul_pos hκ hβ6
  have k3 := mul_pos hκ hγ6
  have k4 := mul_pos (mul_pos hκ hb0) ks
  have k5 := mul_pos hκ hv2
  have k6 := mul_pos (mul_pos hκ hb0) hv2
  have k7 := mul_pos hb0 hv2
  have k8 := mul_pos hb0 hc
  have k9 := mul_pos hκ hc
  have k10 := mul_pos (mul_pos hκ hκ) ks
  have k11 := mul_pos (mul_pos hκ hb0) hβ6
  have k12 := mul_pos (mul_pos hκ hκ) hv2
  have k13 := mul_pos hκ (sub_pos.2 hγ61)
  have k14 := mul_pos (mul_pos hκ hb0) hc
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k17gc_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, s0, s1, s2, s3, k17gcQ4b_0, k17gcQ4b_1, k17gcQ4b_2, k17gcQ4b_3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩)
         | (right; refine ⟨by linear_combination (exp := 1) 0, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, s0, s1, s2, s3, k17gcQ4b_0, k17gcQ4b_1, k17gcQ4b_2, k17gcQ4b_3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩)
       | (right; refine ⟨by linear_combination (-(1:ℝ)) * hκβ, by nlinarith⟩)
       | (right; refine ⟨by linear_combination hκβ, by nlinarith⟩))

theorem k17gcQ4b_inj {κ β1 β6 γ6 : ℝ} (hκ : 0 < κ) (hβ1 : 1 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) :
    ∀ i j, k17gcQ4b κ β1 β6 γ6 i = k17gcQ4b κ β1 β6 γ6 j → i = j := by
  intro i j h
  have k1 := mul_pos hγ6 hκ
  have k2 := mul_pos (sub_pos.2 hγ61) hκ
  have k3 := mul_pos (sub_pos.2 hβ1) hκ
  rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k17gc_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k17gcQ4b_0, k17gcQ4b_1, k17gcQ4b_2, k17gcQ4b_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
/-- **U3a cell** (`pq < 0`): quadrilateral `(a,c',a',b')` at `b' - c`. -/
theorem k17gc_u3a_cell {a a' b b' c c' d : ℝ³} {β1 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ1 : 1 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (htie : ⟪a - d, b - d⟫ + (β1 - 1) * ⟪b - d, c - d⟫ = 0) (hpq : ⟪a - d, b - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set κ : ℝ := 1 / (β1 - 1) with hκdef
  have hb1 : (β1 - 1) ≠ 0 := by linarith
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos one_pos (by linarith)
  have hκβ : κ * (β1 - 1) = 1 := by rw [hκdef]; field_simp
  set P := a - d with hP
  set Q := b - d with hQ
  set R := b' - c with hR
  have hRe : R = P + (β1 - 1) • (c - d) := by rw [hR, hb', hP]; module
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = (β1 - 1) * det3 (a - d) (b - d) (c - d) := by
      rw [hRe]; simp only [hP, hQ, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [e]; exact mul_ne_zero hb1 hdet
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17gc_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gc_fp]; module
  have Eb : fpoint P Q R d (0, 1, 0) = b := by rw [k17gc_fp, hQ]; module
  have Ec : fpoint P Q R d (-κ, 0, κ) = c := by
    rw [k17gc_fp, hRe, hP]; match_scalars <;> (try simp only [hκdef]) <;> (try field_simp) <;> (try ring)
  have Ea' : fpoint P Q R d (-(γ6 * κ), β6, γ6 * κ) = a' := by
    rw [k17gc_fp, hRe, ha', hP, hQ]; match_scalars <;> (try simp only [hκdef]) <;> (try field_simp) <;> (try ring)
  have Eb' : fpoint P Q R d (-κ, 0, β1 * κ) = b' := by
    rw [k17gc_fp, hRe, hb', hP]; match_scalars <;> (try simp only [hκdef]) <;> (try field_simp) <;> (try ring)
  have Ec' : fpoint P Q R d (1, β1, 0) = c' := by rw [k17gc_fp, hc', hP, hQ]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hRe, inner_add_right, inner_smul_right, hQ, hP, real_inner_comm]; linarith
  have hPQ : ⟪P, Q⟫ < 0 := hpq
  set K := β6 * ⟪Q, Q⟫ - κ * (1 - γ6) * ⟪P, Q⟫ with hK
  have hK0 : 0 < K := by rw [hK]; nlinarith [mul_pos hβ6 hQQ, mul_pos (mul_pos hκ (sub_pos.2 hγ61)) (neg_pos.2 hPQ)]
  refine ⟨R, hR0, ?_⟩
  refine cyc_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 4) (by norm_num) (k17gcQ4b κ β1 β6 γ6)
    (k17gcQ4b_inj hκ hβ1 hγ6 hγ61) ?_ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (-κ, 0, κ)] ?_
    (u1 := K) (u2 := 0) (t1 := 0) (t2 := β6 * -⟪P, Q⟫)
    (by nlinarith [mul_pos hK0 (mul_pos hβ6 (neg_pos.2 hPQ))]) (lo := 0) (hi := 1) (by norm_num)
    (fun v1 v2 => 0 < v2 ∧ 0 < β6 * v1 - κ * (1 - γ6) * v2 ∧ v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫ < 0) ?_ ?_ ?_
  · intro i
    rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl
    · rw [k17gcQ4b_0, Ea]; simp [V8]
    · rw [k17gcQ4b_1, Ec']; simp [V8]
    · rw [k17gcQ4b_2, Ea']; simp [V8]
    · rw [k17gcQ4b_3, Eb']; simp [V8]
  · intro y hy
    have hV : y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, β1, 0) ∨
        y = fpoint P Q R d (-(γ6 * κ), β6, γ6 * κ) ∨ y = fpoint P Q R d (-κ, 0, β1 * κ) ∨
        y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (-κ, 0, κ) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    refine ⟨by nlinarith [mul_pos (mul_pos h0 hβ6) (neg_pos.2 hPQ)], ?_, ?_⟩
    · have e : β6 * (K + lam * 0) - κ * (1 - γ6) * (0 + lam * (β6 * -⟪P, Q⟫)) =
          β6 * (β6 * ⟪Q, Q⟫ + κ * (1 - γ6) * (-⟪P, Q⟫) * (1 - lam)) := by rw [hK]; ring
      rw [e]
      have k1 := mul_pos hβ6 hQQ
      have k2 := mul_pos (mul_pos (mul_pos hκ (sub_pos.2 hγ61)) (neg_pos.2 hPQ)) (sub_pos.2 h1)
      exact mul_pos hβ6 (by nlinarith)
    · have e : (K + lam * 0) * ⟪P, Q⟫ + (0 + lam * (β6 * -⟪P, Q⟫)) * ⟪Q, Q⟫ =
          ⟪P, Q⟫ * (β6 * ⟪Q, Q⟫ * (1 - lam) + κ * (1 - γ6) * (-⟪P, Q⟫)) := by rw [hK]; ring
      rw [e]
      have k1 := mul_pos (mul_pos hβ6 hQQ) (sub_pos.2 h1)
      have k2 := mul_pos (mul_pos hκ (sub_pos.2 hγ61)) (neg_pos.2 hPQ)
      exact mul_neg_of_neg_of_pos hPQ (by nlinarith)
  · rintro v1 v2 ⟨hv2, hc, -⟩
    exact k17gc_q4b_tsc hκ hβ1 hκβ hβ6 hγ6 hγ61 hs hv2 hc
  · rintro v1 v2 ⟨-, -, hf⟩ hinj
    have hβκ : κ + 1 = β1 * κ := by linarith
    refine k17gc_lexUni4_b _ _ hinj ?_ ?_
    · right
      simp only [k17gcQ4b_0, k17gcQ4b_1]
      refine ⟨by rw [hz, hz, hQR]; simp only; ring, ?_⟩
      rw [k17f_wexp, k17f_wexp]; simp only; nlinarith [mul_pos (by linarith : (0:ℝ) < β1) (neg_pos.2 hf)]
    · rcases lt_or_ge 0 (⟪R, R⟫ - ⟪P, R⟫) with hS | hS
      · left; left
        simp only [k17gcQ4b_0, k17gcQ4b_3, hz, hQR]
        nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < β1) hκ) hS]
      · right; right; left
        simp only [k17gcQ4b_1, k17gcQ4b_2, hz, hQR]
        nlinarith [mul_nonneg (mul_nonneg hγ6.le hκ.le) (neg_nonneg.2 hS)]

/-- **U3** (`K14LeftPa` 3rd disjunct with `β1 > 1`: `α4 = 1`, `ζ(b',c) = 0`): a cell, or the literal's tie
`⟪a-d, a-c'⟫ = 0`. -/
theorem k17gc_u3 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (h0 : ⟪b' - c, d - b⟫ = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, a - c'⟫ = 0 := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨β1, β6, γ6, hdet, hc', hb', ha', hβ1, hβ6, hγ6, hγ61, hs, htie⟩ :=
    k17gc_u3_frame W hT' hκ (k5z_far1 W hT' hnT) hα hβ h0
  have e : ⟪a - d, a - c'⟫ = -β1 * ⟪a - d, b - d⟫ := by
    have : a - c' = (-β1) • (b - d) := by rw [hc']; module
    rw [this, real_inner_smul_right]
  rcases lt_trichotomy ⟪a - d, b - d⟫ 0 with hn | h0' | hp
  · exact Or.inl (k17gc_u3a_cell hdet hc' hb' ha' hβ1 hβ6 hγ6 hγ61 hs htie hn)
  · right; rw [e, h0', mul_zero]
  · exact Or.inl (k17gc_u3b_cell hdet hc' hb' ha' hβ1 hβ6 hγ6 hγ61 htie hp)

end C2
end Type08Sp
end Minimality
