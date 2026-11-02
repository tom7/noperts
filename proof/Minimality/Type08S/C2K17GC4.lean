module

public import Minimality.Type08S.C2K17GC3

@[expose] public section


/-!
# K17GC / GC4: U2 (`K14LeftPa` 2nd disjunct, `β1 > 1` branch: `ζ(b',c) = 0`, `⟪a-d,d-b⟫ = 0`, `α4 < 1 < β1`).

Frame (`k17gc_u2_frame`): `γ4 = 1 + α4 (β1-1) > 1`, so the two ties give `⟪p,q⟫ = ⟪q,r⟫ = 0` (`q ⟂` the face `Q_ac`);
at `d - b` the face `a,c,d,b'` is a 4-plateau.  Split by `pr = ⟪a-d,c-d⟫` (no leftover):
* `pr > 0` (U2b): pentagon `(b,c',b',c,d)` at `d - b`, frame `(a-d, c-d)`: plateau `b',c,d`; lex needs `w(c) > w(d)`
  (`⟪c-d,v⟫ > 0`); TS cone `v1 > 0 > v2`, `γ4 v1 + (1-α4) v2 > 0`; tilt `(γ4 rr + (1-α4) pr, -λ γ4 pr)`.
* `pr ≤ 0` (so `ζ_{a-d}(a,b') = (1-α4) pp - γ4 pr > 0`, U2a): quadrilateral `(a,c',a',b')` at `c' - b`, frame
  `(b-d, c-d)`: `z(a) < z(c')`, `z(b') < z(a)` (the literal), w-free; cone `v2 > 0`, `(β6-1) v2 > γ6 v1`; tilt `(-(1+λ), γ6)`.
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

/-- 4-cycle lex unimodality: `0 < 1` and `3 < 0`. -/
theorem k17gc_lexUni4 (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : LexLt (z 0, w 0) (z 1, w 1)) (h30 : LexLt (z 3, w 3) (z 0, w 0)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have hne : ∀ i j : ZMod 4, i ≠ j → (z i, w i) ≠ (z j, w j) := fun i j h e =>
    h (hinj i j (congrArg Prod.fst e) (congrArg Prod.snd e))
  have h12 := hne 1 2 (by decide)
  have h23 := hne 2 3 (by decide)
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
  have a01 := lexLt_asymm h01
  have a30 := lexLt_asymm h30
  have hno : LexLt (z 1, w 1) (z 2, w 2) → LexLt (z 2, w 2) (z 3, w 3) → False := fun x y => by
    have := lexLt_trans_K2 (lexLt_trans_K2 (lexLt_trans_K2 h01 x) y) h30
    exact lexLt_asymm this this
  rcases lexLt_total h12 with x | x <;> have ax := lexLt_asymm x <;>
    rcases lexLt_total h23 with y | y <;> have ay := lexLt_asymm y <;>
    (try simp [x, ax, y, ay, h01, a01, h30, a30]) <;>
    exact (hno x y).elim

/-- **Relation lemma, U2**: T' frame, `α4 < 1 < β1`, `γ4 = 1 + α4 (β1 - 1)`, `⟪p,q⟫ = ⟪q,r⟫ = 0`. -/
theorem k17gc_u2_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (h0 : ⟪b' - c, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hpq : ⟪a - d, d - b⟫ = 0) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < α4 ∧ α4 < 1 ∧ 1 < β1 ∧ γ4 = 1 + α4 * (β1 - 1) ∧
      0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 ∧ ⟪a - d, b - d⟫ = 0 ∧ ⟪b - d, c - d⟫ = 0 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_beta1 hc'] at hβ
  have hb1 : 1 < β1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  rw [det_alpha4 hb'] at hα
  have hα1 : α4 < 1 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) hΔ2.le]
  have hg4 : γ4 = 1 + α4 * (β1 - 1) := by
    have := (planar_a_iff hdet hc' hb').1 hκ
    linarith
  have hpq' : ⟪a - d, b - d⟫ = 0 := by
    have e2 : d - b = -(b - d) := by abel
    rw [e2, inner_neg_right] at hpq; linarith
  have hqr : ⟪b - d, c - d⟫ = 0 := by
    have e : b' - c = α4 • (a - d) + (γ4 - 1) • (c - d) := by rw [hb']; module
    have e2 : d - b = -(b - d) := by abel
    rw [e, e2, inner_neg_right, inner_add_left, inner_smul_left, inner_smul_left] at h0
    simp only [conj_trivial] at h0
    rw [hpq'] at h0
    have h1 : (γ4 - 1) * ⟪c - d, b - d⟫ = 0 := by linarith
    rcases mul_eq_zero.1 h1 with h | h
    · nlinarith
    · rw [real_inner_comm]; exact h
  exact ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα1, hb1, hg4, hβ6, hγ6, hfa hfar, hs, hpq', hqr⟩

/-! ## U2b: pentagon `(b,c',b',c,d)` at `d - b`, frame `(a-d, c-d, d-b)` -/

/-- ccw pentagon `b (0,0,-1), c' (1,0,-β1), b' (α4,γ4,0), c (0,1,0), d 0`. -/
def k17gcPentU2 (α4 β1 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (0, 0, -1) (1, 0, -β1) (α4, γ4, 0) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 6400000 in
theorem k17gc_pentU2_tsc {α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hα4 : 0 < α4) (hα41 : α4 ≤ 1) (hβ1 : 0 < β1)
    (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv1 : 0 < v1) (hv2 : v2 < 0) (hc : 0 < γ4 * v1 + (1 - α4) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcPentU2 α4 β1 γ4 (i + 1) - k17gcPentU2 α4 β1 γ4 i)
        (k17gcPentU2 α4 β1 γ4 j - k17gcPentU2 α4 β1 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ6, -β6)], ∀ i : ZMod 5,
      TSc 1 (k17gcPentU2 α4 β1 γ4 (i + 1) - k17gcPentU2 α4 β1 γ4 i) (t - k17gcPentU2 α4 β1 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have n2 : 0 < -v2 := by linarith
  have ka : 0 ≤ 1 - α4 := by linarith
  have kag := sub_pos.2 hαγ
  have kg0 : 0 < γ4 := hγ4
  have kb0 : 0 < β1 := hβ1
  have k1 := mul_pos hα4 n2
  have k2 := mul_pos kg0 n2
  have k3 := mul_pos kb0 n2
  have k4 := mul_pos kb0 hv1
  have k5 := mul_pos kg0 hv1
  have k6 := mul_pos hα4 hv1
  have k7 := mul_pos hγ6 hv1
  have k8 := mul_pos hβ6 n2
  have k9 := mul_pos kag hc
  have k9' := mul_pos kag n2
  have k9'' := mul_pos kag hv1
  have k10 := mul_pos kb0 hc
  have k11 := mul_pos (mul_pos kb0 kg0) hv1
  have k12 := mul_nonneg (mul_pos kb0 n2).le ka
  have k13 := mul_nonneg ka n2.le
  have k14 := mul_pos (mul_pos hβ6 kg0) hv1
  have k15 := mul_nonneg (mul_pos hβ6 n2).le ka
  have k16 := mul_pos (sub_pos.2 hγ61) hv1
  have k17 := mul_pos (mul_pos hγ6 kg0) hv1
  have k18 := mul_pos hβ6 hc
  have k19 := mul_pos hγ6 hc
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcPentU2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcPentU2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcPentU2_inj {α4 β1 γ4 : ℝ} (hα4 : 0 < α4) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) :
    ∀ i j, k17gcPentU2 α4 β1 γ4 i = k17gcPentU2 α4 β1 γ4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcPentU2, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- **U2b cell** (`pr > 0`). -/
theorem k17gc_u2b_cell {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 ≤ 1) (hβ1 : 0 < β1)
    (hγ4 : 0 < γ4) (hαγ : 1 < α4 + γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hpr : 0 < ⟪a - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := c - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by
      simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h]
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17gc_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gc_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17gc_fp, hR]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17gc_fp, hQ]; module
  have Ea' : fpoint P Q R d (0, γ6, -β6) = a' := by rw [k17gc_fp, ha', hQ, hR]; module
  have Eb' : fpoint P Q R d (α4, γ4, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (1, 0, -β1) = c' := by rw [k17gc_fp, hc', hP, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 := k17gc_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  have hPR : ⟪P, R⟫ = 0 := by
    rw [hP, hR, show d - b = -(b - d) by abel, inner_neg_right, hpq, neg_zero]
  have hQR : ⟪Q, R⟫ = 0 := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right, real_inner_comm, hqr, neg_zero]
  have hPQ : 0 < ⟪P, Q⟫ := hpr
  have hQ0 : Q ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hQQ : 0 < ⟪Q, Q⟫ := real_inner_self_pos.2 hQ0
  set K := γ4 * ⟪Q, Q⟫ + (1 - α4) * ⟪P, Q⟫ with hK
  have hK0 : 0 < K := by rw [hK]; nlinarith [mul_nonneg (sub_nonneg.2 hα41) hPQ.le, mul_pos hγ4 hQQ]
  refine ⟨R, hR0, ?_⟩
  refine cyc_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPentU2 α4 β1 γ4)
    (k17gcPentU2_inj hα4 hβ1 hγ4) ?_ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, γ6, -β6)] ?_ (u1 := K) (u2 := 0)
    (t1 := 0) (t2 := -(γ4 * ⟪P, Q⟫)) (by nlinarith [mul_pos hK0 (mul_pos (by linarith : (0:ℝ) < γ4) hPQ)])
    (lo := 0) (hi := 1) (by norm_num)
    (fun v1 v2 => 0 < v1 ∧ v2 < 0 ∧ 0 < γ4 * v1 + (1 - α4) * v2 ∧ 0 < v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫) ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gcPentU2, pc5_0, Eb]; simp [V8]
    · simp only [k17gcPentU2, pc5_1, Ec']; simp [V8]
    · simp only [k17gcPentU2, pc5_2, Eb']; simp [V8]
    · simp only [k17gcPentU2, pc5_3, Ec]; simp [V8]
    · simp only [k17gcPentU2, pc5_4, Ed]; simp [V8]
  · intro y hy
    have hV : y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨
        y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (0, γ6, -β6) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    have hg0 : 0 < γ4 := hγ4
    refine ⟨by nlinarith, by nlinarith [mul_pos (mul_pos h0 hg0) hPQ], ?_, ?_⟩
    · have e : γ4 * (K + lam * 0) + (1 - α4) * (0 + lam * -(γ4 * ⟪P, Q⟫)) =
          γ4 * (γ4 * ⟪Q, Q⟫ + (1 - lam) * (1 - α4) * ⟪P, Q⟫) := by rw [hK]; ring
      rw [e]
      exact mul_pos hg0 (by nlinarith [mul_nonneg (mul_pos (sub_pos.2 h1) hPQ).le (sub_nonneg.2 hα41), mul_pos hg0 hQQ])
    · have e : (K + lam * 0) * ⟪P, Q⟫ + (0 + lam * -(γ4 * ⟪P, Q⟫)) * ⟪Q, Q⟫ =
          ⟪P, Q⟫ * (γ4 * (1 - lam) * ⟪Q, Q⟫ + (1 - α4) * ⟪P, Q⟫) := by rw [hK]; ring
      rw [e]
      exact mul_pos hPQ (by nlinarith [mul_pos (mul_pos hg0 (sub_pos.2 h1)) hQQ, mul_nonneg (sub_nonneg.2 hα41) hPQ.le])
  · rintro v1 v2 ⟨hv1, hv2, hc, -⟩
    exact k17gc_pentU2_tsc hα4 hα41 hβ1 hγ4 hαγ hβ6 hγ6 hγ61 hv1 hv2 hc
  · rintro v1 v2 ⟨-, -, -, hf⟩ hinj
    refine lexUni5_two _ _ hinj ?_ ?_ (Or.inr ?_)
    · left; simp only [k17gcPentU2, pc5_1, pc5_2, hz, hPR, hQR]; nlinarith
    · right
      simp only [k17gcPentU2, pc5_3, pc5_4]
      refine ⟨by rw [hz, hz, hPR, hQR]; simp only; ring, ?_⟩
      rw [k17f_wexp, k17f_wexp]; simp only; nlinarith
    · left; simp only [k17gcPentU2, pc5_0, pc5_4, hz, hPR, hQR]; nlinarith

/-! ## U2a: quadrilateral `(a,c',a',b')` at `c' - b`, frame `(b-d, c-d, c'-b)` -/

/-- ccw quadrilateral `a (1-β1,0,1), c' (1,0,1), a' (β6,γ6,0), b' (1-γ4,γ4,α4)`. -/
def k17gcQ4 (α4 β1 γ4 β6 γ6 : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(1 - β1, 0, 1), (1, 0, 1), (β6, γ6, 0), (1 - γ4, γ4, α4)]

theorem k17gcQ4_0 : k17gcQ4 α4 β1 γ4 β6 γ6 0 = (1 - β1, 0, 1) := rfl
theorem k17gcQ4_1 : k17gcQ4 α4 β1 γ4 β6 γ6 1 = (1, 0, 1) := rfl
theorem k17gcQ4_2 : k17gcQ4 α4 β1 γ4 β6 γ6 2 = (β6, γ6, 0) := rfl
theorem k17gcQ4_3 : k17gcQ4 α4 β1 γ4 β6 γ6 3 = (1 - γ4, γ4, α4) := rfl

theorem k17gc_z4 : (0 : ZMod 4) + 1 = 1 ∧ (1 : ZMod 4) + 1 = 2 ∧ (2 : ZMod 4) + 1 = 3 ∧ (3 : ZMod 4) + 1 = 0 := by
  decide

theorem k17gc_z4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

set_option maxHeartbeats 6400000 in
theorem k17gc_q4_tsc {α4 β1 γ4 β6 γ6 v1 v2 : ℝ} (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 1 < β1)
    (hγ4 : 1 < γ4) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6)
    (hv2 : 0 < v2) (hc : 0 < (β6 - 1) * v2 - γ6 * v1) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcQ4 α4 β1 γ4 β6 γ6 (i + 1) - k17gcQ4 α4 β1 γ4 β6 γ6 i)
        (k17gcQ4 α4 β1 γ4 β6 γ6 j - k17gcQ4 α4 β1 γ4 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0), (0, 1, 0)], ∀ i : ZMod 4,
      TSc 1 (k17gcQ4 α4 β1 γ4 β6 γ6 (i + 1) - k17gcQ4 α4 β1 γ4 β6 γ6 i) (t - k17gcQ4 α4 β1 γ4 β6 γ6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3⟩ := k17gc_z4
  have ka := sub_pos.2 hα41
  have kb := sub_pos.2 hβ1
  have kg := sub_pos.2 hγ4
  have kg0 : 0 < γ4 := by linarith
  have kb0 : 0 < β1 := by linarith
  have ks := sub_pos.2 hs
  have k1 := mul_pos kg0 ks
  have k2 := mul_pos kb0 kg
  have k3 := mul_pos kb hγ6
  have k4 := mul_pos kb0 hγ6
  have k5 := mul_pos kg0 hγ6
  have k6 := mul_pos kb0 hv2
  have k7 := mul_pos kb hv2
  have k8 := mul_pos kg hγ6
  have k9 := mul_pos (sub_pos.2 hγ61) kg0
  have k10 := mul_pos kb0 ks
  have k11 := mul_pos (mul_pos kb0 kg0) ks
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k17gc_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, s0, s1, s2, s3, k17gcQ4_0, k17gcQ4_1, k17gcQ4_2, k17gcQ4_3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, s0, s1, s2, s3, k17gcQ4_0, k17gcQ4_1, k17gcQ4_2, k17gcQ4_3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcQ4_inj {α4 β1 γ4 β6 γ6 : ℝ} (hα4 : 0 < α4) (hβ1 : 1 < β1) (hγ4 : 1 < γ4) (hγ6 : 0 < γ6) :
    ∀ i j, k17gcQ4 α4 β1 γ4 β6 γ6 i = k17gcQ4 α4 β1 γ4 β6 γ6 j → i = j := by
  intro i j h
  rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl <;>
    rcases k17gc_z4_cases j with rfl | rfl | rfl | rfl <;>
    simp only [k17gcQ4_0, k17gcQ4_1, k17gcQ4_2, k17gcQ4_3, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- **U2a cell** (`ζ_{a-d}(a,b') = ⟪a-b',a-d⟫ > 0`): quadrilateral `(a,c',a',b')` at `c' - b`. -/
theorem k17gc_u2a_cell {a a' b b' c c' d : ℝ³} {α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hα4 : 0 < α4) (hα41 : α4 < 1) (hβ1 : 1 < β1)
    (hg4 : γ4 = 1 + α4 * (β1 - 1)) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6)
    (hpq : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ = 0) (hL : 0 < ⟪a - b', a - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  have hγ4 : 1 < γ4 := by rw [hg4]; nlinarith [mul_pos hα4 (sub_pos.2 hβ1)]
  have hzab : ⟪b', c' - b⟫ < ⟪a, c' - b⟫ := by
    have e1 : c' - b = (a - d) + (β1 - 1) • (b - d) := by rw [hc']; module
    have e2 : a - b' = (1 - α4) • (a - d) - γ4 • (c - d) := by rw [hb']; module
    have e3 : ⟪a - b', b - d⟫ = 0 := by
      rw [e2, inner_sub_left, inner_smul_left, inner_smul_left, hpq, real_inner_comm, hqr]; simp
    have : ⟪a - b', c' - b⟫ = ⟪a - b', a - d⟫ := by
      rw [e1, inner_add_right, inner_smul_right, e3, mul_zero, add_zero]
    rw [inner_sub_left] at this; linarith
  set P := b - d with hP
  set Q := c - d with hQ
  set R := c' - b with hR
  have hRe : R = (a - d) + (β1 - 1) • P := by rw [hR, hc', hP]; module
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by
      rw [hRe]; simp only [hP, hQ, det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [e, h]
  have Ea : fpoint P Q R d (1 - β1, 0, 1) = a := by rw [k17gc_fp, hRe]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17gc_fp]; module
  have Eb : fpoint P Q R d (1, 0, 0) = b := by rw [k17gc_fp, hP]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17gc_fp, hQ]; module
  have Ea' : fpoint P Q R d (β6, γ6, 0) = a' := by rw [k17gc_fp, ha', hP, hQ]; module
  have Ec' : fpoint P Q R d (1, 0, 1) = c' := by rw [k17gc_fp, hR, hP]; module
  have Eb' : fpoint P Q R d (1 - γ4, γ4, α4) = b' := by
    rw [k17gc_fp, hRe, hb', hQ, hP, hg4]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 := k17gc_r0 hΔ
  have hP0 : P ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  have hPR : 0 < ⟪P, R⟫ := by
    rw [hRe, inner_add_right, inner_smul_right, real_inner_comm, hpq, zero_add]
    exact mul_pos (sub_pos.2 hβ1) (real_inner_self_pos.2 hP0)
  refine ⟨R, hR0, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 4) (by norm_num) (k17gcQ4 α4 β1 γ4 β6 γ6)
    (k17gcQ4_inj hα4 hβ1 hγ4 hγ6) (u1 := -1) (u2 := γ6) (t1 := -1) (t2 := 0) (by nlinarith) ?_ ?_ ?_ ?_
  · intro i
    rcases k17gc_z4_cases i with rfl | rfl | rfl | rfl
    · rw [k17gcQ4_0, Ea]; simp [V8]
    · rw [k17gcQ4_1, Ec']; simp [V8]
    · rw [k17gcQ4_2, Ea']; simp [V8]
    · rw [k17gcQ4_3, Eb']; simp [V8]
  · intro lam h0 h1 D hD
    have := (k17gc_q4_tsc hα4 hα41 hβ1 hγ4 hβ6 hγ6 hγ61 hs (v1 := -1 + lam * -1) (v2 := γ6 + lam * 0)
      (by linarith) (by nlinarith [mul_pos hγ6 (show (0:ℝ) < β6 + lam by linarith)])).1
    intro i j h1 h2
    exact tsc_scale hD (this i j h1 h2)
  · intro y hy hyx
    have hV : y = fpoint P Q R d (1 - β1, 0, 1) ∨ y = fpoint P Q R d (1, 0, 1) ∨ y = fpoint P Q R d (β6, γ6, 0) ∨
        y = fpoint P Q R d (1 - γ4, γ4, α4) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
        y = fpoint P Q R d (0, 1, 0) := by
      rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    have hT := fun lam (h0 : (0:ℝ) < lam) (h1 : lam < 1) =>
      (k17gc_q4_tsc hα4 hα41 hβ1 hγ4 hβ6 hγ6 hγ61 hs (v1 := -1 + lam * -1) (v2 := γ6 + lam * 0)
        (by linarith) (by nlinarith [mul_pos hγ6 (show (0:ℝ) < β6 + lam by linarith)])).2
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by rw [k17gcQ4_0])).elim
    · exact (hyx 1 (by rw [k17gcQ4_1])).elim
    · exact (hyx 2 (by rw [k17gcQ4_2])).elim
    · exact (hyx 3 (by rw [k17gcQ4_3])).elim
    · exact ⟨_, rfl, fun lam h0 h1 D hD i => tsc_scale hD (hT lam h0 h1 _ (by simp) i)⟩
    · exact ⟨_, rfl, fun lam h0 h1 D hD i => tsc_scale hD (hT lam h0 h1 _ (by simp) i)⟩
    · exact ⟨_, rfl, fun lam h0 h1 D hD i => tsc_scale hD (hT lam h0 h1 _ (by simp) i)⟩
  · intro w hw
    refine k17gc_lexUni4 _ w hw ?_ ?_
    · left; simp only [k17gcQ4_0, k17gcQ4_1, hz]; nlinarith
    · left; simp only [k17gcQ4_0, k17gcQ4_3]; rw [Ea, Eb']; exact hzab

/-- **U2** (`K14LeftPa` 2nd disjunct with `β1 > 1`, so `⟪a-d,d-b⟫ = 0`): closed, no leftover
(split by the sign of `⟪a-d,c-d⟫`). -/
theorem k17gc_u2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (h0 : ⟪b' - c, d - b⟫ = 0)
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hpq : ⟪a - d, d - b⟫ = 0) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hα4, hα41, hβ1, hg4, hβ6, hγ6, hγ61, hs, hpq', hqr⟩ :=
    k17gc_u2_frame W hT' hκ (k5z_far1 W hT' hnT) h0 hα hβ hpq
  have hγ4 : 1 < γ4 := by rw [hg4]; nlinarith [mul_pos hα4 (sub_pos.2 hβ1)]
  rcases lt_or_ge 0 ⟪a - d, c - d⟫ with hpr | hpr
  · exact k17gc_u2b_cell hdet hc' hb' ha' hα4 hα41.le (by linarith) (by linarith) (by linarith) hβ6 hγ6 hγ61
      hpq' hqr hpr
  · refine k17gc_u2a_cell hdet hc' hb' ha' hα4 hα41 hβ1 hg4 hβ6 hγ6 hγ61 hs hpq' hqr ?_
    have hp0 : a - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
    have hpp := real_inner_self_pos.2 hp0
    have e2 : a - b' = (1 - α4) • (a - d) - γ4 • (c - d) := by rw [hb']; module
    rw [e2, inner_sub_left, inner_smul_left, inner_smul_left, real_inner_comm (a - d) (c - d)]
    simp only [conj_trivial]
    nlinarith [mul_pos (sub_pos.2 hα41) hpp, mul_nonneg (by linarith : (0:ℝ) ≤ γ4) (neg_nonneg.2 hpr)]

end C2
end Type08Sp
end Minimality
