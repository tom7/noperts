module

public import Minimality.Type08S.C2K17F1A
public import Minimality.Type08S.C2K17F2A

@[expose] public section


/-!
# K17GC / GC1: S1.5 (Pa(3): `α4 = 1`, `β1 = 1`, view `d - b`), split by `ζ_{a-c'}(a,d) = ⟪a-d, a-c'⟫`.

T' frame with `α4 = β1 = γ4 = 1`: `c' = d + p + q`, `b' = d + p + r`, `a' = d + β6 q + γ6 r` (`p,q,r = a-d,b-d,c-d`).
The slice has no metric tie, so the cells are metric-free; the literal is `⟪a-d,a-c'⟫ = -⟪p,q⟫`.
Frame `(P,Q,R) = (c-d, a-d, d-b)`: `a (0,1,0)`, `d 0`, `b (0,0,-1)`, `a' (γ6,0,-β6)`, `c (1,0,0)`, `b' (1,1,0)`,
`c' (0,1,-1)`; depths `z = ⟪x,R⟫`: `⟪P,R⟫ = -qr`, `⟪Q,R⟫ = -pq`, `⟪R,R⟫ = qq`.
* `pq < 0` (S1.5a): hexagon `(a,d,b,a',c,b')`, tilt cone `v1 > 0 > v2` (zero screen edge `d b`), tilt `(1+λ,-1)`;
  lex: `a > d > b`, `b' > c`, `a'` not a depth peak (`β6+γ6 > 1`, `γ6 < 1`): w-free.
* `pq > 0` (S1.5b): pentagon `(c,b',c',a,d)`, cone `v1, v2 > 0` (zero screen edge `c' a`), tilt `(1,1+λ)`;
  lex `b' < c`, `c' < a < d`: w-free.
* `pq = 0`: leftover (the literal's tie).
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

theorem k17gc_fp (P Q R d : ℝ³) (x y z : ℝ) : fpoint P Q R d (x, y, z) = d + x • P + y • Q + z • R := by
  simp only [fpoint, fcomb]; module

theorem k17gc_r0 {P Q R : ℝ³} (h : det3 P Q R ≠ 0) : R ≠ 0 := by
  intro h0; rw [h0] at h; simp [det3_expand] at h

/-- 6-cycle lex unimodality: `0 > 1 > 2`, `4 < 5`, `3` below `2` or `4` (peak at `0` or `5`). -/
theorem k17gc_lexUni6_a (z w : ZMod 6 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h45 : LexLt (z 4, w 4) (z 5, w 5))
    (h3 : LexLt (z 3, w 3) (z 2, w 2) ∨ LexLt (z 3, w 3) (z 4, w 4)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h05 : (z 0, w 0) ≠ (z 5, w 5) := by
    intro h; have := hinj 0 5 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 6 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := fun g => Fin.sum_univ_six (f := g)
  rw [hs]
  have e0 : (0 : ZMod 6) - 1 = 5 := by decide
  have e1 : (1 : ZMod 6) - 1 = 0 := by decide
  have e2 : (2 : ZMod 6) - 1 = 1 := by decide
  have e3 : (3 : ZMod 6) - 1 = 2 := by decide
  have e4 : (4 : ZMod 6) - 1 = 3 := by decide
  have e5 : (5 : ZMod 6) - 1 = 4 := by decide
  have f0 : (0 : ZMod 6) + 1 = 1 := by decide
  have f1 : (1 : ZMod 6) + 1 = 2 := by decide
  have f2 : (2 : ZMod 6) + 1 = 3 := by decide
  have f3 : (3 : ZMod 6) + 1 = 4 := by decide
  have f4 : (4 : ZMod 6) + 1 = 5 := by decide
  have f5 : (5 : ZMod 6) + 1 = 0 := by decide
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) +
    (if LexLt (z (5 - 1), w (5 - 1)) (z 5, w 5) ∧ LexLt (z (5 + 1), w (5 + 1)) (z 5, w 5) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5]
  have a10 := lexLt_asymm h10
  have a21 := lexLt_asymm h21
  have a45 := lexLt_asymm h45
  rcases lexLt_total h05 with h | h <;> have a := lexLt_asymm h <;>
    rcases h3 with h3 | h3 <;> have a3 := lexLt_asymm h3 <;>
    simp [h, a, h10, a10, h21, a21, h45, a45, h3, a3]

/-! ## Frame of the Pa(3) slice with `β1 = 1` -/

/-- **Relation lemma, Pa(3) with `β1 = 1`**: T' frame with `α4 = β1 = γ4 = 1`. -/
theorem k17gc_pa3_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hfar : W.F.abc'.f c < W.F.abc'.f a')
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) :
    ∃ β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧ 0 < β6 ∧ 0 < γ6 ∧ γ6 < 1 ∧ 1 < β6 + γ6 := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4, hγ4, hαγ, hβ6, hγ6, hs, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) := mul_self_pos.2 hdet
  rw [det_beta1 hc'] at hβ
  have hb1 : β1 = 1 := by
    have : (β1 - 1) * (det3 (a - d) (b - d) (c - d) * det3 (a - d) (b - d) (c - d)) = 0 := by
      linear_combination hβ
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hΔ2.ne'
  subst hb1
  rw [det_alpha4 hb'] at hα
  have ha1 : α4 = 1 := by
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  subst ha1
  have hg4 : γ4 = 1 := by
    have := (planar_a_iff hdet hc' hb').1 hκ
    linarith
  subst hg4
  exact ⟨β6, γ6, hdet, hc', hb', ha', hβ6, hγ6, hfa hfar, hs⟩

/-! ## S1.5a: hexagon `(a,d,b,a',c,b')` at `d - b` -/

/-- ccw hexagon `a (0,1,0), d 0, b (0,0,-1), a' (γ6,0,-β6), c (1,0,0), b' (1,1,0)` (frame `(c-d, a-d, d-b)`). -/
def k17gcHex5 (β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 1, 0) (0, 0, 0) (0, 0, -1) (γ6, 0, -β6) (1, 0, 0) (1, 1, 0)

set_option maxHeartbeats 3200000 in
theorem k17gc_hex5_tsc {D β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k17gcHex5 β6 γ6 (i + 1) - k17gcHex5 β6 γ6 i) (k17gcHex5 β6 γ6 j - k17gcHex5 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 6, TSc D (k17gcHex5 β6 γ6 (i + 1) - k17gcHex5 β6 γ6 i) ((0, 1, -1) - k17gcHex5 β6 γ6 i)
      (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kb := mul_pos hD hβ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kbv2 := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have ksv2 := mul_pos (mul_pos hD (sub_pos.2 hs)) (neg_pos.2 hv2)
  constructor
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcHex5, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcHex5, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcHex5_inj {β6 γ6 : ℝ} (hβ6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j, k17gcHex5 β6 γ6 i = k17gcHex5 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcHex5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

/-! ## S1.5b: pentagon `(c,b',c',a,d)` at `d - b` -/

/-- ccw pentagon `c (1,0,0), b' (1,1,0), c' (0,1,-1), a (0,1,0), d 0` (frame `(c-d, a-d, d-b)`). -/
def k17gcPent5 : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (1, 1, 0) (0, 1, -1) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k17gc_pent5_tsc {D β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17gcPent5 (i + 1) - k17gcPent5 i) (k17gcPent5 j - k17gcPent5 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17gcPent5 (i + 1) - k17gcPent5 i) ((0, 0, -1) - k17gcPent5 i) (v1, v2, 0)) ∧
    (∀ i : ZMod 5, TSc D (k17gcPent5 (i + 1) - k17gcPent5 i) ((γ6, 0, -β6) - k17gcPent5 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kg := mul_pos hD hγ6
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kb := mul_pos hD hβ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kgv2 := mul_pos (mul_pos hD hγ6) hv2
  have kbv2 := mul_pos (mul_pos hD hβ6) hv2
  refine ⟨?_, ?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcPent5, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  all_goals
    intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcPent5, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcPent5_inj : ∀ i j, k17gcPent5 i = k17gcPent5 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcPent5, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

/-! ## The two cells and S1.5 -/

set_option maxHeartbeats 6400000 in
/-- **S1.5 cells** in the frame (`pq ≠ 0`). -/
theorem k17gc_s15_cells {a a' b b' c c' d : ℝ³} {β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6) (hpq : ⟪a - d, b - d⟫ ≠ 0) : HasLexCell (V8 a a' b b' c c' d) := by
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
  have Eb' : fpoint P Q R d (1, 1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gc_r0 hΔ)
  have hQR : ⟪Q, R⟫ = -⟪a - d, b - d⟫ := by
    rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right]
  refine ⟨R, k17gc_r0 hΔ, ?_⟩
  rcases lt_or_gt_of_ne hpq with hn | hp
  · -- S1.5a: hexagon
    have hQR0 : 0 < ⟪Q, R⟫ := by rw [hQR]; linarith
    refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17gcHex5 β6 γ6)
      (k17gcHex5_inj hβ6 hγ6) (u1 := 1) (u2 := -1) (t1 := 1) (t2 := 0) (by norm_num) ?_ ?_ ?_ ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcHex5, pc6_0, Ea]; simp [V8]
      · simp only [k17gcHex5, pc6_1, Ed]; simp [V8]
      · simp only [k17gcHex5, pc6_2, Eb]; simp [V8]
      · simp only [k17gcHex5, pc6_3, Ea']; simp [V8]
      · simp only [k17gcHex5, pc6_4, Ec]; simp [V8]
      · simp only [k17gcHex5, pc6_5, Eb']; simp [V8]
    · intro lam h0 h1 D hD
      exact (k17gc_hex5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
          y = fpoint P Q R d (γ6, 0, -β6) ∨ y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, 1, 0) ∨
          y = fpoint P Q R d (0, 1, -1) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17gcHex5, pc6_0])).elim
      · exact (hyx 1 (by simp only [k17gcHex5, pc6_1])).elim
      · exact (hyx 2 (by simp only [k17gcHex5, pc6_2])).elim
      · exact (hyx 3 (by simp only [k17gcHex5, pc6_3])).elim
      · exact (hyx 4 (by simp only [k17gcHex5, pc6_4])).elim
      · exact (hyx 5 (by simp only [k17gcHex5, pc6_5])).elim
      · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
        exact (k17gc_hex5_tsc hD hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)).2 i
    · intro w hw
      -- depths: a = Qr, d = 0, b = -RR, a' = γ6 Pr - β6 RR, c = Pr, b' = Pr + Qr
      refine k17gc_lexUni6_a _ w hw ?_ ?_ ?_ ?_
      · left; simp only [k17gcHex5, pc6_0, pc6_1, hz]; nlinarith
      · left; simp only [k17gcHex5, pc6_1, pc6_2, hz]; nlinarith
      · left; simp only [k17gcHex5, pc6_4, pc6_5, hz]; nlinarith
      · simp only [k17gcHex5, pc6_2, pc6_3, pc6_4, hz, LexLt]
        by_contra hh
        push Not at hh
        obtain ⟨⟨h2, -⟩, ⟨h4, -⟩⟩ := hh
        -- a' ≥ b: (1-β6) RR + γ6 Pr ≥ 0;  a' ≥ c: (γ6 - 1) Pr ≥ β6 RR
        nlinarith [mul_le_mul_of_nonneg_left h4 hγ6.le, mul_le_mul_of_nonneg_left h2 (sub_pos.2 hγ61).le,
          mul_pos (sub_pos.2 hs) hRR]
  · -- S1.5b: pentagon
    have hQR0 : ⟪Q, R⟫ < 0 := by rw [hQR]; linarith
    refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) k17gcPent5
      k17gcPent5_inj (u1 := 1) (u2 := 1) (t1 := 0) (t2 := 1) (by norm_num) ?_ ?_ ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcPent5, pc5_0, Ec]; simp [V8]
      · simp only [k17gcPent5, pc5_1, Eb']; simp [V8]
      · simp only [k17gcPent5, pc5_2, Ec']; simp [V8]
      · simp only [k17gcPent5, pc5_3, Ea]; simp [V8]
      · simp only [k17gcPent5, pc5_4, Ed]; simp [V8]
    · intro lam h0 h1 D hD
      exact (k17gc_pent5_tsc hD hβ6 hγ6 hγ61 hs (by norm_num) (by linarith)).1
    · intro y hy hyx
      have hV : y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (1, 1, 0) ∨ y = fpoint P Q R d (0, 1, -1) ∨
          y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
          y = fpoint P Q R d (γ6, 0, -β6) := by
        rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
      rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hyx 0 (by simp only [k17gcPent5, pc5_0])).elim
      · exact (hyx 1 (by simp only [k17gcPent5, pc5_1])).elim
      · exact (hyx 2 (by simp only [k17gcPent5, pc5_2])).elim
      · exact (hyx 3 (by simp only [k17gcPent5, pc5_3])).elim
      · exact (hyx 4 (by simp only [k17gcPent5, pc5_4])).elim
      · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
        exact (k17gc_pent5_tsc hD hβ6 hγ6 hγ61 hs (by norm_num) (by linarith)).2.1 i
      · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
        exact (k17gc_pent5_tsc hD hβ6 hγ6 hγ61 hs (by norm_num) (by linarith)).2.2 i
    · intro w hw
      refine lexUni5_top _ w hw ?_ ?_ ?_
      · left; simp only [k17gcPent5, pc5_0, pc5_1, hz]; nlinarith
      · left; simp only [k17gcPent5, pc5_2, pc5_3, hz]; nlinarith
      · left; simp only [k17gcPent5, pc5_3, pc5_4, hz]; nlinarith

/-- **S1.5** (`K14LeftPa` 3rd disjunct, `β1 = 1` branch: `α4 = 1`, `β1 = 1`): a cell, or the literal's tie
`⟪a-d, a-c'⟫ = 0`. -/
theorem k17gc_s15 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPa a a' b b' c c' d)
    (hα : det3 (b' - a) (b - d) (c - d) = 0)
    (hβ : det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪a - d, a - c'⟫ = 0 := by
  obtain ⟨hT', hnT, hκ, -⟩ := h
  obtain ⟨β6, γ6, hdet, hc', hb', ha', hβ6, hγ6, hγ61, hs⟩ :=
    k17gc_pa3_frame W hT' hκ (k5z_far1 W hT' hnT) hα hβ
  have e : ⟪a - d, a - c'⟫ = -⟪a - d, b - d⟫ := by
    have : a - c' = -(b - d) := by rw [hc']; module
    rw [this, inner_neg_right]
  by_cases h0 : ⟪a - d, b - d⟫ = 0
  · right; rw [e, h0, neg_zero]
  · exact Or.inl (k17gc_s15_cells hdet hc' hb' ha' hβ6 hγ6 hγ61 hs h0)

end C2
end Type08Sp
end Minimality
