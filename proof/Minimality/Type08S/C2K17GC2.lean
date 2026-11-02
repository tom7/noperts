module

public import Minimality.Type08S.C2K17GC1

@[expose] public section


/-!
# K17GC / GC2: S1.6 (`K6t3LeftPc`: QPc, `u = ⟪c-a',a-d⟫ = 0 ≤ w = ⟪c-d,c-a'⟫`), split by `⟪a-d, a-c'⟫ = -β1 pq`.

Pc frame: `α4 = β6 = 1`, `c' = d + p + β1 q`, `b' = d + p + γ4 r`, `a' = d + q + γ6 r`, `γ6 < 1`, `β1 (1-γ6) < γ4`.
* `pq < 0` (S1.6a): hexagon `(a,b',c,a',b,d)` at `c - a'` (frame of `k6t3_pc1`: `P = p`, `Q = q/m`, `R = (c-a')/m`,
  `m = 1-γ6`).  `z(a) = z(d)` (the tie `u = 0`); tilt cone `v1 < 0 ∧ v2 < (γ4-1) v1`; lex needs `w(a) > w(d)`, i.e.
  `v1 ⟪P,P⟫ + v2 ⟪P,Q⟫ > 0`: segment `(λ⟪P,Q⟫, -X)`, `X = ⟪P,P⟫ - (γ4+1)⟪P,Q⟫`.  Needs `w > 0`; `w = 0` (the view
  `c - a'` normal to the face `Q_ac`: 4-plateau `c,b',a,d`) is left over.
* `pq > 0` (S1.6b): view `d - b`, frame `(c-d, a-d, d-b)`.  The K15 pentagon `(a,d,c,b',c')` FAILS (two peaks d, b')
  on `qr > 0 ∧ pq < (1-γ4) qr ∧ β1 qq > γ4 qr` (metric-free Gram region the samplers rarely reach; probe
  `probe16b.txt`).  Split: pentagon `(c,b',c',a,d)` (cone `v1,v2 > 0`) when `⟪c-d,d-b⟫ > 0 ∨ z(b') < z(c) ∨ z(b') < z(c')`;
  hexagon `(a,d,b,a',c,b')` (cone `v1 > 0 > v2`, single peak `d`) when `⟪c-d,d-b⟫ < 0 ∧ (z(c) < z(a') ∨ z(c) < z(b'))`;
  on the tie `z(c) = z(b')` (`⟪c-b',d-b⟫ = 0`) the tilt decides: `A = ⟪c-b',c-d⟫ > 0` pentagon, `A < 0` hexagon;
  `A = 0` is left over (codim + 2: `c - b' ⟂ c-d, d-b`).
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

/-! ## Lex lemmas -/

/-- 5-cycle: `2 < 3 < 4`, and not both `0 < 4` (lex) and `1` a peak over `0, 2`. -/
theorem k17gc_lexUni5_b (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h23 : LexLt (z 2, w 2) (z 3, w 3)) (h34 : LexLt (z 3, w 3) (z 4, w 4))
    (hor : LexLt (z 4, w 4) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 0, w 0) ∨ LexLt (z 1, w 1) (z 2, w 2)) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have hne : ∀ i j : ZMod 5, i ≠ j → (z i, w i) ≠ (z j, w j) := fun i j h e =>
    h (hinj i j (congrArg Prod.fst e) (congrArg Prod.snd e))
  have h04 := hne 0 4 (by decide)
  have h01 := hne 0 1 (by decide)
  have h12 := hne 1 2 (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 5 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 := fun g => Fin.sum_univ_five (f := g)
  rw [hs]
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4]
  have a23 := lexLt_asymm h23
  have a34 := lexLt_asymm h34
  have hno : LexLt (z 4, w 4) (z 0, w 0) → LexLt (z 0, w 0) (z 1, w 1) → LexLt (z 1, w 1) (z 2, w 2) → False :=
    fun t y u => by
      have := lexLt_trans_K2 (lexLt_trans_K2 (lexLt_trans_K2 (lexLt_trans_K2 t y) u) h23) h34
      exact lexLt_asymm this this
  rcases lexLt_total h04 with x | x <;> have ax := lexLt_asymm x <;>
    rcases lexLt_total h01 with y | y <;> have ay := lexLt_asymm y <;>
    rcases lexLt_total h12 with u | u <;> have au := lexLt_asymm u <;>
    rcases hor with t | t | t <;>
    (try simp [x, ax, y, ay, u, au, h23, a23, h34, a34]) <;>
    first | exact (hno t y u).elim | exact (lexLt_asymm t ‹_›).elim | exact (hno x y u).elim

/-- 6-cycle with the single peak `1`: `0 < 1 > 2 > 3`, `5 < 0`, `4` below `3` or `5`. -/
theorem k17gc_lexUni6_b (z w : ZMod 6 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : LexLt (z 0, w 0) (z 1, w 1)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h32 : LexLt (z 3, w 3) (z 2, w 2)) (h50 : LexLt (z 5, w 5) (z 0, w 0))
    (h4 : LexLt (z 4, w 4) (z 3, w 3) ∨ LexLt (z 4, w 4) (z 5, w 5)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
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
  have a01 := lexLt_asymm h01
  have a21 := lexLt_asymm h21
  have a32 := lexLt_asymm h32
  have a50 := lexLt_asymm h50
  rcases h4 with h4 | h4 <;> have a4 := lexLt_asymm h4 <;>
    simp [h01, a01, h21, a21, h32, a32, h50, a50, h4, a4]

/-! ## Pc frame -/

/-- **Relation lemma, Pc** (`K5ZsPc`): `α4 = β6 = 1`. -/
theorem k17gc_pc_frame {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZsPc a a' b b' c c' d) :
    ∃ β1 γ4 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d) ∧
      a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d) ∧ 0 < β1 ∧ 0 < γ4 ∧ 0 < γ6 ∧ γ6 < 1 ∧ β1 * (1 - γ6) < γ4 := by
  obtain ⟨hT', hnT, hκc, hα⟩ := h
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfa⟩ :=
    norm08w_coordsTp W hT'
  have hg61 : γ6 < 1 := hfa (k5z_far1 W hT' hnT)
  rw [det_alpha4 hb'] at hα
  have hα41 : α4 = 1 := by
    rcases mul_eq_zero.1 hα with h | h
    · linarith
    · exact absurd h hdet
  have hκ' := (planar_c_iff hdet hb' ha').1 hκc
  subst hα41
  have hβ61 : β6 = 1 := by
    have : γ4 * (1 - β6) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hβ61
  exact ⟨β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hg61, k6t3_facet_a'b'c' W hc' hb' ha' hβ1 hγ4 hγ6⟩

/-! ## S1.6b cells at `d - b` (frame `(c-d, a-d, d-b)`) -/

/-- ccw pentagon `c (1,0,0), b' (γ4,1,0), c' (0,1,-β1), a (0,1,0), d 0`. -/
def k17gcPent6 (β1 γ4 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, 0) (γ4, 1, 0) (0, 1, -β1) (0, 1, 0) (0, 0, 0)

set_option maxHeartbeats 3200000 in
theorem k17gc_pent6_tsc {β1 γ4 γ6 v1 v2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcPent6 β1 γ4 (i + 1) - k17gcPent6 β1 γ4 i) (k17gcPent6 β1 γ4 j - k17gcPent6 β1 γ4 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (γ6, 0, -1)], ∀ i : ZMod 5,
      TSc 1 (k17gcPent6 β1 γ4 (i + 1) - k17gcPent6 β1 γ4 i) (t - k17gcPent6 β1 γ4 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have kb := mul_pos hβ1 hv1
  have kb2 := mul_pos hβ1 hv2
  have kg := mul_pos hγ4 hv2
  have kg1 := mul_pos hγ4 hv1
  have kgb := mul_pos (mul_pos hγ4 hβ1) hv2
  have k6 := mul_pos hγ6 hv2
  have k61 := mul_pos (sub_pos.2 hγ61) hv2
  have kbb := mul_pos hγ4 hβ1
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcPent6, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcPent6, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcPent6_inj {β1 γ4 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) :
    ∀ i j, k17gcPent6 β1 γ4 i = k17gcPent6 β1 γ4 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcPent6, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

/-- ccw hexagon `a (0,1,0), d 0, b (0,0,-1), a' (γ6,0,-1), c (1,0,0), b' (γ4,1,0)`. -/
def k17gcHex6 (γ4 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 1, 0) (0, 0, 0) (0, 0, -1) (γ6, 0, -1) (1, 0, 0) (γ4, 1, 0)

set_option maxHeartbeats 3200000 in
theorem k17gc_hex6_tsc {β1 γ4 γ6 v1 v2 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv1 : 0 < v1) (hv2 : v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc 1 (k17gcHex6 γ4 γ6 (i + 1) - k17gcHex6 γ4 γ6 i) (k17gcHex6 γ4 γ6 j - k17gcHex6 γ4 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), -β1)], ∀ i : ZMod 6,
      TSc 1 (k17gcHex6 γ4 γ6 (i + 1) - k17gcHex6 γ4 γ6 i) (t - k17gcHex6 γ4 γ6 i) (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have n2 : 0 < -v2 := by linarith
  have kb := mul_pos hβ1 hv1
  have kb2 := mul_pos hβ1 n2
  have kg := mul_pos hγ4 n2
  have kg1 := mul_pos hγ4 hv1
  have kgb := mul_pos (mul_pos hγ4 hβ1) n2
  have k6 := mul_pos hγ6 n2
  have k61 := mul_pos (sub_pos.2 hγ61) n2
  have k6v := mul_pos hγ6 hv1
  have kbb := mul_pos hγ4 hβ1
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, k17gcHex6, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gcHex6, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17gcHex6_inj {γ4 γ6 : ℝ} (hγ4 : 0 < γ4) (hγ6 : 0 < γ6) :
    ∀ i j, k17gcHex6 γ4 γ6 i = k17gcHex6 γ4 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gcHex6, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
/-- **S1.6b** in the frame (`pq > 0`): a cell, or the tie `⟪c-b',d-b⟫ = 0` with `⟪c-b',c-d⟫ = 0`. -/
theorem k17gc_s16b_cells {a a' b b' c c' d : ℝ³} {β1 γ4 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + (1 : ℝ) • (a - d) + γ4 • (c - d))
    (ha' : a' = d + (1 : ℝ) • (b - d) + γ6 • (c - d)) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hpq : 0 < ⟪a - d, b - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) ∨ (⟪c - b', d - b⟫ = 0 ∧ ⟪c - b', c - d⟫ = 0) := by
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
  have Ea' : fpoint P Q R d (γ6, 0, -1) = a' := by rw [k17gc_fp, ha', hP, hR]; module
  have Eb' : fpoint P Q R d (γ4, 1, 0) = b' := by rw [k17gc_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (0, 1, -β1) = c' := by rw [k17gc_fp, hc', hQ, hR]; module
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 (k17gc_r0 hΔ)
  have hQR : ⟪Q, R⟫ < 0 := by
    have : ⟪Q, R⟫ = -⟪a - d, b - d⟫ := by
      rw [hQ, hR, show d - b = -(b - d) by abel, inner_neg_right]
    rw [this]; linarith
  have hR0 := k17gc_r0 hΔ
  -- the tie-breaking functional `w(c) - w(b') = v1 A + v2 B`
  set A := (1 - γ4) * ⟪P, P⟫ - ⟪P, Q⟫ with hA
  set B := (1 - γ4) * ⟪P, Q⟫ - ⟪Q, Q⟫ with hB
  have hwcb : ∀ v1 v2 : ℝ, ⟪fpoint P Q R d (1, 0, 0), fcomb P Q R v1 v2 0⟫ -
      ⟪fpoint P Q R d (γ4, 1, 0), fcomb P Q R v1 v2 0⟫ = v1 * A + v2 * B := by
    intro v1 v2; rw [k17f_wexp, k17f_wexp, hA, hB]; simp only; ring
  have hVlist : ∀ y ∈ V8 a a' b b' c c' d, y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨
      y = fpoint P Q R d (0, 1, -β1) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (0, 0, -1) ∨ y = fpoint P Q R d (γ6, 0, -1) := by
    intro y hy
    rw [Ea, Ed, Eb, Ea', Ec, Eb', Ec']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  -- pentagon cell from a segment in the quadrant satisfying its lex condition
  have pent : ∀ u1 u2 t1 t2 : ℝ, u1 * t2 - u2 * t1 ≠ 0 →
      (∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ 0 < u2 + lam * t2 ∧
        (0 < ⟪P, R⟫ ∨ γ4 * ⟪P, R⟫ + ⟪Q, R⟫ < ⟪P, R⟫ ∨ γ4 * ⟪P, R⟫ < -β1 * ⟪R, R⟫ ∨
          (γ4 * ⟪P, R⟫ + ⟪Q, R⟫ = ⟪P, R⟫ ∧ 0 < (u1 + lam * t1) * A + (u2 + lam * t2) * B))) →
      HasLexCell (V8 a a' b b' c c' d) := by
    intro u1 u2 t1 t2 hut hseg
    refine ⟨R, hR0, ?_⟩
    refine cyc_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gcPent6 β1 γ4)
      (k17gcPent6_inj hβ1 hγ4) ?_ [((0 : ℝ), (0 : ℝ), (-1 : ℝ)), (γ6, 0, -1)] ?_ hut (lo := 0) (hi := 1)
      (by norm_num)
      (fun v1 v2 => 0 < v1 ∧ 0 < v2 ∧
        (0 < ⟪P, R⟫ ∨ γ4 * ⟪P, R⟫ + ⟪Q, R⟫ < ⟪P, R⟫ ∨ γ4 * ⟪P, R⟫ < -β1 * ⟪R, R⟫ ∨
          (γ4 * ⟪P, R⟫ + ⟪Q, R⟫ = ⟪P, R⟫ ∧ 0 < v1 * A + v2 * B))) hseg ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcPent6, pc5_0, Ec]; simp [V8]
      · simp only [k17gcPent6, pc5_1, Eb']; simp [V8]
      · simp only [k17gcPent6, pc5_2, Ec']; simp [V8]
      · simp only [k17gcPent6, pc5_3, Ea]; simp [V8]
      · simp only [k17gcPent6, pc5_4, Ed]; simp [V8]
    · intro y hy
      rcases hVlist y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inl ⟨1, rfl⟩
      · exact Or.inl ⟨2, rfl⟩
      · exact Or.inl ⟨3, rfl⟩
      · exact Or.inl ⟨4, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
    · rintro v1 v2 ⟨hv1, hv2, -⟩
      exact k17gc_pent6_tsc hβ1 hγ4 hγ6 hγ61 hv1 hv2
    · rintro v1 v2 ⟨hv1, hv2, hL⟩ hinj
      refine k17gc_lexUni5_b _ _ hinj ?_ ?_ ?_
      · left; simp only [k17gcPent6, pc5_2, pc5_3, hz]; nlinarith [mul_pos hβ1 hRR]
      · left; simp only [k17gcPent6, pc5_3, pc5_4, hz]; nlinarith
      · rcases hL with hL | hL | hL | ⟨hL, hf⟩
        · left; left; simp only [k17gcPent6, pc5_0, pc5_4, hz]; nlinarith
        · right; left; left; simp only [k17gcPent6, pc5_0, pc5_1, hz]; nlinarith
        · right; right; left; simp only [k17gcPent6, pc5_1, pc5_2, hz]; nlinarith
        · right; left; right
          simp only [k17gcPent6, pc5_0, pc5_1]
          refine ⟨by rw [hz, hz]; simp only; linarith, ?_⟩
          have := hwcb v1 v2; linarith
  -- hexagon cell
  have hex : ∀ u1 u2 t1 t2 : ℝ, u1 * t2 - u2 * t1 ≠ 0 → ⟪P, R⟫ < 0 →
      (∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ u2 + lam * t2 < 0 ∧
        ((1 - γ6) * ⟪P, R⟫ < -⟪R, R⟫ ∨ ⟪P, R⟫ < γ4 * ⟪P, R⟫ + ⟪Q, R⟫ ∨
          (γ4 * ⟪P, R⟫ + ⟪Q, R⟫ = ⟪P, R⟫ ∧ (u1 + lam * t1) * A + (u2 + lam * t2) * B < 0))) →
      HasLexCell (V8 a a' b b' c c' d) := by
    intro u1 u2 t1 t2 hut hPR hseg
    refine ⟨R, hR0, ?_⟩
    refine cyc_cell (V8 a a' b b' c c' d) P Q R d hΔ (k := 6) (by norm_num) (k17gcHex6 γ4 γ6)
      (k17gcHex6_inj hγ4 hγ6) ?_ [((0 : ℝ), (1 : ℝ), -β1)] ?_ hut (lo := 0) (hi := 1) (by norm_num)
      (fun v1 v2 => 0 < v1 ∧ v2 < 0 ∧
        ((1 - γ6) * ⟪P, R⟫ < -⟪R, R⟫ ∨ ⟪P, R⟫ < γ4 * ⟪P, R⟫ + ⟪Q, R⟫ ∨
          (γ4 * ⟪P, R⟫ + ⟪Q, R⟫ = ⟪P, R⟫ ∧ v1 * A + v2 * B < 0))) hseg ?_ ?_
    · intro i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [k17gcHex6, pc6_0, Ea]; simp [V8]
      · simp only [k17gcHex6, pc6_1, Ed]; simp [V8]
      · simp only [k17gcHex6, pc6_2, Eb]; simp [V8]
      · simp only [k17gcHex6, pc6_3, Ea']; simp [V8]
      · simp only [k17gcHex6, pc6_4, Ec]; simp [V8]
      · simp only [k17gcHex6, pc6_5, Eb']; simp [V8]
    · intro y hy
      rcases hVlist y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨4, rfl⟩
      · exact Or.inl ⟨5, rfl⟩
      · exact Or.inr ⟨_, by simp, rfl⟩
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inl ⟨1, rfl⟩
      · exact Or.inl ⟨2, rfl⟩
      · exact Or.inl ⟨3, rfl⟩
    · rintro v1 v2 ⟨hv1, hv2, -⟩
      exact k17gc_hex6_tsc hβ1 hγ4 hγ6 hγ61 hv1 hv2
    · rintro v1 v2 ⟨hv1, hv2, hL⟩ hinj
      refine k17gc_lexUni6_b _ _ hinj ?_ ?_ ?_ ?_ ?_
      · left; simp only [k17gcHex6, pc6_0, pc6_1, hz]; nlinarith
      · left; simp only [k17gcHex6, pc6_1, pc6_2, hz]; nlinarith
      · left; simp only [k17gcHex6, pc6_2, pc6_3, hz]; nlinarith
      · left; simp only [k17gcHex6, pc6_0, pc6_5, hz]; nlinarith
      · rcases hL with hL | hL | ⟨hL, hf⟩
        · left; left; simp only [k17gcHex6, pc6_3, pc6_4, hz]; nlinarith
        · right; left; simp only [k17gcHex6, pc6_4, pc6_5, hz]; nlinarith
        · right; right
          simp only [k17gcHex6, pc6_4, pc6_5]
          refine ⟨by rw [hz, hz]; simp only; linarith, ?_⟩
          have := hwcb v1 v2; linarith
  -- the split
  by_cases c1 : 0 < ⟪P, R⟫ ∨ γ4 * ⟪P, R⟫ + ⟪Q, R⟫ < ⟪P, R⟫ ∨ γ4 * ⟪P, R⟫ < -β1 * ⟪R, R⟫
  · left
    refine pent 1 1 0 1 (by norm_num) (fun lam h0 h1 => ⟨by norm_num, by linarith, ?_⟩)
    rcases c1 with c | c | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)
    · exact Or.inr (Or.inr (Or.inl c))
  push Not at c1
  obtain ⟨c1, c2, c3⟩ := c1
  have hPR : ⟪P, R⟫ < 0 := by
    rcases c1.lt_or_eq with h | h
    · exact h
    · rw [h] at c2; nlinarith
  by_cases c4 : (1 - γ6) * ⟪P, R⟫ < -⟪R, R⟫ ∨ ⟪P, R⟫ < γ4 * ⟪P, R⟫ + ⟪Q, R⟫
  · left
    refine hex 1 (-1) 1 0 (by norm_num) hPR (fun lam h0 h1 => ⟨by linarith, by norm_num, ?_⟩)
    rcases c4 with c | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)
  push Not at c4
  have htie : γ4 * ⟪P, R⟫ + ⟪Q, R⟫ = ⟪P, R⟫ := le_antisymm c4.2 c2
  rcases lt_trichotomy A 0 with hAn | hA0 | hAp
  · -- hexagon, tilt `(1, -λη)`
    left
    obtain ⟨η, hη, hηx⟩ := k8_eta (x := B) (y := A) hAn.ne
    refine hex 1 0 0 (-η) (by nlinarith) hPR (fun lam h0 h1 => ⟨by norm_num, by nlinarith, ?_⟩)
    right; right; refine ⟨htie, ?_⟩
    have hle : -(lam * η * B) ≤ η * |B| := by
      rcases le_total 0 B with hx | hx
      · rw [abs_of_nonneg hx]; nlinarith [mul_nonneg (mul_nonneg h0.le hη.le) hx, mul_nonneg hη.le hx]
      · rw [abs_of_nonpos hx]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1.le) hη.le) (neg_nonneg.2 hx)]
    rw [abs_of_neg hAn] at hηx
    nlinarith [abs_nonneg B]
  · -- leftover
    right
    refine ⟨?_, ?_⟩
    · have e : c - b' = (1 - γ4) • P - Q := by rw [hb', hP, hQ]; module
      rw [e, inner_sub_left, inner_smul_left]
      simp only [conj_trivial]; linarith
    · have e : c - b' = (1 - γ4) • P - Q := by rw [hb', hP, hQ]; module
      rw [e, inner_sub_left, inner_smul_left, real_inner_comm P Q]
      simp only [conj_trivial]; linarith
  · -- pentagon, tilt `(1, λη)`
    left
    obtain ⟨η, hη, hηx⟩ := k8_eta (x := B) (y := A) hAp.ne'
    refine pent 1 0 0 η (by nlinarith) (fun lam h0 h1 => ⟨by norm_num, by nlinarith, ?_⟩)
    right; right; right; refine ⟨htie, ?_⟩
    have hle : -(lam * η * B) ≤ η * |B| := by
      rcases le_total 0 B with hx | hx
      · rw [abs_of_nonneg hx]; nlinarith [mul_nonneg (mul_nonneg h0.le hη.le) hx, mul_nonneg hη.le hx]
      · rw [abs_of_nonpos hx]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1.le) hη.le) (neg_nonneg.2 hx)]
    rw [abs_of_pos hAp] at hηx
    nlinarith [abs_nonneg B]

end C2
end Type08Sp
end Minimality
