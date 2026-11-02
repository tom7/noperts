module

public import Minimality.Type08S.C2K17GA4

@[expose] public section


/-!
# K17GA / GA5: R2 (S1.1a, Tc): cell `(c',b',c,a',b)` at `d - b`, frame `(a-d, c-d, d-b)`.
Coordinates: `c' = (α1,0,-β1)`, `b' = (α4,γ4,0)`, `c = (0,1,0)`, `a' = (0,1,-β6)`, `b = (0,0,-1)`; rest `a = (1,0,0)`, `d = 0`.
Tilt cone `v1 < 0, v2 < 0, α4 v2 < (γ4-1) v1`; tilt `(-α4, -γ4 - λ α4)`.
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

def k17gaR2 (α1 β1 α4 γ4 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (α1, 0, -β1) (α4, γ4, 0) (0, 1, 0) (0, 1, -β6) (0, 0, -1)

set_option maxHeartbeats 3200000 in
theorem k17ga_r2_tsc {D α1 β1 α4 γ4 β6 v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 0 < α4)
    (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6) (hcv : 0 < α4 - α1 + α1 * γ4) (hv1 : v1 < 0) (hv2 : v2 < 0)
    (hc : α4 * v2 < (γ4 - 1) * v1) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k17gaR2 α1 β1 α4 γ4 β6 (i + 1) - k17gaR2 α1 β1 α4 γ4 β6 i)
        (k17gaR2 α1 β1 α4 γ4 β6 j - k17gaR2 α1 β1 α4 γ4 β6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 0, 0)], ∀ i : ZMod 5,
      TSc D (k17gaR2 α1 β1 α4 γ4 β6 (i + 1) - k17gaR2 α1 β1 α4 γ4 β6 i) (t - k17gaR2 α1 β1 α4 γ4 β6 i)
        (v1, v2, 0)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have a1 : 0 < α1 - 1 := by linarith
  have b6 : 0 ≤ β6 - 1 := by linarith
  have nv1 : 0 < -v1 := by linarith
  have nv2 : 0 < -v2 := by linarith
  have hc' : 0 < (γ4 - 1) * v1 - α4 * v2 := by linarith
  have k1 := hD
  have kg := mul_pos hD hγ4
  have ka := mul_pos hD hα4
  have kb := mul_pos hD hβ1
  have ka1 := mul_pos hD a1
  have kb6 := mul_nonneg hD.le b6
  have kcv := mul_pos hD hcv
  have kn1 := mul_pos hD nv1
  have kn2 := mul_pos hD nv2
  have kc := mul_pos hD hc'
  have kn1b := mul_pos kn1 hβ1
  have kn2b := mul_pos kn2 hβ1
  have kn1a := mul_pos kn1 a1
  have kn2a := mul_pos kn2 a1
  have kn2g := mul_pos kn2 hγ4
  have kn1g := mul_pos kn1 hγ4
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k17gaR2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k17gaR2, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

theorem k17ga_lexUni5_R2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h32 : LexLt (z 3, w 3) (z 2, w 2)) (h34 : LexLt (z 3, w 3) (z 4, w 4))
    (h40 : LexLt (z 4, w 4) (z 0, w 0)) (h : LexLt (z 0, w 0) (z 1, w 1) ∨ LexLt (z 2, w 2) (z 1, w 1)) :
    LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  have h01 : (z 0, w 0) ≠ (z 1, w 1) := by
    intro h; have := hinj 0 1 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
  have h12 : (z 1, w 1) ≠ (z 2, w 2) := by
    intro h; have := hinj 1 2 (congrArg Prod.fst h) (congrArg Prod.snd h); exact absurd this (by decide)
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
  have a32 := lexLt_asymm h32
  have a34 := lexLt_asymm h34
  have a40 := lexLt_asymm h40
  rcases lexLt_total h01 with x | x <;> rcases lexLt_total h12 with y | y <;> rcases h with hh | hh <;>
    have ax := lexLt_asymm x <;> have ay := lexLt_asymm y <;> have ah := lexLt_asymm hh <;>
    first | exact absurd hh ay | exact absurd hh ax | exact absurd x ah | exact absurd y ah | simp [x, y, hh, ax, ay, ah, h32, h34, h40, a32, a34, a40]


theorem k17gaR2_inj {α1 β1 α4 γ4 β6 : ℝ} (hb6 : 1 ≤ β6) (hα1 : 1 < α1) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) :
    ∀ i j, k17gaR2 α1 β1 α4 γ4 β6 i = k17gaR2 α1 β1 α4 γ4 β6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k17gaR2, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; nlinarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 3200000 in
/-- **R2 cell** `(c',b',c,a',b)` at `d - b`. -/
theorem k17ga_r2_cell {a a' b b' c c' d : ℝ³} {α1 α4 β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα1 : 1 < α1) (hβ1 : 0 < β1) (hα4 : 0 < α4)
    (hγ4 : 0 < γ4) (hb6 : 1 ≤ β6) (hcv : 0 < α4 - α1 + α1 * γ4)
    (hy : ⟪c - d, d - b⟫ < (β6 - 1) * ⟪d - b, d - b⟫)
    (hl : (β1 - 1) * ⟪d - b, d - b⟫ < α1 * ⟪a - d, d - b⟫)
    (hh : α1 * ⟪a - d, d - b⟫ - β1 * ⟪d - b, d - b⟫ < α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫ ∨
      ⟪c - d, d - b⟫ < α4 * ⟪a - d, d - b⟫ + γ4 * ⟪c - d, d - b⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  set P := a - d with hP
  set Q := c - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    have e : det3 P Q R = det3 (a - d) (b - d) (c - d) := by
      rw [hP, hQ, hR]
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply]; ring
    rw [e]; exact hdet
  have hq : b - d = -R := by rw [hR]; abel
  have Ea : fpoint P Q R d (1, 0, 0) = a := by rw [k17ga_fp, hP]; module
  have Ed : fpoint P Q R d (0, 0, 0) = d := by rw [k17ga_fp]; module
  have Eb : fpoint P Q R d (0, 0, -1) = b := by rw [k17ga_fp, hR]; module
  have Ec : fpoint P Q R d (0, 1, 0) = c := by rw [k17ga_fp, hQ]; module
  have Ea' : fpoint P Q R d (0, 1, -β6) = a' := by rw [k17ga_fp, ha', hq, hQ]; module
  have Eb' : fpoint P Q R d (α4, γ4, 0) = b' := by rw [k17ga_fp, hb', hP, hQ]; module
  have Ec' : fpoint P Q R d (α1, 0, -β1) = c' := by rw [k17ga_fp, hc', hq, hP]; module
  have hz' : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint P Q R d t, R⟫ = ⟪d, R⟫ + t.1 * ⟪P, R⟫ + t.2.1 * ⟪Q, R⟫ + t.2.2 * ⟪R, R⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hR0 : R ≠ 0 := k17ga_r0 hΔ
  have hRR : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hR0
  refine ⟨R, hR0, ?_⟩
  refine k3_cell_gen (V8 a a' b b' c c' d) P Q R d hΔ (k := 5) (by norm_num) (k17gaR2 α1 β1 α4 γ4 β6)
    (k17gaR2_inj hb6 hα1 hα4 hγ4 hβ1) (u1 := -α4) (u2 := -γ4) (t1 := 0) (t2 := -α4) (by nlinarith) ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17gaR2, pc5_0, Ec']; simp [V8]
    · simp only [k17gaR2, pc5_1, Eb']; simp [V8]
    · simp only [k17gaR2, pc5_2, Ec]; simp [V8]
    · simp only [k17gaR2, pc5_3, Ea']; simp [V8]
    · simp only [k17gaR2, pc5_4, Eb]; simp [V8]
  · intro lam h0 h1 D hD
    exact (k17ga_r2_tsc hD hα1 hβ1 hα4 hγ4 hb6 hcv (by simp; linarith) (by simp; nlinarith)
      (by simp; nlinarith [mul_pos hα4 hα4, mul_pos (mul_pos hα4 hα4) h0])).1
  · intro y hy' hyx
    have hV : y = fpoint P Q R d (α1, 0, -β1) ∨ y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨
        y = fpoint P Q R d (0, 1, -β6) ∨ y = fpoint P Q R d (0, 0, -1) ∨
        y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (0, 0, 0) := by
      rw [Ea, Ed, Eb, Ea', Eb', Ec, Ec']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy'
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [k17gaR2, pc5_0])).elim
    · exact (hyx 1 (by simp only [k17gaR2, pc5_1])).elim
    · exact (hyx 2 (by simp only [k17gaR2, pc5_2])).elim
    · exact (hyx 3 (by simp only [k17gaR2, pc5_3])).elim
    · exact (hyx 4 (by simp only [k17gaR2, pc5_4])).elim
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17ga_r2_tsc hD hα1 hβ1 hα4 hγ4 hb6 hcv (by simp; linarith) (by simp; nlinarith)
        (by simp; nlinarith [mul_pos hα4 hα4, mul_pos (mul_pos hα4 hα4) h0])).2 _ (by simp) i
    · refine ⟨_, rfl, fun lam h0 h1 D hD i => ?_⟩
      exact (k17ga_r2_tsc hD hα1 hβ1 hα4 hγ4 hb6 hcv (by simp; linarith) (by simp; nlinarith)
        (by simp; nlinarith [mul_pos hα4 hα4, mul_pos (mul_pos hα4 hα4) h0])).2 _ (by simp) i
  · intro w hw
    refine k17ga_lexUni5_R2 _ w hw ?_ ?_ ?_ ?_
    · left; simp only [k17gaR2, pc5_3, pc5_2, hz']; nlinarith
    · left; simp only [k17gaR2, pc5_3, pc5_4, hz']; nlinarith
    · left; simp only [k17gaR2, pc5_4, pc5_0, hz']; nlinarith
    · rcases hh with hh | hh
      · left; left; simp only [k17gaR2, pc5_0, pc5_1, hz']; nlinarith
      · right; left; simp only [k17gaR2, pc5_2, pc5_1, hz']; nlinarith


end C2
end Type08Sp
end Minimality
