module

public import Minimality.Type08S.LexK
public import Minimality.Type08S.C2K28B4d2

@[expose] public section

/-!
# LEXK worked example: `k28b4_D` (type 08, M stratum, β6 = 1, leaf D) by the k-level lex cell `lexk_cell_frame`.
Generator output shape: cycle `Y = k28b4dY`, tilts `T = [(1,0,0), (0,-1,0)]` (3-level lex: `R`, then `a - d`, then
`-(b - d)`), sorted depths `s = [3, 2, 1, 0]` (b' < c < a' <lex c'), every row closed by `lexk_row`.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- TS rows of the example, as a generator emits them (pure polynomial rows, hint products in context). -/
theorem lexk_ex_ts {α1 β1 γ6 μ : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hγ6 : 0 < γ6) (hσ : β1 < 1 + γ6) (hμ : μ < 0) (hLp : 0 < α1 + (β1 - 1) * μ)
    (hLq : 0 < α1 - 1 + β1 * μ) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → lexkPos ((((0:ℝ), (0:ℝ), (1:ℝ)) :: [(1, 0, 0), (0, -1, 0)]).map
      (lexkD3 (k28b4dY α1 β1 γ6 μ (i + 1) - k28b4dY α1 β1 γ6 μ i) (k28b4dY α1 β1 γ6 μ j - k28b4dY α1 β1 γ6 μ i)))) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0), (1, 0, 0)], ∀ i : ZMod 4,
      lexkPos ((((0:ℝ), (0:ℝ), (1:ℝ)) :: [(1, 0, 0), (0, -1, 0)]).map
        (lexkD3 (k28b4dY α1 β1 γ6 μ (i + 1) - k28b4dY α1 β1 γ6 μ i) (t - k28b4dY α1 β1 γ6 μ i)))) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := k19_z4
  have a1 := sub_pos.2 hα1
  have b1 := sub_pos.2 hβ1
  have s1 : 0 < 1 + γ6 - β1 := by linarith
  have n1 : 0 < -μ := by linarith
  have hb0 : (0:ℝ) < β1 := by linarith
  have ha0 : (0:ℝ) < α1 := by linarith
  have k13 := mul_pos hγ6 n1
  have k15 := mul_pos hb0 n1
  have k17 := mul_pos hb0 hLp
  have k18 := mul_pos hb0 hLq
  have k19 := mul_pos hγ6 hLp
  have k20 := mul_pos hγ6 hLq
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases k19_z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [lexkD3, d3, e0, e1, e2, e3, f0, f1, f2, f3, k28b4dY_0, k28b4dY_1, k28b4dY_2, k28b4dY_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, List.map_cons, List.map_nil]
         lexk_row)
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [lexkD3, d3, e0, e1, e2, e3, f0, f1, f2, f3, k28b4dY_0, k28b4dY_1, k28b4dY_2, k28b4dY_3,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, List.map_cons, List.map_nil]
       lexk_row)

set_option maxHeartbeats 6400000 in
/-- `k28b4_D` re-proved by `lexk_cell_frame` (same statement). -/
theorem lexk_ex_k28b4_D {a a' b b' c c' d : ℝ³} {α1 β1 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 1 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hσ : β1 < 1 + γ6)
    (hLq : 0 < ⟪c' - a', b' - a⟫)
    (hLz : 0 < ⟪c' - c, k28b4c_u0 a a' c c' d⟫) : HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨k1, k3, kc, ka, kp, kq⟩ := k28b4d_keys hC hM hrel hα hβ hσ hLq
  obtain ⟨hdet, hc', hb', ha', -, -, -, -, hγ6, -⟩ := hC
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = ⟪c' - a', a - d⟫ := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = ⟪c' - a', b - d⟫ := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = ⟪c' - a', c - d⟫ := ⟨_, rfl⟩
  have hu0 : k28b4c_u0 a a' c c' d = m3 • (a - d) - m1 • (c - d) := by
    unfold k28b4c_u0; rw [hm1, hm3]
  rw [hu0] at hLz
  rw [← hm1] at k1 kc ka kp kq
  rw [← hm3] at k3 kc ka kp kq
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = m3 / m1 := ⟨_, rfl⟩
  rw [← hμ] at kc ka
  have hμ0 : μ < 0 := by rw [hμ]; exact div_neg_of_neg_of_pos k3 k1
  have hm3μ : m3 = μ * m1 := by rw [hμ]; field_simp
  have hLp' : 0 < α1 + (β1 - 1) * μ := by
    rw [hm3μ] at kp
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (by linarith : 0 ≤ -(α1 + (β1 - 1) * μ)) k1.le]
  have hLq' : 0 < α1 - 1 + β1 * μ := by
    rw [hm3μ] at kq
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (by linarith : 0 ≤ -(α1 - 1 + β1 * μ)) k1.le]
  obtain ⟨R, hR⟩ : ∃ R : ℝ³, R = μ • (a - d) - (c - d) := ⟨_, rfl⟩
  rw [← hR] at kc ka
  have hu0R : m3 • (a - d) - m1 • (c - d) = m1 • R := by rw [hR, hm3μ]; module
  rw [hu0R, inner_smul_right] at hLz
  have kz : 0 < ⟪c' - c, R⟫ := by
    by_contra hn; push Not at hn; nlinarith [mul_nonneg k1.le (neg_nonneg.2 hn)]
  have hΔ : det3 (a - d) (b - d) R ≠ 0 := by
    have e : det3 (a - d) (b - d) R = -det3 (a - d) (b - d) (c - d) := by
      rw [hR]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact neg_ne_zero.2 hdet
  have hR0 : R ≠ 0 := k17f_r0 hΔ
  have Ea : fpoint (a - d) (b - d) R d (1, 0, 0) = a := by rw [k17f_fp]; module
  have Ed : fpoint (a - d) (b - d) R d (0, 0, 0) = d := by rw [k17f_fp]; module
  have Eb : fpoint (a - d) (b - d) R d (0, 1, 0) = b := by rw [k17f_fp]; module
  have Ec : fpoint (a - d) (b - d) R d (μ, 0, -1) = c := by rw [k17f_fp, hR]; module
  have Ec' : fpoint (a - d) (b - d) R d (α1, β1, 0) = c' := by rw [k17f_fp, hc']; module
  have Ea' : fpoint (a - d) (b - d) R d (γ6 * μ, 1, -γ6) = a' := by rw [k17f_fp, ha', hR]; module
  have Eb' : fpoint (a - d) (b - d) R d (α1 + β1 * μ, 0, -β1) = b' := by rw [k17f_fp, hb', hR]; module
  -- depth facts
  have F2 : ⟪a', R⟫ = ⟪c', R⟫ := by
    have : ⟪c' - a', R⟫ = 0 := by
      rw [hR, inner_sub_right, inner_smul_right, ← hm1, ← hm3, hm3μ]; ring
    rw [inner_sub_left] at this; linarith
  have Fcc : ⟪c, R⟫ < ⟪c', R⟫ := by rw [← sub_pos, ← inner_sub_left]; exact kz
  have Fc : ⟪c, R⟫ < ⟪a', R⟫ := by rw [F2]; exact Fcc
  have Fb : ⟪b', R⟫ < ⟪c, R⟫ := by
    rw [← sub_neg, ← inner_sub_left]
    have e : b' - c = α1 • (a - d) + (β1 - 1) • (c - d) := by rw [hb']; module
    rw [e]
    have hdc : ⟪c - d, R⟫ < 0 := kc
    have hda : ⟪a - d, R⟫ < 0 := ka
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    nlinarith [mul_pos (by linarith : (0:ℝ) < α1) (neg_pos.2 hda), mul_pos (sub_pos.2 hβ) (neg_pos.2 hdc)]
  refine ⟨R, hR0, ?_⟩
  set Y := k28b4dY α1 β1 γ6 μ with hY
  have hY0 : fpoint (a - d) (b - d) R d (Y 0) = c' := Ec'
  have hY1 : fpoint (a - d) (b - d) R d (Y 1) = a' := Ea'
  have hY2 : fpoint (a - d) (b - d) R d (Y 2) = c := Ec
  have hY3 : fpoint (a - d) (b - d) R d (Y 3) = b' := Eb'
  have hmem : ∀ i, fpoint (a - d) (b - d) R d (Y i) ∈ V8 a a' b b' c c' d := by
    intro i
    rcases k19_z4_cases i with rfl | rfl | rfl | rfl
    · rw [hY0]; simp [V8]
    · rw [hY1]; simp [V8]
    · rw [hY2]; simp [V8]
    · rw [hY3]; simp [V8]
  have TS := lexk_ex_ts hα hβ hγ6 hσ hμ0 hLp' hLq'
  have hm1' : ⟪c', a - d⟫ - ⟪a', a - d⟫ = m1 := by rw [hm1, inner_sub_left]
  refine lexk_cell_frame _ _ _ _ _ hΔ (by norm_num) Y [(1, 0, 0), (0, -1, 0)] hmem TS.1 ?_ [3, 2, 1, 0]
    (by decide) ?_ (by decide)
  · intro y hy hyx
    have hV : y = fpoint (a - d) (b - d) R d (γ6 * μ, 1, -γ6) ∨ y = fpoint (a - d) (b - d) R d (α1, β1, 0) ∨
        y = fpoint (a - d) (b - d) R d (α1 + β1 * μ, 0, -β1) ∨ y = fpoint (a - d) (b - d) R d (1, 0, 0) ∨
        y = fpoint (a - d) (b - d) R d (0, 0, 0) ∨ y = fpoint (a - d) (b - d) R d (0, 1, 0) ∨
        y = fpoint (a - d) (b - d) R d (μ, 0, -1) := by
      rw [Ea', Ec', Eb', Ea, Ed, Eb, Ec]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    rcases hV with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 1 (by rw [hY1, Ea'])).elim
    · exact (hyx 0 (by rw [hY0, Ec'])).elim
    · exact (hyx 3 (by rw [hY3, Eb'])).elim
    · exact ⟨_, rfl, TS.2 _ (by simp)⟩
    · exact ⟨_, rfl, TS.2 _ (by simp)⟩
    · exact ⟨_, rfl, TS.2 _ (by simp)⟩
    · exact (hyx 2 (by rw [hY2, Ec])).elim
  · simp only [lexkChain_cons2, lexkChain_one, and_true, List.map_cons, List.map_nil, lexk_inner_F,
      hY0, hY1, hY2, hY3, inner_sub_left]
    refine ⟨?_, ?_, ?_⟩ <;> lexk_row
