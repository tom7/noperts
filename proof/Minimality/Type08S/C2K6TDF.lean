module

public import Minimality.Type08S.C2K6TDE

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Cell 1 `(a, d, b, a', b')` of the `β1 = 1` frame, `B := ⟪b-d, a-d⟫ ≤ 0` (`B = 0`: `b` below `d` in the tilt). -/
theorem k6t4_b11_cell1_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j)
    {z A B C β6 α4 : ℝ} (hA : 0 < A) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (h0 : zz 0 = z + A) (h1 : zz 1 = z) (h2 : zz 2 = z + B) (h3 : zz 3 = z + β6 * B + C)
    (h4 : zz 4 = z + C + α4 * A) (hB : B < 0 ∨ (B = 0 ∧ ww 2 < ww 1)) : LexUni zz ww := by
  refine lexUni5_r2 zz ww hinj ?_ ?_ ?_
  · left; simp only; rw [h3, h4]
    rcases hB with hB | ⟨hB, -⟩
    · nlinarith
    · rw [hB]; nlinarith
  · left; simp only; rw [h0, h1]; linarith
  · right
    rcases hB with hB | ⟨hB, hw⟩
    · left; simp only; rw [h2, h1]; linarith
    · right; exact ⟨by simp only; rw [h2, h1, hB]; ring, hw⟩

/-- Cell 2 `(a, d, c, a', c')` (frame `(q, p, r)`), `B > 0`, `α1 ≥ 1`. -/
theorem k6t4_b11_cell2_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j)
    {z A B C β6 α1 : ℝ} (hA : 0 < A) (hα1 : 1 ≤ α1) (hβ6 : 0 < β6) (hB : 0 < B)
    (h0 : zz 0 = z + A) (h1 : zz 1 = z) (h2 : zz 2 = z + C) (h3 : zz 3 = z + 1 * C + β6 * B)
    (h4 : zz 4 = z + B + α1 * A) : LexUni zz ww := by
  refine lexUni5_r1 zz ww hinj ?_ ?_ ?_
  · left; simp only; rw [h2, h3]; nlinarith
  · left; simp only; rw [h0, h4]; nlinarith
  · right; left; simp only; rw [h1, h0]; linarith

set_option maxHeartbeats 3200000 in
/-- **`β1 = 1` frame (K6TL4)**: `T`, `κ_a = 0`, `β1 = 1`, `1 < α1` (far end).  Rule: `B := ⟪b - d, a - d⟫ < 0` ->
cell `(a,d,b,a',b')`, `B > 0` -> cell `(a,d,c,a',c')` (both at `a - d`; no Gram condition, no use of `C`);
`B = 0` needs `TouchT` (gives `⟪b - d, c - d⟫ = ⟪b - d, b - d⟫`), then cell 1 with the tilt below `1`. -/
theorem k6t4_B11_core {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hβ1 : det3 (a - d) (c' - b) (c - d) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hB : ⟪b - d, a - d⟫ ≠ 0 ∨ TouchT b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1p, hαβ, hα4, hγ4, hαγ, hβ6, hfa⟩ :=
    norm08w_coordsT W hT
  have hα11 : 1 < α1 := hfa hfar
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ1
  have hβ1e : β1 = 1 := by
    have : β1 - 1 = 0 := by
      rcases mul_eq_zero.1 hβ1 with h | h
      · exact h
      · exact absurd h hdet
    linarith
  subst hβ1e
  have hγ4e : γ4 = 1 := by
    have : α1 * (1 - γ4) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hγ4e
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hcyc : ∀ x y z : ℝ³, det3 x y z = det3 z x y := by
    intro x y z; simp only [det3_expand]; ring
  have hΔ : det3 p q r ≠ 0 := by rw [hcyc]; exact hdet
  have hΔ' : det3 q p r ≠ 0 := by
    have : det3 q p r = - det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hΔ
  have hfp : ∀ (u v : ℝ³) (x y z : ℝ), fpoint u v r d (x, y, z) = d + x • u + y • v + z • r := by
    intro u v x y z; simp only [fpoint, fcomb]; module
  have P1a : fpoint p q r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P1d : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have P1b : fpoint p q r d (1, 0, 0) = b := by rw [hfp]; simp only [hp]; module
  have P1a' : fpoint p q r d (β6, 1, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P1b' : fpoint p q r d (0, 1, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  have P1c : fpoint p q r d (0, 1, 0) = c := by rw [hfp]; simp only [hq]; module
  have P1c' : fpoint p q r d (1, 0, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2a : fpoint q p r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P2d : fpoint q p r d (0, 0, 0) = d := by rw [hfp]; module
  have P2c : fpoint q p r d (1, 0, 0) = c := by rw [hfp]; simp only [hq]; module
  have P2a' : fpoint q p r d (1, β6, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P2c' : fpoint q p r d (0, 1, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2b : fpoint q p r d (0, 1, 0) = b := by rw [hfp]; simp only [hp]; module
  have P2b' : fpoint q p r d (1, 0, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  refine ⟨r, hr0, ?_⟩
  have hz : ∀ (u v : ℝ³) (t : ℝ × ℝ × ℝ), ⟪fpoint u v r d t, r⟫ =
      ⟪d, r⟫ + t.1 * ⟪u, r⟫ + t.2.1 * ⟪v, r⟫ + t.2.2 * ⟪r, r⟫ := fun u v t => inner_fpoint _ _ _ _ _ _
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  rcases lt_trichotomy ⟪p, r⟫ 0 with hBn | hB0 | hBp
  · -- `B < 0`: cell 1
    refine k6t4_core (V8 a a' b b' c c' d) p q r d hΔ (α1 := α1) (α4 := α4) (β6 := β6) (γ6 := 1)
      (by linarith) hα4 hβ6 one_pos (by linarith) (lo := max 0 (1 - β6)) (hi := max 0 (1 - β6) + 1) (by linarith)
      ?_ ?_ ?_ ?_
    · intro lam hl0 hl1
      have := lt_of_le_of_lt (le_max_left _ _) hl0
      have := lt_of_le_of_lt (le_max_right _ _) hl0
      refine ⟨by linarith, by linarith, by nlinarith⟩
    · intro lam hl0 hl1 hinj
      refine k6t4_b11_cell1_lex _ _ hinj (z := ⟪d, r⟫) (A := ⟪r, r⟫) (B := ⟪p, r⟫) (C := ⟪q, r⟫) (β6 := β6)
        (α4 := α4) hA hα4 hβ6 ?_ ?_ ?_ ?_ ?_ (Or.inl hBn)
      · simp only [kCyc, pc5_0, hz]; ring
      · simp only [kCyc, pc5_1, hz]; ring
      · simp only [kCyc, pc5_2, hz]; ring
      · simp only [kCyc, pc5_3, hz]; ring
      · simp only [kCyc, pc5_4, hz]; ring
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kCyc, pc5_0, P1a]; simp [V8]
      · simp only [kCyc, pc5_1, P1d]; simp [V8]
      · simp only [kCyc, pc5_2, P1b]; simp [V8]
      · simp only [kCyc, pc5_3, P1a']; simp [V8]
      · simp only [kCyc, pc5_4, P1b']; simp [V8]
    · intro y hy
      rw [P1a, P1d, P1b, P1a', P1b', P1c, P1c']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · -- `B = 0` (Touch-like): cell 1 with `b` below `d` in the tilt
    have hPQ : ⟪p, q⟫ = ⟪p, p⟫ := by
      rcases hB with hB | hTo
      · exact absurd hB0 hB
      · have t2 := hTo.1.2
        rw [hc', hb'] at t2
        simp only [inner_add_left, real_inner_smul_left] at t2
        have hrp : ⟪r, p⟫ = 0 := (real_inner_comm p r).trans hB0
        have hqp : ⟪q, p⟫ = ⟪p, q⟫ := real_inner_comm p q
        rw [hrp] at t2
        rw [hqp] at t2
        linarith
    have hp0 : p ≠ 0 := by intro h0; rw [h0] at hΔ; simp [det3_expand] at hΔ
    have hP : 0 < ⟪p, p⟫ := real_inner_self_pos.2 hp0
    have hlo : max 0 (1 - β6) < 1 := max_lt one_pos (by linarith)
    refine k6t4_core (V8 a a' b b' c c' d) p q r d hΔ (α1 := α1) (α4 := α4) (β6 := β6) (γ6 := 1)
      (by linarith) hα4 hβ6 one_pos (by linarith) (lo := max 0 (1 - β6)) (hi := 1) hlo
      ?_ ?_ ?_ ?_
    · intro lam hl0 hl1
      have := lt_of_le_of_lt (le_max_left _ _) hl0
      have := lt_of_le_of_lt (le_max_right _ _) hl0
      refine ⟨by linarith, by linarith, by nlinarith⟩
    · intro lam hl0 hl1 hinj
      refine k6t4_b11_cell1_lex _ _ hinj (z := ⟪d, r⟫) (A := ⟪r, r⟫) (B := ⟪p, r⟫) (C := ⟪q, r⟫) (β6 := β6)
        (α4 := α4) hA hα4 hβ6 ?_ ?_ ?_ ?_ ?_ (Or.inr ⟨hB0, ?_⟩)
      · simp only [kCyc, pc5_0, hz]; ring
      · simp only [kCyc, pc5_1, hz]; ring
      · simp only [kCyc, pc5_2, hz]; ring
      · simp only [kCyc, pc5_3, hz]; ring
      · simp only [kCyc, pc5_4, hz]; ring
      · have e : ⟪p, fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0⟫ = lam * ⟪p, p⟫ - ⟪p, q⟫ := by
          rw [real_inner_comm, inner_fcomb_left]
          have h := real_inner_comm p q
          rw [h]; ring
        simp only [kCyc, pc5_2, pc5_1, inner_fpoint]
        rw [e, hPQ]
        nlinarith
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kCyc, pc5_0, P1a]; simp [V8]
      · simp only [kCyc, pc5_1, P1d]; simp [V8]
      · simp only [kCyc, pc5_2, P1b]; simp [V8]
      · simp only [kCyc, pc5_3, P1a']; simp [V8]
      · simp only [kCyc, pc5_4, P1b']; simp [V8]
    · intro y hy
      rw [P1a, P1d, P1b, P1a', P1b', P1c, P1c']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · -- `B > 0`: cell 2 in the frame `(q, p, r)`
    refine k6t4_core (V8 a a' b b' c c' d) q p r d hΔ' (α1 := α4) (α4 := α1) (β6 := 1) (γ6 := β6)
      hα4 (by linarith) one_pos hβ6 (by linarith) (lo := 0) (hi := 1) one_pos
      ?_ ?_ ?_ ?_
    · intro lam hl0 hl1
      refine ⟨hl0, by nlinarith, by nlinarith⟩
    · intro lam hl0 hl1 hinj
      refine k6t4_b11_cell2_lex _ _ hinj (z := ⟪d, r⟫) (A := ⟪r, r⟫) (B := ⟪p, r⟫) (C := ⟪q, r⟫) (β6 := β6)
        (α1 := α1) hA hα11.le hβ6 hBp ?_ ?_ ?_ ?_ ?_
      · simp only [kCyc, pc5_0, hz]; ring
      · simp only [kCyc, pc5_1, hz]; ring
      · simp only [kCyc, pc5_2, hz]; ring
      · simp only [kCyc, pc5_3, hz]; ring
      · simp only [kCyc, pc5_4, hz]; ring
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kCyc, pc5_0, P2a]; simp [V8]
      · simp only [kCyc, pc5_1, P2d]; simp [V8]
      · simp only [kCyc, pc5_2, P2c]; simp [V8]
      · simp only [kCyc, pc5_3, P2a']; simp [V8]
      · simp only [kCyc, pc5_4, P2c']; simp [V8]
    · intro y hy
      rw [P2a, P2d, P2c, P2a', P2c', P2b, P2b']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto

/-- **Touch**: `β1 = 1` with `TouchT`: always a cell. -/
theorem k6t4_B11_touch {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hβ1 : det3 (a - d) (c' - b) (c - d) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) (hTo : TouchT b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) :=
  k6t4_B11_core W hT hκ hβ1 hfar (Or.inr hTo)

/-- **Ta, `β1 = 1`**: a cell or the codim-5 tie `B = ⟪b - d, a - d⟫ = 0`. -/
theorem k6t4_B11_ta {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hβ1 : det3 (a - d) (c' - b) (c - d) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a) :
    HasLexCell (V8 a a' b b' c c' d) ∨ ⟪b - d, a - d⟫ = 0 := by
  by_cases hB : ⟪b - d, a - d⟫ = 0
  · exact Or.inr hB
  · exact Or.inl (k6t4_B11_core W hT hκ hβ1 hfar (Or.inl hB))

end C2
end Type08Sp
end Minimality
