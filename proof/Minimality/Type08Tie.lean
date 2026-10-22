module

public import Minimality.Type08Slide

@[expose] public section

/-!
# Type 08: the far-end ties (`FEWER-FACES-PROOFS.md` §10 addendum, Lemma X)

At the tie `T` (`a' c ∥ d b`: `β₂ = 1`, the far ends of `Q_bc` along `d b` coincide in
projection) and the tie `T'` (`a c' ∥ d b`: `α₁ = 1`), the slides of `Type08Slide.lean`
need a vertex that is a middle at the view `u₀ = b − d` to go inside along the slide,
or they pick up a poked-out corner.  The routes of Lemma X (in the frame `d; a, c, b` of
`Type08Slide.lean`):

* at `T` (`α₁ > 1` by the far-end identity, `Type08Codim.lean`):
  R1 `K_b` along `Q_bc` (`isRupert_kb_four`); R2′ `K_d` along `Q_ab` with `a'` hidden
  (`β > 1`, `isRupert_kd_four`) or poking out (`β < 1`, rim `d c' b' a' c`,
  `isRupert_r2p`); R2″ `Q_bc` with the rim `d a c' b' a'` (`isRupert_r2pp`);
* at `T'` (`β₂ < 1`): R3 `K_d` along `Q_ab` (`isRupert_kd_four`); R4′ `K_b` along `Q_bc`
  with `a` hidden (`α > 1`, `isRupert_kb_four`) or poking out (`α < 1`, rim `b c' a b' c`,
  `isRupert_r4p`); R4″ `Q_ab` with the rim `b a b' c a'` (`isRupert_r4pp`).

Each five-corner route asks its rim to be strictly unimodal at `u₀` (`StrictUnimodal`)
and `NoBadNormal` along its circle (for R2′ and R4′ with a poked-out vertex the refined
`NoBadNormalR`: a double normal of the short edge, which is parallel to the face, is
excluded through its feet); the four-corner routes ask `NWS4` (no weak saddle) and
`NoBadNormal`.  Which route applies is decided by the depths (the paper's analysis):
`isRupert_routeT`, `isRupert_routeT'` in `Type08X.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The two derivative tests of the four-corner routes at the ties. -/
theorem tie_extra_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) :
    det3 (b' - c') (a - c') (c - d) = (α * β₁ - β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a' - b') (d - a) = (β * α₂ - α₂) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> ring

set_option maxHeartbeats 1000000 in
/-- **`K_b` along `Q_bc` (routes R1 and R4′ of Lemma X, and Lemma C).**  In the frame
`d; a, c, b`, with `α₁ ≥ 1` (at `α₁ = 1`, the tie `T'`, `a` must go inside: `α > 1`) and
`β₂ ≤ 1` (at `β₂ = 1`, the tie `T`, `a'` is a middle next to `c`), if `K_b`'s rim
`b c' b' c` has no weak saddle at the view along `d b` and `NoBadNormal` holds along
`Q_bc`, `K` is Rupert. -/
theorem isRupert_kb_four {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 1 ≤ α₁) (hα₁α : α₁ = 1 → 1 < α)
    (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ ≤ 1) (hαβ₂ : 1 < α₂ + β₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hN : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫))
    (hsb : NoBadNormal (quad b c' b' c) (b - d) (c - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := t4_slide_dets hb' hc' ha'
  obtain ⟨X1, -⟩ := tie_extra_dets hb' hc' ha'
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hα₁p : 0 < α₁ := by linarith
  have hκ' : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  refine isRupert_of_slide' V {d, a'} (b - d) (c - d) hu (quad b c' b' c) ?_ ?_
    (quad_injective hbc' hbb' hbc (Ne.symm hb'c') (Ne.symm hcc') hb'c) (by norm_num)
    (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_ (eventually_unimodal_quad_slide hN) hsb
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [V, quad_0, quad_1, quad_2, quad_3]
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
    exacts [⟨Ne.symm hdb, Ne.symm ha'b⟩, ⟨Ne.symm hdc', Ne.symm ha'c'⟩,
      ⟨Ne.symm hdb', Ne.symm ha'b'⟩, ⟨Ne.symm hdc, Ne.symm ha'c⟩]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [pos_of_coef K0 (by positivity) hE, pos_of_coef K1 hα₁p hE,
      pos_of_coef K2 hκ' hE, pos_of_coef K3 (by positivity) hE, pos_of_coef K4 hα hE,
      pos_of_coef K5 hκ' hE, pos_of_coef K6 hα₁p hE, pos_of_coef K7 hα hE]
  · intro z hz hzM hzx i
    have hza : z = a := by
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      simp only [mem_insert, mem_singleton, not_or] at hzM
      rcases hmemV z hz with h | h | h | h | h | h | h
      exacts [absurd h hzM.1, h, absurd h hzM.2, absurd h h0, absurd h h2, absurd h h3,
        absurd h h1]
    rw [hza]
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    · exact slideTest_zero K8 K9 (by linarith) hE
    · rcases hα₁.lt_or_eq with h1 | h1
      · refine slideTest_strict K10 ?_ hE
        rw [show β * α₁ - β = β * (α₁ - 1) by ring]; exact mul_pos hβ (by linarith)
      · refine slideTest_zero (by rw [K10, ← h1]; ring) X1 ?_ hE
        rw [show α * β₁ - β₁ = β₁ * (α - 1) by ring]
        exact mul_pos hβ₁ (by linarith [hα₁α h1.symm])
    · exact slideTest_strict K11 (by linarith) hE
    · exact slideTest_strict K12 one_pos hE
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht : (0 : ℝ) < t := ht0
      have h1 : (1 + t) ≠ 0 := by positivity
      refine ⟨3, 1 / (1 + t), -1 / (1 + t), by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · exact div_ne_zero (by norm_num) h1
      · simp only [a3, quad_3, quad_0]; match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := 1 - α₂) hβ₂] with t ht0 hlt
      have ht : (0 : ℝ) < t := ht0
      have h1 : (1 + t) ≠ 0 := by positivity
      refine ⟨3, (1 - β₂ + t * α₂) / (1 + t), (α₂ + β₂ - 1) / (1 + t), ?_, ?_, ?_, ?_⟩
      · exact div_pos (by have := mul_pos ht hα₂; linarith) (by positivity)
      · rw [div_lt_one (by positivity)]; linarith
      · exact div_ne_zero (by linarith) h1
      · simp only [a3, quad_3, quad_0]; rw [ha']; match_scalars <;> field_simp <;> ring

set_option maxHeartbeats 1000000 in
/-- **`K_d` along `Q_ab` (routes R2′ and R3 of Lemma X, and Lemma C).**  In the frame
`d; a, c, b`, with `α₁ ≥ 1` (at `α₁ = 1`, the tie `T'`, `a` is a middle next to `c'`) and
`β₂ ≤ 1` (at `β₂ = 1`, the tie `T`, `a'` must go inside: `β > 1`), if `K_d`'s rim
`d c' b' c` has no weak saddle at the view along `d b` and `NoBadNormal` holds along
`Q_ab`, `K` is Rupert. -/
theorem isRupert_kd_four {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hα₁ : 1 ≤ α₁) (hβ₁ : 0 < β₁)
    (hα₂ : 0 < α₂) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ ≤ 1) (hβ₂β : β₂ = 1 → 1 < β)
    (hκ : 0 < α + α₁ * (β - 1))
    (hN' : NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫))
    (hsd : NoBadNormal (quad d c' b' c) (b - d) (a - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨-, -, K2, -, -, K5, -, -, -, -, -, -, -, K13, K14, K15, K16, K17, K18,
    K19, K20, K21, K22, K23, -, -, -, -, -, -, -⟩ := t4_slide_dets hb' hc' ha'
  obtain ⟨-, X2⟩ := tie_extra_dets hb' hc' ha'
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hα₁p : 0 < α₁ := by linarith
  have hκ' : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have pK20 : 0 < α * β₂ + β * α₁ - α₁ * β₂ := by
    rw [show α * β₂ + β * α₁ - α₁ * β₂ = β₂ * (α + α₁ * (β - 1)) + α₁ * β * (1 - β₂) by ring]
    exact add_pos_of_pos_of_nonneg (mul_pos hβ₂ hκ)
      (mul_nonneg (mul_pos hα₁p hβ).le (by linarith))
  refine isRupert_of_slide' V {b, a} (b - d) (d - a) hu (quad d c' b' c) ?_ ?_
    (quad_injective hdc' hdb' hdc (Ne.symm hb'c') (Ne.symm hcc') hb'c) (by norm_num)
    (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_ (eventually_unimodal_quad_slide hN') ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [V, quad_0, quad_1, quad_2, quad_3]
  · intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [quad_0, quad_1, quad_2, quad_3, mem_insert, mem_singleton, not_or]
    exacts [⟨hdb, hda⟩, ⟨Ne.symm hbc', Ne.symm hac'⟩, ⟨Ne.symm hbb', Ne.symm hab'⟩,
      ⟨Ne.symm hbc, Ne.symm hac⟩]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [pos_of_coef K13 (by positivity) hE, pos_of_coef K14 hα₁p hE,
      pos_of_coef K2 hκ' hE, pos_of_coef K15 (by positivity) hE, pos_of_coef K16 hα hE,
      pos_of_coef K5 hκ' hE, pos_of_coef K17 hα₁p hE, pos_of_coef K18 hα hE]
  · intro z hz hzM hzx i
    have hza : z = a' := by
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      simp only [mem_insert, mem_singleton, not_or] at hzM
      rcases hmemV z hz with h | h | h | h | h | h | h
      exacts [absurd h h0, absurd h hzM.2, h, absurd h hzM.1, absurd h h2, absurd h h3,
        absurd h h1]
    rw [hza]
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    · exact slideTest_strict K19 (by positivity) hE
    · exact slideTest_strict K20 pK20 hE
    · rcases hβ₂1.lt_or_eq with h1 | h1
      · refine slideTest_strict K21 ?_ hE
        rw [show -α * β₂ + α = α * (1 - β₂) by ring]; exact mul_pos hα (by linarith)
      · refine slideTest_zero (by rw [K21, h1]; ring) X2 ?_ hE
        rw [show β * α₂ - α₂ = α₂ * (β - 1) by ring]
        exact mul_pos hα₂ (by linarith [hβ₂β h1])
    · exact slideTest_zero K22 K23 hα₂ hE
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := β₁ - 1) hα₁p] with t ht0 hlt
      have ht : (0 : ℝ) < t := ht0
      have h1 : (α₁ + t * β₁) ≠ 0 := by positivity
      refine ⟨0, t / (α₁ + t * β₁), α₁ / (α₁ + t * β₁), by positivity, ?_, by positivity, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · simp only [a0, quad_0, quad_1]; rw [hc']
        match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht : (0 : ℝ) < t := ht0
      have h1 : (α₁ + t * β₁) ≠ 0 := by positivity
      refine ⟨0, 1 / (α₁ + t * β₁), -β₁ / (α₁ + t * β₁), by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith [mul_pos ht hβ₁]
      · exact div_ne_zero (by linarith) h1
      · simp only [a0, quad_0, quad_1]; rw [hc']
        match_scalars <;> field_simp <;> ring
  · exact hsd.of_span 0 (-1) (by module)

/-- The tests of the rim `d a c' b' a'` at the tie `T` (route R2″, along `Q_bc`). -/
theorem r2pp_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + (c - d)) :
    det3 (a - d) (c' - d) (b - d) = 0 ∧
    det3 (a - d) (c' - d) (d - c) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (b' - d) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - d) (a' - d) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - a) (b' - a) (b - d) = (β*α₁ - β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - a) (a' - a) (b - d) = (α₁ - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - a) (d - a) (b - d) = 0 ∧
    det3 (c' - a) (d - a) (d - c) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a' - c') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (d - c') (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a - c') (b - d) = (β*α₁ - β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - b') (d - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - b') (a - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - b') (c' - b') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - a') (a - a') (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - a') (c' - a') (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - a') (b' - a') (b - d) = (α) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring


/-- The tests of the rim `d c' b' a' c` at the tie `T` (route R2′ with `a'` poking out, along `Q_ab`). -/
theorem r2p_dets {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + (c - d)) :
    det3 (c' - d) (b' - d) (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - d) (a' - d) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - d) (c - d) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (a' - c') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (c - c') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - c') (d - c') (b - d) = (β*α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - b') (c - b') (b - d) = 0 ∧
    det3 (a' - b') (c - b') (d - a) = (-β*α₂ + α₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - b') (d - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - b') (c' - b') (b - d) = (α + β*α₁ - α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - a') (d - a') (b - d) = 0 ∧
    det3 (c - a') (d - a') (d - a) = (α₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - a') (c' - a') (b - d) = 0 ∧
    det3 (c - a') (c' - a') (d - a) = (α₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - a') (b' - a') (b - d) = 0 ∧
    det3 (c - a') (b' - a') (d - a) = (-β*α₂ + α₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (c' - c) (b - d) = (α₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (b' - c) (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (d - c) (a' - c) (b - d) = 0 ∧
    det3 (d - c) (a' - c) (d - a) = (α₂) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring


/-- The tests of the rim `b a b' c a'` at the tie `T'` (route R4″, along `Q_ab`). -/
theorem r4pp_dets {a a' b b' c d : ℝ³} {α β α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d)) :
    det3 (a - b) (b' - b) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - b) (c - b) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - b) (a' - b) (b - d) = (β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (c - a) (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (a' - a) (b - d) = (α*β₂ + β - β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (b - a) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a' - b') (b - d) = (-α*β₂ + α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (b - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - c) (b - c) (b - d) = 0 ∧
    det3 (a' - c) (b - c) (a - d) = (α₂ + β₂ - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - c) (a - c) (b - d) = (-β₂ + 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a' - c) (b' - c) (b - d) = (-α*β₂ + α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - a') (a - a') (b - d) = (β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - a') (b' - a') (b - d) = (α*β₂) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - a') (c - a') (b - d) = 0 ∧
    det3 (b - a') (c - a') (a - d) = (α₂ + β₂ - 1) * det3 (a - d) (c - d) (b - d) := by
  subst hb' ha'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring


/-- The tests of the rim `b c' a b' c` at the tie `T'` (route R4′ with `a` poking out, along `Q_bc`). -/
theorem r4p_dets {a b b' c c' d : ℝ³} {α β β₁ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + (a - d) + β₁ • (b - d)) :
    det3 (c' - b) (a - b) (b - d) = 0 ∧
    det3 (c' - b) (a - b) (c - d) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - b) (b' - b) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c' - b) (c - b) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - c') (b' - c') (b - d) = 0 ∧
    det3 (a - c') (b' - c') (c - d) = (-α*β₁ + β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - c') (c - c') (b - d) = 0 ∧
    det3 (a - c') (c - c') (c - d) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (a - c') (b - c') (b - d) = 0 ∧
    det3 (a - c') (b - c') (c - d) = (β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (c - a) (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (b - a) (b - d) = (β) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b' - a) (c' - a) (b - d) = 0 ∧
    det3 (b' - a) (c' - a) (c - d) = (-α*β₁ + β₁) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (b - b') (b - d) = (α) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (c' - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (c - b') (a - b') (b - d) = (α + β - 1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - c) (c' - c) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - c) (a - c) (b - d) = (1) * det3 (a - d) (c - d) (b - d) ∧
    det3 (b - c) (b' - c) (b - d) = (α) * det3 (a - d) (c - d) (b - d) := by
  subst hb' hc'
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring




set_option maxHeartbeats 1000000 in
/-- **Route R2″ of Lemma X** (at the tie `T`, `β₂ = 1`): slide along `Q_bc` (`e = d − c`);
`b`, `c` lie over its side `a' d`, and `a` pokes out of `Q_ab`'s lower chain; the rim is
`d a c' b' a'`. -/
theorem isRupert_r2pp {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hu5 : StrictUnimodal (fun i => ⟪quint d a c' b' a' i, b - d⟫))
    (hs5 : NoBadNormal (quint d a c' b' a') (b - d) (c - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16⟩ :=
    r2pp_dets hb' hc' ha'
  have hα₁p : 0 < α₁ := by linarith
  have p4 : 0 < β * α₁ - β := by
    rw [show β * α₁ - β = β * (α₁ - 1) by ring]; exact mul_pos hβ (by linarith)
  have p8 : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  refine isRupert_of_slide'' V {b, c} (b - d) (d - c) hu (quint d a c' b' a') ?_ ?_
    (quint_injective hda hdc' hdb' hda' hac' hab' haa' (Ne.symm hb'c') (Ne.symm ha'c')
      (Ne.symm ha'b'))
    (by norm_num) (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_
    (eventually_unimodal_of_strict _ _ _ hu5) (hs5.of_span 0 (-1) (by module))
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, mem_singleton, not_or]
    exacts [⟨hdb, hdc⟩, ⟨hab, hac⟩, ⟨Ne.symm hbc', Ne.symm hcc'⟩, ⟨Ne.symm hbb', hb'c⟩,
      ⟨ha'b, ha'c⟩]
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [slideTest_zero P0 P1 hβ₁ hE, slideTest_strict P2 hβ hE, slideTest_strict P3 one_pos hE,
      slideTest_strict P4 p4 hE, slideTest_strict P5 (by linarith) hE, slideTest_zero P6 P7 hβ₁ hE,
      slideTest_strict P8 p8 hE, slideTest_strict P9 (mul_pos hβ hα₁p) hE,
      slideTest_strict P10 p4 hE, slideTest_strict P11 hα hE, slideTest_strict P12 (by linarith) hE,
      slideTest_strict P13 p8 hE, slideTest_strict P14 one_pos hE, slideTest_strict P15 hα₁p hE,
      slideTest_strict P16 hα hE]
  · intro z hz hzM hzx
    exfalso
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    simp only [mem_insert, mem_singleton, not_or] at hzM
    rcases hmemV z hz with h | h | h | h | h | h | h
    exacts [h0 h, h1 h, h4 h, hzM.1 h, h3 h, hzM.2 h, h2 h]
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := α₂ - 1) one_pos]
        with t ht0 hlt
      have ht : (0 : ℝ) < t := ht0
      have hD : 0 < 1 + t * α₂ := by positivity
      refine ⟨4, (1 + t * (α₂ - 1)) / (1 + t * α₂), 1 / (1 + t * α₂), div_pos hlt hD, ?_,
        div_ne_zero one_ne_zero hD.ne', ?_⟩
      · rw [div_lt_one hD]; linarith
      · simp only [b4, quint_4, quint_0]; rw [ha']; match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht : (0 : ℝ) < t := ht0
      have hD : 0 < 1 + t * α₂ := by positivity
      refine ⟨4, t * α₂ / (1 + t * α₂), -α₂ / (1 + t * α₂), by positivity, ?_,
        div_ne_zero (by linarith) hD.ne', ?_⟩
      · rw [div_lt_one hD]; linarith
      · simp only [b4, quint_4, quint_0]; rw [ha']; match_scalars <;> field_simp <;> ring

set_option maxHeartbeats 1000000 in
/-- **Route R2′ of Lemma X with `a'` poking out** (at the tie `T`, `β₂ = 1`, `β < 1`):
slide along `Q_ab` (`e = d − a`); `b`, `a` lie over its side `d c'`, and `a'` pokes out
between `b'` and `c`; the rim is `d c' b' a' c`. -/
theorem isRupert_r2p {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hα₁ : 1 ≤ α₁) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hu5 : StrictUnimodal (fun i => ⟪quint d c' b' a' c i, b - d⟫))
    (hs5 : NoBadNormalR (quint d c' b' a' c) (b - d) (a - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18,
    P19⟩ := r2p_dets hb' hc' ha'
  have hα₁p : 0 < α₁ := by linarith
  have p3 : 0 < α + β * α₁ - α₁ := by
    rw [show α + β * α₁ - α₁ = α + α₁ * (β - 1) by ring]; exact hκ
  have p7 : 0 < -β * α₂ + α₂ := by
    rw [show -β * α₂ + α₂ = α₂ * (1 - β) by ring]; exact mul_pos hα₂ (by linarith)
  refine isRupert_of_slide_uos V {b, a} (b - d) (d - a) hu (quint d c' b' a' c) ?_ ?_
    (quint_injective hdc' hdb' hda' hdc (Ne.symm hb'c') (Ne.symm ha'c') (Ne.symm hcc')
      (Ne.symm ha'b') hb'c ha'c)
    (by norm_num) (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_
    (Or.inl hu5) (hs5.of_span 0 (-1) (by module))
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, mem_singleton, not_or]
    exacts [⟨hdb, hda⟩, ⟨Ne.symm hbc', Ne.symm hac'⟩, ⟨Ne.symm hbb', Ne.symm hab'⟩,
      ⟨ha'b, Ne.symm haa'⟩, ⟨Ne.symm hbc, Ne.symm hac⟩]
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [slideTest_strict P0 (mul_pos hβ hα₁p) hE, slideTest_strict P1 hα₁p hE,
      slideTest_strict P2 hα₁p hE, slideTest_strict P3 p3 hE, slideTest_strict P4 p3 hE,
      slideTest_strict P5 (mul_pos hβ hα₁p) hE, slideTest_zero P6 P7 p7 hE,
      slideTest_strict P8 hα hE, slideTest_strict P9 p3 hE, slideTest_zero P10 P11 hα₂ hE,
      slideTest_zero P12 P13 hα₂ hE, slideTest_zero P14 P15 p7 hE,
      slideTest_strict P16 hα₁p hE, slideTest_strict P17 hα hE, slideTest_zero P18 P19 hα₂ hE]
  · intro z hz hzM hzx
    exfalso
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    simp only [mem_insert, mem_singleton, not_or] at hzM
    rcases hmemV z hz with h | h | h | h | h | h | h
    exacts [h0 h, hzM.2 h, h3 h, hzM.1 h, h2 h, h4 h, h1 h]
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := β₁ - 1) hα₁p] with t ht0 hlt
      have ht : (0 : ℝ) < t := ht0
      have h1 : (α₁ + t * β₁) ≠ 0 := by positivity
      refine ⟨0, t / (α₁ + t * β₁), α₁ / (α₁ + t * β₁), by positivity, ?_, by positivity, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · simp only [b0, quint_0, quint_1]; rw [hc']
        match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht : (0 : ℝ) < t := ht0
      have h1 : (α₁ + t * β₁) ≠ 0 := by positivity
      refine ⟨0, 1 / (α₁ + t * β₁), -β₁ / (α₁ + t * β₁), by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith [mul_pos ht hβ₁]
      · exact div_ne_zero (by linarith) h1
      · simp only [b0, quint_0, quint_1]; rw [hc']
        match_scalars <;> field_simp <;> ring

set_option maxHeartbeats 1000000 in
/-- **Route R4″ of Lemma X** (at the tie `T'`, `α₁ = 1`): slide along `Q_ab`
(`e = a − d`); `d`, `c'` lie over its side `b a`, and `a'` pokes out of `Q_bc`'s upper
chain; the rim is `b a b' c a'`. -/
theorem isRupert_r4pp {a a' b b' c c' d : ℝ³} {α β β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hαβ₂ : 1 < α₂ + β₂)
    (hu5 : StrictUnimodal (fun i => ⟪quint b a b' c a' i, b - d⟫))
    (hs5 : NoBadNormal (quint b a b' c a') (b - d) (a - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16⟩ :=
    r4pp_dets hb' ha'
  have p4 : 0 < α * β₂ + β - β₂ := by
    rcases le_or_gt 1 α with h1 | h1
    · rw [show α * β₂ + β - β₂ = β + β₂ * (α - 1) by ring]
      exact add_pos_of_pos_of_nonneg hβ (mul_nonneg hβ₂.le (by linarith))
    · rw [show α * β₂ + β - β₂ = (α + β - 1) + (1 - α) * (1 - β₂) by ring]
      exact add_pos (by linarith) (mul_pos (by linarith) (by linarith))
  have p6 : 0 < -α * β₂ + α := by
    rw [show -α * β₂ + α = α * (1 - β₂) by ring]; exact mul_pos hα (by linarith)
  refine isRupert_of_slide'' V {d, c'} (b - d) (a - d) hu (quint b a b' c a') ?_ ?_
    (quint_injective (Ne.symm hab) hbb' hbc (Ne.symm ha'b) hab' hac haa' hb'c (Ne.symm ha'b')
      (Ne.symm ha'c))
    (by norm_num) (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_
    (eventually_unimodal_of_strict _ _ _ hu5) hs5
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, mem_singleton, not_or]
    exacts [⟨Ne.symm hdb, hbc'⟩, ⟨Ne.symm hda, hac'⟩, ⟨Ne.symm hdb', hb'c'⟩,
      ⟨Ne.symm hdc, hcc'⟩, ⟨Ne.symm hda', ha'c'⟩]
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [slideTest_strict P0 hβ hE, slideTest_strict P1 one_pos hE, slideTest_strict P2 hβ₂ hE,
      slideTest_strict P3 (by linarith) hE, slideTest_strict P4 p4 hE, slideTest_strict P5 hβ hE,
      slideTest_strict P6 p6 hE, slideTest_strict P7 hα hE, slideTest_strict P8 (by linarith) hE,
      slideTest_zero P9 P10 (by linarith) hE, slideTest_strict P11 (by linarith) hE,
      slideTest_strict P12 p6 hE, slideTest_strict P13 hβ₂ hE,
      slideTest_strict P14 (mul_pos hα hβ₂) hE, slideTest_zero P15 P16 (by linarith) hE]
  · intro z hz hzM hzx
    exfalso
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    simp only [mem_insert, mem_singleton, not_or] at hzM
    rcases hmemV z hz with h | h | h | h | h | h | h
    exacts [hzM.1 h, h1 h, h4 h, h0 h, h2 h, h3 h, hzM.2 h]
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht : (0 : ℝ) < t := ht0
      have hD : 0 < 1 + t := by positivity
      refine ⟨0, t / (1 + t), -1 / (1 + t), by positivity, ?_, div_ne_zero (by norm_num) hD.ne', ?_⟩
      · rw [div_lt_one hD]; linarith
      · simp only [b0, quint_0, quint_1]; match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := 1 - β₁) one_pos]
        with t ht0 hlt
      have ht : (0 : ℝ) < t := ht0
      have hD : 0 < 1 + t := by positivity
      refine ⟨0, (1 + t * (1 - β₁)) / (1 + t), β₁ / (1 + t), div_pos hlt hD, ?_,
        div_ne_zero hβ₁.ne' hD.ne', ?_⟩
      · rw [div_lt_one hD]; nlinarith [mul_pos ht hβ₁]
      · simp only [b0, quint_0, quint_1]; rw [hc']; match_scalars <;> field_simp <;> ring

set_option maxHeartbeats 1000000 in
/-- **Route R4′ of Lemma X with `a` poking out** (at the tie `T'`, `α₁ = 1`, `α < 1`):
slide along `Q_bc` (`e = c − d`); `d`, `a'` lie over its side `c b`, and `a` pokes out
between `c'` and `b'`; the rim is `b c' a b' c`. -/
theorem isRupert_r4p {a a' b b' c c' d : ℝ³} {α β β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hαβ : 1 < α + β) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hαβ₂ : 1 < α₂ + β₂)
    (hu5 : StrictUnimodal (fun i => ⟪quint b c' a b' c i, b - d⟫))
    (hs5 : NoBadNormalR (quint b c' a b' c) (b - d) (c - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hda, hda', hdb, hdb', hdc, hdc'⟩, ⟨haa', hab, hab', hac, hac'⟩,
    ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩, ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14, P15, P16, P17, P18,
    P19⟩ := r4p_dets hb' hc'
  have p5 : 0 < -α * β₁ + β₁ := by
    rw [show -α * β₁ + β₁ = β₁ * (1 - α) by ring]; exact mul_pos hβ₁ (by linarith)
  refine isRupert_of_slide_uos V {d, a'} (b - d) (c - d) hu (quint b c' a b' c) ?_ ?_
    (quint_injective hbc' (Ne.symm hab) hbb' hbc (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc')
      hab' hac hb'c)
    (by norm_num) (det3 (a - d) (c - d) (b - d)) hE ?_ ?_ ?_
    (Or.inl hu5) hs5
  · intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [V, quint_0, quint_1, quint_2, quint_3, quint_4]
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp only [quint_0, quint_1, quint_2, quint_3, quint_4, mem_insert, mem_singleton, not_or]
    exacts [⟨Ne.symm hdb, Ne.symm ha'b⟩, ⟨Ne.symm hdc', Ne.symm ha'c'⟩, ⟨Ne.symm hda, haa'⟩,
      ⟨Ne.symm hdb', Ne.symm ha'b'⟩, ⟨Ne.symm hdc, Ne.symm ha'c⟩]
  · intro i j hi hj
    rcases zmod5_pairs i j hi hj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    simp only [b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3, quint_4]
    exacts [slideTest_zero P0 P1 hβ₁ hE, slideTest_strict P2 hβ hE, slideTest_strict P3 one_pos hE,
      slideTest_zero P4 P5 p5 hE, slideTest_zero P6 P7 hβ₁ hE, slideTest_zero P8 P9 hβ₁ hE,
      slideTest_strict P10 (by linarith) hE, slideTest_strict P11 hβ hE,
      slideTest_zero P12 P13 p5 hE, slideTest_strict P14 hα hE,
      slideTest_strict P15 (by linarith) hE, slideTest_strict P16 (by linarith) hE,
      slideTest_strict P17 one_pos hE, slideTest_strict P18 one_pos hE, slideTest_strict P19 hα hE]
  · intro z hz hzM hzx
    exfalso
    have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3; have h4 := hzx 4
    simp only [quint_0, quint_1, quint_2, quint_3, quint_4] at h0 h1 h2 h3 h4
    simp only [mem_insert, mem_singleton, not_or] at hzM
    rcases hmemV z hz with h | h | h | h | h | h | h
    exacts [hzM.1 h, h2 h, hzM.2 h, h0 h, h3 h, h4 h, h1 h]
  · intro m hm
    rcases mem_insert.mp hm with h | h
    · rw [h]
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have ht : (0 : ℝ) < t := ht0
      have h1 : (1 + t) ≠ 0 := by positivity
      refine ⟨4, 1 / (1 + t), -1 / (1 + t), by positivity, ?_, ?_, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · exact div_ne_zero (by norm_num) h1
      · simp only [b4, quint_4, quint_0]; match_scalars <;> field_simp <;> ring
    · rw [mem_singleton.mp h]
      filter_upwards [self_mem_nhdsWithin, eventually_pos_of_pos (B := 1 - α₂) hβ₂] with t ht0 hlt
      have ht : (0 : ℝ) < t := ht0
      have h1 : (1 + t) ≠ 0 := by positivity
      refine ⟨4, (1 - β₂ + t * α₂) / (1 + t), (α₂ + β₂ - 1) / (1 + t), ?_, ?_, ?_, ?_⟩
      · exact div_pos (by have := mul_pos ht hα₂; linarith) (by positivity)
      · rw [div_lt_one (by positivity)]; linarith
      · exact div_ne_zero (by linarith) h1
      · simp only [b4, quint_4, quint_0]; rw [ha']; match_scalars <;> field_simp <;> ring

end Minimality

end
