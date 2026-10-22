module

public import Minimality.Type08Tie
public import Minimality.Type08R0

@[expose] public section

/-!
# Type 08: which route of Lemma X applies (`FEWER-FACES-PROOFS.md` §10 addendum, A.6)

At the far-end ties `T` (`a' c ∥ d b`, `β₂ = 1`) and `T'` (`a c' ∥ d b`, `α₁ = 1`) the
routes of Lemma X (`Type08Tie.lean`) each need a depth condition (a rim without a weak
saddle, a strictly unimodal five-corner rim, the side of the hidden vertex).  The paper's
case analysis decides which route applies from the depths alone; here it is done in Lean,
so that the hypotheses left (`RouteT`, `RouteT'`) are generic: no tie between neighbours of
the rims used, the hidden vertex not on the side (`β ≠ 1`, `α ≠ 1`), and the slides'
double-normal conditions.

At `T` (the edge `d → b` not bad, no triple tie at the view along `d b`):
* `K_b` without a weak saddle: R1 (`isRupert_kb_four`).
* Otherwise the depths are separated, `min(z_b, z_{b'}) ≥ max(z_c, z_{c'})`, and `K_d` has no
  weak saddle (Lemma 5's closing); the claim gives `z_d < max(z_c, z_{c'})`.  If `a'` is
  hidden (`β > 1`): R2′ (`isRupert_kd_four`).  If `a'` pokes out (`β < 1`): the rim
  `d c' b' a' c` is strictly unimodal (its peak is `b'` or `a'`, `z_{a'} > z_c`), and R2′
  applies unless the short edge `[a', c]` and the side `[d, c']` (both parallel to `Q_ab`)
  carry a double normal along the normal of `Q_ab` (their projections onto `Q_ab` meet: the
  persistent double normal).  Then that double normal gives `z_d < z_{a'}`, the rim
  `d a c' b' a'` is strictly unimodal (`a` lies below the chord `d c'`), and R2″ applies
  (`isRupert_r2pp`).
* `isRupert_routeT`.

At `T'` (same inputs):
* `K_d` without a weak saddle: R3 (`isRupert_kd_four`).
* Otherwise the claim excludes the saddle with `d`, `b'` high, so
  `max(z_d, z_{b'}) ≤ min(z_c, z_{c'})`, `K_b` has no weak saddle (Lemma 5's closing), and
  "not bad" gives `min(z_c, z_{c'}) < z_b`.  If `a` is hidden (`α > 1`): R4′
  (`isRupert_kb_four`).  If `a` pokes out (`α < 1`): the rim `b c' a b' c` is strictly
  unimodal (`z_a < z_{c'}`), and R4′ applies unless the short edge `[c', a]` and the side
  `[c, b]` carry a persistent double normal (along the normal of `Q_bc`); then
  `z_a < z_b`, the rim `b a b' c a'` is strictly unimodal (`a'` lies above the chord `b c`),
  and R4″ applies (`isRupert_r4pp`).
* `isRupert_routeT'`.

The persistent double normal is excluded through its feet (`NoBadNormalR`, `NoFeet`,
`SlideDS.lean`); `NoBadNormal` would also exclude the open set where the depth intervals of
the two parallel edges merely meet.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- A cyclic sequence with distinct neighbours and at most one strict local maximum is
strictly unimodal (the global maximum is a strict local maximum). -/
theorem strictUnimodal_of_unique {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hne : ∀ i, z i ≠ z (i + 1))
    (huniq : ∀ i j, z (i - 1) < z i → z (i + 1) < z i → z (j - 1) < z j → z (j + 1) < z j →
      i = j) :
    StrictUnimodal z := by
  classical
  refine ⟨hne, Finset.card_eq_one.mpr ?_⟩
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (univ : Finset (ZMod k)) z univ_nonempty
  have h1 : z (i₀ - 1) < z i₀ := lt_of_le_of_ne (hmax _ (mem_univ _)) (by
    have := hne (i₀ - 1); rwa [sub_add_cancel] at this)
  have h2 : z (i₀ + 1) < z i₀ := lt_of_le_of_ne (hmax _ (mem_univ _)) (hne i₀).symm
  refine ⟨i₀, ?_⟩
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => huniq j i₀ h.1 h.2 h1 h2, fun h => by subst h; exact ⟨h1, h2⟩⟩

/-- A point of a segment, by its depth. -/
theorem segment_inner {p q Y w : ℝ³} (hY : Y ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ⟪Y, w⟫ = ⟪p, w⟫ + t * (⟪q, w⟫ - ⟪p, w⟫) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hY
  refine ⟨β, hβ, by linarith, ?_⟩
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, show α = 1 - β by linarith]
  ring

/-- The weak saddles of a 4-rim. -/
theorem not_NWS4_quad {z₀ z₁ z₂ z₃ : ℝ} (h : ¬ NWS4 (quad z₀ z₁ z₂ z₃)) :
    (z₁ ≤ z₀ ∧ z₃ ≤ z₀ ∧ z₁ ≤ z₂ ∧ z₃ ≤ z₂) ∨ (z₀ ≤ z₁ ∧ z₀ ≤ z₃ ∧ z₂ ≤ z₁ ∧ z₂ ≤ z₃) := by
  simpa only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] using h

/-- The claim of Lemma 9.3 / 5 (`A z_d + B z_{b'} < C z_c + E z_{c'}`, `A + B = C + E`)
excludes `z_d, z_{b'} ≥ max(z_c, z_{c'})`. -/
theorem claim_contra {A B C E zd zb' zc zc' : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hE : 0 < E) (hsum : A + B = C + E) (hlow : A * zd + B * zb' < C * zc + E * zc')
    (h1 : zc ≤ zd) (h2 : zc' ≤ zd) (h3 : zc ≤ zb') (h4 : zc' ≤ zb') : False := by
  have hMd : max zc zc' ≤ zd := max_le h1 h2
  have hMb : max zc zc' ≤ zb' := max_le h3 h4
  have e1 := mul_le_mul_of_nonneg_left hMd hA.le
  have e2 := mul_le_mul_of_nonneg_left hMb hB.le
  have e3 := mul_le_mul_of_nonneg_left (le_max_left zc zc') hC.le
  have e4 := mul_le_mul_of_nonneg_left (le_max_right zc zc') hE.le
  have e5 : (A + B) * max zc zc' = (C + E) * max zc zc' := by rw [hsum]
  linarith

/-- **The generic conditions of Lemma X at the tie `T`** (in the frame `d; a, c, b`, at the
view along `d b`): `a'` is not on the side `[d, c']` of `Q_ab` (`β ≠ 1`); `NoBadNormal` for
`K_b` along `Q_bc` (R1) and for `K_d` along `Q_ab` (R2′); no tie between neighbours of the
rims `d c' b' a'  c` (R2′ with `a'` poking out) and `d a c' b' a'` (R2″); `NoBadNormal` for
the latter along `Q_bc`; and, unless the short edge `[a', c]` and the side `[d, c']` have a
double normal along the normal of `Q_ab` (the persistent double normal), `NoBadNormalR` for
the former along `Q_ab`.  All fail only in codimension 2 on `T`. -/
structure RouteT (a a' b b' c c' d : ℝ³) : Prop where
  beta : det3 (a - d) (b' - c) (b - d) ≠ 0
  r1 : NoBadNormal (quad b c' b' c) (b - d) (c - d)
  r2 : NoBadNormal (quad d c' b' c) (b - d) (a - d)
  poke : ∀ i, ⟪quint d c' b' a' c i, b - d⟫ ≠ ⟪quint d c' b' a' c (i + 1), b - d⟫
  r2pp_ne : ∀ i, ⟪quint d a c' b' a' i, b - d⟫ ≠ ⟪quint d a c' b' a' (i + 1), b - d⟫
  r2pp : NoBadNormal (quint d a c' b' a') (b - d) (c - d)
  r2p : (¬ ∃ Y ∈ segment ℝ d c', ∃ Y' ∈ segment ℝ a' c, Y' ≠ Y ∧ ⟪Y' - Y, b - d⟫ = 0 ∧
      ⟪Y' - Y, a - d⟫ = 0) → NoBadNormalR (quint d c' b' a' c) (b - d) (a - d)

/-- **The generic conditions of Lemma X at the tie `T'`**: `a` is not on the side `[b, c]`
of `Q_bc` (`α ≠ 1`); `NoBadNormal` for `K_d` along `Q_ab` (R3) and for `K_b` along `Q_bc`
(R4′); no tie between neighbours of the rims `b c' a b' c` (R4′ with `a` poking out) and
`b a b' c a'` (R4″); `NoBadNormal` for the latter along `Q_ab`; and, unless the short edge
`[c', a]` and the side `[c, b]` have a double normal along the normal of `Q_bc`,
`NoBadNormalR` for the former along `Q_bc`. -/
structure RouteT' (a a' b b' c c' d : ℝ³) : Prop where
  alpha : det3 (b' - a) (c - d) (b - d) ≠ 0
  r3 : NoBadNormal (quad d c' b' c) (b - d) (a - d)
  r4 : NoBadNormal (quad b c' b' c) (b - d) (c - d)
  poke : ∀ i, ⟪quint b c' a b' c i, b - d⟫ ≠ ⟪quint b c' a b' c (i + 1), b - d⟫
  r4pp_ne : ∀ i, ⟪quint b a b' c a' i, b - d⟫ ≠ ⟪quint b a b' c a' (i + 1), b - d⟫
  r4pp : NoBadNormal (quint b a b' c a') (b - d) (a - d)
  r4p : (¬ ∃ Y ∈ segment ℝ c' a, ∃ Y' ∈ segment ℝ c b, Y' ≠ Y ∧ ⟪Y' - Y, b - d⟫ = 0 ∧
      ⟪Y' - Y, c - d⟫ = 0) → NoBadNormalR (quint b c' a b' c) (b - d) (c - d)

theorem quint_ne_of {v₀ v₁ v₂ v₃ v₄ u : ℝ³}
    (h : ∀ i, ⟪quint v₀ v₁ v₂ v₃ v₄ i, u⟫ ≠ ⟪quint v₀ v₁ v₂ v₃ v₄ (i + 1), u⟫) :
    ∀ i, quint ⟪v₀, u⟫ ⟪v₁, u⟫ ⟪v₂, u⟫ ⟪v₃, u⟫ ⟪v₄, u⟫ i ≠
      quint ⟪v₀, u⟫ ⟪v₁, u⟫ ⟪v₂, u⟫ ⟪v₃, u⟫ ⟪v₄, u⟫ (i + 1) := by
  intro i
  have e := congrFun (quint_inner_eq v₀ v₁ v₂ v₃ v₄ u)
  rw [← e i, ← e (i + 1)]
  exact h i

set_option maxHeartbeats 1000000 in
/-- **Lemma X at `T`: a route applies** (the paper's case analysis).  In the frame
`d; a, c, b` at the tie `T` (`a' = d + α₂ (b − d) + (c − d)`), with `α₁ > 1` (the far end of
`Q_ab` is `c'`), `κ' > 0`, the edge `d → b` not bad and no triple tie, the generic
conditions `RouteT` make `K` Rupert. -/
theorem isRupert_routeT {a a' b b' c c' d : ℝ³} {α β α₁ β₁ α₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hα₁ : 1 < α₁) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hκ : 0 < α + α₁ * (β - 1))
    (hgood : ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (htouch : ¬ (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫))
    (hR : RouteT a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hdb : d ≠ b := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    exact hnd.1.2.2.1
  have ha'1 : a' = d + α₂ • (b - d) + (1 : ℝ) • (c - d) := by rw [one_smul]; exact ha'
  by_cases hNb : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
  · -- R1: `K_b` has no weak saddle
    exact isRupert_kb_four hb' hc' ha'1 hnd hE hα hβ hαβ hα₁.le (fun h => absurd h hα₁.ne')
      hβ₁ hα₂ one_pos le_rfl (by linarith) hκ hNb hR.r1
  have hNd := t4_closing hb' hc' ha'1 hdb hE hα hβ (by linarith) hβ₁ hκ hgood htouch hNb
  have hB : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hdb))
  -- the separated depths
  have hsep : ⟪c', b - d⟫ ≤ ⟪b', b - d⟫ ∧ ⟪c, b - d⟫ ≤ ⟪b', b - d⟫ := by
    rcases not_NWS4_quad hNb with ⟨-, -, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h3, h4⟩
    · exact absurd (max_le (le_min h2 h1) (le_min h4 h3)) hgood
  -- the claim of Lemma 5: `z_d < max(z_c, z_{c'})`
  obtain ⟨A, B, C, E', hA, hB', hC, hE', hsum, hlow⟩ :=
    t4_claim hb' hc' ha'1 hdb hE hα hβ (by linarith) hβ₁ hκ
  have hclaim : ⟪d, b - d⟫ < ⟪c, b - d⟫ ∨ ⟪d, b - d⟫ < ⟪c', b - d⟫ := by
    by_contra hc
    push Not at hc
    exact claim_contra hA hB' hC hE' hsum hlow hc.1 hc.2 hsep.2 hsep.1
  -- `β ≠ 1`
  have eβ : det3 (a - d) (b' - c) (b - d) = (β - 1) * det3 (a - d) (c - d) (b - d) := by
    rw [hb']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have hβne : β ≠ 1 := fun h => hR.beta (by rw [eβ, h, sub_self, zero_mul])
  rcases lt_or_gt_of_ne hβne with hβ1 | hβ1
  swap
  · -- R2′ with `a'` hidden
    exact isRupert_kd_four hb' hc' ha'1 hnd hE hα hβ hα₁.le hβ₁ hα₂ one_pos le_rfl
      (fun _ => hβ1) hκ hNd hR.r2
  -- `a'` pokes out: `z_{a'} = z_c + α₂ |b − d|²`, and `a` lies below the chord `d c'`
  have za' : ⟪a', b - d⟫ = ⟪c, b - d⟫ + α₂ * ⟪b - d, b - d⟫ := by
    rw [ha']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring
  have za : ⟪c', b - d⟫ - ⟪d, b - d⟫ =
      α₁ * (⟪a, b - d⟫ - ⟪d, b - d⟫) + β₁ * ⟪b - d, b - d⟫ := by
    rw [hc']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring
  have hca' : ⟪c, b - d⟫ < ⟪a', b - d⟫ := by rw [za']; nlinarith [mul_pos hα₂ hB]
  have hachord : ⟪a, b - d⟫ ≤ ⟪d, b - d⟫ ∨ ⟪a, b - d⟫ < ⟪c', b - d⟫ := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.mpr hα₁) (sub_pos.mpr hc.1), mul_pos hβ₁ hB]
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨s0, s1, s2, s3, s4⟩ := zmod5_sub_one
  by_cases hF : ∃ Y ∈ segment ℝ d c', ∃ Y' ∈ segment ℝ a' c, Y' ≠ Y ∧ ⟪Y' - Y, b - d⟫ = 0 ∧
      ⟪Y' - Y, a - d⟫ = 0
  · -- R2″: the persistent double normal gives `z_d < z_{a'}`
    obtain ⟨Y, hY, Y', hY', -, hD, -⟩ := hF
    obtain ⟨t, ht0, ht1, hYt⟩ := segment_inner (w := b - d) hY
    obtain ⟨s, hs0, hs1, hYs⟩ := segment_inner (w := b - d) hY'
    rw [inner_sub_left] at hD
    have hne := quint_ne_of hR.r2pp_ne
    have hda' : ⟪d, b - d⟫ < ⟪a', b - d⟫ := by
      by_contra hc
      push Not at hc
      have n4 := hne 4
      simp only [b4, quint_4, quint_0] at n4
      rcases hclaim with h | h
      · linarith
      · have k1 := mul_nonneg ht0 (sub_nonneg.mpr h.le)
        have k2 := mul_nonneg hs0 (sub_nonneg.mpr hca'.le)
        have k3 : ⟪d, b - d⟫ ≤ ⟪a', b - d⟫ := by nlinarith
        exact n4 (le_antisymm hc k3)
    refine isRupert_r2pp hb' hc' ha' hnd hE hα hβ hαβ hα₁ hβ₁ hα₂ hκ ?_ hR.r2pp
    rw [quint_inner_eq]
    refine strictUnimodal_of_unique hne ?_
    intro i j hi1 hi2 hj1 hj2
    rcases hachord with h | h <;>
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi1 hi2 hj1 hj2 <;>
    first | rfl | (exfalso; linarith)
  · -- R2′ with `a'` poking out
    refine isRupert_r2p hb' hc' ha' hnd hE hα hβ hβ1 hα₁.le hβ₁ hα₂ hκ ?_ (hR.r2p hF)
    rw [quint_inner_eq]
    refine strictUnimodal_of_unique (quint_ne_of hR.poke) ?_
    intro i j hi1 hi2 hj1 hj2
    rcases hclaim with h | h <;>
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi1 hi2 hj1 hj2 <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 1000000 in
/-- **Lemma X at `T'`: a route applies** (the paper's case analysis).  In the frame
`d; a, c, b` at the tie `T'` (`c' = d + (a − d) + β₁ (b − d)`), with `β₂ < 1` (the far end
of `Q_bc` is `c`), the edge `d → b` not bad and no triple tie, the generic conditions
`RouteT'` make `K` Rupert. -/
theorem isRupert_routeT' {a a' b b' c c' d : ℝ³} {α β β₁ α₂ β₂ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + (a - d) + β₁ • (b - d))
    (ha' : a' = d + α₂ • (b - d) + β₂ • (c - d))
    (hnd : [d, a, a', b, b', c, c'].Nodup) (hE : det3 (a - d) (c - d) (b - d) ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : 1 < α + β) (hβ₁ : 0 < β₁) (hα₂ : 0 < α₂)
    (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hαβ₂ : 1 < α₂ + β₂)
    (hgood : ¬ max ⟪b, b - d⟫ ⟪b', b - d⟫ ≤ min ⟪c, b - d⟫ ⟪c', b - d⟫)
    (htouch : ¬ (⟪c, b - d⟫ = ⟪b', b - d⟫ ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫))
    (hR : RouteT' a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  have hdb : d ≠ b := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    exact hnd.1.2.2.1
  have hc'1 : c' = d + (1 : ℝ) • (a - d) + β₁ • (b - d) := by rw [one_smul]; exact hc'
  have hκ : 0 < α + 1 * (β - 1) := by linarith
  by_cases hNd : NWS4 (quad ⟪d, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
  · -- R3: `K_d` has no weak saddle
    exact isRupert_kd_four hb' hc'1 ha' hnd hE hα hβ le_rfl hβ₁ hα₂ hβ₂ hβ₂1.le
      (fun h => absurd h hβ₂1.ne) hκ hNd hR.r3
  have hNb : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫) := by
    by_contra h
    exact hNd (t4_closing hb' hc'1 ha' hdb hE hα hβ one_pos hβ₁ hκ hgood htouch h)
  have hB : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr (Ne.symm hdb))
  -- the claim excludes the saddle with `d`, `b'` high
  obtain ⟨A, B, C, E', hA, hB', hC, hE', hsum, hlow⟩ :=
    t4_claim hb' hc'1 ha' hdb hE hα hβ one_pos hβ₁ hκ
  have hsad : ⟪b', b - d⟫ ≤ ⟪c', b - d⟫ ∧ ⟪b', b - d⟫ ≤ ⟪c, b - d⟫ := by
    rcases not_NWS4_quad hNd with ⟨h1, h2, h3, h4⟩ | ⟨-, -, h3, h4⟩
    · exact (claim_contra hA hB' hC hE' hsum hlow h2 h1 h4 h3).elim
    · exact ⟨h3, h4⟩
  -- "not bad": `min(z_c, z_{c'}) < z_b`
  have hbmin : ⟪c, b - d⟫ < ⟪b, b - d⟫ ∨ ⟪c', b - d⟫ < ⟪b, b - d⟫ := by
    by_contra hc
    push Not at hc
    exact hgood (max_le (le_min hc.1 hc.2) (le_min hsad.2 hsad.1))
  -- `α ≠ 1`
  have eα : det3 (b' - a) (c - d) (b - d) = (α - 1) * det3 (a - d) (c - d) (b - d) := by
    rw [hb']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have hαne : α ≠ 1 := fun h => hR.alpha (by rw [eα, h, sub_self, zero_mul])
  rcases lt_or_gt_of_ne hαne with hα1 | hα1
  swap
  · -- R4′ with `a` hidden
    exact isRupert_kb_four hb' hc'1 ha' hnd hE hα hβ hαβ le_rfl (fun _ => hα1) hβ₁ hα₂ hβ₂
      hβ₂1.le hαβ₂ hκ hNb hR.r4
  -- `a` pokes out: `z_a = z_{c'} − β₁ |b − d|²`, and `a'` lies above the chord `b c`
  have za : ⟪a, b - d⟫ = ⟪c', b - d⟫ - β₁ * ⟪b - d, b - d⟫ := by
    rw [hc']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring
  have hac' : ⟪a, b - d⟫ < ⟪c', b - d⟫ := by rw [za]; nlinarith [mul_pos hβ₁ hB]
  have za' : ⟪a', b - d⟫ = ⟪b, b - d⟫ + β₂ * (⟪c, b - d⟫ - ⟪b, b - d⟫) +
      (α₂ + β₂ - 1) * ⟪b - d, b - d⟫ := by
    rw [ha']; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring
  have hchord : ⟪b, b - d⟫ < ⟪a', b - d⟫ ∨ ⟪c, b - d⟫ < ⟪a', b - d⟫ := by
    rcases le_or_gt ⟪b, b - d⟫ ⟪c, b - d⟫ with h | h
    · left; rw [za']
      nlinarith [mul_nonneg hβ₂.le (sub_nonneg.mpr h),
        mul_pos (show 0 < α₂ + β₂ - 1 by linarith) hB]
    · right; rw [za']
      nlinarith [mul_pos (sub_pos.mpr hβ₂1) (sub_pos.mpr h),
        mul_pos (show 0 < α₂ + β₂ - 1 by linarith) hB]
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_add_one
  obtain ⟨s0, s1, s2, s3, s4⟩ := zmod5_sub_one
  by_cases hF : ∃ Y ∈ segment ℝ c' a, ∃ Y' ∈ segment ℝ c b, Y' ≠ Y ∧ ⟪Y' - Y, b - d⟫ = 0 ∧
      ⟪Y' - Y, c - d⟫ = 0
  · -- R4″: the persistent double normal gives `z_a < z_b`
    obtain ⟨Y, hY, Y', hY', -, hD, -⟩ := hF
    obtain ⟨t, ht0, ht1, hYt⟩ := segment_inner (w := b - d) hY
    obtain ⟨s, hs0, hs1, hYs⟩ := segment_inner (w := b - d) hY'
    rw [inner_sub_left] at hD
    have hne := quint_ne_of hR.r4pp_ne
    have hab : ⟪a, b - d⟫ < ⟪b, b - d⟫ := by
      by_contra hc
      push Not at hc
      have n0 := hne 0
      simp only [b0, quint_0, quint_1] at n0
      rcases hbmin with h | h
      · have k1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hac'.le)
        have k2 := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr h.le)
        have k3 : ⟪a, b - d⟫ ≤ ⟪b, b - d⟫ := by nlinarith
        exact n0 (le_antisymm hc k3)
      · linarith
    refine isRupert_r4pp hb' hc' ha' hnd hE hα hβ hαβ hβ₁ hβ₂ hβ₂1 hαβ₂ ?_ hR.r4pp
    rw [quint_inner_eq]
    refine strictUnimodal_of_unique hne ?_
    intro i j hi1 hi2 hj1 hj2
    rcases hchord with h | h <;>
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi1 hi2 hj1 hj2 <;>
    first | rfl | (exfalso; linarith)
  · -- R4′ with `a` poking out
    refine isRupert_r4p hb' hc' ha' hnd hE hα hα1 hβ hαβ hβ₁ hα₂ hβ₂ hβ₂1 hαβ₂ ?_ (hR.r4p hF)
    rw [quint_inner_eq]
    refine strictUnimodal_of_unique (quint_ne_of hR.poke) ?_
    intro i j hi1 hi2 hj1 hj2
    rcases hbmin with h | h <;>
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [b0, b1, b2, b3, b4, s0, s1, s2, s3, s4, quint_0, quint_1, quint_2, quint_3,
      quint_4] at hi1 hi2 hj1 hj2 <;>
    first | rfl | (exfalso; linarith)

end Minimality

end
