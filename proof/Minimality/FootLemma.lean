module

public import Minimality.TieMerge
public import Minimality.HiddenCap

@[expose] public section

/-!
# The Foot Lemma: a depth tie at the foot of a perpendicular, in a hidden cone

Let `v` be a point with three points `a, b, c ∈ O` such that `a - v, b - v, c - v` are linearly
independent; at every view in the open cone of these edges `v` is hidden by `O`
(`hiddenAt_of_cone`, Lemma HC (iii)), so the rim of `insert v O` is the rim of `O`.

* `isRupert_of_tieMerge_cone`: a view `u` in the OPEN cone, a rim of `O` with strict tests at `u`,
  an adjacent depth tie and a unimodal merged rim: `insert v O` is Rupert (Lemma TA).
* `isRupert_of_tieMerge_coneFace`: the same at a view `u = s (a - v) + t (b - v)` on the FACE of
  the cone spanned by `a - v, b - v` (`s, t > 0`), when the tied rim edge is not perpendicular to
  `a - b`: a tilt into the open cone that keeps the tie reduces it to the previous theorem.
* `isRupert_foot` (**Foot Lemma**, nopert229 p4/sat/OB1XPROOF.md §2): `u` the direction from `v`
  to the foot of its perpendicular on the line `ab`, the foot strictly inside the segment
  (`⟪a - v, a - b⟫ > 0`, `⟪b - v, b - a⟫ > 0`): `a` and `b` tie in depth, and if they are adjacent
  on the rim of `O` at `u` (strict tests) with a unimodal merged rim, `insert v O` is Rupert.
* `foot_inside_of_nonacute`: the foot is strictly inside when the angle `a-v-b` is non-acute;
  `isRupert_foot_of_nonacute`, `isRupert_foot_four` (4-corner rims: merged values distinct).
-/

set_option autoImplicit false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- On a cycle of `m + 1 ≥ 3` indices, `i + 2` differs from `i` and `i + 1`. -/
theorem add_one_add_one_ne {m : ℕ} (hm : 2 ≤ m) (i : ZMod (m + 1)) :
    i + 1 + 1 ≠ i ∧ i + 1 + 1 ≠ i + 1 := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h2 : ((2 : ℕ) : ZMod (m + 1)) = 0 := by
      have : i + 1 + 1 = i + ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
      rw [this] at e; simpa using e
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2; omega
  · have : Fact (1 < m + 1) := ⟨by omega⟩
    simp at e

/-- Cyclic unimodality passes to any `w` keeping every strict comparison of `z`. -/
theorem isCyclicUnimodal_of_keep {k : ℕ} [NeZero k] {z w : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) (hord : ∀ p q, z p < z q → w p < w q) : IsCyclicUnimodal w := by
  refine isCyclicUnimodal_of_refine hz (fun p q h => ?_) hord
  by_contra hne
  rcases lt_or_gt_of_ne (hz.1.ne hne) with h' | h'
  · exact (hord _ _ h').ne h
  · exact (hord _ _ h').ne' h

/-- A rim of `O` with strict tests at `u`, and `v` hidden by `O` at `u`: the tests of the
non-rim points hold over `insert v O`. -/
theorem rest_insert_of_hiddenAt (O : Finset ℝ³) (v u : ℝ³) (hv : HiddenAt O u v) {m : ℕ}
    [NeZero m] (hm : 2 ≤ m) (x : ZMod (m + 1) → ℝ³) (hxO : ∀ i, x i ∈ O)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u) :
    ∀ y ∈ insert v O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u := by
  intro y hy hyx i
  rcases Finset.mem_insert.1 hy with rfl | hy
  · refine hv (x i) (hxO i) (x (i + 1)) (hxO (i + 1)) (fun z hz => ?_)
      ⟨x (i + 1 + 1), hxO _, hcyc i _ (add_one_add_one_ne hm i).1 (add_one_add_one_ne hm i).2⟩
    by_cases hzx : ∃ j, z = x j
    · obtain ⟨j, rfl⟩ := hzx
      by_cases hji : j = i
      · subst hji; rw [sub_self, det3_zero_mid]
      by_cases hji' : j = i + 1
      · subst hji'; rw [det3_self_left]
      exact (hcyc i j hji hji').le
    · push Not at hzx
      exact (hrest z hz hzx i).le
  · exact hrest y hy hyx i

/-- **Tie merge in a hidden cone.**  `u` in the open cone of the independent edges
`a - v, b - v, c - v` (`a, b, c ∈ O`), a rim `x` of `O` (`m + 1 ≥ 3` corners) with strict tests
at `u`, an adjacent depth tie `⟪x i, u⟫ = ⟪x (i+1), u⟫` and the merged cycle cyclically unimodal:
`insert v O` is Rupert. -/
theorem isRupert_of_tieMerge_cone (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hli : LinearIndependent ℝ ![a - v, b - v, c - v]) (ca cb cc : ℝ)
    (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc) (u : ℝ³)
    (hu : u = ca • (a - v) + cb • (b - v) + cc • (c - v)) {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (x : ZMod (m + 1) → ℝ³) (hxO : ∀ i, x i ∈ O)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (i : ZMod (m + 1)) (htie : ⟪x i, u⟫ = ⟪x (i + 1), u⟫)
    (hU : IsCyclicUnimodal (skipAt (fun j => ⟪x j, u⟫) i)) : IsRupert (insert v O) := by
  have hu0 : u ≠ 0 := by
    intro h0
    have := Fintype.linearIndependent_iff.1 hli ![ca, cb, cc] (by
      rw [← h0, hu]; simp [Fin.sum_univ_three])
    exact hca.ne' (by simpa using this 0)
  have hv : HiddenAt O u v := by
    rw [hu]; exact hiddenAt_of_cone O v a b c ha hb hc hli ca cb cc hca hcb hcc
  exact isRupert_of_tieMerge (insert v O) u hu0 hm x (fun j => Finset.mem_insert_of_mem (hxO j))
    hcyc (rest_insert_of_hiddenAt O v u hv hm x hxO hcyc hrest) i htie hU

/-- **Tie merge on a face of the hidden cone.**  As `isRupert_of_tieMerge_cone`, at a view
`u = s (a - v) + t (b - v)` (`s, t > 0`) on the face of the cone; the tied edge
`x (i+1) - x i` must not be perpendicular to `a - b`.  A tilt `u + δ ((c - v) + μ (a - b))` into
the open cone keeps the tie and, for small `δ > 0`, every strict test. -/
theorem isRupert_of_tieMerge_coneFace (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hli : LinearIndependent ℝ ![a - v, b - v, c - v]) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (u : ℝ³) (hu : u = s • (a - v) + t • (b - v)) {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (x : ZMod (m + 1) → ℝ³) (hxO : ∀ i, x i ∈ O)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (i : ZMod (m + 1)) (htie : ⟪x i, u⟫ = ⟪x (i + 1), u⟫)
    (hE : ⟪a - b, x (i + 1) - x i⟫ ≠ 0)
    (hU : IsCyclicUnimodal (skipAt (fun j => ⟪x j, u⟫) i)) : IsRupert (insert v O) := by
  set E := x (i + 1) - x i with hEdef
  set μ : ℝ := -⟪c - v, E⟫ / ⟪a - b, E⟫ with hμ
  set w : ℝ³ := (c - v) + μ • (a - b) with hw
  have hwE : ⟪w, E⟫ = 0 := by
    rw [hw, inner_add_left, real_inner_smul_left, hμ]; field_simp; ring
  have e1 : ∀ (δ : ℝ) (p : ℝ³), ⟪p, u + δ • w⟫ = ⟪p, u⟫ + δ * ⟪p, w⟫ := by
    intro δ p; rw [inner_add_right, inner_smul_right]
  -- the strict conditions persist for small `δ > 0`
  have hcyc' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (i + 1) - x i) (x j - x i) (u + δ • w) := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases h : j ≠ i ∧ j ≠ i + 1
    · filter_upwards [eventually_pos_affine (A := det3 (x (i + 1) - x i) (x j - x i) u)
        (B := det3 (x (i + 1) - x i) (x j - x i) w) (Or.inl (hcyc i j h.1 h.2))] with δ hδ
      intro _ _; rw [det3_add_smul]; exact hδ
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ h
  have hrest' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) (u + δ • w) := by
    refine (eventually_all_finset O).2 fun y hy => ?_
    by_cases h : ∀ j, y ≠ x j
    · refine (eventually_all.2 fun i => ?_).mono fun δ hδ _ => hδ
      filter_upwards [eventually_pos_affine (A := det3 (x (i + 1) - x i) (y - x i) u)
        (B := det3 (x (i + 1) - x i) (y - x i) w) (Or.inl (hrest y hy h i))] with δ hδ
      rw [det3_add_smul]; exact hδ
    · exact Eventually.of_forall fun _ h1 => absurd h1 h
  have hdep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p q : ZMod (m + 1),
      ⟪x p, u⟫ < ⟪x q, u⟫ → ⟪x p, u + δ • w⟫ < ⟪x q, u + δ • w⟫ := by
    refine eventually_all.2 fun p => eventually_all.2 fun q => ?_
    by_cases h : ⟪x p, u⟫ < ⟪x q, u⟫
    · filter_upwards [eventually_pos_affine (A := ⟪x q, u⟫ - ⟪x p, u⟫)
        (B := ⟪x q, w⟫ - ⟪x p, w⟫) (Or.inl (sub_pos.2 h))] with δ hδ _
      rw [e1, e1]; nlinarith
    · exact Eventually.of_forall fun _ h' => absurd h' h
  have hcs : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < s + δ * μ := eventually_pos_affine (Or.inl hs)
  have hct : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < t + δ * (-μ) := eventually_pos_affine (Or.inl ht)
  obtain ⟨δ, ⟨⟨⟨⟨hc1, hr1⟩, hd1⟩, hs1⟩, ht1⟩, hδ⟩ :=
    ((((hcyc'.and hrest').and hdep).and hcs).and hct).and self_mem_nhdsWithin |>.exists
  have hδ0 : 0 < δ := hδ
  refine isRupert_of_tieMerge_cone O v a b c ha hb hc hli (s + δ * μ) (t + δ * (-μ)) δ hs1 ht1
    hδ0 (u + δ • w) (by rw [hu, hw]; module) hm x hxO hc1 hr1 i ?_ ?_
  · rw [e1, e1, htie]
    have : ⟪x (i + 1), w⟫ - ⟪x i, w⟫ = 0 := by
      rw [← inner_sub_left, real_inner_comm, hwE]
    have h2 : δ * ⟪x (i + 1), w⟫ - δ * ⟪x i, w⟫ = 0 := by rw [← mul_sub, this, mul_zero]
    linarith
  · exact isCyclicUnimodal_of_keep hU fun p q h => hd1 _ _ h

/-- The view of the Foot Lemma has the tie: `⟪a, u⟫ = ⟪b, u⟫` for
`u = ⟪b - v, b - a⟫ (a - v) + ⟪a - v, a - b⟫ (b - v)`, a positive multiple of the direction from
`v` to the foot of its perpendicular on the line `ab`. -/
theorem foot_tie (v a b : ℝ³) :
    ⟪a, ⟪b - v, b - a⟫ • (a - v) + ⟪a - v, a - b⟫ • (b - v)⟫ =
      ⟪b, ⟪b - v, b - a⟫ • (a - v) + ⟪a - v, a - b⟫ • (b - v)⟫ := by
  rw [← sub_eq_zero, ← inner_sub_left]
  simp only [inner_add_right, real_inner_smul_right]
  have h1 : ⟪a - b, a - v⟫ = ⟪a - v, a - b⟫ := real_inner_comm _ _
  have h2 : ⟪a - b, b - v⟫ = -⟪b - v, b - a⟫ := by
    rw [real_inner_comm, ← neg_sub b a, inner_neg_right]
  rw [h1, h2]; ring

/-- The foot of the perpendicular from `v` on the line `ab` lies strictly inside the segment
when the angle `a-v-b` is non-acute. -/
theorem foot_inside_of_nonacute {v a b : ℝ³} (ha : a ≠ v) (hb : b ≠ v)
    (hab : ⟪a - v, b - v⟫ ≤ 0) : 0 < ⟪a - v, a - b⟫ ∧ 0 < ⟪b - v, b - a⟫ := by
  have ea : a - b = (a - v) - (b - v) := by abel
  have eb : b - a = (b - v) - (a - v) := by abel
  have pa := real_inner_self_pos.2 (sub_ne_zero.2 ha)
  have pb := real_inner_self_pos.2 (sub_ne_zero.2 hb)
  rw [ea, eb, inner_sub_right (a - v) (a - v) (b - v), inner_sub_right (b - v) (b - v) (a - v)]
  have := real_inner_comm (a - v) (b - v)
  constructor <;> linarith

/-- **Foot Lemma.**  `a, b, c ∈ O` with independent edges `a - v, b - v, c - v`; the foot of the
perpendicular from `v` on the line `ab` strictly inside the segment; `u` the direction to the
foot (up to a positive factor).  If `a, b` are adjacent on a rim `x` of `O` with strict tests at
`u` and the rim with `a, b` merged is cyclically unimodal, `insert v O` is Rupert. -/
theorem isRupert_foot (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hli : LinearIndependent ℝ ![a - v, b - v, c - v])
    (hfa : 0 < ⟪a - v, a - b⟫) (hfb : 0 < ⟪b - v, b - a⟫) (u : ℝ³)
    (hu : u = ⟪b - v, b - a⟫ • (a - v) + ⟪a - v, a - b⟫ • (b - v)) {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (x : ZMod (m + 1) → ℝ³) (hxO : ∀ i, x i ∈ O)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (i : ZMod (m + 1)) (hxi : (x i = a ∧ x (i + 1) = b) ∨ (x i = b ∧ x (i + 1) = a))
    (hU : IsCyclicUnimodal (skipAt (fun j => ⟪x j, u⟫) i)) : IsRupert (insert v O) := by
  have hne : a - b ≠ 0 := by
    intro h; rw [h, inner_zero_right] at hfa; exact lt_irrefl _ hfa
  have hab : 0 < ⟪a - b, a - b⟫ := real_inner_self_pos.2 hne
  have htie := foot_tie v a b
  rw [← hu] at htie
  refine isRupert_of_tieMerge_coneFace O v a b c ha hb hc hli _ _ hfb hfa u hu hm x hxO hcyc
    hrest i ?_ ?_ hU
  · rcases hxi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact htie
    · exact htie.symm
  · rcases hxi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · rw [← neg_sub a b, inner_neg_right]; exact neg_ne_zero.2 hab.ne'
    · exact hab.ne'

/-- **Foot Lemma, non-acute angle at `v`**: the foot is then strictly inside `ab`. -/
theorem isRupert_foot_of_nonacute (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hli : LinearIndependent ℝ ![a - v, b - v, c - v])
    (hav : a ≠ v) (hbv : b ≠ v) (hang : ⟪a - v, b - v⟫ ≤ 0) (u : ℝ³)
    (hu : u = ⟪b - v, b - a⟫ • (a - v) + ⟪a - v, a - b⟫ • (b - v)) {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (x : ZMod (m + 1) → ℝ³) (hxO : ∀ i, x i ∈ O)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (i : ZMod (m + 1)) (hxi : (x i = a ∧ x (i + 1) = b) ∨ (x i = b ∧ x (i + 1) = a))
    (hU : IsCyclicUnimodal (skipAt (fun j => ⟪x j, u⟫) i)) : IsRupert (insert v O) :=
  isRupert_foot O v a b c ha hb hc hli (foot_inside_of_nonacute hav hbv hang).1
    (foot_inside_of_nonacute hav hbv hang).2 u hu hm x hxO hcyc hrest i hxi hU

/-- **Foot Lemma, four corners**: for a 4-corner rim the merged hypothesis is that the three
merged values are distinct. -/
theorem isRupert_foot_four (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hli : LinearIndependent ℝ ![a - v, b - v, c - v])
    (hfa : 0 < ⟪a - v, a - b⟫) (hfb : 0 < ⟪b - v, b - a⟫) (u : ℝ³)
    (hu : u = ⟪b - v, b - a⟫ • (a - v) + ⟪a - v, a - b⟫ • (b - v))
    (x : ZMod 4 → ℝ³) (hxO : ∀ i, x i ∈ O)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u)
    (hrest : ∀ y ∈ O, (∀ j, y ≠ x j) → ∀ i, 0 < det3 (x (i + 1) - x i) (y - x i) u)
    (i : ZMod 4) (hxi : (x i = a ∧ x (i + 1) = b) ∨ (x i = b ∧ x (i + 1) = a))
    (hdist : Function.Injective (skipAt (m := 3) (fun j => ⟪x j, u⟫) i)) :
    IsRupert (insert v O) :=
  isRupert_foot O v a b c ha hb hc hli hfa hfb u hu (m := 3) (by norm_num) x hxO hcyc hrest i hxi
    (isCyclicUnimodal_three hdist)

end Minimality

end
