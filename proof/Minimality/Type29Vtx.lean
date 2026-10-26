module

public import Minimality.Type29TwoFace
public import Minimality.VtxLimit

@[expose] public section

/-!
# Type 29: the one-circle vertex closings T1 and T2 (`FEWER-FACES-PROOFS.md` §22.3–22.10, §28)

The vertex lines `012/1456` (T1) and `1456/234` (T2) are seen along a triangle and the quad
`1456`, whose far end (`6` for T1, `5` for T2) is opposite to the apex: the closing is realized on
the quad's circle only.  At the limit it is closed by `isRupert_vtx_limit` (Theorem 22.8,
Lemma 22.10), where the class-d condition `⟪N_Q, c⟫ = ⟪N_Q, b⟫` is excluded by the region facts
carried by the certificate (Lemma 28.8, the paper's K.2).

* `quad_offsets29`, `quad_middles29`, `isRupert_vSector29`, `isRupert_vTriLim29`: the lemmas of
  type 21's `V` (`Type21Vtx.lean`) for the facets of type 29 (copied, not generalized).
* `isRupert_T2quad29`: the four-corner rims `(4, 3, 0, 5)`, `(4, 2, 0, 5)` of T2; the class-d
  condition fails by the carried region facts (Lemma 28.8).
* `isRupert_T2tri29`: the triangle rim `(4, 3, 5)` of T2 (a sector rim, Lemma 22.6 (b)).
* `isRupert_T1_29`, `T1_h4esc`, `T1_esc_P14`, `T1_esc_P11`: the rim `(1, 2, 3, 6)` of T1: (H4)
  for the upper middle and the escape for the lower one (Lemma 28.7).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- **The middles of a quadrilateral face lie on opposite sides of the chord** (generic labels):
the face `S_Q ∋ v, a, m₁, m₂` with apex `v` and far end `a` opposite (the sides `v m₁`, `v m₂` are
edges: facets `S₁ ∋ v, m₁` and `S₂ ∋ v, m₂` with the other two beneath), seen edge-on at `u`:
if `m_i = v + s_i (a − v) + δ_i u`, then `δ₁ δ₂ < 0`. -/
theorem quad_offsets29 {x : Fin 7 → ℝ³} (T : Facets29 x) {v a b m₁ m₂ : Fin 7}
    {SQ S₁ S₂ : Finset (Fin 7)} (FQ : Face16 x SQ) (F₁ : Face16 x S₁) (F₂ : Face16 x S₂)
    (hmem : v ∈ SQ ∧ a ∈ SQ ∧ m₁ ∈ SQ ∧ m₂ ∈ SQ ∧ b ∉ SQ ∧ v ∈ S₁ ∧ m₁ ∈ S₁ ∧ a ∉ S₁ ∧
      m₂ ∉ S₁ ∧ v ∈ S₂ ∧ m₂ ∈ S₂ ∧ a ∉ S₂ ∧ m₁ ∉ S₂)
    (hnd : [v, a, m₁, m₂].Nodup) {u : ℝ³}
    (hpar : NoParAt (univ.image x) u) {s₁ δ₁ s₂ δ₂ : ℝ}
    (hm₁ : x m₁ = x v + s₁ • (x a - x v) + δ₁ • u)
    (hm₂ : x m₂ = x v + s₂ • (x a - x v) + δ₂ • u) : δ₁ * δ₂ < 0 := by
  obtain ⟨hvQ, haQ, h1Q, h2Q, hbQ, hv1, h11, ha1, h21, hv2, h22, ha2, h12⟩ := hmem
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hva, hv1', hv2'⟩, ⟨ha1', ha2'⟩, h12', -⟩ := hnd
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hNQ : FQ.N ≠ 0 := FQ.N_ne hvQ hbQ
  have hcu : cross (x a - x v) u ≠ 0 := hpar _ (mem v) _ (mem a) (T.inj.ne hva)
  -- `a − v = α (m₁ − v) + β (m₂ − v)` with `α, β > 0` (the sides `v m₁`, `v m₂` are edges)
  obtain ⟨α, β, hab'⟩ := EdgeConf.exists_coords_of_perp (FQ.inner_sub h1Q hvQ)
    (FQ.inner_sub h2Q hvQ) (FQ.inner_sub haQ hvQ)
    (cross_ne_zero_of_noSeg T.inj T.noSeg hv1' hv2' h12') hNQ
  have hβ : 0 < β := by
    have k := congrArg (fun w => ⟪F₁.N, w⟫) hab'
    simp only [inner_add_right, real_inner_smul_right, F₁.inner_sub h11 hv1, mul_zero,
      zero_add] at k
    have k1 : ⟪F₁.N, x a - x v⟫ < 0 := by rw [← F₁.hN, F₁.zero v hv1, sub_zero]; exact F₁.neg a ha1
    have k2 : ⟪F₁.N, x m₂ - x v⟫ < 0 := by
      rw [← F₁.hN, F₁.zero v hv1, sub_zero]; exact F₁.neg m₂ h21
    rw [k] at k1
    exact pos_of_mul_neg_left k1 k2.le |> fun h => by nlinarith
  have hα : 0 < α := by
    have k := congrArg (fun w => ⟪F₂.N, w⟫) hab'
    simp only [inner_add_right, real_inner_smul_right, F₂.inner_sub h22 hv2, mul_zero,
      add_zero] at k
    have k1 : ⟪F₂.N, x a - x v⟫ < 0 := by rw [← F₂.hN, F₂.zero v hv2, sub_zero]; exact F₂.neg a ha2
    have k2 : ⟪F₂.N, x m₁ - x v⟫ < 0 := by
      rw [← F₂.hN, F₂.zero v hv2, sub_zero]; exact F₂.neg m₁ h12
    rw [k] at k1
    exact pos_of_mul_neg_left k1 k2.le |> fun h => by nlinarith
  -- the offsets: `α δ₁ + β δ₂ = 0`, `δ₁ ≠ 0`
  have hsum : α * δ₁ + β * δ₂ = 0 := by
    have k : (α * s₁ + β * s₂ - 1) • (x a - x v) + (α * δ₁ + β * δ₂) • u = 0 := by
      have e1 : x m₁ - x v = s₁ • (x a - x v) + δ₁ • u := by rw [hm₁]; abel
      have e2 : x m₂ - x v = s₂ • (x a - x v) + δ₂ • u := by rw [hm₂]; abel
      rw [e1, e2] at hab'
      linear_combination (norm := module) -hab'
    have k' := congrArg (fun w => det3 (x a - x v) w (cross (x a - x v) u)) k
    have e : det3 (x a - x v) ((α * s₁ + β * s₂ - 1) • (x a - x v) + (α * δ₁ + β * δ₂) • u)
        (cross (x a - x v) u) = (α * δ₁ + β * δ₂) *
          ⟪cross (x a - x v) u, cross (x a - x v) u⟫ := by
      rw [det3_expand]
      simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.inner_apply, Fin.sum_univ_three,
        RCLike.inner_apply, conj_trivial]
      ring
    rw [e] at k'
    have hz : det3 (x a - x v) (0 : ℝ³) (cross (x a - x v) u) = 0 := by
      simp [det3_expand]
    rw [hz] at k'
    exact (mul_eq_zero.mp k').resolve_right (real_inner_self_pos.mpr hcu).ne'
  have hδ₁ : δ₁ ≠ 0 := by
    rintro rfl
    apply cross_ne_zero_of_noSeg T.inj T.noSeg hv1' hva (Ne.symm ha1')
    have : x m₁ - x v = s₁ • (x a - x v) := by rw [hm₁]; module
    rw [this, EdgeConf.cross_smul_left'', cross_self, smul_zero]
  have hδ₂ : δ₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero, add_zero] at hsum
    exact hδ₁ ((mul_eq_zero.mp hsum).resolve_left hα.ne')
  have k : α * (δ₁ * δ₂) = -(β * (δ₂ * δ₂)) := by linear_combination δ₂ * hsum
  have := mul_pos hβ (mul_self_pos.mpr hδ₂)
  exact neg_of_mul_neg_right (by linarith) hα.le


/-! ### Triangle rims: a sector rim (Proposition 22.2, Lemma 22.6 (b)) -/

/-- **A sector rim of `V`'s triangle closing** (Proposition 22.2 for the rim `v m a b`).  At a
vertex view `u` the quadrilateral `S_Q = {v, a, m, m'}` (apex `v`, far end `a`) and the triangle
`S_T = {v, b, n}` are seen edge-on; the middles are `m = v + s (a − v) + δ u`,
`m' = v + s' (a − v) + δ' u` on opposite sides of the chord (`δ δ' < 0`); every point is weakly
left of the sides of the triangle rim `v a b`.  If the sector rim `v m a b` (the middle `m` shown,
`m'` and `n` hidden) is robustly unimodal, a tilt into the sector shows it, so the set is Rupert,
whatever its horizontal double normals. -/
theorem isRupert_vSector29 {x : Fin 7 → ℝ³} (T : Facets29 x) {v a b n m m' : Fin 7}
    {SQ ST : Finset (Fin 7)} (FQ : Face16 x SQ) (FT : Face16 x ST)
    (hmem : v ∈ SQ ∧ a ∈ SQ ∧ m ∈ SQ ∧ m' ∈ SQ ∧ b ∉ SQ ∧
      (∀ i ∈ SQ, i = v ∨ i = a ∨ i = m ∨ i = m') ∧
      v ∈ ST ∧ b ∈ ST ∧ n ∈ ST ∧ a ∉ ST ∧ m ∉ ST ∧ (∀ i ∈ ST, i = v ∨ i = b ∨ i = n))
    (hnd : [v, a, b, n, m, m'].Nodup)
    {u : ℝ³} (hu : u ≠ 0) (hQu : ⟪FQ.N, u⟫ = 0)
    {s δ s' δ' : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hs0' : 0 < s') (hs1' : s' < 1)
    (hδδ : δ * δ' < 0)
    (hm : x m = x v + s • (x a - x v) + δ • u) (hm' : x m' = x v + s' • (x a - x v) + δ' • u)
    (hleft₀ : ∀ z ∈ univ.image x, 0 ≤ det3 (x a - x v) (z - x v) u ∧
      0 ≤ det3 (x b - x a) (z - x a) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u)
    (hpar : NoParAt (univ.image x) u)
    (hg1 : G1At (univ.image x) u (SQ.image x) (ST.image x))
    (hz : IsRobustUnimodal (fun i => ⟪x (quad v m a b i), u⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨hvQ, haQ, hmQ, hm'Q, hbQ, hQall, hvT, hbT, hnT, haT, hmT, hTall⟩ := hmem
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hva, hvb, hvn, hvm, hvm'⟩, ⟨hab, han, ham, ham'⟩, ⟨hbn, hbm, hbm'⟩, ⟨hnm, hnm'⟩,
    hmm', -⟩ := hnd'
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  set e := x a - x v with he
  have hδ : δ ≠ 0 := by rintro rfl; simp at hδδ
  have hNQ : FQ.N ≠ 0 := FQ.N_ne hvQ hbQ
  have hNT : FT.N ≠ 0 := FT.N_ne hvT haT
  have hQe : ⟪FQ.N, e⟫ = 0 := FQ.inner_sub haQ hvQ
  have hcu : cross e u ≠ 0 := hpar _ (mem v) _ (mem a) (T.inj.ne hva)
  have hcu' : cross u e ≠ 0 := by
    intro h0; apply hcu
    have : cross e u = -cross u e := by ext j; fin_cases j <;> simp [cross] <;> ring
    rw [this, h0, neg_zero]
  have hD : det3 u e FQ.N ≠ 0 := det3_perp_ne hQu hQe hcu' hNQ
  -- the sector rim `v m a b`
  set lab : ZMod 4 → Fin 7 := quad v m a b with hlab
  have hlabi : Function.Injective lab := by
    intro i j hij
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      simp only [hlab, quad_0, quad_1, quad_2, quad_3] at hij <;>
      first | rfl | (exfalso; simp_all)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  have hab' : cross FQ.N FT.N ≠ 0 := by
    refine cross_normals_ne hNQ (FQ.inner_sub haQ hvQ) ?_
    rw [← FT.hN, FT.zero v hvT, sub_zero]; exact FT.neg a haT
  have hσT : det3 (x v - x b) (x n - x b) FT.N ≠ 0 :=
    FT.det3_normal_ne hbT hvT hnT haT (cross_ne_zero_of_noSeg T.inj T.noSeg (Ne.symm hvb) hbn hvn)
  have hdm : x m - x v = s • e + δ • u := by rw [hm]; abel
  have hdm' : x m' - x v = s' • e + δ' • u := by rw [hm']; abel
  refine isRupert_twoFace (by norm_num) x T.inj lab hlabi hu
    (fun i hi => ((FQ.hf hvQ) i).1 hi) (fun i hi => ((FT.hf hvT) i).1 hi) hab' ?_ ?_ hg1
    (mul_ne_zero hδ hD) hσT ?_ ?_ hz
  · -- every point weakly left of the sides
    intro z i
    obtain ⟨l0, -, l2, l3⟩ : 0 ≤ det3 (x a - x v) (x z - x v) u ∧ True ∧
        0 ≤ det3 (x b - x a) (x z - x a) u ∧ 0 ≤ det3 (x v - x b) (x z - x b) u :=
      ⟨(hleft₀ _ (mem z)).1, trivial, (hleft₀ _ (mem z)).2.1, (hleft₀ _ (mem z)).2.2⟩
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [hlab, a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    · have : det3 (x m - x v) (x z - x v) u = s * det3 (x a - x v) (x z - x v) u := by
        rw [hm]; simp only [he, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_nonneg hs0.le l0
    · have : det3 (x a - x m) (x z - x m) u = (1 - s) * det3 (x a - x v) (x z - x v) u := by
        rw [hm]; simp only [he, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      rw [this]; exact mul_nonneg (by linarith) l0
    · exact l2
    · exact l3
  · intro i
    exact hpar _ (mem _) _ (mem _) (T.inj.ne (hlabi.ne (zmod_ne_add_one (by norm_num) i)))
  · -- the sides on `S_Q`: `v → m` and `m → a`
    intro i z h1 h2 h3 h4 h5
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [hlab, a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at h1 h2 h4 h5 ⊢
    · rcases hQall z h3 with rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · have : det3 (x m - x v) (x z - x v) FQ.N = δ * det3 u e FQ.N := by
          rw [hdm]; simp only [he, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        rw [this]
        have := mul_self_pos.mpr (mul_ne_zero hδ hD)
        linarith [this]
      · exact absurd rfl h5
      · have : det3 (x m - x v) (x z - x v) FQ.N = (δ * s' - s * δ') * det3 u e FQ.N := by
          rw [hdm, hdm']; simp only [he, det3_expand, PiLp.add_apply, PiLp.sub_apply,
            PiLp.smul_apply, smul_eq_mul]; ring
        rw [this]
        have k : 0 < δ * (δ * s' - s * δ') := by nlinarith [mul_self_pos.mpr hδ]
        have := mul_pos k (mul_self_pos.mpr hD)
        linarith [this]
    · rcases hQall z h3 with rfl | rfl | rfl | rfl
      · have : det3 (x a - x m) (x z - x m) FQ.N = δ * det3 u e FQ.N := by
          rw [hm]; simp only [he, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
            smul_eq_mul]; ring
        rw [this]
        have := mul_self_pos.mpr (mul_ne_zero hδ hD)
        linarith [this]
      · exact absurd rfl h5
      · exact absurd rfl h4
      · have : det3 (x a - x m) (x z - x m) FQ.N =
            (δ * (1 - s') - (1 - s) * δ') * det3 u e FQ.N := by
          rw [hm, hm']; simp only [he, det3_expand, PiLp.add_apply, PiLp.sub_apply,
            PiLp.smul_apply, smul_eq_mul]; ring
        rw [this]
        have k : 0 < δ * (δ * (1 - s') - (1 - s) * δ') := by
          nlinarith [mul_self_pos.mpr hδ]
        have := mul_pos k (mul_self_pos.mpr hD)
        linarith [this]
    · exact absurd h2 hbQ
    · exact absurd h1 hbQ
  · -- the side on `S_T`: `b → v`
    intro i z h1 h2 h3 h4 h5
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [hlab, a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] at h1 h2 h4 h5 ⊢
    · exact absurd h2 hmT
    · exact absurd h1 hmT
    · exact absurd h1 haT
    · rcases hTall z h3 with rfl | rfl | rfl
      · exact absurd rfl h5
      · exact absurd rfl h4
      · exact mul_self_pos.mpr hσT

/-- **The middles of a quadrilateral face seen edge-on at a vertex view** (generic labels): the
face `S_Q ∋ v, a, m₁, m₂` with apex `v` and far end `a` opposite (the sides `v m₁`, `v m₂` are
edges: facets `S₁ ∋ v, m₁` and `S₂ ∋ v, m₂` with the other two beneath); the view `u` lies in
the face's plane and is not along `a − v`, and `b` (off the face) is strictly left of `v a`.  If
every point is weakly left of the triangle `v a b`, then `m₁`, `m₂` lie over the open chord, on
opposite sides: `m_i = v + s_i (a − v) + δ_i u`, `0 < s_i < 1`, `δ₁ δ₂ < 0`. -/
theorem quad_middles29 {x : Fin 7 → ℝ³} (T : Facets29 x) {v a b m₁ m₂ : Fin 7}
    {SQ S₁ S₂ : Finset (Fin 7)} (FQ : Face16 x SQ) (F₁ : Face16 x S₁) (F₂ : Face16 x S₂)
    (hmem : v ∈ SQ ∧ a ∈ SQ ∧ m₁ ∈ SQ ∧ m₂ ∈ SQ ∧ b ∉ SQ ∧ v ∈ S₁ ∧ m₁ ∈ S₁ ∧ a ∉ S₁ ∧
      m₂ ∉ S₁ ∧ v ∈ S₂ ∧ m₂ ∈ S₂ ∧ a ∉ S₂ ∧ m₁ ∉ S₂)
    (hnd : [v, a, b, m₁, m₂].Nodup) {u : ℝ³} (hQu : ⟪FQ.N, u⟫ = 0)
    (hpar : NoParAt (univ.image x) u)
    (hD : 0 < det3 (x a - x v) (x b - x v) u)
    (hleft : ∀ z ∈ univ.image x, 0 ≤ det3 (x b - x a) (z - x a) u ∧
      0 ≤ det3 (x v - x b) (z - x b) u) :
    ∃ s₁ δ₁ s₂ δ₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧ δ₁ * δ₂ < 0 ∧
      x m₁ = x v + s₁ • (x a - x v) + δ₁ • u ∧ x m₂ = x v + s₂ • (x a - x v) + δ₂ • u := by
  obtain ⟨hvQ, haQ, h1Q, h2Q, hbQ, hv1, h11, ha1, h21, hv2, h22, ha2, h12⟩ := hmem
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hva, hvb, hv1', hv2'⟩, ⟨hab, ha1', ha2'⟩, ⟨hb1, hb2⟩, h12', -⟩ := hnd
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hNQ : FQ.N ≠ 0 := FQ.N_ne hvQ hbQ
  have hcu : cross (x a - x v) u ≠ 0 := hpar _ (mem v) _ (mem a) (T.inj.ne hva)
  -- coordinates over the chord
  have coords : ∀ {i : Fin 7}, i ∈ SQ → i ≠ v → i ≠ a →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ x i = x v + s • (x a - x v) + δ • u := by
    intro i hi hiv hia
    obtain ⟨s, δ, hX⟩ := EdgeConf.exists_coords_of_perp (FQ.inner_sub haQ hvQ) hQu
      (FQ.inner_sub hi hvQ) hcu hNQ
    have hxi : x i = x v + s • (x a - x v) + δ • u := by linear_combination (norm := module) hX
    have l1 := (hleft _ (mem i)).1
    have l2 := (hleft _ (mem i)).2
    have e1 : det3 (x b - x a) (x i - x a) u = (1 - s) * det3 (x a - x v) (x b - x v) u := by
      rw [hxi]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    have e2 : det3 (x v - x b) (x i - x b) u = s * det3 (x a - x v) (x b - x v) u := by
      rw [hxi]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [e1] at l1; rw [e2] at l2
    have hs0 : 0 ≤ s := nonneg_of_mul_nonneg_left l2 hD
    have hs1 : 0 ≤ 1 - s := nonneg_of_mul_nonneg_left l1 hD
    refine ⟨s, δ, lt_of_le_of_ne hs0 fun h => ?_, lt_of_le_of_ne (by linarith) fun h => ?_, hxi⟩
    · apply hpar _ (mem v) _ (mem i) (T.inj.ne (Ne.symm hiv))
      have : x i - x v = δ • u := by rw [hxi, ← h]; module
      rw [this, EdgeConf.cross_smul_left'', cross_self, smul_zero]
    · apply hpar _ (mem a) _ (mem i) (T.inj.ne (Ne.symm hia))
      have : x i - x a = δ • u := by rw [hxi, h]; module
      rw [this, EdgeConf.cross_smul_left'', cross_self, smul_zero]
  obtain ⟨s₁, δ₁, hs₁0, hs₁1, hm₁⟩ := coords h1Q (Ne.symm hv1') (Ne.symm ha1')
  obtain ⟨s₂, δ₂, hs₂0, hs₂1, hm₂⟩ := coords h2Q (Ne.symm hv2') (Ne.symm ha2')
  refine ⟨s₁, δ₁, s₂, δ₂, hs₁0, hs₁1, hs₂0, hs₂1, ?_, hm₁, hm₂⟩
  exact quad_offsets29 T FQ F₁ F₂ ⟨hvQ, haQ, h1Q, h2Q, hbQ, hv1, h11, ha1, h21, hv2, h22, ha2, h12⟩
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]; exact ⟨⟨hva, hv1', hv2'⟩, ⟨ha1', ha2'⟩, h12', not_false⟩)
    hpar hm₁ hm₂

/-- **`V`'s triangle closing at the limit** (Lemma 18.2 with Proposition 22.2 for a sector rim).
The shapes `K_n → x` carry the triangle certificate `v a b` at views `u_n → u`; the faces at
`v` are the quadrilateral `S_Q = {v, a, m₁, m₂}` (apex `v`, far end `a`) and the triangle
`S_T = {v, b, n}`.  At the limit, with no two points over one point, (G1) and distinct depths, one
of the two sector rims `v m a b` is unimodal: if `b` is below the higher of `v`, `a`, the middle
above the chord, else the one below.  So `x` is Rupert, whatever its horizontal double normals. -/
theorem isRupert_vTriLim29 {x : Fin 7 → ℝ³} (T : Facets29 x) {v a b n m₁ m₂ : Fin 7}
    {SQ ST S₁ S₂ : Finset (Fin 7)} (FQ : Face16 x SQ) (FT : Face16 x ST) (F₁ : Face16 x S₁)
    (F₂ : Face16 x S₂)
    (hmem : v ∈ SQ ∧ a ∈ SQ ∧ m₁ ∈ SQ ∧ m₂ ∈ SQ ∧ b ∉ SQ ∧
      (∀ i ∈ SQ, i = v ∨ i = a ∨ i = m₁ ∨ i = m₂) ∧
      v ∈ ST ∧ b ∈ ST ∧ n ∈ ST ∧ a ∉ ST ∧ m₁ ∉ ST ∧ m₂ ∉ ST ∧
      (∀ i ∈ ST, i = v ∨ i = b ∨ i = n) ∧
      v ∈ S₁ ∧ m₁ ∈ S₁ ∧ a ∉ S₁ ∧ m₂ ∉ S₁ ∧ v ∈ S₂ ∧ m₂ ∈ S₂ ∧ a ∉ S₂ ∧ m₁ ∉ S₂)
    (hnd : [v, a, b, n, m₁, m₂].Nodup)
    {u : ℝ³} (hu : u ≠ 0) (hQu : ⟪FQ.N, u⟫ = 0) (us : ℕ → ℝ³) (hus : Tendsto us atTop (𝓝 u))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i)))
    (hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n)) (us n) (tri (K n v) (K n a) (K n b)))
    (hpar : NoParAt (univ.image x) u)
    (hg1 : G1At (univ.image x) u (SQ.image x) (ST.image x))
    (hdist : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨hvQ, haQ, h1Q, h2Q, hbQ, hQall, hvT, hbT, hnT, haT, h1T, h2T, hTall, hv1, h11, ha1, h21,
    hv2, h22, ha2, h12⟩ := hmem
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hva, hvb, hvn, hv1', hv2'⟩, ⟨hab, han, ha1', ha2'⟩, ⟨hbn, hb1, hb2⟩, ⟨hn1, hn2⟩,
    h12', -⟩ := hnd'
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have memK : ∀ j i, K j i ∈ univ.image (K j) := fun j i => mem_image_of_mem _ (mem_univ i)
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  -- every point weakly left of the triangle rim at the limit
  have lim0 : ∀ {f : ℕ → ℝ} {L : ℝ}, Tendsto f atTop (𝓝 L) → (∃ᶠ k in atTop, 0 ≤ f k) →
      0 ≤ L := fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  have hleft₀ : ∀ z ∈ univ.image x, 0 ≤ det3 (x a - x v) (z - x v) u ∧
      0 ≤ det3 (x b - x a) (z - x a) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    refine ⟨lim0 (Tendsto.det3' ((hK a).sub (hK v)) ((hK i).sub (hK v)) hus)
      (hfreq.mono fun k hk => by simpa [b0, tri_0, tri_1] using hk.left _ (memK k i) 0),
      lim0 (Tendsto.det3' ((hK b).sub (hK a)) ((hK i).sub (hK a)) hus)
      (hfreq.mono fun k hk => by simpa [b1, tri_1, tri_2] using hk.left _ (memK k i) 1),
      lim0 (Tendsto.det3' ((hK v).sub (hK b)) ((hK i).sub (hK b)) hus)
      (hfreq.mono fun k hk => by simpa [b2, tri_2, tri_0] using hk.left _ (memK k i) 2)⟩
  -- the triangle is strictly counterclockwise: `b` is not over the line `v a` ((G1))
  have hD : 0 < det3 (x a - x v) (x b - x v) u := by
    refine lt_of_le_of_ne (hleft₀ _ (mem b)).1 fun h0 => ?_
    rcases hg1 _ (mem v) _ (mem a) _ (mem b) (hpar _ (mem v) _ (mem a) (T.inj.ne hva))
        (fun z hz => (hleft₀ z hz).1) h0.symm (T.inj.ne (Ne.symm hvb)) (T.inj.ne (Ne.symm hab))
      with ⟨-, -, h⟩ | ⟨-, h, -⟩
    · obtain ⟨i, hi, he⟩ := mem_image.mp h
      exact hbQ (T.inj he ▸ hi)
    · obtain ⟨i, hi, he⟩ := mem_image.mp h
      exact haT (T.inj he ▸ hi)
  obtain ⟨s₁, δ₁, s₂, δ₂, hs₁0, hs₁1, hs₂0, hs₂1, hδδ, hm₁, hm₂⟩ :=
    quad_middles29 T FQ F₁ F₂ ⟨hvQ, haQ, h1Q, h2Q, hbQ, hv1, h11, ha1, h21, hv2, h22, ha2, h12⟩
      (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true]; exact ⟨⟨hva, hvb, hv1', hv2'⟩, ⟨hab, ha1', ha2'⟩,
          ⟨hb1, hb2⟩, h12', not_false⟩) hQu hpar hD
      (fun z hz => ⟨(hleft₀ z hz).2.1, (hleft₀ z hz).2.2⟩)
  -- the sector rim with the middle `m` (`δ > 0` if `b` is below the higher of `v`, `a`)
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have key : ∀ {m m' : Fin 7} {s δ s' δ' : ℝ}, m ∈ SQ → m' ∈ SQ → m ∉ ST →
      (∀ i ∈ SQ, i = v ∨ i = a ∨ i = m ∨ i = m') → [v, a, b, n, m, m'].Nodup →
      0 < s → s < 1 → 0 < s' → s' < 1 → δ * δ' < 0 →
      x m = x v + s • (x a - x v) + δ • u → x m' = x v + s' • (x a - x v) + δ' • u →
      (⟪x b, u⟫ < max ⟪x v, u⟫ ⟪x a, u⟫ → 0 < δ) →
      (max ⟪x v, u⟫ ⟪x a, u⟫ ≤ ⟪x b, u⟫ → δ < 0) → IsRupert (univ.image x) := by
    intro m m' s δ s' δ' hmQ hm'Q hmT hall hnd6 hs0 hs1 hs0' hs1' hdd hm hm' hup hdown
    have hnd6' := hnd6
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd6'
    obtain ⟨⟨-, -, -, hvm, -⟩, ⟨-, -, ham, -⟩, ⟨-, hbm, -⟩, -, -, -⟩ := hnd6'
    refine isRupert_vSector29 T FQ FT
      ⟨hvQ, haQ, hmQ, hm'Q, hbQ, hall, hvT, hbT, hnT, haT, hmT, hTall⟩
      hnd6 hu hQu hs0 hs1 hs0' hs1' hdd hm hm' hleft₀ hpar hg1 ?_
    have e : (fun i => ⟪x (quad v m a b i), u⟫) = quad ⟪x v, u⟫ ⟪x m, u⟫ ⟪x a, u⟫ ⟪x b, u⟫ := by
      funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    have zm : ⟪x m, u⟫ = (1 - s) * ⟪x v, u⟫ + s * ⟪x a, u⟫ + δ * ⟪u, u⟫ := by
      rw [hm]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]; ring
    have hcv := seg_bounds (x := ⟪x v, u⟫) (y := ⟪x a, u⟫) hs0.le hs1.le
    have dvm := hdist _ (mem v) _ (mem m) (T.inj.ne hvm)
    have dva := hdist _ (mem v) _ (mem a) (T.inj.ne hva)
    have dvb := hdist _ (mem v) _ (mem b) (T.inj.ne hvb)
    have dma := hdist _ (mem m) _ (mem a) (T.inj.ne (Ne.symm ham))
    have dmb := hdist _ (mem m) _ (mem b) (T.inj.ne (Ne.symm hbm))
    have dab := hdist _ (mem a) _ (mem b) (T.inj.ne hab)
    refine isRobustUnimodal_quad_of (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true]
      exact ⟨⟨dvm, dva, dvb⟩, ⟨dma, dmb⟩, dab, not_false⟩) ?_ ?_
    · intro h
      rcases lt_or_ge ⟪x b, u⟫ (max ⟪x v, u⟫ ⟪x a, u⟫) with hb | hb
      · have := hup hb
        have := mul_pos this huu
        have h1 := lt_of_le_of_lt (le_max_left _ _) h
        have h2 := min_le_left ⟪x v, u⟫ ⟪x a, u⟫
        have h3 := min_le_right ⟪x v, u⟫ ⟪x a, u⟫
        rw [zm] at h1
        rcases le_total ⟪x v, u⟫ ⟪x a, u⟫ with h4 | h4 <;> nlinarith [hcv.1]
      · have h1 := lt_of_le_of_lt (le_max_right _ _) h
        have h2 := min_le_max (a := ⟪x v, u⟫) (b := ⟪x a, u⟫)
        linarith
    · intro h
      rcases lt_or_ge ⟪x b, u⟫ (max ⟪x v, u⟫ ⟪x a, u⟫) with hb | hb
      · have h1 := lt_of_lt_of_le h (min_le_right _ _)
        linarith
      · have := hdown hb
        have := mul_neg_of_neg_of_pos this huu
        have h1 := lt_of_lt_of_le h (min_le_left _ _)
        rw [zm] at h1
        nlinarith [hcv.2]
  have hall₁ : ∀ i ∈ SQ, i = v ∨ i = a ∨ i = m₁ ∨ i = m₂ := hQall
  have hall₂ : ∀ i ∈ SQ, i = v ∨ i = a ∨ i = m₂ ∨ i = m₁ := fun i hi => by
    rcases hQall i hi with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
  have nd₁ : [v, a, b, n, m₁, m₂].Nodup := hnd
  have nd₂ : [v, a, b, n, m₂, m₁].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hva, hvb, hvn, hv2', hv1'⟩, ⟨hab, han, ha2', ha1'⟩, ⟨hbn, hb2, hb1⟩, ⟨hn2, hn1⟩,
      Ne.symm h12', not_false⟩
  have hδδ' : δ₂ * δ₁ < 0 := by linarith [mul_comm δ₁ δ₂]
  have hδ₁ : δ₁ ≠ 0 := by rintro rfl; simp at hδδ
  rcases lt_or_ge ⟪x b, u⟫ (max ⟪x v, u⟫ ⟪x a, u⟫) with hb | hb
  · -- the middle above the chord
    rcases lt_or_gt_of_ne hδ₁ with h1 | h1
    · have h2 : 0 < δ₂ := pos_of_mul_neg_right hδδ h1.le
      exact key h2Q h1Q h2T hall₂ nd₂ hs₂0 hs₂1 hs₁0 hs₁1 hδδ' hm₂ hm₁ (fun _ => h2)
        (fun h => absurd (lt_of_lt_of_le hb h) (lt_irrefl _))
    · exact key h1Q h2Q h1T hall₁ nd₁ hs₁0 hs₁1 hs₂0 hs₂1 hδδ hm₁ hm₂ (fun _ => h1)
        (fun h => absurd (lt_of_lt_of_le hb h) (lt_irrefl _))
  · -- the middle below the chord
    rcases lt_or_gt_of_ne hδ₁ with h1 | h1
    · exact key h1Q h2Q h1T hall₁ nd₁ hs₁0 hs₁1 hs₂0 hs₂1 hδδ hm₁ hm₂
        (fun h => absurd (lt_of_lt_of_le h hb) (lt_irrefl _)) (fun _ => h1)
    · have h2 : δ₂ < 0 := neg_of_mul_neg_right hδδ h1.le
      exact key h2Q h1Q h2T hall₂ nd₂ hs₂0 hs₂1 hs₁0 hs₁1 hδδ' hm₂ hm₁
        (fun h => absurd (lt_of_lt_of_le h hb) (lt_irrefl _)) (fun _ => h2)


/-! ### T2: the four-corner rims `(4, b, 0, 5)` -/

/-- **T2's quadrilateral rims at the limit** (Lemma 18.2 with Theorem 22.8): the rim
`(4, b, 0, 5)` at the vertex line `234/1456` (`b ∈ {3, 2}`, `m` the third vertex of `234`) read
backwards is `(v, a, c, b) = (4, 5, 0, b)`, the quad `1456` with chord `[4, 5]` and the triangle
`234`.  Under `VtxGen` at the view, if `0` and `b` are at different heights over the quad
(`hcb`: the class-d condition of Lemma 28.8 fails) then no (H4)/escape is needed, and the limit
is Rupert. -/
theorem isRupert_T2quad29 (N : NF29 x) {b m : Fin 7}
    (hnd1 : [4, 5, 0, b, 1, 6, m].Nodup) (hnd2 : [4, 5, 0, b, 6, 1, m].Nodup)
    (hSb : ({2, 3, 4} : Finset (Fin 7)) = {4, b, m})
    (hcb : ⟪N.f1456.N, x 0⟫ ≠ ⟪N.f1456.N, x b⟫)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i))) (ε : Bool)
    (hgen : VtxGen (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x) N.f1456.N)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 1)) (quad 4 b 0 5) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  have hs := sgnB_ne_zero ε
  have hw0 : view29 x (.inr 1) ≠ 0 := N.view29_ne_zero _ (by simp)
  have hc0 : -sgnB ε ≠ 0 := neg_ne_zero.mpr hs
  have hcε : -sgnB ε = 1 ∨ -sgnB ε = -1 := by
    rcases sgnB_cases ε with h | h <;> simp [h]
  have hg := hgen.sign hcε
  have hu : (-sgnB ε) • view29 x (.inr 1) ≠ 0 := smul_ne_zero hc0 hw0
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hwQ : ⟪N.f1456.N, view29 x (.inr 1)⟫ = 0 :=
    inner_planeLine_right (N.f1456.inner_sub (by decide) (by decide))
      (N.f1456.inner_sub (by decide) (by decide))
  have hwT : ⟪N.f234.N, view29 x (.inr 1)⟫ = 0 :=
    inner_planeLine_left (N.f234.inner_sub (by decide) (by decide))
      (N.f234.inner_sub (by decide) (by decide))
  have hNa : ⟪N.f1456.N, (-sgnB ε) • view29 x (.inr 1)⟫ = 0 := by
    rw [real_inner_smul_right, hwQ, mul_zero]
  have hNb : ⟪N.f234.N, (-sgnB ε) • view29 x (.inr 1)⟫ = 0 := by
    rw [real_inner_smul_right, hwT, mul_zero]
  have hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n)) ((-sgnB ε) • view29 (K n) (.inr 1))
      (quad (K n 4) (K n 5) (K n 0) (K n b)) := hc.mono fun n hn => by
    have h1 := hn.1.rev4.toPts
    rw [quad_map, ← neg_smul] at h1
    exact h1
  have hNQ : N.f1456.N ≠ 0 := N.f1456.N_ne (i := 4) (j := 0) (by decide) (by decide)
  have hcu : cross (x 5 - x 4) ((-sgnB ε) • view29 x (.inr 1)) ≠ 0 :=
    hg.par _ (mem 4) _ (mem 5) (N.inj.ne (by decide))
  obtain ⟨s1, δ1, h1⟩ := EdgeConf.exists_coords_of_perp (N.f1456.inner_sub (by decide : 5 ∈
    ({1, 4, 5, 6} : Finset (Fin 7))) (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hNa
    (N.f1456.inner_sub (by decide : 1 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))
      (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hcu hNQ
  obtain ⟨s6, δ6, h6⟩ := EdgeConf.exists_coords_of_perp (N.f1456.inner_sub (by decide : 5 ∈
    ({1, 4, 5, 6} : Finset (Fin 7))) (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hNa
    (N.f1456.inner_sub (by decide : 6 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))
      (by decide : 4 ∈ ({1, 4, 5, 6} : Finset (Fin 7)))) hcu hNQ
  have hx1 : x 1 = x 4 + s1 • (x 5 - x 4) + δ1 • ((-sgnB ε) • view29 x (.inr 1)) := by
    linear_combination (norm := module) h1
  have hx6 : x 6 = x 4 + s6 • (x 5 - x 4) + δ6 • ((-sgnB ε) • view29 x (.inr 1)) := by
    linear_combination (norm := module) h6
  have hδ : δ1 * δ6 < 0 := quad_offsets29 N.facets N.f1456 N.f124 N.f346
    (v := 4) (a := 5) (b := 0) (m₁ := 1) (m₂ := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide) hg.par hx1 hx6
  have hfa := N.f1456.hf (i₀ := 4) (by decide)
  have hfb := N.f234.hf (i₀ := 4) (by decide)
  have hδ1 : δ1 ≠ 0 := by rintro rfl; simp at hδ
  rcases lt_or_gt_of_ne hδ1 with hneg | hpos
  · have hδ6 : 0 < δ6 := pos_of_mul_neg_right hδ hneg.le
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 4) (a := 5) (c := 0) (b := b) (p := 6)
      (q := 1) (m := m) hnd2 (Sa := {1, 4, 5, 6}) (Sb := {2, 3, 4}) (by decide) hSb hfa hfb hu
      hNa hNb ⟨s6, δ6, hδ6, hx6⟩ ⟨s1, δ1, hneg, hx1⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 1)) ((tendsto_view29 hK _).const_smul _) hfreq hg
      (fun _ hcb' => absurd hcb' hcb)
  · have hδ6 : δ6 < 0 := neg_of_mul_neg_right hδ hpos.le
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 4) (a := 5) (c := 0) (b := b) (p := 1)
      (q := 6) (m := m) hnd1 (Sa := {1, 4, 5, 6}) (Sb := {2, 3, 4}) (by decide) hSb hfa hfb hu
      hNa hNb ⟨s1, δ1, hpos, hx1⟩ ⟨s6, δ6, hδ6, hx6⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 1)) ((tendsto_view29 hK _).const_smul _) hfreq hg
      (fun _ hcb' => absurd hcb' hcb)

/-! ### T2: the triangle rim `(4, 3, 5)` -/

/-- **T2's triangle rim at the limit** (Lemma 18.2, Proposition 22.2 for a sector rim, Lemma
22.6 (b)): the rim `(4, 3, 5)` at the vertex line `234/1456`, read backwards `(v, a, b) = (4, 5, 3)`
with the quad `1456` and the triangle `234` (`n = 2`); at the limit, with no two points over one
point, (G1) and distinct depths, the limit is Rupert whatever its horizontal double normals. -/
theorem isRupert_T2tri29 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i))) (ε : Bool)
    (hgen : TwoGen29 (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 1)) (tri 4 3 5) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  have hs := sgnB_ne_zero ε
  have hw0 : view29 x (.inr 1) ≠ 0 := N.view29_ne_zero _ (by simp)
  have hc0 : -sgnB ε ≠ 0 := neg_ne_zero.mpr hs
  have hcε : -sgnB ε = 1 ∨ -sgnB ε = -1 := by
    rcases sgnB_cases ε with h | h <;> simp [h]
  have hg := hgen.sign hcε
  have hwQ : ⟪N.f1456.N, view29 x (.inr 1)⟫ = 0 :=
    inner_planeLine_right (N.f1456.inner_sub (by decide) (by decide))
      (N.f1456.inner_sub (by decide) (by decide))
  have hQu : ⟪N.f1456.N, (-sgnB ε) • view29 x (.inr 1)⟫ = 0 := by
    rw [real_inner_smul_right, hwQ, mul_zero]
  have hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n)) ((-sgnB ε) • view29 (K n) (.inr 1))
      (tri (K n 4) (K n 5) (K n 3)) := hc.mono fun n hn => by
    have h1 := hn.1.rev3.toPts
    rw [tri_map, ← neg_smul] at h1
    exact h1
  exact isRupert_vTriLim29 N.facets N.f1456 N.f234 N.f124 N.f346
    (v := 4) (a := 5) (b := 3) (n := 2) (m₁ := 1) (m₂ := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)
    (smul_ne_zero hc0 hw0) hQu (fun n => (-sgnB ε) • view29 (K n) (.inr 1))
    ((tendsto_view29 hK _).const_smul _) K hK hfreq hg.par hg.g1 hg.dist

/-! ### T1: the four-corner rim `(1, 2, 3, 6)` at `012/1456` -/

theorem lt_of_neg_mul_lt {k a b : ℝ} (hk : 0 < k) (h : -k * a < -k * b) : b < a := by
  nlinarith

/-- **(H4) and the escape for T1 on `{h2 = 1}`** (Lemma 28.7).  For the view `u = r • vT1`
(`vT1 = u1`), with `h2 = 1`, `l = a2 t − b2 s < 0` and the escape `hesc` at `u1` (the pattern
`z5 < z1`, `z2 < z1`, `z1 < z6`, `z1 < z3` of Lemma 22.9 for the lower middle `5` is impossible):
the upper middle `4` shown in the sense `s` (`s r > 0`) has (H4) (the product of the plane
`6 3 2` at `1` and at `u` is `−l · (a0 b2 − a2 b0) · D² > 0`), and the other middle `5`, shown in
the opposite sense, has the escape. -/
theorem T1_h4esc (N : NF29 x) (hh : N.h2 = 1) (hl : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hesc : ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫))
    {r s : ℝ} (hsr : 0 < s * r) :
    VtxConf.H4orEsc (r • N.vT1) (x 1) (x 6) (x 3) (x 2) (x 4) s ∧
      VtxConf.H4orEsc (r • N.vT1) (x 1) (x 6) (x 3) (x 2) (x 5) (-s) := by
  have key1 : det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) * det3 (x 3 - x 6) (x 2 - x 6) N.vT1 =
      ((-N.a2 * N.t + N.b2 * N.s) * (N.a0 * N.b2 - N.a2 * N.b0)) * N.D ^ 2 := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c, NF29.D]; rw [hh]; ring
  have hpos : 0 < det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) *
      det3 (x 3 - x 6) (x 2 - x 6) N.vT1 := by
    rw [key1]
    have := N.hD
    exact mul_pos (mul_pos hl N.hDD) (by positivity)
  refine ⟨Or.inl (Or.inl ?_), Or.inr fun hpat => hesc ?_⟩
  · rw [det3_smul_right]
    have e : det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) *
        (s * (r * det3 (x 3 - x 6) (x 2 - x 6) N.vT1)) =
        (s * r) * (det3 (x 3 - x 6) (x 2 - x 6) (x 1 - x 6) *
          det3 (x 3 - x 6) (x 2 - x 6) N.vT1) := by ring
    rw [e]; exact mul_pos hsr hpos
  · obtain ⟨p1, p2, p3, p4⟩ := hpat
    simp only [real_inner_smul_right] at p1 p2 p3 p4
    have hk : 0 < s * r := hsr
    have q : ∀ {a b : ℝ}, -s * (r * a) < -s * (r * b) → b < a := fun {a b} h =>
      lt_of_neg_mul_lt hk (by
        have e1 : -(s * r) * a = -s * (r * a) := by ring
        have e2 : -(s * r) * b = -s * (r * b) := by ring
        rw [e1, e2]; exact h)
    exact ⟨q p1, q p2, q p3, q p4⟩

/-- **The escape for T1 in P14** (Lemma 28.7 (b)): at `h2 = 1` the view `u2 = vT2` of the partner
is `3 − 2`, so the carried fact `⟪vT1, vT2⟫ ≤ 0` (`0 ≤ ⟪w₀, w₁⟫` for the named views) gives
`z3 ≤ z2` along `vT1`, against the pattern `z2 < z1 < z3` of Lemma 22.9. -/
theorem T1_esc_P14 (N : NF29 x) (hh : N.h2 = 1)
    (hex : 0 ≤ ⟪view29 x (.inr 0), view29 x (.inr 1)⟫) :
    ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫) := by
  rintro ⟨-, h2z, -, h3z⟩
  have w0 : view29 x (.inr 0) = N.D • N.vT1 := by
    rw [show view29 x (.inr 0) = vtxView29 x 0 from rfl, N.vtxView29_0, one_mul]
  have w1 : view29 x (.inr 1) = (-N.D) • N.vT2 := by
    rw [show view29 x (.inr 1) = vtxView29 x 1 from rfl, N.vtxView29_1, neg_one_mul]
  have hv : N.vT2 = x 3 - x 2 := by
    simp only [NF29.vT2]; nf29_simp N; rw [hh]
    ext; simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
      PiLp.zero_apply, WithLp.ofLp_zero, Pi.zero_apply, smul_eq_mul]; ring
  rw [w0, w1, real_inner_smul_left, real_inner_smul_right, hv, inner_sub_right,
    real_inner_comm (x 3), real_inner_comm (x 2)] at hex
  have hD2 : 0 < N.D * N.D := mul_self_pos.mpr N.hD
  nlinarith [mul_pos hD2 (sub_pos.mpr (h2z.trans h3z))]

/-- **The escape for T1 in P11**: the view `vT3` of the partner is
`h0 (1 − 2) + α vT1 + β (6 − 1)` with `α, β > 0` (a polynomial identity), so the carried fact
`⟪vT1, vT3⟫ ≤ 0` is incompatible with the pattern `z2 < z1 < z6` of Lemma 22.9. -/
theorem T1_esc_P11 (N : NF29 x) (hex : ⟪view29 x (.inr 0), view29 x (.inr 3)⟫ ≤ 0) :
    ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫) := by
  rintro ⟨-, h2z, h6z, -⟩
  have w0 : view29 x (.inr 0) = N.D • N.vT1 := by
    rw [show view29 x (.inr 0) = vtxView29 x 0 from rfl, N.vtxView29_0, one_mul]
  have w3 : view29 x (.inr 3) = N.D • N.vT3 := by
    rw [show view29 x (.inr 3) = vtxView29 x 3 from rfl, N.vtxView29_3, one_mul]
  have hvec : ((N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s) •
      N.vT3 = (((N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s) * N.h0) •
        (x 1 - x 2) + ((N.h0 * N.a2 - N.h2 * N.a0) * N.t) • N.vT1 +
        ((N.h2 * N.b0 - N.h0 * N.b2) * (N.h0 * N.a2 - N.h2 * N.a0)) • (x 6 - x 1) := by
    simp only [NF29.vT3, NF29.vT1]; nf29_vec N
  have hF5 := N.hF5
  have hF4 := N.hF4
  have hf : 0 < (N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s :=
    add_pos (mul_pos hF5 N.ht) (mul_pos hF4 N.hs)
  have hn : 0 < ⟪N.vT1, N.vT1⟫ :=
    real_inner_self_pos.mpr (nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5)))
  rw [w0, w3, real_inner_smul_left, real_inner_smul_right] at hex
  have hD2 : 0 < N.D * N.D := mul_self_pos.mpr N.hD
  have h13 : ⟪N.vT1, N.vT3⟫ ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hD2 h]
  have key := congrArg (fun w => ⟪N.vT1, w⟫) hvec
  simp only [inner_add_right, real_inner_smul_right, inner_sub_right] at key
  have h2z' : ⟪N.vT1, x 2⟫ < ⟪N.vT1, x 1⟫ := by
    rw [real_inner_comm (x 2) N.vT1, real_inner_comm (x 1) N.vT1]; exact h2z
  have h6z' : ⟪N.vT1, x 1⟫ < ⟪N.vT1, x 6⟫ := by
    rw [real_inner_comm (x 1) N.vT1, real_inner_comm (x 6) N.vT1]; exact h6z
  have p1 : 0 < ((N.h0 * N.a2 - N.h2 * N.a0) * N.t + (N.h2 * N.b0 - N.h0 * N.b2) * N.s) *
      N.h0 * (⟪N.vT1, x 1⟫ - ⟪N.vT1, x 2⟫) := mul_pos (mul_pos hf N.hh0) (by linarith [h2z'])
  have p2 : 0 < (N.h0 * N.a2 - N.h2 * N.a0) * N.t * ⟪N.vT1, N.vT1⟫ :=
    mul_pos (mul_pos hF5 N.ht) hn
  have p3 : 0 < (N.h2 * N.b0 - N.h0 * N.b2) * (N.h0 * N.a2 - N.h2 * N.a0) *
      (⟪N.vT1, x 6⟫ - ⟪N.vT1, x 1⟫) := mul_pos (mul_pos hF4 hF5) (by linarith [h6z'])
  nlinarith [mul_nonneg hf.le (neg_nonneg.mpr h13)]

/-- **T1's quadrilateral rim at the limit** (Lemma 18.2 with Theorem 22.8, Lemma 28.7).  The rim
`(1, 2, 3, 6)` at the vertex line `012/1456`, read backwards `(v, a, c, b) = (1, 6, 3, 2)`: the
quad `1456` (chord `[1, 6]`, middles `4`, `5` on opposite sides) and the triangle `012`
(`m = 0`).  Where the far edge `[3, 2]` is parallel to the quad (`h2 = 1`), (H4) holds for the
upper middle (`l = a2 t − b2 s < 0`: `hl`) and the lower middle has the escape `hesc`. -/
theorem isRupert_T1_29 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i))) (ε : Bool)
    (hgen : VtxGen (univ.image x) (view29 x (.inr 0)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({0, 1, 2} : Finset (Fin 7)).image x) N.f1456.N)
    (hl : N.h2 = 1 → 0 < -N.a2 * N.t + N.b2 * N.s)
    (hesc : N.h2 = 1 → ¬ (⟪x 5, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧ ⟪x 2, N.vT1⟫ < ⟪x 1, N.vT1⟫ ∧
      ⟪x 1, N.vT1⟫ < ⟪x 6, N.vT1⟫ ∧ ⟪x 1, N.vT1⟫ < ⟪x 3, N.vT1⟫))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 0)) (quad 1 2 3 6) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  have hs := sgnB_ne_zero ε
  have hc0 : -sgnB ε ≠ 0 := neg_ne_zero.mpr hs
  have hcε : -sgnB ε = 1 ∨ -sgnB ε = -1 := by
    rcases sgnB_cases ε with h | h <;> simp [h]
  have hD := N.hD
  have hw : view29 x (.inr 0) = N.D • N.vT1 := by
    rw [show view29 x (.inr 0) = vtxView29 x 0 from rfl, N.vtxView29_0, one_mul]
  have hu_eq : (-sgnB ε) • view29 x (.inr 0) = ((-sgnB ε) * N.D) • N.vT1 := by
    rw [hw, smul_smul]
  have hr0 : (-sgnB ε) * N.D ≠ 0 := mul_ne_zero hc0 hD
  have hg0 := hgen.sign hcε
  rw [hu_eq] at hg0
  have hvT : N.vT1 ≠ 0 := nfV_ne_zero N.hD (Or.inl (ne_of_gt N.hF5))
  have hwQ : ⟪N.f1456.N, view29 x (.inr 0)⟫ = 0 :=
    inner_planeLine_right (N.f1456.inner_sub (by decide) (by decide))
      (N.f1456.inner_sub (by decide) (by decide))
  have hwT : ⟪N.f012.N, view29 x (.inr 0)⟫ = 0 :=
    inner_planeLine_left (N.f012.inner_sub (by decide) (by decide))
      (N.f012.inner_sub (by decide) (by decide))
  have hNa : ⟪N.f1456.N, ((-sgnB ε) * N.D) • N.vT1⟫ = 0 := by
    rw [← hu_eq, real_inner_smul_right, hwQ, mul_zero]
  have hNb : ⟪N.f012.N, ((-sgnB ε) * N.D) • N.vT1⟫ = 0 := by
    rw [← hu_eq, real_inner_smul_right, hwT, mul_zero]
  have hu : ((-sgnB ε) * N.D) • N.vT1 ≠ 0 := smul_ne_zero hr0 hvT
  have hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n))
      ((-sgnB ε) • view29 (K n) (.inr 0)) (quad (K n 1) (K n 6) (K n 3) (K n 2)) :=
    hc.mono fun n hn => by
      have h1 := hn.1.rev4.toPts
      rw [quad_map, ← neg_smul] at h1
      exact h1
  have hus : Tendsto (fun n => (-sgnB ε) • view29 (K n) (.inr 0)) atTop
      (𝓝 (((-sgnB ε) * N.D) • N.vT1)) := by
    rw [← hu_eq]; exact (tendsto_view29 hK _).const_smul _
  -- the middles `4`, `5` over the chord `[1, 6]` in the direction `vT1`
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ, f = (N.h0 * N.a2 - N.h2 * N.a0) * N.t +
      (N.h2 * N.b0 - N.h0 * N.b2) * N.s := ⟨_, rfl⟩
  have hf : 0 < f := by
    rw [hfdef]; exact add_pos (mul_pos N.hF5 N.ht) (mul_pos N.hF4 N.hs)
  have e4 : f • (x 4 - x 1) = (N.h2 * N.b0 - N.h0 * N.b2) • (x 6 - x 1) + N.t • N.vT1 := by
    rw [hfdef]; simp only [NF29.vT1]; nf29_vec N
  have e5 : f • (x 5 - x 1) = (N.h0 * N.a2 - N.h2 * N.a0) • (x 6 - x 1) + (-N.s) • N.vT1 := by
    rw [hfdef]; simp only [NF29.vT1]; nf29_vec N
  have hfa := N.f1456.hf (i₀ := 1) (by decide)
  have hfb := N.f012.hf (i₀ := 1) (by decide)
  have hh_of : ⟪N.f1456.N, x 3⟫ = ⟪N.f1456.N, x 2⟫ → N.h2 = 1 := fun hcb => by
    have h01 := N.f1456_eq hcb
    simp only [Matrix.cons_val_zero, Matrix.cons_val] at h01
    linarith
  set r : ℝ := (-sgnB ε) * N.D with hrdef
  have hx4 : x 4 = x 1 + ((N.h2 * N.b0 - N.h0 * N.b2) / f) • (x 6 - x 1) +
      ((N.t / r) / f) • (r • N.vT1) := by
    refine eq_comb_div (D₀ := f) hf.ne' ?_
    rw [e4, smul_smul, div_mul_cancel₀ _ hr0]
  have hx5 : x 5 = x 1 + ((N.h0 * N.a2 - N.h2 * N.a0) / f) • (x 6 - x 1) +
      (((-N.s) / r) / f) • (r • N.vT1) := by
    refine eq_comb_div (D₀ := f) hf.ne' ?_
    rw [e5, smul_smul, div_mul_cancel₀ _ hr0]
  have hF4f : 0 < N.t / f := div_pos N.ht hf
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · -- `r < 0`: `5` is above, `4` below
    have hδ5 : 0 < ((-N.s) / r) / f := div_pos (div_pos_of_neg_of_neg (by linarith [N.hs]) hneg) hf
    have hδ4 : (N.t / r) / f < 0 := div_neg_of_neg_of_pos (div_neg_of_pos_of_neg N.ht hneg) hf
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 1) (a := 6) (c := 3) (b := 2) (p := 5)
      (q := 4) (m := 0) (by decide) (Sa := {1, 4, 5, 6}) (Sb := {0, 1, 2}) (by decide)
      (by decide) hfa hfb hu hNa hNb ⟨_, _, hδ5, hx5⟩ ⟨_, _, hδ4, hx4⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 0)) hus hfreq hg0 (fun _ hcb => by
        have hh := hh_of hcb
        obtain ⟨A, B⟩ := T1_h4esc N hh (hl hh) (hesc hh) (r := r) (s := -1) (by linarith)
        exact ⟨by simpa using B, A⟩)
  · -- `r > 0`: `4` is above, `5` below
    have hδ4 : 0 < (N.t / r) / f := div_pos (div_pos N.ht hpos) hf
    have hδ5 : ((-N.s) / r) / f < 0 :=
      div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith [N.hs]) hpos) hf
    exact isRupert_vtx_limit x N.inj N.noSeg (v := 1) (a := 6) (c := 3) (b := 2) (p := 4)
      (q := 5) (m := 0) (by decide) (Sa := {1, 4, 5, 6}) (Sb := {0, 1, 2}) (by decide)
      (by decide) hfa hfb hu hNa hNb ⟨_, _, hδ4, hx4⟩ ⟨_, _, hδ5, hx5⟩ K hK
      (fun n => (-sgnB ε) • view29 (K n) (.inr 0)) hus hfreq hg0 (fun _ hcb => by
        have hh := hh_of hcb
        obtain ⟨A, B⟩ := T1_h4esc N hh (hl hh) (hesc hh) (r := r) (s := 1) (by linarith)
        exact ⟨by simpa using A, by simpa using B⟩)

end Minimality

end
