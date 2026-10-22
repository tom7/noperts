module

public import Minimality.Type21Ridge
public import Minimality.Type16Vtx

@[expose] public section

/-!
# Type 21: §22 at the four vertex lines with a quadrilateral (`FEWER-FACES-PROOFS.md` §22, §3)

The lines `014/0256` (at `0`), `014/2346` (at `4`), `135/0256` (at `5`), `135/2346` (at `3`)
carry two certificates of the tier cover, in different labellings: F1's `T1` and F2's `V`
(`VtxDat21`).

* **`T1`** (rim `0 5 3 4` or `0 5 4` in the cap labelling): the far end `5` of the quadrilateral
  `0256` is adjacent to the apex `0`, so the closing is realized on both face circles and
  Proposition 22.2 tilts it to a generic unimodal view (`isRupert_t1Lim`), whatever the
  horizontal double normals.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- A facet's normal is not orthogonal to the cross product of two of its edges at a vertex. -/
theorem Face16.det3_normal_ne {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S)
    {i j a b : Fin 7} (hi : i ∈ S) (hj : j ∈ S) (ha : a ∈ S) (hb : b ∉ S)
    (hc : cross (x j - x i) (x a - x i) ≠ 0) :
    det3 (x j - x i) (x a - x i) F.N ≠ 0 := by
  intro h0
  have hN := F.N_ne hi hb
  have hpar : cross (cross (x j - x i) (x a - x i)) F.N = 0 := by
    rw [cross_cross_eq, real_inner_comm, F.inner_sub hj hi, real_inner_comm, F.inner_sub ha hi,
      zero_smul, zero_smul, sub_zero]
  obtain e := eq_smul_of_cross_eq_zero hc hpar
  have h1 : det3 (x j - x i) (x a - x i) F.N =
      ⟪F.N, cross (x j - x i) (x a - x i)⟫ := by
    rw [det3, real_inner_comm]
  rw [h1] at h0
  rw [h0, zero_div, zero_smul] at e
  exact hN e

/-- **Proposition 22.2 for a labelled rim at a vertex view, at the limit** (Lemma 18.2): the
shapes `K_n → x` carry one labelled rim certificate at views `u_n → u`; at the limit, no two
points lie over one point, (G1) holds and the depths are distinct at `u`; the two faces at the
vertex are facets with non-parallel normals and the points of each face over a side of the rim
lie on one side of it.  Then `x` is Rupert, whatever its horizontal double normals. -/
theorem isRupert_vtxTwoFace_limit {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³)
    (hx : Function.Injective x) (lab : ZMod k → Fin n) (hlab : Function.Injective lab)
    {u : ℝ³} (hu : u ≠ 0) (us : ℕ → ℝ³) (hus : Tendsto us atTop (𝓝 u))
    (K : ℕ → Fin n → ℝ³) (hK : ∀ m, Tendsto (fun j => K j m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ j in atTop, RimCertPts (univ.image (K j)) (us j) (fun i => K j (lab i)))
    {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, i ∈ Sa → ⟪Na, x i⟫ = κa) (hfb : ∀ i, i ∈ Sb → ⟪Nb, x i⟫ = κb)
    (hab : cross Na Nb ≠ 0)
    (hpar : NoParAt (univ.image x) u)
    (hg1 : G1At (univ.image x) u (Sa.image x) (Sb.image x))
    (hdist : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫)
    {σa σb : ℝ} (hσa : σa ≠ 0) (hσb : σb ≠ 0)
    (hsa : ∀ i m, lab i ∈ Sa → lab (i + 1) ∈ Sa → m ∈ Sa → m ≠ lab i → m ≠ lab (i + 1) →
      0 < σa * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) Na)
    (hsb : ∀ i m, lab i ∈ Sb → lab (i + 1) ∈ Sb → m ∈ Sb → m ≠ lab i → m ≠ lab (i + 1) →
      0 < σb * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) Nb) :
    IsRupert (univ.image x) := by
  classical
  have memK : ∀ j i, K j i ∈ univ.image (K j) := fun j i => mem_image_of_mem _ (mem_univ i)
  have hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u := by
    intro m i
    exact le_of_tendsto_frequently tendsto_const_nhds
      (Tendsto.det3' ((hK _).sub (hK _)) ((hK _).sub (hK _)) hus)
      (hfreq.mono fun j hj => hj.left _ (memK j m) i)
  have hside : ∀ i, cross (x (lab (i + 1)) - x (lab i)) u ≠ 0 := by
    intro i
    refine hpar _ (mem_image_of_mem x (mem_univ _)) _ (mem_image_of_mem x (mem_univ _)) ?_
    exact (hx.comp hlab).ne (zmod_ne_add_one (by omega) i)
  have hrob : IsRobustUnimodal (fun i => ⟪x (lab i), u⟫) := by
    refine isRobustUnimodal_of_tendsto_ties (fun i => (hK (lab i)).inner hus)
      (hfreq.mono fun j hj => ⟨hj.robust, fun i i' e => ?_⟩)
    by_cases hii : i = i'
    · rw [hii]
    · exfalso
      exact hdist _ (mem_image_of_mem x (mem_univ _)) _ (mem_image_of_mem x (mem_univ _))
        (hx.ne (hlab.ne hii)) e
  exact isRupert_twoFace hk x hx lab hlab hu hfa hfb hab hleft hside hg1 hσa hσb hsa hsb hrob

/-- **Proposition 22.2 at a vertex line of type 21, generic in the labels.**  The faces at the
vertex `v` are the triangle `S_T ∋ v, e, m` and a face `S_Q ∋ v, f, q₁, q₂` whose side `v f` is an
edge (another facet `S_O` through `v`, `f` has `q₁`, `q₂` beneath).  If every side of the
labelled rim on `S_T` is `e → v` (with the third point `m`) and every side on `S_Q` is `v → f`
(with `q₁`, `q₂`), the closing is realized on both face circles; with frequent certificates of
this rim along `K_n → x` and (G1), no two points over one point and distinct depths at the limit
view, `x` is Rupert. -/
theorem isRupert_twoFaceLab21 {x : Fin 7 → ℝ³} (T : Facets21 x) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (lab : ZMod k → Fin 7) (hlab : Function.Injective lab)
    {ST SQ SO : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (FO : Face16 x SO)
    {v e m f q₁ q₂ : Fin 7}
    (hmem : v ∈ ST ∧ e ∈ ST ∧ m ∈ ST ∧ f ∉ ST ∧ v ∈ SQ ∧ f ∈ SQ ∧ q₁ ∈ SQ ∧ q₂ ∈ SQ ∧ e ∉ SQ ∧
      v ∈ SO ∧ f ∈ SO ∧ q₁ ∉ SO ∧ q₂ ∉ SO)
    (hnd : [v, e, m, f, q₁, q₂].Nodup)
    (hsideT : ∀ i m', lab i ∈ ST → lab (i + 1) ∈ ST → m' ∈ ST → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = e ∧ lab (i + 1) = v ∧ m' = m)
    (hsideQ : ∀ i m', lab i ∈ SQ → lab (i + 1) ∈ SQ → m' ∈ SQ → m' ≠ lab i → m' ≠ lab (i + 1) →
      lab i = v ∧ lab (i + 1) = f ∧ (m' = q₁ ∨ m' = q₂))
    {u : ℝ³} (hu : u ≠ 0) (us : ℕ → ℝ³) (hus : Tendsto us atTop (𝓝 u))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i)))
    (hfreq : ∃ᶠ n in atTop, RimCertPts (univ.image (K n)) (us n) (fun i => K n (lab i)))
    (hpar : NoParAt (univ.image x) u)
    (hg1 : G1At (univ.image x) u (ST.image x) (SQ.image x))
    (hdist : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' → ⟪y, u⟫ ≠ ⟪y', u⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨hvT, heT, hmT, hfT, hvQ, hfQ, hq₁Q, hq₂Q, heQ, hvO, hfO, hq₁O, hq₂O⟩ := hmem
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hve, hvm, hvf, hvq₁, -⟩, ⟨hem, -, -, -⟩, -, ⟨hfq₁, -⟩, -⟩ := hnd
  have hσT : det3 (x v - x e) (x m - x e) FT.N ≠ 0 :=
    FT.det3_normal_ne heT hvT hmT hfT
      (cross_ne_zero_of_noSeg T.inj T.noSeg (Ne.symm hve) hem hvm)
  have hσQ : det3 (x f - x v) (x q₁ - x v) FQ.N ≠ 0 :=
    FQ.det3_normal_ne hvQ hfQ hq₁Q heQ (cross_ne_zero_of_noSeg T.inj T.noSeg hvf hvq₁ hfq₁)
  have hq₂ : 0 < det3 (x f - x v) (x q₁ - x v) FQ.N * det3 (x f - x v) (x q₂ - x v) FQ.N :=
    side_pos21 T FQ FO hvQ hfQ hq₁Q hq₂Q hvO hfO hq₁O hq₂O hvf hvq₁ hfq₁ heQ
  have hab : cross FT.N FQ.N ≠ 0 := by
    refine cross_normals_ne (FT.N_ne hvT hfT) (FT.inner_sub heT hvT) ?_
    rw [← FQ.hN, FQ.zero v hvQ, sub_zero]; exact FQ.neg e heQ
  refine isRupert_vtxTwoFace_limit hk x T.inj lab hlab hu us hus K hK hfreq
    (fun i hi => ((FT.hf hvT) i).1 hi) (fun i hi => ((FQ.hf hvQ) i).1 hi) hab hpar hg1 hdist
    hσT hσQ (fun i m' h1 h2 h3 h4 h5 => ?_) (fun i m' h1 h2 h3 h4 h5 => ?_)
  · obtain ⟨hi, hi1, rfl⟩ := hsideT i m' h1 h2 h3 h4 h5
    rw [hi, hi1]; exact mul_self_pos.mpr hσT
  · obtain ⟨hi, hi1, hm'⟩ := hsideQ i m' h1 h2 h3 h4 h5
    rw [hi, hi1]
    rcases hm' with rfl | rfl
    · exact mul_self_pos.mpr hσQ
    · exact hq₂

/-! ### `V` with the triangle rim: a sector rim (Proposition 22.2, Lemma 22.6 (b)) -/

/-- Two vectors orthogonal to a nonzero `N` with nonzero cross product: `det(A, B, N) ≠ 0`. -/
theorem det3_perp_ne {A B N : ℝ³} (hA : ⟪N, A⟫ = 0) (hB : ⟪N, B⟫ = 0) (hAB : cross A B ≠ 0)
    (hN : N ≠ 0) : det3 A B N ≠ 0 := by
  intro h0
  have hpar : cross (cross A B) N = 0 := by
    rw [cross_cross_eq, real_inner_comm, hA, real_inner_comm, hB, zero_smul, zero_smul, sub_zero]
  have e := eq_smul_of_cross_eq_zero hAB hpar
  have h1 : det3 A B N = ⟪N, cross A B⟫ := by rw [det3, real_inner_comm]
  rw [h1] at h0
  rw [h0, zero_div, zero_smul] at e
  exact hN e

/-- **A sector rim of `V`'s triangle closing** (Proposition 22.2 for the rim `v m a b`).  At a vertex
view `u` the quadrilateral `S_Q = {v, a, m, m'}` (apex `v`, far end `a`) and the triangle
`S_T = {v, b, n}` are seen edge-on; the middles are `m = v + s (a − v) + δ u`,
`m' = v + s' (a − v) + δ' u` on opposite sides of the chord (`δ δ' < 0`); every point is weakly
left of the sides of the triangle rim `v a b`.  If the sector rim `v m a b` (the middle `m` shown,
`m'` and `n` hidden) is robustly unimodal, a tilt into the sector shows it, so the set is Rupert,
whatever its horizontal double normals. -/
theorem isRupert_vSector {x : Fin 7 → ℝ³} (T : Facets21 x) {v a b n m m' : Fin 7}
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

/-- Robust unimodality of a four-cycle with distinct values and no separated diagonals. -/
theorem isRobustUnimodal_quad_of {z₀ z₁ z₂ z₃ : ℝ} (hd : [z₀, z₁, z₂, z₃].Nodup)
    (h1 : ¬ (max z₁ z₃ < min z₀ z₂)) (h2 : ¬ (max z₀ z₂ < min z₁ z₃)) :
    IsRobustUnimodal (quad z₀ z₁ z₂ z₃) :=
  isRobustUnimodal_quad (QuadTie.of_nodup hd) h1 h2

/-- **The middles of a quadrilateral face lie on opposite sides of the chord** (generic labels):
the face `S_Q ∋ v, a, m₁, m₂` with apex `v` and far end `a` opposite (the sides `v m₁`, `v m₂` are
edges: facets `S₁ ∋ v, m₁` and `S₂ ∋ v, m₂` with the other two beneath), seen edge-on at `u`:
if `m_i = v + s_i (a − v) + δ_i u`, then `δ₁ δ₂ < 0`. -/
theorem quad_offsets21 {x : Fin 7 → ℝ³} (T : Facets21 x) {v a b m₁ m₂ : Fin 7}
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

/-- **The middles of a quadrilateral face seen edge-on at a vertex view** (generic labels): the
face `S_Q ∋ v, a, m₁, m₂` with apex `v` and far end `a` opposite (the sides `v m₁`, `v m₂` are
edges: facets `S₁ ∋ v, m₁` and `S₂ ∋ v, m₂` with the other two beneath); the view `u` lies in
the face's plane and is not along `a − v`, and `b` (off the face) is strictly left of `v a`.  If
every point is weakly left of the triangle `v a b`, then `m₁`, `m₂` lie over the open chord, on
opposite sides: `m_i = v + s_i (a − v) + δ_i u`, `0 < s_i < 1`, `δ₁ δ₂ < 0`. -/
theorem quad_middles21 {x : Fin 7 → ℝ³} (T : Facets21 x) {v a b m₁ m₂ : Fin 7}
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
  exact quad_offsets21 T FQ F₁ F₂ ⟨hvQ, haQ, h1Q, h2Q, hbQ, hv1, h11, ha1, h21, hv2, h22, ha2, h12⟩
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]; exact ⟨⟨hva, hv1', hv2'⟩, ⟨ha1', ha2'⟩, h12', not_false⟩)
    hpar hm₁ hm₂

/-- **`V`'s triangle closing at the limit** (Lemma 18.2 with Proposition 22.2 for a sector rim).
The shapes `K_n → x` carry the triangle certificate `v a b` at views `u_n → u`; the faces at
`v` are the quadrilateral `S_Q = {v, a, m₁, m₂}` (apex `v`, far end `a`) and the triangle
`S_T = {v, b, n}`.  At the limit, with no two points over one point, (G1) and distinct depths, one
of the two sector rims `v m a b` is unimodal: if `b` is below the higher of `v`, `a`, the middle
above the chord, else the one below.  So `x` is Rupert, whatever its horizontal double normals. -/
theorem isRupert_vTriLim {x : Fin 7 → ℝ³} (T : Facets21 x) {v a b n m₁ m₂ : Fin 7}
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
    quad_middles21 T FQ F₁ F₂ ⟨hvQ, haQ, h1Q, h2Q, hbQ, hv1, h11, ha1, h21, hv2, h22, ha2, h12⟩
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
    refine isRupert_vSector T FQ FT ⟨hvQ, haQ, hmQ, hm'Q, hbQ, hall, hvT, hbT, hnT, haT, hmT, hTall⟩
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

/-! ### `V` with the quadrilateral rim: (H4) by Lemma 22.13, the middle `6` by Lemma 22.14 -/

namespace VtxConf

variable {V : Finset ℝ³} {u v a c b p q n Na Nb : ℝ³} {κa κb : ℝ}

/-- **(H4) from a separation by the plane `a c b`**: if the plane `a c b` separates `v` from the
lower middle `q`, (H4) holds in the sense of `u`. -/
theorem h4_of_sepQ (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (h : det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (q - a) < 0) :
    H4orCopl u v a c b p 1 := by
  left
  obtain ⟨s, δ, hs0, hs1, hδ, hq⟩ := E.q_coords
  have e : det3 (c - a) (b - a) (q - a) = (1 - s) * det3 (c - a) (b - a) (v - a) +
      δ * det3 (c - a) (b - a) u := by
    rw [hq]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [e] at h
  have h1 := mul_self_nonneg (det3 (c - a) (b - a) (v - a))
  have h2 : δ * (det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) u) < 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s) h1]
  rw [one_mul]
  exact pos_of_mul_neg_right h2 hδ.le |> fun h' => by nlinarith

/-- As `h4_of_sepQ` with the upper middle `p`: (H4) in the sense `−u`. -/
theorem h4_of_sepP (E : VtxConf V u v a c b p q n Na Nb κa κb)
    (h : det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (p - a) < 0) :
    H4orCopl u v a c b q (-1) := by
  left
  obtain ⟨s, δ, hs0, hs1, hδ, hp⟩ := E.p_coords
  have e : det3 (c - a) (b - a) (p - a) = (1 - s) * det3 (c - a) (b - a) (v - a) +
      δ * det3 (c - a) (b - a) u := by
    rw [hp]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [e] at h
  have h1 := mul_self_nonneg (det3 (c - a) (b - a) (v - a))
  have h2 : δ * (det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) u) < 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s) h1]
  have h3 : det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) u < 0 := by
    by_contra hc; push Not at hc; nlinarith [mul_nonneg hδ.le hc]
  linarith

theorem det3_copl_eq (a c b m : ℝ³) :
    det3 (a - m) (c - m) (b - m) = -det3 (c - a) (b - a) (m - a) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

end VtxConf

/-- **Lemma 22.13 at the limit, algebra.**  If `b − c` is parallel to the plane of `v, a, w`
(normal `N`), then with `Π(y) = det(c − a, b − a, y − a)` (the plane `a c b`) and
`Δ(y) = det(v − b, c − b, y − b)` (the plane `b v c`): `Π(v) = −Δ(a)` and `Π(w) = Δ(w) − Δ(a)`.
So if `Δ(a)(Δ(w) − Δ(a)) ≥ 0` (closed: `ρ = Δ(a)/Δ(w) ∈ [0, 1]`) and `a` is off the plane
`b v c`, the plane `a c b` separates `v` and `w`, or contains `w`. -/
theorem pi_sep_of_delta {v a c b w N : ℝ³} (hN : N ≠ 0) (hav : ⟪N, a - v⟫ = 0)
    (hwv : ⟪N, w - v⟫ = 0) (hcb : ⟪N, b - c⟫ = 0) (hcr : cross (a - v) (w - v) ≠ 0)
    (hΔ : 0 ≤ det3 (v - b) (c - b) (a - b) *
      (det3 (v - b) (c - b) (w - b) - det3 (v - b) (c - b) (a - b)))
    (hoff : det3 (v - b) (c - b) (a - b) ≠ 0) :
    det3 (c - a) (b - a) (v - a) * det3 (c - a) (b - a) (w - a) < 0 ∨
      det3 (c - a) (b - a) (w - a) = 0 := by
  obtain ⟨μ, ν, hbc⟩ := EdgeConf.exists_coords_of_perp hav hwv hcb hcr hN
  have hb : b = c + μ • (a - v) + ν • (w - v) := by linear_combination (norm := module) hbc
  have e1 : det3 (c - a) (b - a) (v - a) = -det3 (v - b) (c - b) (a - b) := by
    rw [hb]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  have e2 : det3 (c - a) (b - a) (w - a) =
      det3 (v - b) (c - b) (w - b) - det3 (v - b) (c - b) (a - b) := by
    rw [hb]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  by_cases h0 : det3 (c - a) (b - a) (w - a) = 0
  · exact Or.inr h0
  left
  rw [e1, e2]
  rw [e2] at h0
  have := mul_ne_zero hoff h0
  have h' : -det3 (v - b) (c - b) (a - b) *
      (det3 (v - b) (c - b) (w - b) - det3 (v - b) (c - b) (a - b)) =
      -(det3 (v - b) (c - b) (a - b) *
        (det3 (v - b) (c - b) (w - b) - det3 (v - b) (c - b) (a - b))) := by ring
  rw [h']
  exact neg_neg_of_pos (lt_of_le_of_ne hΔ (Ne.symm this))

/-- **Lagrange's identity** for two cross products with a common factor. -/
theorem inner_cross_cross (A B C : ℝ³) :
    ⟪cross A B, cross A C⟫ = ⟪A, A⟫ * ⟪B, C⟫ - ⟪A, B⟫ * ⟪A, C⟫ := by
  simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp; ring

/-- **Lemma 22.14 at the limit (the escape for the middle `w`)**: if a nonzero `y` lies in the
cone of `b − v`, `v − a`, `w − v` (closed form: Cramer determinants with the sign of the frame
determinant, which is nonzero) and `δ ⟪y, u⟫ ≤ 0` for a number `δ` of sign `ε` (the offset of
`w = v + s (a − v) + δ u`), then the residual pattern of Lemma 22.9 for `w` (`w`, `b` above `v`, and `a`,
`c` below it, in the sense `ε = sign δ`) is impossible. -/
theorem esc_of_cone {u v a c b w y : ℝ³} {δ ε : ℝ} (hy : y ≠ 0)
    (hDg : det3 (b - v) (v - a) (w - v) ≠ 0)
    (h1 : 0 ≤ det3 y (v - a) (w - v) * det3 (b - v) (v - a) (w - v))
    (h2 : 0 ≤ det3 (b - v) y (w - v) * det3 (b - v) (v - a) (w - v))
    (h3 : 0 ≤ det3 (b - v) (v - a) y * det3 (b - v) (v - a) (w - v))
    (hδy : δ * ⟪y, u⟫ ≤ 0) (hεδ : 0 < ε * δ) :
    ¬ (ε * ⟪v, u⟫ < ε * ⟪w, u⟫ ∧ ε * ⟪v, u⟫ < ε * ⟪b, u⟫ ∧ ε * ⟪a, u⟫ < ε * ⟪v, u⟫ ∧
      ε * ⟪c, u⟫ < ε * ⟪v, u⟫) := by
  rintro ⟨k1, k2, k3, -⟩
  set Dg := det3 (b - v) (v - a) (w - v) with hDgdef
  -- Cramer's rule
  have cr : Dg • y = det3 y (v - a) (w - v) • (b - v) + det3 (b - v) y (w - v) • (v - a) +
      det3 (b - v) (v - a) y • (w - v) := by
    rw [hDgdef]; ext j; fin_cases j <;>
      simp [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply] <;> ring
  have i1 := congrArg (fun z => ε * ⟪z, u⟫) cr
  simp only [real_inner_smul_left, inner_add_left] at i1
  have p1 : 0 < ε * ⟪b - v, u⟫ := by rw [inner_sub_left]; linarith
  have p2 : 0 < ε * ⟪v - a, u⟫ := by rw [inner_sub_left]; linarith
  have p3 : 0 < ε * ⟪w - v, u⟫ := by rw [inner_sub_left]; linarith
  have hDD : 0 < Dg * Dg := mul_self_pos.mpr hDg
  -- `ε ⟪y, u⟫ > 0`
  have hyu : 0 < ε * ⟪y, u⟫ := by
    have key : (Dg * Dg) * (ε * ⟪y, u⟫) =
        (det3 y (v - a) (w - v) * Dg) * (ε * ⟪b - v, u⟫) +
        (det3 (b - v) y (w - v) * Dg) * (ε * ⟪v - a, u⟫) +
        (det3 (b - v) (v - a) y * Dg) * (ε * ⟪w - v, u⟫) := by
      linear_combination Dg * i1
    have hnz : det3 y (v - a) (w - v) * Dg ≠ 0 ∨ det3 (b - v) y (w - v) * Dg ≠ 0 ∨
        det3 (b - v) (v - a) y * Dg ≠ 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3⟩ := hc
      have z1 := (mul_eq_zero.mp c1).resolve_right hDg
      have z2 := (mul_eq_zero.mp c2).resolve_right hDg
      have z3 := (mul_eq_zero.mp c3).resolve_right hDg
      rw [z1, z2, z3, zero_smul, zero_smul, zero_smul, add_zero, add_zero] at cr
      exact hy ((smul_eq_zero.mp cr).resolve_left hDg)
    have hpos : 0 < (Dg * Dg) * (ε * ⟪y, u⟫) := by
      rw [key]
      rcases hnz with hnz | hnz | hnz
      · have := mul_pos (lt_of_le_of_ne h1 (Ne.symm hnz)) p1
        nlinarith [mul_nonneg h2 p2.le, mul_nonneg h3 p3.le]
      · have := mul_pos (lt_of_le_of_ne h2 (Ne.symm hnz)) p2
        nlinarith [mul_nonneg h1 p1.le, mul_nonneg h3 p3.le]
      · have := mul_pos (lt_of_le_of_ne h3 (Ne.symm hnz)) p3
        nlinarith [mul_nonneg h1 p1.le, mul_nonneg h2 p2.le]
    exact pos_of_mul_pos_right hpos hDD.le
  have := mul_pos hεδ hyu
  nlinarith [mul_self_nonneg ε]

/-- **`V`'s quadrilateral closing at the limit** (Lemma 18.2 with §22.3–22.10, 22.13, 22.14).  The
shapes `K_n → x` carry the four-corner certificate `v a c b` at views `u_n → u`; the faces at `v`
are the quadrilateral `S_Q = {v, a, h, w}` (apex `v`, far end `a`, middles `h`, `w`; the sides
`v h`, `v w` are edges) and the triangle `S_T = {v, b, n}`.  At the limit, under §22.4's
conditions (`VtxGen`), with `a` off the plane `b v c` (`hoff`), and with the limit data of F2's
region: the fact of Lemma 22.13 (`hΔ`, closed) and the cone of Lemma 22.14 (`y`, `hcone`), `x` is
Rupert: where the far edge `c b` is parallel to `S_Q`, (H4) holds for the middle `h` (the plane
`a c b` separates `v` from `w`, `pi_sep_of_delta`), and the residual pattern of Lemma 22.9 is
impossible for `w` (`esc_of_cone`). -/
theorem isRupert_vQuadLim {x : Fin 7 → ℝ³} (T : Facets21 x) {v a c b h w n : Fin 7}
    {SQ ST S₁ S₂ : Finset (Fin 7)} (FQ : Face16 x SQ) (FT : Face16 x ST) (F₁ : Face16 x S₁)
    (F₂ : Face16 x S₂) (hSQ : SQ = {v, a, h, w}) (hST : ST = {v, b, n})
    (h₁ : v ∈ S₁ ∧ h ∈ S₁ ∧ a ∉ S₁ ∧ w ∉ S₁) (h₂ : v ∈ S₂ ∧ w ∈ S₂ ∧ a ∉ S₂ ∧ h ∉ S₂)
    (hnd : [v, a, c, b, h, w, n].Nodup)
    {u : ℝ³} (hu : u ≠ 0) (hQu : ⟪FQ.N, u⟫ = 0) (hTu : ⟪FT.N, u⟫ = 0)
    (us : ℕ → ℝ³) (hus : Tendsto us atTop (𝓝 u))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ i, Tendsto (fun n => K n i) atTop (𝓝 (x i)))
    (hfreq : ∃ᶠ k in atTop,
      RimCertPts (univ.image (K k)) (us k) (quad (K k v) (K k a) (K k c) (K k b)))
    (hgen : VtxGen (univ.image x) u (SQ.image x) (ST.image x) FQ.N)
    {y : ℝ³} (hy : y ≠ 0) (hcone : VQuadCone (x v) (x b) (x w) (x a) u y)
    (hΔ : 0 ≤ det3 (x v - x b) (x c - x b) (x a - x b) *
      (det3 (x v - x b) (x c - x b) (x w - x b) - det3 (x v - x b) (x c - x b) (x a - x b)))
    (hoff : det3 (x v - x b) (x c - x b) (x a - x b) ≠ 0) : IsRupert (univ.image x) := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hva, hvc, hvb, hvh, hvw, hvn⟩, ⟨hac, hab, hah, haw, han⟩, ⟨hcb, hch, hcw, hcn⟩,
    ⟨hbh, hbw, hbn⟩, ⟨hhw, hhn⟩, hwn, -⟩ := hnd'
  obtain ⟨hv1, hh1, ha1, hw1⟩ := h₁
  obtain ⟨hv2, hw2, ha2, hh2⟩ := h₂
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hvQ : v ∈ SQ := by rw [hSQ]; simp
  have haQ : a ∈ SQ := by rw [hSQ]; simp
  have hhQ : h ∈ SQ := by rw [hSQ]; simp
  have hwQ : w ∈ SQ := by rw [hSQ]; simp
  have hbQ : b ∉ SQ := by rw [hSQ]; simp [Ne.symm hvb, Ne.symm hab, hbh, hbw]
  have hNQ : FQ.N ≠ 0 := FQ.N_ne hvQ hbQ
  have hpar := hgen.par
  have hcu : cross (x a - x v) u ≠ 0 := hpar _ (mem v) _ (mem a) (T.inj.ne hva)
  -- the middles over the chord, on opposite sides
  obtain ⟨sh, δh, hhX⟩ := EdgeConf.exists_coords_of_perp (FQ.inner_sub haQ hvQ) hQu
    (FQ.inner_sub hhQ hvQ) hcu hNQ
  obtain ⟨sw, δw, hwX⟩ := EdgeConf.exists_coords_of_perp (FQ.inner_sub haQ hvQ) hQu
    (FQ.inner_sub hwQ hvQ) hcu hNQ
  have hxh : x h = x v + sh • (x a - x v) + δh • u := by linear_combination (norm := module) hhX
  have hxw : x w = x v + sw • (x a - x v) + δw • u := by linear_combination (norm := module) hwX
  have hδδ : δh * δw < 0 := quad_offsets21 T FQ F₁ F₂
    ⟨hvQ, haQ, hhQ, hwQ, hbQ, hv1, hh1, ha1, hw1, hv2, hw2, ha2, hh2⟩
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]; exact ⟨⟨hva, hvh, hvw⟩, ⟨hah, haw⟩, hhw, not_false⟩)
    hpar hxh hxw
  -- the data at the limit
  obtain ⟨c1, c2, c3, c4⟩ := hcone
  have hcrw : cross (x a - x v) (x w - x v) = δw • cross (x a - x v) u := by
    rw [hxw]; ext j; fin_cases j <;> simp [cross] <;> ring
  have hδy : δw * ⟪y, u⟫ ≤ 0 := by
    rw [hcrw, real_inner_smul_left] at c4
    have hC : 0 < ⟪cross (x a - x v) u, cross (x a - x v) u⟫ := real_inner_self_pos.mpr hcu
    nlinarith
  have hDg : det3 (x b - x v) (x v - x a) (x w - x v) ≠ 0 := by
    have e : det3 (x b - x v) (x v - x a) (x w - x v) =
        -det3 (x a - x v) (x w - x v) (x b - x v) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, neg_ne_zero]
    exact FQ.det3_ne hvQ haQ hwQ hbQ (cross_ne_zero_of_noSeg T.inj T.noSeg hva hvw haw)
  have hcr : cross (x a - x v) (x w - x v) ≠ 0 := cross_ne_zero_of_noSeg T.inj T.noSeg hva hvw haw
  -- Lemma 22.13 where `c b ∥ S_Q`: the plane `a c b` separates `v` and `w` (or contains `w`)
  have sep : ⟪FQ.N, x c⟫ = ⟪FQ.N, x b⟫ →
      det3 (x c - x a) (x b - x a) (x v - x a) * det3 (x c - x a) (x b - x a) (x w - x a) < 0 ∨
        det3 (x c - x a) (x b - x a) (x w - x a) = 0 := fun hcb =>
    pi_sep_of_delta hNQ (FQ.inner_sub haQ hvQ) (FQ.inner_sub hwQ hvQ)
      (by rw [inner_sub_right, hcb, sub_self]) hcr hΔ hoff
  have hfa := FQ.hf hvQ
  have hfb := FT.hf (i₀ := v) (by rw [hST]; simp)
  rcases lt_or_gt_of_ne (show δh ≠ 0 by rintro rfl; simp at hδδ) with hneg | hpos
  · -- `w` above the chord, `h` below
    have hδw : 0 < δw := pos_of_mul_neg_right hδδ hneg.le
    refine isRupert_vtx_limit x T.inj T.noSeg (v := v) (a := a) (c := c) (b := b) (p := w)
      (q := h) (m := n) (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true]
        exact ⟨⟨hva, hvc, hvb, hvw, hvh, hvn⟩, ⟨hac, hab, haw, hah, han⟩, ⟨hcb, hcw, hch, hcn⟩,
          ⟨hbw, hbh, hbn⟩, ⟨Ne.symm hhw, hwn⟩, hhn, not_false⟩)
      (Sa := SQ) (by rw [hSQ, Finset.pair_comm]) hST hfa hfb
      hu hQu hTu ⟨sw, δw, hδw, hxw⟩ ⟨sh, δh, hneg, hxh⟩ K hK us hus hfreq hgen fun E hcb => ?_
    refine ⟨Or.inr (esc_of_cone hy hDg c1 c2 c3 hδy (by rw [one_mul]; exact hδw)), Or.inl ?_⟩
    rcases sep hcb with h1 | h1
    · exact E.h4_of_sepP h1
    · exact E.h4_of_coplP (by rw [VtxConf.det3_copl_eq, h1, neg_zero])
  · -- `h` above the chord, `w` below
    have hδw : δw < 0 := neg_of_mul_neg_right hδδ hpos.le
    refine isRupert_vtx_limit x T.inj T.noSeg (v := v) (a := a) (c := c) (b := b) (p := h)
      (q := w) (m := n) hnd hSQ hST hfa hfb hu hQu hTu
      ⟨sh, δh, hpos, hxh⟩ ⟨sw, δw, hδw, hxw⟩ K hK us hus hfreq hgen fun E hcb => ?_
    refine ⟨Or.inl ?_, Or.inr (esc_of_cone hy hDg c1 c2 c3 hδy (by linarith))⟩
    rcases sep hcb with h1 | h1
    · exact E.h4_of_sepQ h1
    · exact E.h4_of_coplQ (by rw [VtxConf.det3_copl_eq, h1, neg_zero])

/-! ### The data at the limit -/

/-- `VQuadCone` passes to limits (it is a closed condition). -/
theorem VQuadCone.limit {ι : Type*} {l : Filter ι} {bs cs c's ds us ys : ι → ℝ³}
    {b c c' d u y : ℝ³} (hb : Tendsto bs l (𝓝 b)) (hc : Tendsto cs l (𝓝 c))
    (hc' : Tendsto c's l (𝓝 c')) (hd : Tendsto ds l (𝓝 d)) (hu : Tendsto us l (𝓝 u))
    (hy : Tendsto ys l (𝓝 y))
    (h : ∃ᶠ t in l, VQuadCone (bs t) (cs t) (c's t) (ds t) (us t) (ys t)) :
    VQuadCone b c c' d u y := by
  have hDg := Tendsto.det3' (hc.sub hb) (hb.sub hd) (hc'.sub hb)
  have lim0 : ∀ {f : ι → ℝ} {L : ℝ}, Tendsto f l (𝓝 L) → (∃ᶠ t in l, 0 ≤ f t) → 0 ≤ L :=
    fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  refine ⟨lim0 ((Tendsto.det3' hy (hb.sub hd) (hc'.sub hb)).mul hDg) (h.mono fun t ht => ht.1),
    lim0 ((Tendsto.det3' (hc.sub hb) hy (hc'.sub hb)).mul hDg) (h.mono fun t ht => ht.2.1),
    lim0 ((Tendsto.det3' (hc.sub hb) (hb.sub hd) hy).mul hDg) (h.mono fun t ht => ht.2.2.1), ?_⟩
  have e : ∀ A B C Y U : ℝ³, ⟪cross A B, cross A C⟫ * ⟪Y, U⟫ =
      (⟪A, A⟫ * ⟪B, C⟫ - ⟪A, B⟫ * ⟪A, C⟫) * ⟪Y, U⟫ := fun A B C Y U => by
    rw [inner_cross_cross]
  have hlim : Tendsto (fun t => ⟪cross (ds t - bs t) (c's t - bs t), cross (ds t - bs t) (us t)⟫ *
      ⟪ys t, us t⟫) l (𝓝 (⟪cross (d - b) (c' - b), cross (d - b) u⟫ * ⟪y, u⟫)) := by
    simp only [e]
    have hdb := hd.sub hb
    have hcb := hc'.sub hb
    exact (((hdb.inner hdb).mul (hcb.inner hu)).sub ((hdb.inner hcb).mul (hdb.inner hu))).mul
      (hy.inner hu)
  exact le_of_tendsto_frequently hlim tendsto_const_nhds (h.mono fun t ht => ht.2.2.2)

/-- `VDelta` passes to limits as a weak inequality. -/
theorem VDelta.limit {ι : Type*} {l : Filter ι} {bs b's cs c's ds : ι → ℝ³} {b b' c c' d : ℝ³}
    (hb : Tendsto bs l (𝓝 b)) (hb' : Tendsto b's l (𝓝 b')) (hc : Tendsto cs l (𝓝 c))
    (hc' : Tendsto c's l (𝓝 c')) (hd : Tendsto ds l (𝓝 d))
    (h : ∃ᶠ t in l, VDelta (bs t) (b's t) (cs t) (c's t) (ds t)) :
    0 ≤ det3 (b - c) (b' - c) (d - c) *
      (det3 (b - c) (b' - c) (c' - c) - det3 (b - c) (b' - c) (d - c)) := by
  have h1 := Tendsto.det3' (hb.sub hc) (hb'.sub hc) (hd.sub hc)
  have h2 := Tendsto.det3' (hb.sub hc) (hb'.sub hc) (hc'.sub hc)
  exact le_of_tendsto_frequently tendsto_const_nhds (h1.mul (h2.sub h1))
    (h.mono fun t ht => le_of_lt (by unfold VDelta at ht; exact ht))

/-- `VQuadCone` is invariant under a rescaling of the view. -/
theorem VQuadCone.smul_view {b c c' d u y : ℝ³} (h : VQuadCone b c c' d u y) (r : ℝ) :
    VQuadCone b c c' d (r • u) y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [cross_smul_right', real_inner_smul_right, real_inner_smul_right]
  have : r * ⟪cross (d - b) (c' - b), cross (d - b) u⟫ * (r * ⟪y, u⟫) = (r * r) *
      (⟪cross (d - b) (c' - b), cross (d - b) u⟫ * ⟪y, u⟫) := by ring
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg r) h4

/-! ### One vertex line with a quadrilateral -/

/-- **The data of a certificate at a vertex line, in generic labels**: `T1`'s rim
`v h c n` / `v h n` (the quadrilateral's far end `h` adjacent to the apex `v`) or `V`'s rim
`v a c b` / `v a b` with its data (`a` opposite `v`; `w'` the named view of `V′`). -/
def LineDat21 (y : Fin 7 → ℝ³) (v a c b h w n : Fin 7) (u w' : ℝ³) : Prop :=
  T1Rim (univ.image y) (y v) (y c) (y n) (y h) u ∨
    VRimN (univ.image y) (y v) (y c) (y b) (y w) (y a) u w'

theorem LineDat21.smul {y : Fin 7 → ℝ³} {v a c b h w n : Fin 7} {u w' : ℝ³}
    (hd : LineDat21 y v a c b h w n u w') {r : ℝ} (hr : 0 < r) :
    LineDat21 y v a c b h w n (r • u) w' := by
  rcases hd with hd | hd
  · exact Or.inl (hd.imp (·.smul hr) (·.smul hr))
  · refine Or.inr (hd.imp (fun ⟨h1, ⟨s', hs', h2⟩, h3⟩ => ⟨h1.smul hr, ⟨s', hs', h2.smul_view r⟩,
      h3⟩) (·.smul hr))

set_option maxHeartbeats 1000000 in
/-- **§22 at one vertex line with a quadrilateral** (generic labels; `T1` and `V` in their
labellings).  The faces at the apex `v` are the triangle `S_T = {v, b, n}` and the quadrilateral
`S_Q = {v, a, h, w}` (`a` opposite `v`; the sides `v h`, `v w` are edges, of the facets `S₁`,
`S₂`).  Shapes `K_n → x` frequently carry a certificate at `±` the named view `W_n → W`
(`LineDat21`); at the limit §22.4's conditions hold at `W` (`VtxGen`) and `a` is off the plane
`b v c`.  Then `x` is Rupert: `T1` by Proposition 22.2 (realized on both circles), `V`'s
triangle by a sector rim, `V`'s quadrilateral by §22.3–22.10 with Lemmas 22.13 and 22.14. -/
theorem isRupert_line21 {x : Fin 7 → ℝ³} (T : Facets21 x) {v a c b h w n : Fin 7}
    {ST SQ S₁ S₂ : Finset (Fin 7)} (FT : Face16 x ST) (FQ : Face16 x SQ) (F₁ : Face16 x S₁)
    (F₂ : Face16 x S₂) (hST : ST = {v, b, n}) (hSQ : SQ = {v, a, h, w})
    (hS : v ∈ S₁ ∧ h ∈ S₁ ∧ a ∉ S₁ ∧ w ∉ S₁ ∧ v ∈ S₂ ∧ w ∈ S₂ ∧ a ∉ S₂ ∧ h ∉ S₂)
    (hnd : [v, a, c, b, h, w, n].Nodup)
    -- the decidable facts of the labels (`T1`'s rims, `V`'s triangle)
    (t1 : v ∈ ST ∧ n ∈ ST ∧ b ∈ ST ∧ h ∉ ST ∧ v ∈ SQ ∧ h ∈ SQ ∧ a ∈ SQ ∧ w ∈ SQ ∧ n ∉ SQ ∧
      v ∈ S₁ ∧ h ∈ S₁ ∧ a ∉ S₁ ∧ w ∉ S₁)
    (t1nd : [v, n, b, h, a, w].Nodup)
    (t1q : Function.Injective (quad v h c n) ∧
      (∀ i m', quad v h c n i ∈ ST → quad v h c n (i + 1) ∈ ST → m' ∈ ST →
        m' ≠ quad v h c n i → m' ≠ quad v h c n (i + 1) →
        quad v h c n i = n ∧ quad v h c n (i + 1) = v ∧ m' = b) ∧
      (∀ i m', quad v h c n i ∈ SQ → quad v h c n (i + 1) ∈ SQ → m' ∈ SQ →
        m' ≠ quad v h c n i → m' ≠ quad v h c n (i + 1) →
        quad v h c n i = v ∧ quad v h c n (i + 1) = h ∧ (m' = a ∨ m' = w)))
    (t1t : Function.Injective (tri v h n) ∧
      (∀ i m', tri v h n i ∈ ST → tri v h n (i + 1) ∈ ST → m' ∈ ST →
        m' ≠ tri v h n i → m' ≠ tri v h n (i + 1) →
        tri v h n i = n ∧ tri v h n (i + 1) = v ∧ m' = b) ∧
      (∀ i m', tri v h n i ∈ SQ → tri v h n (i + 1) ∈ SQ → m' ∈ SQ →
        m' ≠ tri v h n i → m' ≠ tri v h n (i + 1) →
        tri v h n i = v ∧ tri v h n (i + 1) = h ∧ (m' = a ∨ m' = w)))
    (vt : v ∈ SQ ∧ a ∈ SQ ∧ h ∈ SQ ∧ w ∈ SQ ∧ b ∉ SQ ∧
      (∀ i ∈ SQ, i = v ∨ i = a ∨ i = h ∨ i = w) ∧
      v ∈ ST ∧ b ∈ ST ∧ n ∈ ST ∧ a ∉ ST ∧ h ∉ ST ∧ w ∉ ST ∧
      (∀ i ∈ ST, i = v ∨ i = b ∨ i = n) ∧
      v ∈ S₁ ∧ h ∈ S₁ ∧ a ∉ S₁ ∧ w ∉ S₁ ∧ v ∈ S₂ ∧ w ∈ S₂ ∧ a ∉ S₂ ∧ h ∉ S₂)
    (vtnd : [v, a, b, n, h, w].Nodup)
    -- the views
    {W W' : ℝ³} (hW : W ≠ 0) (hQW : ⟪FQ.N, W⟫ = 0) (hTW : ⟪FT.N, W⟫ = 0) (hW' : W' ≠ 0)
    (Ws Ws' : ℕ → ℝ³) (hWs : Tendsto Ws atTop (𝓝 W)) (hWs' : Tendsto Ws' atTop (𝓝 W'))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ i, Tendsto (fun k => K k i) atTop (𝓝 (x i)))
    (hfreq : ∃ᶠ k in atTop, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      LineDat21 (K k) v a c b h w n (ε • Ws k) (Ws' k))
    (hgen : VtxGen (univ.image x) W (SQ.image x) (ST.image x) FQ.N)
    (hoff : det3 (x v - x b) (x c - x b) (x a - x b) ≠ 0) : IsRupert (univ.image x) := by
  -- a sign of the certificates' views
  have hε : (∃ᶠ k in atTop, LineDat21 (K k) v a c b h w n ((1 : ℝ) • Ws k) (Ws' k)) ∨
      ∃ᶠ k in atTop, LineDat21 (K k) v a c b h w n ((-1 : ℝ) • Ws k) (Ws' k) := by
    refine frequently_or_distrib.mp (hfreq.mono fun k ⟨ε, hε, hd⟩ => ?_)
    rcases hε with rfl | rfl
    exacts [Or.inl hd, Or.inr hd]
  obtain ⟨ε, hε1, hfr⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∃ᶠ k in atTop, LineDat21 (K k) v a c b h w n (ε • Ws k) (Ws' k) := by
    rcases hε with h | h
    exacts [⟨1, Or.inl rfl, h⟩, ⟨-1, Or.inr rfl, h⟩]
  have hε0 : ε ≠ 0 := by rcases hε1 with rfl | rfl <;> norm_num
  set u := ε • W with hudef
  have hu : u ≠ 0 := smul_ne_zero hε0 hW
  have hus : Tendsto (fun k => ε • Ws k) atTop (𝓝 u) := hWs.const_smul ε
  have hQu : ⟪FQ.N, u⟫ = 0 := by rw [hudef, real_inner_smul_right, hQW, mul_zero]
  have hTu : ⟪FT.N, u⟫ = 0 := by rw [hudef, real_inner_smul_right, hTW, mul_zero]
  have hg : VtxGen (univ.image x) u (SQ.image x) (ST.image x) FQ.N := hgen.sign hε1
  -- the four kinds of certificates
  unfold LineDat21 T1Rim VRimN at hfr
  rcases frequently_or_distrib.mp hfr with hT | hV
  · rcases frequently_or_distrib.mp hT with hq | ht
    · refine isRupert_twoFaceLab21 T (by norm_num) (quad v h c n) t1q.1 FT FQ F₁ t1 t1nd t1q.2.1
        t1q.2.2 hu _ hus K hK (hq.mono fun k hk => ?_) hg.par hg.g1.swapF hg.dist
      have e : (fun i => K k (quad v h c n i)) = quad (K k v) (K k h) (K k c) (K k n) := by
        funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
      rw [e]; exact hk
    · refine isRupert_twoFaceLab21 T (by norm_num) (tri v h n) t1t.1 FT FQ F₁ t1 t1nd t1t.2.1
        t1t.2.2 hu _ hus K hK (ht.mono fun k hk => ?_) hg.par hg.g1.swapF hg.dist
      have e : (fun i => K k (tri v h n i)) = tri (K k v) (K k h) (K k n) := by
        funext i; rcases zmod3_cases i with rfl | rfl | rfl <;> rfl
      rw [e]; exact hk
  · rcases frequently_or_distrib.mp hV with hq | ht
    · -- `V`'s quadrilateral: a sign of `V′`'s view, and the data at the limit
      have hs : (∃ᶠ k in atTop, RimCertPts (univ.image (K k)) (ε • Ws k)
            (quad (K k v) (K k a) (K k c) (K k b)) ∧
          VQuadCone (K k v) (K k b) (K k w) (K k a) (ε • Ws k) ((1 : ℝ) • Ws' k) ∧
          VDelta (K k v) (K k c) (K k b) (K k w) (K k a)) ∨
          ∃ᶠ k in atTop, RimCertPts (univ.image (K k)) (ε • Ws k)
            (quad (K k v) (K k a) (K k c) (K k b)) ∧
          VQuadCone (K k v) (K k b) (K k w) (K k a) (ε • Ws k) ((-1 : ℝ) • Ws' k) ∧
          VDelta (K k v) (K k c) (K k b) (K k w) (K k a) := by
        refine frequently_or_distrib.mp (hq.mono fun k ⟨h1, ⟨s', hs', h2⟩, h3⟩ => ?_)
        rcases hs' with rfl | rfl
        exacts [Or.inl ⟨h1, h2, h3⟩, Or.inr ⟨h1, h2, h3⟩]
      obtain ⟨s', hs', hfr'⟩ : ∃ s' : ℝ, (s' = 1 ∨ s' = -1) ∧ ∃ᶠ k in atTop,
          RimCertPts (univ.image (K k)) (ε • Ws k) (quad (K k v) (K k a) (K k c) (K k b)) ∧
          VQuadCone (K k v) (K k b) (K k w) (K k a) (ε • Ws k) (s' • Ws' k) ∧
          VDelta (K k v) (K k c) (K k b) (K k w) (K k a) := by
        rcases hs with h | h
        exacts [⟨1, Or.inl rfl, h⟩, ⟨-1, Or.inr rfl, h⟩]
      have hs0 : s' ≠ 0 := by rcases hs' with rfl | rfl <;> norm_num
      have hcone := VQuadCone.limit (hK v) (hK b) (hK w) (hK a) hus (hWs'.const_smul s')
        (hfr'.mono fun k hk => hk.2.1)
      have hΔ := VDelta.limit (hK v) (hK c) (hK b) (hK w) (hK a) (hfr'.mono fun k hk => hk.2.2)
      obtain ⟨hvS₁, hhS₁, haS₁, hwS₁, hvS₂, hwS₂, haS₂, hhS₂⟩ := hS
      exact isRupert_vQuadLim T FQ FT F₁ F₂ hSQ hST ⟨hvS₁, hhS₁, haS₁, hwS₁⟩
        ⟨hvS₂, hwS₂, haS₂, hhS₂⟩ hnd hu hQu hTu _ hus K hK (hfr'.mono fun k hk => hk.1) hg
        (smul_ne_zero hs0 hW') hcone hΔ hoff
    · exact isRupert_vTriLim T FQ FT F₁ F₂ vt vtnd hu hQu _ hus K hK ht hg.par hg.g1 hg.dist

theorem LineDat21.norm {y : Fin 7 → ℝ³} {v a c b h w n : Fin 7} {W W' : ℝ³} {r : ℝ}
    (hr : r ≠ 0) (hd : LineDat21 y v a c b h w n (r • W) W') :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ LineDat21 y v a c b h w n (ε • W) W' := by
  have := hd.smul (inv_pos.mpr (abs_pos.mpr hr))
  rw [smul_smul] at this
  refine ⟨|r|⁻¹ * r, ?_, this⟩
  rcases lt_or_gt_of_ne hr with h | h
  · right; rw [abs_of_neg h]; field_simp
  · left; rw [abs_of_pos h, inv_mul_cancel₀ h.ne']

/-- **The conditions at a vertex line with a quadrilateral** (`fQ`, `S_Q`) and a triangle (`fT`,
`S_T`), for every direction `u` of the line: no horizontal double normal, or §22.4's conditions
(`VtxGen`, with the normal of the quadrilateral) and `a` off the plane `b v c` (the boundary
`ρ = 0` of Lemma 22.13 in `V`'s labelling).  With a horizontal double normal each fails in
codimension 2. -/
def HDNOrVtx21Aff (x : Fin 7 → ℝ³) (fQ fT : ℝ³ →ᵃ[ℝ] ℝ) (SQ ST : Finset (Fin 7))
    (v b c a : Fin 7) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fQ.linear u = 0 → fT.linear u = 0 → NoHDNAt (univ.image x) u ∨
    ((∀ N : ℝ³, (∀ y, fQ.linear y = ⟪N, y⟫) →
      VtxGen (univ.image x) u (SQ.image x) (ST.image x) N) ∧
      det3 (x v - x b) (x c - x b) (x a - x b) ≠ 0)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 2048 in
/-- **Type 21 outside codimension 2, from the facets** (§18.6 step 2 with §22): seven points
labelled so that `014`, `015`, `0256`, `046`, `134`, `135`, `2346`, `235` are facets (functionals
negative off them) are Rupert if, at the named views: along `06`, `46`, `25`, `23` no horizontal
double normal or `QGenAff21` (`hQ`); along `05`, `34` no horizontal double normal or
`Q5GenAff21` (`h5`); along `26` no horizontal double normal or `R26GenAff21` (`h26`); along the
six two-triangle edges no horizontal double normal or (G1) (`hEd`); along the lines of
`014/0256`, `014/2346`, `135/0256`, `135/2346` no horizontal double normal or §22.4's conditions
with `2` off `013`, `2` off `145`, `6` off `145`, `6` off `013` (`HDNOrVtx21Aff`); along those of
`046/134`, `046/015`, `235/134`, `235/015` no horizontal double normal or (G1) (`hV`); and at most
one tie at these views (`OneTie21`).  No plain horizontal-double-normal hypothesis is left. -/
theorem isRupert_type21_limit_facets_codim2 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hQ : (NoHDNAt (univ.image x) (x 6 - x 0) ∨
        QGenAff21 x fD fC 0 3 4 5 6 {0, 4, 6} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 6 - x 4) ∨ QGenAff21 x fD fG 4 5 0 3 6 {0, 4, 6} {2, 3, 4, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 5) ∨ QGenAff21 x fH fC 5 4 3 0 2 {2, 3, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 2 - x 3) ∨ QGenAff21 x fH fG 3 0 5 4 2 {2, 3, 5} {2, 3, 4, 6}))
    (h5 : (NoHDNAt (univ.image x) (x 5 - x 0) ∨
        Q5GenAff21 x fB fC 0 3 1 6 2 5 4 {0, 1, 5} {0, 2, 5, 6}) ∧
      (NoHDNAt (univ.image x) (x 3 - x 4) ∨
        Q5GenAff21 x fE fG 4 5 1 6 2 3 0 {1, 3, 4} {2, 3, 4, 6}))
    (h26 : NoHDNAt (univ.image x) (x 2 - x 6) ∨ R26GenAff21 x fC fG)
    (hEd : HDNOrG1Edge (univ.image x) (x 0) (x 1) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 0) (x 4) (x 1) (x 6) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 4) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 5) (x 0) (x 3) ∧
      HDNOrG1Edge (univ.image x) (x 1) (x 3) (x 4) (x 5) ∧
      HDNOrG1Edge (univ.image x) (x 3) (x 5) (x 1) (x 2))
    (hVq : HDNOrVtx21Aff x fC fA {0, 2, 5, 6} {0, 1, 4} 0 1 3 2 ∧
      HDNOrVtx21Aff x fG fA {2, 3, 4, 6} {0, 1, 4} 4 1 5 2 ∧
      HDNOrVtx21Aff x fC fF {0, 2, 5, 6} {1, 3, 5} 5 1 4 6 ∧
      HDNOrVtx21Aff x fG fF {2, 3, 4, 6} {1, 3, 5} 3 1 0 6)
    (hV : HDNOrG1Aff (univ.image x) fD fE (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ∧
      HDNOrG1Aff (univ.image x) fD fB (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fE (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ∧
      HDNOrG1Aff (univ.image x) fH fB (x 5) (x 3) (x 2) (x 5) (x 0) (x 1))
    (htie : OneTie21 x) : IsRupert (univ.image x) := by
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  refine isRupert_type21_limit_facets_codim2_of x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF
    hG hH hQ h5 h26 hEd (fun K hK h => ?_) hV htie
  obtain ⟨V0, V1, V2, V3⟩ := hVq
  have h' : ∃ᶠ n in atTop, ∃ t : Fin 8, (t.val < 4 ∧ ∃ c : ℝ, c ≠ 0 ∧
      VtxDat21 (K n) t (c • vtxView21 (K n) t)) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 :=
    h.mono fun n ⟨⟨t, ht, hc⟩, hties⟩ => ⟨t, ⟨ht, hc⟩, hties⟩
  obtain ⟨t, hft⟩ := frequently_exists_of_finite h'
  obtain ⟨n₀, ⟨htv, -⟩, -⟩ := hft.exists
  -- without a horizontal double normal at the named view: Lemma 18.2
  have plain : NoHDNAt (univ.image x) (vtxView21 x t) → IsRupert (univ.image x) := fun hnd =>
    isRupert_of_cert_seq21 T (P := fun v => v = .inr t) (fun v hv _ => by subst hv; exact hnd) K
      hK (hft.mono fun n ⟨⟨_, c, hc, hd⟩, hties⟩ =>
        ⟨⟨_, ⟨.inr t, rfl, c, hc, rfl⟩, hd.rimCert htv⟩, hties⟩)
  have norm : ∀ {v a c b h w n : Fin 7} {t' : Fin 8},
      (∀ y u, VtxDat21 y t u = LineDat21 y v a c b h w n u (vtxView21 y t')) →
      ∃ᶠ k in atTop, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        LineDat21 (K k) v a c b h w n (ε • vtxView21 (K k) t) (vtxView21 (K k) t') :=
    fun e => hft.mono fun n ⟨⟨_, c, hc, hd⟩, _⟩ => LineDat21.norm hc (by rw [← e]; exact hd)
  fin_cases t
  · -- `014/0256` at `0`: `T1` and `σ1`'s `V`
    rcases V0 (vtxView21 x 0) (T.vtxView21_ne_zero 0)
      (affine_planeLine_perp' fC hC (by decide) (by decide) (by decide))
      (affine_planeLine_perp fA hA (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f014 T.f0256 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f014 T.f0256 T.f015 T.f046 (v := 0) (a := 2) (c := 3) (b := 1)
      (h := 5) (w := 6) (n := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 0) p2 p1
      (T.vtxView21_ne_zero 5) _ _ (tendsto_view21 hK (.inr 0)) (tendsto_view21 hK (.inr 5)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hC y).symm) hoff
  · -- `014/2346` at `4`: `σ1`'s `T1` and `V`
    rcases V1 (vtxView21 x 1) (T.vtxView21_ne_zero 1)
      (affine_planeLine_perp' fG hG (by decide) (by decide) (by decide))
      (affine_planeLine_perp fA hA (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f014 T.f2346 1 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f014 T.f2346 T.f134 T.f046 (v := 4) (a := 2) (c := 5) (b := 1)
      (h := 3) (w := 6) (n := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 1) p2 p1
      (T.vtxView21_ne_zero 4) _ _ (tendsto_view21 hK (.inr 1)) (tendsto_view21 hK (.inr 4)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hG y).symm) hoff
  · -- `135/0256` at `5`: `σ2`'s `T1` and `σ2σ1`'s `V`
    rcases V2 (vtxView21 x 2) (T.vtxView21_ne_zero 2)
      (affine_planeLine_perp' fC hC (by decide) (by decide) (by decide))
      (affine_planeLine_perp fF hF (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f135 T.f0256 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f135 T.f0256 T.f015 T.f235 (v := 5) (a := 6) (c := 4) (b := 1)
      (h := 0) (w := 2) (n := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 2) p2 p1
      (T.vtxView21_ne_zero 7) _ _ (tendsto_view21 hK (.inr 2)) (tendsto_view21 hK (.inr 7)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hC y).symm) hoff
  · -- `135/2346` at `3`: `σ2σ1`'s `T1` and `σ2`'s `V`
    rcases V3 (vtxView21 x 3) (T.vtxView21_ne_zero 3)
      (affine_planeLine_perp' fG hG (by decide) (by decide) (by decide))
      (affine_planeLine_perp fF hF (by decide) (by decide) (by decide)) with hnd | ⟨hg, hoff⟩
    · exact plain hnd
    obtain ⟨p1, p2⟩ := vtxView21_perp (x := x) T.f135 T.f2346 3 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact isRupert_line21 T T.f135 T.f2346 T.f134 T.f235 (v := 3) (a := 6) (c := 0) (b := 1)
      (h := 4) (w := 2) (n := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (T.vtxView21_ne_zero 3) p2 p1
      (T.vtxView21_ne_zero 6) _ _ (tendsto_view21 hK (.inr 3)) (tendsto_view21 hK (.inr 6)) K hK
      (norm fun y u => rfl) (hg _ fun y => (Face16.ofAffine_inner _ hG y).symm) hoff
  all_goals exact absurd htv (by decide)

end Minimality

end
