module

public import Minimality.EdgeLimit

@[expose] public section

/-!
# Proposition 22.2 for any labelled rim with two faces seen edge-on

At a view `u` where two facets `S_a`, `S_b` are seen edge-on (`⟪N_a, u⟫ = ⟪N_b, u⟫ = 0`, normals
not parallel), a labelled rim `x ∘ lab` with every point weakly left of its sides and robustly
unimodal depths makes the set Rupert, whatever its horizontal double normals, if (G1) holds at
`u` and the points of each face over a side of the rim lie on one side of it in the face's plane
(`σ_a`, `σ_b`: the closing is realized on both circles).  This is `isRupert_of_tiltHides` with the
cone of tilts of `exists_tiltHides_of_normals`.

* `isRupert_twoFace`.
* `side_sign_of_adj`: the side sign from an adjacent facet (the side is an edge of its face).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem G1At.swapF {V : Finset ℝ³} {u : ℝ³} {SA SB : Finset ℝ³} (h : G1At V u SA SB) :
    G1At V u SB SA := fun p hp q hq y hy hc hl h0 h1 h2 =>
  (h p hp q hq y hy hc hl h0 h1 h2).symm

/-- **Proposition 22.2 for a labelled rim with two faces.** -/
theorem isRupert_twoFace {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³)
    (hx : Function.Injective x) (lab : ZMod k → Fin n) (hlab : Function.Injective lab)
    {u : ℝ³} (hu : u ≠ 0) {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, i ∈ Sa → ⟪Na, x i⟫ = κa) (hfb : ∀ i, i ∈ Sb → ⟪Nb, x i⟫ = κb)
    (hab : cross Na Nb ≠ 0)
    (hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u)
    (hside : ∀ i, cross (x (lab (i + 1)) - x (lab i)) u ≠ 0)
    (hg1 : G1At (univ.image x) u (Sa.image x) (Sb.image x))
    {σa σb : ℝ} (hσa : σa ≠ 0) (hσb : σb ≠ 0)
    (hsa : ∀ i m, lab i ∈ Sa → lab (i + 1) ∈ Sa → m ∈ Sa → m ≠ lab i → m ≠ lab (i + 1) →
      0 < σa * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) Na)
    (hsb : ∀ i m, lab i ∈ Sb → lab (i + 1) ∈ Sb → m ∈ Sb → m ≠ lab i → m ≠ lab (i + 1) →
      0 < σb * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) Nb)
    (hrob : IsRobustUnimodal (fun i => ⟪x (lab i), u⟫)) : IsRupert (univ.image x) := by
  classical
  have hNa : Na ≠ 0 := by rintro rfl; apply hab; ext j; fin_cases j <;> simp [cross]
  have hNb : Nb ≠ 0 := by rintro rfl; apply hab; ext j; fin_cases j <;> simp [cross]
  -- the constraint of a side point on a face is a positive multiple of `σ |N|² N`
  have face_cons : ∀ {S : Finset (Fin n)} {N : ℝ³} {κ σ : ℝ}, N ≠ 0 → σ ≠ 0 →
      (∀ i, i ∈ S → ⟪N, x i⟫ = κ) → ∀ p q m : Fin n, p ∈ S → q ∈ S → m ∈ S →
      0 < σ * det3 (x q - x p) (x m - x p) N →
      ∃ c : ℝ, 0 < c ∧ cross (x q - x p) (x m - x p) = c • ((σ * ⟪N, N⟫) • N) := by
    intro S N κ σ hN hσ0 hf p q m hp hq hm hpos
    have hNN : 0 < ⟪N, N⟫ := real_inner_self_pos.mpr hN
    have hpar : cross N (cross (x q - x p) (x m - x p)) = 0 := by
      have e1 : ⟪x q - x p, N⟫ = 0 := by
        rw [inner_sub_left, real_inner_comm, hf q hq, real_inner_comm, hf p hp, sub_self]
      have e2 : ⟪x m - x p, N⟫ = 0 := by
        rw [inner_sub_left, real_inner_comm, hf m hm, real_inner_comm, hf p hp, sub_self]
      have e : cross (cross (x q - x p) (x m - x p)) N = 0 := by
        rw [cross_cross_eq, e1, e2, zero_smul, zero_smul, sub_zero]
      have : cross N (cross (x q - x p) (x m - x p)) =
          -cross (cross (x q - x p) (x m - x p)) N := by
        ext j; fin_cases j <;> simp [cross] <;> ring
      rw [this, e, neg_zero]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, cross (x q - x p) (x m - x p) = t • N :=
      ⟨_, eq_smul_of_cross_eq_zero hN hpar⟩
    have hdet : det3 (x q - x p) (x m - x p) N = t * ⟪N, N⟫ := by
      rw [det3, ht, real_inner_smul_left]
    have h2 : 0 < (σ * ⟪N, N⟫) * (σ * ⟪N, N⟫) := mul_self_pos.mpr (mul_ne_zero hσ0 hNN.ne')
    refine ⟨t / (σ * ⟪N, N⟫), ?_, ?_⟩
    · rw [hdet] at hpos
      have e : t / (σ * ⟪N, N⟫) = (σ * (t * ⟪N, N⟫)) / ((σ * ⟪N, N⟫) * (σ * ⟪N, N⟫)) := by
        field_simp
      rw [e]; exact div_pos hpos h2
    · rw [ht, smul_smul, div_mul_cancel₀ _ (mul_ne_zero hσ0 hNN.ne')]
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have imgA : ∀ i, x i ∈ Sa.image x ↔ i ∈ Sa := fun i => ⟨fun h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hx he ▸ hj, fun h => mem_image_of_mem x h⟩
  have imgB : ∀ i, x i ∈ Sb.image x ↔ i ∈ Sb := fun i => ⟨fun h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hx he ▸ hj, fun h => mem_image_of_mem x h⟩
  have hW : cross ((σa * ⟪Na, Na⟫) • Na) ((σb * ⟪Nb, Nb⟫) • Nb) ≠ 0 := by
    rw [EdgeConf.cross_smul_left'', cross_smul_right', smul_smul]
    exact smul_ne_zero (mul_ne_zero (mul_ne_zero hσa (real_inner_self_pos.mpr hNa).ne')
      (mul_ne_zero hσb (real_inner_self_pos.mpr hNb).ne')) hab
  obtain ⟨d, hd⟩ := exists_tiltHides_of_normals (univ.image x) u (fun i => x (lab i)) hW
    fun z hz i hz1 hz2 h0 => by
    obtain ⟨m, -, rfl⟩ := mem_image.mp hz
    have hzl : ∀ y ∈ univ.image x, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (y - x (lab i)) u := by
      intro y hy; obtain ⟨m', -, rfl⟩ := mem_image.mp hy; exact hleft m' i
    rcases hg1 _ (mem _) _ (mem _) _ hz (hside i) hzl h0 hz1 hz2 with
      ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
    · rw [imgA] at k1 k2 k3
      exact (face_cons hNa hσa hfa _ _ m k1 k2 k3 (hsa i m k1 k2 k3
        (fun e => hz1 (by rw [e])) (fun e => hz2 (by rw [e])))).imp fun c hc => ⟨hc.1, Or.inl hc.2⟩
    · rw [imgB] at k1 k2 k3
      exact (face_cons hNb hσb hfb _ _ m k1 k2 k3 (hsb i m k1 k2 k3
        (fun e => hz1 (by rw [e])) (fun e => hz2 (by rw [e])))).imp fun c hc => ⟨hc.1, Or.inr hc.2⟩
  refine isRupert_of_tiltHides (univ.image x) u d hu hk (fun i => x (lab i)) (fun i => mem _)
    (hx.comp hlab) (fun z hz i => ?_) hd hrob
  obtain ⟨m, -, rfl⟩ := mem_image.mp hz
  exact hleft m i

/-- **The side sign from an adjacent facet**: if the side `p q` of a face (normal `N`, all its
vertices on one plane) is an edge of the face (a facet `G` through `p`, `q`, below the other
vertices of the face), every other vertex `m` of the face has the sign of the reference vertex
`m₀`. -/
theorem side_sign_of_adj {N NG p q m₀ m : ℝ³} (hq : ⟪N, q - p⟫ = 0) (hm₀ : ⟪N, m₀ - p⟫ = 0)
    (hm : ⟪N, m - p⟫ = 0) (hc : cross (q - p) (m₀ - p) ≠ 0) (hN : N ≠ 0)
    (hGq : ⟪NG, q - p⟫ = 0) (hGm₀ : ⟪NG, m₀ - p⟫ < 0) (hGm : ⟪NG, m - p⟫ < 0) :
    0 < det3 (q - p) (m - p) N * det3 (q - p) (m₀ - p) N := by
  obtain ⟨k, hk, hk'⟩ := real_of_adj hq hm₀ hm hc hN hGq hGm₀ hGm
  have e : det3 (q - p) (m - p) N = k * det3 (q - p) (m₀ - p) N := by
    rw [det3, hk', real_inner_smul_left]; rfl
  rw [e]
  have h0 : det3 (q - p) (m₀ - p) N ≠ 0 := by
    have hpar : cross N (cross (q - p) (m₀ - p)) = 0 := by
      have e1 : ⟪q - p, N⟫ = 0 := by rw [real_inner_comm]; exact hq
      have e2 : ⟪m₀ - p, N⟫ = 0 := by rw [real_inner_comm]; exact hm₀
      have e : cross (cross (q - p) (m₀ - p)) N = 0 := by
        rw [cross_cross_eq, e1, e2, zero_smul, zero_smul, sub_zero]
      have : cross N (cross (q - p) (m₀ - p)) = -cross (cross (q - p) (m₀ - p)) N := by
        ext j; fin_cases j <;> simp [cross] <;> ring
      rw [this, e, neg_zero]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, cross (q - p) (m₀ - p) = t • N :=
      ⟨_, eq_smul_of_cross_eq_zero hN hpar⟩
    have ht0 : t ≠ 0 := by rintro rfl; rw [zero_smul] at ht; exact hc ht
    rw [det3, ht, real_inner_smul_left]
    exact mul_ne_zero ht0 (real_inner_self_pos.mpr hN).ne'
  nlinarith [mul_self_pos.mpr h0]

/-- **Proposition 22.2 for a labelled rim at the limit** (Lemma 18.2): the shapes `K_k → x`
carry one labelled rim certificate at the edge view `±(w − v)`; at the limit, only the axle is
seen end-on, (G1) holds and the depths are distinct at `w − v`; the two faces at the axle are
facets with non-parallel normals and the points of each face over a side of the rim lie on one
side of it.  Then `x` is Rupert. -/
theorem isRupert_twoFace_limit {n k : ℕ} [NeZero k] (x : Fin n → ℝ³)
    (hx : Function.Injective x) (lab : ZMod k → Fin n) {v w : Fin n} (hvw : v ≠ w)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (K : ℕ → Fin n → ℝ³) (hK : ∀ m, Tendsto (fun j => K j m) atTop (𝓝 (x m)))
    (hfreq : ∃ᶠ j in atTop, RimCertAt (K j) (ε • (K j w - K j v)) lab)
    {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, i ∈ Sa → ⟪Na, x i⟫ = κa) (hfb : ∀ i, i ∈ Sb → ⟪Nb, x i⟫ = κb)
    (hab : cross Na Nb ≠ 0)
    (hpar : ParOnly (univ.image x) (x w - x v) (x v) (x w))
    (hg1 : G1At (univ.image x) (x w - x v) (Sa.image x) (Sb.image x))
    (hdist : ∀ y ∈ univ.image x, ∀ y' ∈ univ.image x, y ≠ y' →
      ⟪y, x w - x v⟫ ≠ ⟪y', x w - x v⟫)
    {σa σb : ℝ} (hσa : σa ≠ 0) (hσb : σb ≠ 0)
    (hsa : ∀ i m, lab i ∈ Sa → lab (i + 1) ∈ Sa → m ∈ Sa → m ≠ lab i → m ≠ lab (i + 1) →
      0 < σa * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) Na)
    (hsb : ∀ i m, lab i ∈ Sb → lab (i + 1) ∈ Sb → m ∈ Sb → m ≠ lab i → m ≠ lab (i + 1) →
      0 < σb * det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) Nb) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨j₀, hj₀⟩ := hfreq.exists
  have hk := hj₀.three
  have hlab := hj₀.lab_injective
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  set u := ε • (x w - x v) with hudef
  have hu : u ≠ 0 := smul_ne_zero hε0 (sub_ne_zero.mpr (hx.ne hvw.symm))
  have hus : Tendsto (fun j => ε • (K j w - K j v)) atTop (𝓝 u) :=
    ((hK w).sub (hK v)).const_smul ε
  have hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u := by
    intro m i
    exact le_of_tendsto_frequently tendsto_const_nhds
      (Tendsto.det3' ((hK _).sub (hK _)) ((hK _).sub (hK _)) hus)
      (hfreq.mono fun j hj => hj.left m i)
  have hpar' : ParOnly (univ.image x) u (x v) (x w) := hpar.smul hε0
  have hside := side_cross_ne_of_parOnly hx hlab hpar' (i₀ := v) (j₀ := w)
    (hj₀.not_axle (c := ε)) (by omega)
  have hg1' : G1At (univ.image x) u (Sa.image x) (Sb.image x) := by
    rcases hε with h | h <;> simp only [hudef, h, one_smul, neg_one_smul]
    · exact hg1
    · exact G1At.swapF (EdgeConf.G1At.neg hg1)
  have hrob : IsRobustUnimodal (fun i => ⟪x (lab i), u⟫) := by
    refine isRobustUnimodal_of_tendsto_ties (fun i => (hK (lab i)).inner hus)
      (hfreq.mono fun j hj => ⟨hj.robust, fun i i' e => ?_⟩)
    by_cases hii : i = i'
    · rw [hii]
    · exfalso
      rw [hudef, real_inner_smul_right, real_inner_smul_right] at e
      exact hdist _ (mem_image_of_mem x (mem_univ _)) _ (mem_image_of_mem x (mem_univ _))
        (hx.ne (hlab.ne hii)) (mul_left_cancel₀ hε0 e)
  exact isRupert_twoFace hk x hx lab hlab hu hfa hfb hab hleft hside hg1' hσa hσb hsa hsb hrob

/-- Two facets through a common point `p`, with a vertex `q` of the first strictly below the
second: their normals are not parallel. -/
theorem cross_normals_ne {Na Nb p q : ℝ³} (hNa : Na ≠ 0) (hqa : ⟪Na, q - p⟫ = 0)
    (hqb : ⟪Nb, q - p⟫ < 0) : cross Na Nb ≠ 0 := by
  intro h0
  have : cross Na Nb = 0 := h0
  obtain ⟨t, ht⟩ : ∃ t : ℝ, Nb = t • Na := ⟨_, eq_smul_of_cross_eq_zero hNa h0⟩
  rw [ht, real_inner_smul_left, hqa, mul_zero] at hqb
  exact lt_irrefl _ hqb

end Minimality

end
