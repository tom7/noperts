module

public import Minimality.CaseC09Cross
public import Minimality.CaseC18Frame

@[expose] public section

/-!
# Type 18, acute case (c): the frame-coordinate bridges (`FEWER-FACES-PROOFS.md` §27, continued (2))

The bridges of `CaseC09Tests`/`CaseC09Cross` (`rupert_crossing`, `rupert_rim`, `rupert_rim4`,
`rupert_rim5`, `rupert_rim5p`) for an arbitrary frame of the seven points, `Frame7`: a base
point, three independent vectors `u₁, u₂, e` with `u₁ ⟂ e`, `u₂ ⟂ e`, and frame coordinates `ptC j`
of the points.  `Frame18.toFrame7` is the frame of type 18; the 09 files are not touched.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- A frame of the seven points: `x j = base + ptC j` in the coordinates of `u₁, u₂, e`. -/
structure Frame7 (x : Fin 7 → ℝ³) where
  base : ℝ³
  u1 : ℝ³
  u2 : ℝ³
  e : ℝ³
  indep : LinearIndependent ℝ ![u1, u2, e]
  inner_u1_e : ⟪u1, e⟫ = 0
  inner_u2_e : ⟪u2, e⟫ = 0
  ptC : Fin 7 → C3
  x_eq : ∀ j, x j = base + (ptC j).x • u1 + (ptC j).y • u2 + (ptC j).z • e

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

/-- The vector with frame coordinates `p`. -/
noncomputable def fvC (p : C3) : ℝ³ := p.x • F.u1 + p.y • F.u2 + p.z • F.e

noncomputable def kap : ℝ := det3 F.u1 F.u2 F.e
noncomputable def a11 : ℝ := ⟪F.u1, F.u1⟫
noncomputable def a12 : ℝ := ⟪F.u1, F.u2⟫
noncomputable def a22 : ℝ := ⟪F.u2, F.u2⟫
noncomputable def gg : ℝ := ⟪F.e, F.e⟫

/-- The depth form of the frame. -/
noncomputable def GG (a b : C3) : ℝ := Gf F.a11 F.a12 F.a22 F.gg a b

noncomputable def basis : Module.Basis (Fin 3) ℝ ℝ³ :=
  basisOfLinearIndependentOfCardEqFinrank F.indep (by simp)

lemma basis_apply (i : Fin 3) : F.basis i = ![F.u1, F.u2, F.e] i := by
  simp [basis]

lemma inner_frame (a b c a' b' c' : ℝ) :
    ⟪a • F.u1 + b • F.u2 + c • F.e, a' • F.u1 + b' • F.u2 + c' • F.e⟫ =
      F.a11 * (a * a') + F.a12 * (a * b' + a' * b) + F.a22 * (b * b') + F.gg * (c * c') := by
  have h1 := F.inner_u1_e
  have h2 := F.inner_u2_e
  have h1' : ⟪F.e, F.u1⟫ = 0 := by rw [real_inner_comm]; exact h1
  have h2' : ⟪F.e, F.u2⟫ = 0 := by rw [real_inner_comm]; exact h2
  have h12 : ⟪F.u2, F.u1⟫ = ⟪F.u1, F.u2⟫ := real_inner_comm _ _
  simp only [a11, a12, a22, gg, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h1, h2, h1', h2', h12, conj_trivial]
  ring

lemma coord_zero {a b c : ℝ} (h : a • F.u1 + b • F.u2 + c • F.e = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have := Fintype.linearIndependent_iff.mp F.indep ![a, b, c] (by
    simpa [Fin.sum_univ_three] using h)
  exact ⟨this 0, this 1, this 2⟩

lemma exists_normal (a1 a2 a3 : ℝ) :
    ∃ N : ℝ³, ∀ a b c : ℝ, ⟪N, a • F.u1 + b • F.u2 + c • F.e⟫ = a1 * a + a2 * b + a3 * c := by
  let ℓ : ℝ³ →ₗ[ℝ] ℝ := F.basis.constr ℝ ![a1, a2, a3]
  refine ⟨(InnerProductSpace.toDual ℝ ℝ³).symm (LinearMap.toContinuousLinearMap ℓ), fun a b c => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  have h0 : ℓ F.u1 = a1 := by
    have := F.basis.constr_basis ℝ ![a1, a2, a3] 0
    rwa [F.basis_apply] at this
  have h1 : ℓ F.u2 = a2 := by
    have := F.basis.constr_basis ℝ ![a1, a2, a3] 1
    rwa [F.basis_apply] at this
  have h2 : ℓ F.e = a3 := by
    have := F.basis.constr_basis ℝ ![a1, a2, a3] 2
    rwa [F.basis_apply] at this
  show ℓ _ = _
  rw [map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2]
  simp only [smul_eq_mul]; ring

lemma x_sub (j i : Fin 7) : x j - x i = F.fvC ((F.ptC j).sub (F.ptC i)) := by
  rw [F.x_eq j, F.x_eq i]
  simp only [fvC, C3.sub]
  module

lemma x_eq' (j : Fin 7) : x j = F.base + F.fvC (F.ptC j) := by
  rw [F.x_eq j]
  simp only [fvC]
  module

lemma decomp (w : ℝ³) : ∃ p : C3, w = F.fvC p := by
  have h := F.basis.sum_repr w
  simp only [Fin.sum_univ_three, F.basis_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact ⟨⟨F.basis.repr w 0, F.basis.repr w 1, F.basis.repr w 2⟩, h.symm⟩

lemma det3_fvC (a b w : C3) :
    det3 (F.fvC a) (F.fvC b) (F.fvC w) = F.kap * Dc a b w := by
  simp only [det3, kap, fvC, Dc, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

lemma inner_fvC (p q : C3) : ⟪F.fvC p, F.fvC q⟫ = F.GG p q := by
  simp only [fvC, GG, Gf]
  rw [F.inner_frame]

lemma inner_x_fvC (j : Fin 7) (q : C3) :
    ⟪x j, F.fvC q⟫ = ⟪F.base, F.fvC q⟫ + F.GG (F.ptC j) q := by
  conv_lhs => rw [F.x_eq' j]
  rw [inner_add_left, F.inner_fvC]

lemma kap_ne : F.kap ≠ 0 := by
  intro h0
  have hN : ∀ w : ℝ³, ⟪cross F.u1 F.u2, w⟫ = 0 := by
    intro w
    obtain ⟨p, rfl⟩ := F.decomp w
    simp only [fvC, inner_add_right, real_inner_smul_right, inner_cross_left, inner_cross_right]
    have : ⟪cross F.u1 F.u2, F.e⟫ = 0 := h0
    rw [this]; ring
  have hc : cross F.u1 F.u2 = 0 := by
    have := hN (cross F.u1 F.u2)
    exact inner_self_eq_zero.mp this
  have hu1 : F.u1 ≠ 0 := by
    intro h
    have := F.coord_zero (a := 1) (b := 0) (c := 0) (by rw [h]; simp)
    exact one_ne_zero this.1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, F.u2 = r • F.u1 := ⟨_, eq_smul_of_cross_eq_zero hu1 hc⟩
  have := F.coord_zero (a := -r) (b := 1) (c := 0) (by rw [one_smul, hr]; simp [neg_smul])
  exact one_ne_zero this.2.1

lemma GG_self_pos (p : C3) (hp : p.x ≠ 0 ∨ p.y ≠ 0 ∨ p.z ≠ 0) : 0 < F.GG p p := by
  rw [← F.inner_fvC]
  apply real_inner_self_pos.mpr
  intro h0
  have := F.coord_zero (a := p.x) (b := p.y) (c := p.z) (by exact h0)
  rcases hp with h | h | h
  · exact h this.1
  · exact h this.2.1
  · exact h this.2.2

/-- **Theorem 5 in frame coordinates.**  `W = {x j | j ∈ I}` lies in the plane
`a₁ cx + a₂ cy + a₃ cz = c₀`, contains three points of independent directions, and along the view
`u₀ = p u₁ + q u₂ + r e` every other point of the set reaches a point of `W` with positive
weights. -/
theorem rupert_crossing (hx : Function.Injective x) (I : Finset (Fin 7)) (j0 j1 j2 : Fin 7)
    (h0 : j0 ∈ I) (h1 : j1 ∈ I) (h2 : j2 ∈ I)
    (hind : ∀ s t : ℝ,
      s * ((F.ptC j1).x - (F.ptC j0).x) + t * ((F.ptC j2).x - (F.ptC j0).x) = 0 →
      s * ((F.ptC j1).y - (F.ptC j0).y) + t * ((F.ptC j2).y - (F.ptC j0).y) = 0 →
      s * ((F.ptC j1).z - (F.ptC j0).z) + t * ((F.ptC j2).z - (F.ptC j0).z) = 0 → s = 0 ∧ t = 0)
    (a1 a2 a3 c0 : ℝ) (hplane : ∀ j ∈ I, a1 * (F.ptC j).x + a2 * (F.ptC j).y + a3 * (F.ptC j).z = c0)
    (p q r : ℝ) (hnp : a1 * p + a2 * q + a3 * r ≠ 0)
    (hcross : ∀ i : Fin 7, i ∉ I → ∃ (τ : ℝ) (m : Fin 7 → ℝ), (∀ j ∈ I, 0 < m j) ∧
      ∑ j ∈ I, m j = 1 ∧ ∑ j ∈ I, m j * (F.ptC j).x = (F.ptC i).x + τ * p ∧
      ∑ j ∈ I, m j * (F.ptC j).y = (F.ptC i).y + τ * q ∧
      ∑ j ∈ I, m j * (F.ptC j).z = (F.ptC i).z + τ * r) :
    IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨N, hN⟩ := F.exists_normal a1 a2 a3
  have hNpt : ∀ j : Fin 7, ⟪N, x j⟫ = ⟪N, F.base⟫ +
      (a1 * (F.ptC j).x + a2 * (F.ptC j).y + a3 * (F.ptC j).z) := by
    intro j
    rw [F.x_eq j, add_assoc, add_assoc, ← add_assoc ((F.ptC j).x • F.u1), inner_add_right]
    rw [show (F.ptC j).x • F.u1 + (F.ptC j).y • F.u2 + (F.ptC j).z • F.e =
      (F.ptC j).x • F.u1 + (F.ptC j).y • F.u2 + (F.ptC j).z • F.e from rfl]
    rw [hN]
  set W : Finset ℝ³ := I.image x with hW
  have hWV : W ⊆ Finset.univ.image x := Finset.image_subset_image (Finset.subset_univ _)
  have hWN : ∀ w ∈ W, ⟪N, w⟫ = ⟪N, F.base⟫ + c0 := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    rw [hNpt, hplane j hj]
  have hind3 : AffineIndependent ℝ ![x j0, x j1, x j2] := by
    refine affineIndependent_of_pair fun s t hst => hind s t ?_ ?_ ?_ |> fun h => h
    all_goals
      have e : s • (x j1 - x j0) + t • (x j2 - x j0) =
          (s * ((F.ptC j1).x - (F.ptC j0).x) + t * ((F.ptC j2).x - (F.ptC j0).x)) • F.u1 +
          (s * ((F.ptC j1).y - (F.ptC j0).y) + t * ((F.ptC j2).y - (F.ptC j0).y)) • F.u2 +
          (s * ((F.ptC j1).z - (F.ptC j0).z) + t * ((F.ptC j2).z - (F.ptC j0).z)) • F.e := by
        rw [F.x_eq j1, F.x_eq j0, F.x_eq j2]; module
      rw [e] at hst
      have := F.coord_zero hst
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  have hu0 : ⟪N, p • F.u1 + q • F.u2 + r • F.e⟫ ≠ 0 := by
    rw [hN]; exact hnp
  refine isRupert_of_crossing (Finset.univ.image x) W hWV N (⟪N, F.base⟫ + c0) hWN
    (a := x j0) (b := x j1) (d := x j2) (Finset.mem_image_of_mem x h0)
    (Finset.mem_image_of_mem x h1) (Finset.mem_image_of_mem x h2) hind3
    (p • F.u1 + q • F.u2 + r • F.e) hu0 ?_
  intro v hv hvW
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  have hi : i ∉ I := fun h => hvW (Finset.mem_image_of_mem x h)
  obtain ⟨τ, m, hm, hm1, hcx, hcy, hcz⟩ := hcross i hi
  have hinv : ∀ j, Function.invFun x (x j) = j := Function.leftInverse_invFun hx
  refine ⟨τ, fun w => m (Function.invFun x w), ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    simp only [hinv]
    exact hm j hj
  · rw [hW, Finset.sum_image hx.injOn]
    simp only [hinv]
    exact hm1
  · rw [hW, Finset.sum_image hx.injOn]
    simp only [hinv]
    have key : ∑ j ∈ I, m j • x j = (∑ j ∈ I, m j) • F.base +
        (∑ j ∈ I, m j * (F.ptC j).x) • F.u1 + (∑ j ∈ I, m j * (F.ptC j).y) • F.u2 +
        (∑ j ∈ I, m j * (F.ptC j).z) • F.e := by
      simp only [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [F.x_eq j]; module
    rw [key, hm1, hcx, hcy, hcz, F.x_eq i]
    module

/-- **The bridge.**  A cycle `c` of the seven points, the view `u` and the tilt `v` in frame
coordinates, the determinant tests `ST` for the cycle and for the remaining points, and an open,
positively homogeneous, shift-invariant depth condition `Q` holding eventually at the tilted
depths and forcing unimodality. -/
theorem rupert_rim {k : ℕ} [NeZero k] (hk : 3 ≤ k) (c : ZMod k → Fin 7) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      ST σ u v ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (Q : (ZMod k → ℝ) → Prop) (hQo : IsOpen {z | Q z})
    (hQs : ∀ z : ZMod k → ℝ, ∀ a : ℝ, 0 < a → Q z → Q fun i => a * z i)
    (hQsh : ∀ z : ZMod k → ℝ, ∀ a : ℝ, Q z → Q fun i => z i + a)
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q fun i => F.GG (F.ptC (c i)) u + s * F.GG (F.ptC (c i)) v)
    (hQu : ∀ z, Function.Injective z → Q z → IsCyclicUnimodal z) :
    IsRupert (Finset.univ.image x) := by
  classical
  set u0 : ℝ³ := F.fvC u with hu0def
  set w : ℝ³ := F.fvC v with hwdef
  have hκ := F.kap_ne
  set t := σ * F.kap with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hconv : ∀ a b : C3, ST σ u v a b →
      TiltSign (F.fvC a) (F.fvC b) (ε • u0) (ε • w) := by
    intro a b h
    have hk2 : 0 < F.kap ^ 2 := by positivity
    rcases h with h | ⟨h0, h1⟩
    · left
      rw [det3_smul_right, hu0def, F.det3_fvC]
      refine sgn_pos t _ ?_
      have := mul_pos hk2 h
      calc 0 < F.kap ^ 2 * (σ * Dc a b u) := this
        _ = t * (F.kap * Dc a b u) := by rw [ht]; ring
    · right
      refine ⟨by rw [det3_smul_right, hu0def, F.det3_fvC, h0, mul_zero, mul_zero], ?_⟩
      rw [det3_smul_right, hwdef, F.det3_fvC]
      refine sgn_pos t _ ?_
      have := mul_pos hk2 h1
      calc 0 < F.kap ^ 2 * (σ * Dc a b v) := this
        _ = t * (F.kap * Dc a b v) := by rw [ht]; ring
  have hu0 : u0 ≠ 0 := by
    intro h0
    have := F.coord_zero (a := u.x) (b := u.y) (c := u.z) (by exact h0)
    rcases hu with h | h | h
    · exact h this.1
    · exact h this.2.1
    · exact h this.2.2
  have hu' : ε • u0 ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  refine isRupert_of_tilted_unimodal' (Finset.univ.image x) (ε • u0) (ε • w) hu' (k := k) hk
    (fun i => x (c i)) (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _))
    (fun i j hi hj => ?_) (fun y hy hyx i => ?_)
    (fun z => Q fun i => ε * z i) ?_ ?_ ?_ ?_
  · show TiltSign (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) (ε • u0) (ε • w)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hcyc i j hi hj)
  · obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hy
    show TiltSign (x (c (i + 1)) - x (c i)) (x j' - x (c i)) (ε • u0) (ε • w)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hrest j' (fun jj h => hyx jj (by simp [h])) i)
  · have : {z : ZMod k → ℝ | Q fun i => ε * z i} =
        (fun z : ZMod k → ℝ => fun i => ε * z i) ⁻¹' {z | Q z} := rfl
    rw [this]
    exact hQo.preimage (by fun_prop)
  · intro z a ha hQ
    have := hQs _ a ha hQ
    convert this using 2 with i
    ring
  · have hdep : ∀ (s : ℝ) (i : ZMod k), ε * ⟪x (c i), ε • u0 + s • (ε • w)⟫ =
        (⟪F.base, u0⟫ + s * ⟪F.base, w⟫) +
          (F.GG (F.ptC (c i)) u + s * F.GG (F.ptC (c i)) v) := by
      intro s i
      have h1 : ⟪x (c i), ε • u0 + s • (ε • w)⟫ = ε * (⟪x (c i), u0⟫ + s * ⟪x (c i), w⟫) := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_right]; ring
      rw [h1, ← mul_assoc, hεε, one_mul, hu0def, hwdef, F.inner_x_fvC (c i) u, F.inner_x_fvC (c i) v]
      ring
    filter_upwards [hQe] with s hs
    have := hQsh _ (⟪F.base, u0⟫ + s * ⟪F.base, w⟫) hs
    show Q fun i => ε * ⟪x (c i), ε • u0 + s • (ε • w)⟫
    convert this using 2 with i
    rw [hdep s i]; ring
  · intro z hinj hQ
    have h1 : IsCyclicUnimodal (fun i => ε * z i) :=
      hQu _ (fun i j hij => hinj (by
        rcases hεs with h | h <;> rw [h] at hij <;> simpa using hij)) hQ
    have h2 := h1.affine_sign (by omega) hεs 0
    convert h2 using 2 with i
    simp only [add_zero]
    rw [← mul_assoc, hεε, one_mul]

/-- The bridge for four-corner rims. -/
theorem rupert_rim4 (c0 c1 c2 c3 : Fin 7) (P0 P1 P2 P3 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        ((quad P0 P1 P2 P3 j).sub (quad P0 P1 P2 P3 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → ∀ i : ZMod 4,
      ST σ u v ((quad P0 P1 P2 P3 (i + 1)).sub (quad P0 P1 P2 P3 i))
        ((F.ptC j').sub (quad P0 P1 P2 P3 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q4 fun i => F.GG (quad P0 P1 P2 P3 i) u +
      s * F.GG (quad P0 P1 P2 P3 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quad c0 c1 c2 c3 i) = quad P0 P1 P2 P3 i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, e0, e1, e2, e3]
  refine F.rupert_rim (k := 4) (by norm_num) (quad c0 c1 c2 c3) σ hσ u v hu ?_ ?_ Q4 Q4_open
    (fun z a ha => Q4_smul ha) (fun z a => Q4_shift a) ?_ (fun z hz hq => Q4_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quad_0, h])
    · exact fun h => hj' 1 (by simp [quad_1, h])
    · exact fun h => hj' 2 (by simp [quad_2, h])
    · exact fun h => hj' 3 (by simp [quad_3, h])
  · simpa only [hc] using hQe

/-- The bridge for five-corner rims. -/
theorem rupert_rim5 (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 → ∀ i : ZMod 5,
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((F.ptC j').sub (quint P0 P1 P2 P3 P4 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5c fun i => F.GG (quint P0 P1 P2 P3 P4 i) u +
      s * F.GG (quint P0 P1 P2 P3 P4 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quint c0 c1 c2 c3 c4 i) = quint P0 P1 P2 P3 P4 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, e0, e1, e2, e3, e4]
  refine F.rupert_rim (k := 5) (by norm_num) (quint c0 c1 c2 c3 c4) σ hσ u v hu ?_ ?_ Q5c
    Q5c_open (fun z a ha => Q5c_smul ha) (fun z a => Q5c_shift a) ?_
    (fun z hz hq => Q5c_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quint_0, h])
    · exact fun h => hj' 1 (by simp [quint_1, h])
    · exact fun h => hj' 2 (by simp [quint_2, h])
    · exact fun h => hj' 3 (by simp [quint_3, h])
    · exact fun h => hj' 4 (by simp [quint_4, h])
  · simpa only [hc] using hQe

/-- The bridge for five-corner rims, with the five-pairs condition `Q5p`. -/
theorem rupert_rim5p (c0 c1 c2 c3 c4 : Fin 7) (P0 P1 P2 P3 P4 : C3)
    (e0 : F.ptC c0 = P0) (e1 : F.ptC c1 = P1) (e2 : F.ptC c2 = P2) (e3 : F.ptC c3 = P3)
    (e4 : F.ptC c4 = P4)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u v : C3) (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0)
    (hcyc : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((quint P0 P1 P2 P3 P4 j).sub (quint P0 P1 P2 P3 P4 i)))
    (hrest : ∀ j' : Fin 7, j' ≠ c0 → j' ≠ c1 → j' ≠ c2 → j' ≠ c3 → j' ≠ c4 → ∀ i : ZMod 5,
      ST σ u v ((quint P0 P1 P2 P3 P4 (i + 1)).sub (quint P0 P1 P2 P3 P4 i))
        ((F.ptC j').sub (quint P0 P1 P2 P3 P4 i)))
    (hQe : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q5p fun i => F.GG (quint P0 P1 P2 P3 P4 i) u +
      s * F.GG (quint P0 P1 P2 P3 P4 i) v) :
    IsRupert (Finset.univ.image x) := by
  have hc : ∀ i, F.ptC (quint c0 c1 c2 c3 c4 i) = quint P0 P1 P2 P3 P4 i := by
    intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      simp [quint_0, quint_1, quint_2, quint_3, quint_4, e0, e1, e2, e3, e4]
  refine F.rupert_rim (k := 5) (by norm_num) (quint c0 c1 c2 c3 c4) σ hσ u v hu ?_ ?_ Q5p
    Q5p_open (fun z a ha => Q5p_smul ha) (fun z a => Q5p_shift a) ?_
    (fun z hz hq => Q5p_unimodal hz hq)
  · intro i j h1 h2
    simp only [hc]
    exact hcyc i j h1 h2
  · intro j' hj' i
    simp only [hc]
    refine hrest j' ?_ ?_ ?_ ?_ ?_ i
    · exact fun h => hj' 0 (by simp [quint_0, h])
    · exact fun h => hj' 1 (by simp [quint_1, h])
    · exact fun h => hj' 2 (by simp [quint_2, h])
    · exact fun h => hj' 3 (by simp [quint_3, h])
    · exact fun h => hj' 4 (by simp [quint_4, h])
  · simpa only [hc] using hQe

end Frame7

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- The frame-coordinates of the seven points of type 18:
`v = 0`, `m1+ = (t+, 0, h+)`, `m2+ = (0, s+, k+)`, `m2- = (0, s-, -k-)`, `xa = (1, 0, 0)`,
`xb = (0, 1, 0)`, `m1- = (t-, 0, -h-)` (labels `0, 1, 2, 3, 4, 5, 6`). -/
noncomputable def pt (S : Shape18) : Fin 7 → C3 := ![⟨S.tp, 0, S.hp⟩, ⟨0, S.sp, S.kp⟩,
  ⟨0, S.sm, -S.km⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 0⟩, ⟨S.tm, 0, -S.hm⟩]

/-- The `Frame7` of a type-18 frame. -/
noncomputable def toFrame7 : Frame7 x where
  base := x 5
  u1 := x 3 - x 5
  u2 := x 4 - x 5
  e := F.e
  indep := F.indep
  inner_u1_e := F.inner_u1_e
  inner_u2_e := F.inner_u2_e
  ptC := pt F.S
  x_eq := by
    intro j
    fin_cases j
    · show x 0 = x 5 + F.S.tp • (x 3 - x 5) + 0 • (x 4 - x 5) + F.S.hp • F.e
      rw [F.x0_eq]; simp
    · show x 1 = x 5 + 0 • (x 3 - x 5) + F.S.sp • (x 4 - x 5) + F.S.kp • F.e
      rw [F.x1_eq]; simp
    · show x 2 = x 5 + 0 • (x 3 - x 5) + F.S.sm • (x 4 - x 5) + (-F.S.km) • F.e
      rw [F.x2_eq]; simp [sub_eq_add_neg]
    · show x 3 = x 5 + (1:ℝ) • (x 3 - x 5) + 0 • (x 4 - x 5) + 0 • F.e
      simp
    · show x 4 = x 5 + 0 • (x 3 - x 5) + (1:ℝ) • (x 4 - x 5) + 0 • F.e
      simp
    · show x 5 = x 5 + 0 • (x 3 - x 5) + 0 • (x 4 - x 5) + 0 • F.e
      simp
    · show x 6 = x 5 + F.S.tm • (x 3 - x 5) + 0 • (x 4 - x 5) + (-F.S.hm) • F.e
      rw [F.x6_eq]; simp [sub_eq_add_neg]

end Frame18

end Minimality.CaseC18

end
