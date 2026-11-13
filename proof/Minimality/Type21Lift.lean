module

public import Minimality.Type21Lemmas

@[expose] public section

/-!
# Type 21: Lemmas 2 and 3 of §9 (`FEWER-FACES-PROOFS.md` §9)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`,
`O = O6 = K − 2`, the cap `d` (`IsCap21`).

* **Lemma 2 of §9 (exact lift).**  (a) `isRupert_type21_hidden`: at a quad edge of an
  octahedron that is not bad, with one more point hidden at its view (`HiddenAt`), the
  reduced polygons are those of the octahedron and Lemma 9.3 applies (any octahedron and
  any point: it serves both `K − 2` and `K − 6`).  (b) A middle (`QuadMiddle`): the
  first cases of Lemma 3 below, through `isRupert_quad_edge_lift`.
* **Lemma 3 of §9 (the quad edges always lift).**  For each of the eight directions of
  the K-quad edges `05, 34, 06, 46` of `O6`, a quad edge of `O6` that is not bad gives a
  passage, off special positions (`GenPosTie`, `NoHDNEdges`):
  - `0 → 5` (`isRupert_type21_05`): `3` hidden forces `β < 1`, so `2` is a middle of
    `0256` (Lemma 3 (a));
  - `5 → 0` (`isRupert_type21_50`): `4` hidden forces `β > 1`, so `2` is the far end and
    `6` the middle; then `K`'s test is the test of the octahedron `O2 = K − 6`
    (`IsCap21.O2`), at the quad edge `5 → 0` of `O2`, which is not bad
    (`type21_far_not_bad_core`: the diagonal `0 – 2` of `0256`, the up face `2346`, the
    silhouette edge `23` of the faces `2346`, `235`, the side `36` of the shadow of `O`)
    (Lemma 3 (b));
  - `0 → 6` (`isRupert_type21_06`): `3` hidden forces `α < 1`, a middle;
  - `6 → 0` (`isRupert_type21_60`): `α < 1`, a middle; `α > 1`, `2` the far end and `5`
    the middle, `K_6`'s rim is the face `2346` (`isRupert_type21_60_far`, planar, hence
    unimodal; `1` is hidden because it is hidden in `O`) (Lemma 3 (c)); `α = 1` would
    make `25 ∥ 06`;
  - `4 → 3`, `3 → 4`, `4 → 6`, `6 → 4`: the images under `σ1 = (04)(35)`.
  The paper's route through Lemma 1 (the rim neighbours) to exclude the other hidden
  vertex is replaced by the facet inequality of the quad edge itself.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The relabellings of `K` used in this file. -/
theorem type21_set (a a' b b' c c' d : ℝ³) :
    insert d ({a, a', b', b, c, c'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert c' ({b', b, a, a', c, d} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert d ({a, a', c', c, b, b'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert d ({c', c, a, a', b, b'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} ∧
    insert d ({b, b', a, a', c, c'} : Finset ℝ³) = insert d {a, a', b, b', c, c'} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

/-! ### Lemma 2 (a): a hidden point -/

/-! ### Lemma 3: the quad edges `05` and `06` with the cap a middle -/

section Lift

variable {a a' b b' c c' d : ℝ³}

/-! ### Lemma 3 (c): `6 → 0` with the cap the far end; `K_6` is the face `2346` -/

theorem zmod4_three_sub_one : (3 : ZMod 4) - 1 = 2 := by decide
theorem zmod4_one_sub_one : (1 : ZMod 4) - 1 = 0 := by decide

/-! ### Lemma 3 (b): `5 → 0` with the cap the far end, through `O2 = K − 6` -/

/-- Two facets through `P Q` with a combination constant along `u`, negative at `r` and
`w`: the tests of `r` and `w` at the line `P Q` have one sign. -/
theorem det3_mul_pos_of_combo {f₁ f₂ : ℝ³ → ℝ} {N₁ N₂ : ℝ³}
    (h₁ : ∀ y z, f₁ y - f₁ z = ⟪N₁, y - z⟫) (h₂ : ∀ y z, f₂ y - f₂ z = ⟪N₂, y - z⟫)
    {P Q u : ℝ³} (h1P : f₁ P = 0) (h1Q : f₁ Q = 0) (h2P : f₂ P = 0) (h2Q : f₂ Q = 0)
    {α β : ℝ} (hαβ : α * ⟪N₁, u⟫ + β * ⟪N₂, u⟫ = 0) {r w : ℝ³}
    (hr : det3 (Q - P) (r - P) u ≠ 0) (hgr : α * f₁ r + β * f₂ r < 0)
    (hgw : α * f₁ w + β * f₂ w < 0) :
    0 < det3 (Q - P) (r - P) u * det3 (Q - P) (w - P) u := by
  have e : ∀ z, det3 (P - Q) (z - Q) u = -det3 (Q - P) (z - P) u := fun z => by
    simp only [det3_expand, PiLp.sub_apply]; ring
  rcases lt_or_gt_of_ne hr with hn | hp
  · have := det3_pos_of_combo h₁ h₂ h1Q h1P h2Q h2P hαβ (r := r) (w := w)
      (by rw [e]; linarith) hgr hgw
    rw [e] at this
    nlinarith
  · exact mul_pos hp (det3_pos_of_combo h₁ h₂ h1P h1Q h2P h2Q hαβ hp hgr hgw)

/-- **Step 3 of Lemma 3 (b), in reals.**  Depths `z` along `u = 0 − 5` (`uu = ⟪u, u⟫`): the
middle `6 = 0 + (2 − 0)/β + (α/β) u` lies above the diagonal `0 – 2` (`hc'`); the identity
`D (1 − 3) = S1 (6 − 3) − SA (2 − 3) + λ u` of the point `1` in the frame `6, 2, 3` on the
screen (`D = S_{623}`), applied to the face `2346` (`hf`: `fc = f(1) < 0`, `Nu = ⟪N, u⟫ > 0`,
the up face) and to the depth (`hz`); `D S1 > 0` (`1`, `6` on one side of the side `23` of
`S_K`) and `D SA > 0` (the side `36` of `S_O` against the far end `2`).  If `5 → 0` is not
bad in `O6`, it is not bad in `O2`. -/
theorem type21_far_not_bad_core {za za' zc zc' zd uu α β D S1 SA SB lam fc Nu : ℝ}
    (huu : 0 < uu) (hα : 0 < α) (hβ : 1 < β)
    (hc' : β * zc' = β * za + (zd - za) + α * uu)
    (hf : -(D * fc) = lam * Nu)
    (hz : S1 * zc' - SA * zd + SB * za' - D * zc = lam * uu)
    (hsum : S1 - SA + SB - D = 0)
    (hS1 : 0 < D * S1) (hSA : 0 < D * SA) (hfc : fc < 0) (hNu : 0 < Nu)
    (hgoodO : ¬ max za za' ≤ min zc zc') : ¬ max za za' ≤ min zc zd := by
  intro hbad
  rw [max_le_iff, le_min_iff, le_min_iff] at hbad
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbad
  have hD : D ≠ 0 := by rintro rfl; simp at hS1
  have hD2 : 0 < D * D := mul_self_pos.mpr hD
  have hlam : 0 < lam * D := by
    have e : (lam * D) * Nu = -(D * D * fc) := by linear_combination (-D) * hf
    have : 0 < (lam * D) * Nu := by rw [e]; nlinarith
    by_contra hneg
    push Not at hneg
    nlinarith
  have hza : za < zc' := by nlinarith [mul_pos hα huu]
  have hzc' : zc' < za' := by
    by_contra hcon
    push Not at hcon
    apply hgoodO
    rw [max_le_iff, le_min_iff, le_min_iff]
    exact ⟨⟨h1, hza.le⟩, h3, hcon⟩
  have key : D * D * (za' - zc) =
      lam * D * uu - D * S1 * (zc' - za') + D * SA * (zd - za') := by
    have hSB : SB = D - S1 + SA := by linarith
    rw [hSB] at hz
    linear_combination D * hz
  have : 0 < D * D * (za' - zc) := by
    rw [key]
    nlinarith [mul_pos hlam huu, mul_neg_of_pos_of_neg hS1 (sub_neg.mpr hzc'),
      mul_nonneg hSA.le (sub_nonneg.mpr h4)]
  nlinarith

/-! ### The images under `σ1 = (04)(35)` -/

end Lift

end Minimality

end
