module

public import Minimality.ArcLemma

@[expose] public section


/-!
# Proposition 33.3 (type 24, the arc of 016)
(`FEWER-FACES-PROOFS.md` §33; the identity is `ref/Prop53.lean`)

Cap frame of cu17: `X0 = e_a`, `X6 = e_c`, `X3 = a3 e_a + b3 e_b + c3 e_c`,
`X5 = a5 e_a + b5 e_b + c5 e_c`, the face 016 in the plane `b = 0` (spanned by `e_a`, `e_c`, so
its normal is `e_a × e_c`).  In Lean the metric is the Euclidean inner product of the
realization: `e_a, e_b, e_c : ℝ³` are arbitrary, `G_ij = ⟪e_i, e_j⟫`.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **`Prop53.lean` over `ℝ`** (`prop53_identity`, proved by `ring`; there over `ℚ`). -/
theorem prop53_identity_real (a3 b3 c3 a5 b5 c5 gaa gbb gcc gab gac gbc W A F D N : ℝ)
    (hW : W = b3 + c3 - 1) (hA : A = a5 + b5 - 1) (hF : F = a3 * c5 - W * A)
    (hD : D = (a3 + c3) - (a5 + c5))
    (hN : N = a3*a5*b3 + a3*a5*c3 - a3*a5 + a3*b3*b5 - a3*b3 + a3*b5*c3 - a3*b5 + a3*c3*c5
      - a3*c3 - a3*c5^2 + a3 - a5^2*b3 - a5^2*c3 + a5^2 - a5*b3*b5 + a5*b3 - a5*b5*c3
      + a5*b5 + a5*c3 - a5) :
    let bil := fun (x1 x2 x3 y1 y2 y3 : ℝ) =>
      gaa * x1 * y1 + gbb * x2 * y2 + gcc * x3 * y3 + gab * (x1 * y2 + x2 * y1) +
        gac * (x1 * y3 + x3 * y1) + gbc * (x2 * y3 + x3 * y2)
    c5 * A * D * bil 1 0 (-1) a3 0 W - N * bil 1 0 (-1) A 0 c5
      - F * bil (a3 - a5) (b3 - b5) (c3 - c5) A 0 c5 =
      -(b3 - b5) * F * A * gab - (a5 + b5 + c5 - 1) * F * D * gac - (b3 - b5) * F * c5 * gbc := by
  intro bil
  subst hF hN hW hA hD
  simp only [bil]
  ring

/-- **The identity of Proposition 33.3 as inner products of a realization**
(`prop53_identity_real` with `gij = ⟪e_i, e_j⟫`, the three rows written as inner products with
`d_a = a3 e_a + W e_c`, `d_b = A e_a + c5 e_c`). -/
theorem prop33_3_inner_identity (ea eb ec X3 X5 : ℝ³) (a3 b3 c3 a5 b5 c5 W A F D N : ℝ)
    (hX3 : X3 = a3 • ea + b3 • eb + c3 • ec) (hX5 : X5 = a5 • ea + b5 • eb + c5 • ec)
    (hW : W = b3 + c3 - 1) (hA : A = a5 + b5 - 1) (hF : F = a3 * c5 - W * A)
    (hD : D = (a3 + c3) - (a5 + c5))
    (hN : N = a3*a5*b3 + a3*a5*c3 - a3*a5 + a3*b3*b5 - a3*b3 + a3*b5*c3 - a3*b5 + a3*c3*c5
      - a3*c3 - a3*c5^2 + a3 - a5^2*b3 - a5^2*c3 + a5^2 - a5*b3*b5 + a5*b3 - a5*b5*c3
      + a5*b5 + a5*c3 - a5) :
    c5 * A * D * ⟪ea - ec, a3 • ea + W • ec⟫ - N * ⟪ea - ec, A • ea + c5 • ec⟫
      - F * ⟪X3 - X5, A • ea + c5 • ec⟫ =
      -(b3 - b5) * F * A * ⟪ea, eb⟫ - (a5 + b5 + c5 - 1) * F * D * ⟪ea, ec⟫
        - (b3 - b5) * F * c5 * ⟪eb, ec⟫ := by
  have c1 : ⟪eb, ea⟫ = ⟪ea, eb⟫ := real_inner_comm _ _
  have c2 : ⟪ec, ea⟫ = ⟪ea, ec⟫ := real_inner_comm _ _
  have c3' : ⟪ec, eb⟫ = ⟪eb, ec⟫ := real_inner_comm _ _
  subst hX3 hX5 hF hN hW hA hD
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, c1, c2, c3']
  ring

/-- **Proposition 33.3 (type 24, the arc of 016, closed obtuse octant).**
`Ar` is the arc of 016's circle with corner polygon `(0, 5, 3, 6)` (so `Ar.x = (X0, X5, X3, X6)`,
front diagonal `{0, 3}`, back `{5, 6}`, middle `X1 ∈ Ar.M` over the chord `06`), ends
`d_a = (a3, 0, W) = 016 ∩ 236`, `d_b = (A, 0, c5) = 016 ∩ 025`; its hypothesis (a) (non-coplanar,
convex, everything else inside, the middle over the chord) is exactly the determinant
inequalities at `d_a`, `d_b` in the fields of `Ar`.  Hypotheses (b): `a3, W, A, c5 > 0`,
`F < 0`, `D > 0`, `b3 > b5`, `a5 + b5 + c5 ≥ 1`, `N ≤ 0`; closed obtuse octant
`G_ab, G_ac, G_bc ≤ 0`; (E2): no persistent HDN on the arc.
Then `V` is Rupert, except where the rows `(z0 - z6)(d_a)`, `(z3 - z5)(d_b)` (and
`(z0 - z6)(d_b)` if `N < 0`) vanish and the `G_ij` with nonzero coefficient vanish
(`G_ab = G_bc = 0`, and `G_ac = 0` if `a5 + b5 + c5 > 1`). -/
theorem prop33_3 {V : Finset ℝ³} (ea eb ec X3 X5 : ℝ³) (a3 b3 c3 a5 b5 c5 W A F D N : ℝ)
    (hX3 : X3 = a3 • ea + b3 • eb + c3 • ec) (hX5 : X5 = a5 • ea + b5 • eb + c5 • ec)
    (hW : W = b3 + c3 - 1) (hA : A = a5 + b5 - 1) (hF : F = a3 * c5 - W * A)
    (hD : D = (a3 + c3) - (a5 + c5))
    (hN : N = a3*a5*b3 + a3*a5*c3 - a3*a5 + a3*b3*b5 - a3*b3 + a3*b5*c3 - a3*b5 + a3*c3*c5
      - a3*c3 - a3*c5^2 + a3 - a5^2*b3 - a5^2*c3 + a5^2 - a5*b3*b5 + a5*b3 - a5*b5*c3
      + a5*b5 + a5*c3 - a5)
    -- (a): the arc of 016
    (Ar : Arc V) (hx : Ar.x = ![ea, X5, X3, ec])
    (hda : Ar.da = a3 • ea + W • ec) (hdb : Ar.db = A • ea + c5 • ec)
    (hn : Ar.n = cross ea ec)
    -- (b)
    (ha3 : 0 < a3) (hW0 : 0 < W) (hA0 : 0 < A) (hc5 : 0 < c5)
    (hF0 : F < 0) (hD0 : 0 < D) (hb : b5 < b3) (hs : 1 ≤ a5 + b5 + c5) (hN0 : N ≤ 0)
    -- closed obtuse octant
    (hab : ⟪ea, eb⟫ ≤ 0) (hac : ⟪ea, ec⟫ ≤ 0) (hbc : ⟪eb, ec⟫ ≤ 0)
    -- (E2)
    (hnd : Ar.NoHDNNearEnds) :
    IsRupert V ∨
      (⟪ea - ec, a3 • ea + W • ec⟫ = 0 ∧ ⟪X3 - X5, A • ea + c5 • ec⟫ = 0 ∧
        (N < 0 → ⟪ea - ec, A • ea + c5 • ec⟫ = 0) ∧
        ⟪ea, eb⟫ = 0 ∧ ⟪eb, ec⟫ = 0 ∧ (1 < a5 + b5 + c5 → ⟪ea, ec⟫ = 0)) := by
  have hID := prop33_3_inner_identity ea eb ec X3 X5 a3 b3 c3 a5 b5 c5 W A F D N hX3 hX5 hW hA hF
    hD hN
  have r1 : Ar.row (0, 1, 0) = ⟪ea - ec, a3 • ea + W • ec⟫ := by
    unfold Arc.row; rw [hx, hda]; rfl
  have r2 : Ar.row (0, 1, 1) = ⟪ea - ec, A • ea + c5 • ec⟫ := by
    unfold Arc.row; rw [hx, hdb]; rfl
  have r3 : Ar.row (1, 0, 1) = ⟪X3 - X5, A • ea + c5 • ec⟫ := by
    unfold Arc.row; rw [hx, hdb]; rfl
  have hDpos : 0 < c5 * A * D := by positivity
  have hb' : 0 < b3 - b5 := sub_pos.mpr hb
  have hF' : 0 < -F := neg_pos.mpr hF0
  have hN' : 0 ≤ -N := neg_nonneg.mpr hN0
  have hs' : 0 ≤ a5 + b5 + c5 - 1 := by linarith
  let lam : Unit → Fin 2 × Fin 2 × Fin 2 → ℝ := fun _ r =>
    if r = (0, 1, 0) then c5 * A * D else if r = (0, 1, 1) then -N else
      if r = (1, 0, 1) then -F else 0
  let nu : Fin 3 → ℝ := ![(b3 - b5) * -F * A, (a5 + b5 + c5 - 1) * -F * D, (b3 - b5) * -F * c5]
  let w : Fin 3 → ℝ := ![-⟪ea, eb⟫, -⟪ea, ec⟫, -⟪eb, ec⟫]
  have hlam : ∀ k r, 0 ≤ lam k r := by
    intro k r
    simp only [lam]
    split_ifs <;> first | positivity | linarith
  have hlam0 : 0 < ∑ k, ∑ r, lam k r := by
    simp [lam, Fintype.sum_prod_type, Fin.sum_univ_two]
    nlinarith [hF', hN', hDpos]
  have hnu : ∀ t, 0 ≤ nu t := by
    intro t; fin_cases t
    · exact (mul_pos (mul_pos hb' hF') hA0).le
    · exact mul_nonneg (mul_nonneg hs' hF'.le) hD0.le
    · exact (mul_pos (mul_pos hb' hF') hc5).le
  have hw : ∀ t, 0 ≤ w t := by
    intro t; fin_cases t
    · exact neg_nonneg.mpr hab
    · exact neg_nonneg.mpr hac
    · exact neg_nonneg.mpr hbc
  have hcert : ∑ k : Unit, ∑ r, lam k r * ((fun _ : Unit => Ar) k).row r = -∑ t, nu t * w t := by
    simp only [lam, nu, w, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Finset.univ_unique, Finset.sum_singleton, r1, r2, r3]
    simp
    linarith [hID]
  rcases arc_certificate (fun _ : Unit => Ar) lam nu w hlam hlam0 hnu hw hcert
    (fun _ _ => hnd) with h | ⟨hr, hv⟩
  · exact Or.inl h
  · right
    have e1 := hr () (0, 1, 0) (by simp [lam, hDpos])
    have e3 := hr () (1, 0, 1) (by simp [lam, hF'])
    rw [r1] at e1
    rw [r3] at e3
    have e2 : N < 0 → ⟪ea - ec, A • ea + c5 • ec⟫ = 0 := fun hN1 => by
      rw [← r2]; exact hr () (0, 1, 1) (by simp [lam]; linarith)
    have f1 := hv 0 (show 0 < (b3 - b5) * -F * A from mul_pos (mul_pos hb' hF') hA0)
    have f3 := hv 2 (show 0 < (b3 - b5) * -F * c5 from mul_pos (mul_pos hb' hF') hc5)
    have f2 : 1 < a5 + b5 + c5 → ⟪ea, ec⟫ = 0 := fun h1 => by
      have := hv 1 (show 0 < (a5 + b5 + c5 - 1) * -F * D from mul_pos (mul_pos (by linarith) hF') hD0)
      simpa [w] using this
    simp [w] at f1 f3
    exact ⟨e1, e3, e2, f1, f3, f2⟩

end Minimality
