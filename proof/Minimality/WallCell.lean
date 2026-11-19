module

public import Minimality.OrthoView2

@[expose] public section

/-!
# Wall cells at a diagonal metric (Lemmas WT and WD of p4/sat/WALLTHM24.md)

Frame form: `x i = p + sum_e y_i,e v_e` with pairwise orthogonal `v_e`, `|v_e|^2 = s_e` (diagonal
metric `G = diag s`).  A wall view is `g = sum r_e v_e` with `r_K = 0`; then
`<x i - x j, g> = sum_e (y_i,e - y_j,e) s_e r_e`.

* `wall_depth_tie` : for corners `J, M` and `g = v_J + t v_M`: `<v_J - v_M, g> = s_J - s_M t`.
* `isRupert_of_wallTie` (**Lemma WT**): wall rays `g = v_J + t2 v_M`, `g' = v_J + t1 v_M` in the closed
  cell (`CellLe`), `t1 s_M < s_J < t2 s_M`, `J`, `M` adjacent on the rim: Rupert.  A corollary of
  `isRupert_of_cevian` (CV1).
* `wall_depth_dom` / `isRupert_of_wallDom` (**Lemma WD**): front end `A = v_Ef`, back vertex
  `x = p + yA A + yB B + yK K`, `yA >= 1`, `yB > 0`, wall ray `rA A + rB B` (`rA >= 0 < rB`):
  `<x_Ef - x_Vb, g> < 0` for every diagonal metric; with a positive diagonal form at a second closure
  point (the front diagonal) Q4 gives Rupert.  The proof is not `dominance_pos` (the wall view
  has a zero covector entry `r_K = 0`, so no coordinatewise dominance): the sign comes from
  `s_A rA (1 - yA) - s_B rB yB < 0`.
-/

open scoped RealInnerProductSpace

namespace Minimality.H21

open Minimality.RimCell

variable {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Depth difference of two corners on the wall ray `v_J + t v_M` (orthogonal frame). -/
theorem wall_depth_tie (vJ vM : ℝ³) (h : ⟪vJ, vM⟫ = 0) (t : ℝ) :
    ⟪vJ - vM, vJ + t • vM⟫ = ⟪vJ, vJ⟫ - ⟪vM, vM⟫ * t := by
  have h' : ⟪vM, vJ⟫ = 0 := by rw [real_inner_comm]; exact h
  simp only [inner_sub_left, inner_add_right, inner_smul_right, h, h']
  ring

/-- **Lemma WT (wall tie).**  Rim `c` of a closed-cell certificate with adjacent corners
`x (c a) = p + v_J`, `x (c (a+1)) = p + v_M` (orthogonal `v_J, v_M`, `s = |v|^2`), and the two wall
rays `v_J + t2 v_M`, `v_J + t1 v_M` in the closed cell with `t1 s_M < s_J < t2 s_M`:
the form `z_J - z_M` has opposite strict signs at the two rays, so Q4 gives Rupert. -/
theorem isRupert_of_wallTie (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a₀ : ℝ³} (ha : CellAt F U Dn a₀) (a : ZMod 4)
    (p vJ vM : ℝ³) (hJM : ⟪vJ, vM⟫ = 0)
    (hJ : x (c a) = p + vJ) (hM : x (c (a + 1)) = p + vM) {t1 t2 : ℝ}
    (hg : CellLe F U Dn (vJ + t2 • vM)) (hg' : CellLe F U Dn (vJ + t1 • vM))
    (h1 : ⟪vM, vM⟫ * t1 < ⟪vJ, vJ⟫) (h2 : ⟪vJ, vJ⟫ < ⟪vM, vM⟫ * t2) :
    IsRupert (Finset.univ.image x) := by
  have e : x (c a) - x (c (a + 1)) = vJ - vM := by rw [hJ, hM]; abel
  refine isRupert_of_cevian F hx hc hcyc ha hg hg' a ?_ ?_
  · rw [e, wall_depth_tie _ _ hJM]; linarith
  · rw [e, wall_depth_tie _ _ hJM]; linarith

/-- Depth difference `z_Ef - z_Vb` on a wall ray `rA A + rB B` (with `K` orthogonal to both). -/
theorem wall_depth_dom (A B K : ℝ³) (hAB : ⟪A, B⟫ = 0) (hAK : ⟪A, K⟫ = 0) (hBK : ⟪B, K⟫ = 0)
    (yA yB yK rA rB : ℝ) :
    ⟪A - (yA • A + yB • B + yK • K), rA • A + rB • B⟫ =
      ⟪A, A⟫ * rA * (1 - yA) - ⟪B, B⟫ * rB * yB := by
  have h1 : ⟪B, A⟫ = 0 := by rw [real_inner_comm]; exact hAB
  have h2 : ⟪K, A⟫ = 0 := by rw [real_inner_comm]; exact hAK
  have h3 : ⟪K, B⟫ = 0 := by rw [real_inner_comm]; exact hBK
  simp only [inner_sub_left, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hAB, h1, h2, h3, RCLike.conj_to_real]
  ring

/-- Sign of `z_Ef - z_Vb` on the wall ray, for every diagonal metric `s_A, s_B > 0`:
`y_Vb[E_f] >= 1`, `y_Vb[E_b] > 0`, `r_B > 0`, `r_A >= 0`. -/
theorem wall_depth_dom_neg (A B K : ℝ³) (hAB : ⟪A, B⟫ = 0) (hAK : ⟪A, K⟫ = 0)
    (hBK : ⟪B, K⟫ = 0) (hA : 0 < ⟪A, A⟫) (hB : 0 < ⟪B, B⟫)
    {yA yB yK rA rB : ℝ} (hyA : 1 ≤ yA) (hyB : 0 < yB) (hrA : 0 ≤ rA) (hrB : 0 < rB) :
    ⟪A - (yA • A + yB • B + yK • K), rA • A + rB • B⟫ < 0 := by
  rw [wall_depth_dom A B K hAB hAK hBK]
  have : ⟪A, A⟫ * rA * (1 - yA) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA.le hrA) (by linarith)
  have : 0 < ⟪B, B⟫ * rB * yB := mul_pos (mul_pos hB hrB) hyB
  linarith

/-- **Lemma WD (wall dominance, metric-free).**  Rim `c`; `x (c i) = p + A` (front end `E_f`),
`x (c j) = p + yA A + yB B + yK K` (back v-vertex) with `(i, j)` a Q4 pair (a rim edge), wall ray
`g = rA A + rB B` in the closed cell, `yA >= 1`, `yB > 0`.  Then the form `z_Ef - z_Vb` is negative
at `g` at every diagonal metric (orthogonal `A, B, K` of any positive lengths); together with a
closure point `g'` where some Q4 form is positive (the front diagonal), Rupert. -/
theorem isRupert_of_wallDom (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod 4 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {a₀ g' : ℝ³} (ha : CellAt F U Dn a₀)
    (p A B K : ℝ³) (hAB : ⟪A, B⟫ = 0) (hAK : ⟪A, K⟫ = 0) (hBK : ⟪B, K⟫ = 0)
    (hA : 0 < ⟪A, A⟫) (hB : 0 < ⟪B, B⟫) {yA yB yK rA rB : ℝ} (i j : ZMod 4)
    (hij : (i, j) ∈ diagPairs) (hi : x (c i) = p + A) (hj : x (c j) = p + (yA • A + yB • B + yK • K))
    (hyA : 1 ≤ yA) (hyB : 0 < yB) (hrA : 0 ≤ rA) (hrB : 0 < rB)
    (hg : CellLe F U Dn (rA • A + rB • B)) (hg' : CellLe F U Dn g')
    (hp : ∃ q ∈ diagPairs, 0 < ⟪x (c q.1) - x (c q.2), g'⟫) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_of_closedCell_q4 F hx hc hcyc ha hg hg' ⟨(i, j), hij, ?_⟩ hp
  have e : x (c i) - x (c j) = A - (yA • A + yB • B + yK • K) := by rw [hi, hj]; abel
  rw [e]
  exact wall_depth_dom_neg A B K hAB hAK hBK hA hB hyA hyB hrA hrB

end Minimality.H21
