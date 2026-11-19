module

public import Minimality.WallCell
public import Minimality.RimCellClosed

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.H21

variable {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Depth of a frame point `p + sum_e y_e v_e` (orthogonal `v_e`) at the wall view `v J + t v M`:
`<p,w> + s_J (y_J + lam y_M)` where `lam s_J = t s_M`. -/
theorem wo_depth {k : ℕ} (p : ℝ³) (v : Fin k → ℝ³) (hv : ∀ a b, a ≠ b → ⟪v a, v b⟫ = 0)
    (y : Fin k → ℝ) (J M : Fin k) (hJM : J ≠ M) (t lam : ℝ)
    (hl : t * ⟪v M, v M⟫ = lam * ⟪v J, v J⟫) :
    ⟪p + ∑ e, y e • v e, v J + t • v M⟫ =
      ⟪p, v J + t • v M⟫ + ⟪v J, v J⟫ * (y J + lam * y M) := by
  rw [inner_add_left, sum_inner]
  have key : ∀ e, ⟪y e • v e, v J + t • v M⟫ =
      y e * (⟪v e, v J⟫ + t * ⟪v e, v M⟫) := by
    intro e; rw [inner_smul_left, inner_add_right, inner_smul_right]; simp
  simp_rw [key]
  rw [Fintype.sum_eq_add J M hJM]
  · have h1 : ⟪v M, v J⟫ = 0 := hv M J hJM.symm
    have h2 : ⟪v J, v M⟫ = 0 := hv J M hJM
    rw [h1, h2]
    linear_combination y M * hl
  · intro e ⟨h1, h2⟩
    rw [hv e J h1, hv e M h2]; ring

/-- A `RobUni` profile stays `RobUni` under a positive affine map. -/
theorem robUni_affine {k : ℕ} {d : ZMod k → ℝ} (hd : RobUni d) {s : ℝ} (hs : 0 < s) (C : ℝ) :
    RobUni (fun i => C + s * d i) := by
  intro B b c e hb hbc hce hek ⟨h1, h2, h3, h4⟩
  refine hd B b c e hb hbc hce hek ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **Lemma WO (wall orthocentre leaf), closed-cell form.**  Rim `c` of a cell `(U, Dn)` with
`k >= 4` corners, frame `x i = p + sum_e y i e v_e` with pairwise orthogonal `v_e`, a wall point
`w = v J + t v M` of the closed cell (`CellLe`), a strict cell point `a`.  If the profile
`d_i = y (c i) J + lam y (c i) M` (`lam s_J = t s_M`; on the wall rim the entry of the corner `K`
is `0`) is robustly unimodal (e.g. strictly unimodal with distinct values, `s0x_robUni_of_uni`),
then Rupert.  The depths at `w` are `<p,w> + s_J d_i`, so `isRupert_of_closedCell` applies at `w`
itself (no move to an interior point is needed: weak facings are allowed there). -/
theorem isRupert_of_wallOrtho {k kk : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    (p : ℝ³) (v : Fin kk → ℝ³) (hv : ∀ a b, a ≠ b → ⟪v a, v b⟫ = 0)
    (y : Fin n → Fin kk → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e)
    (J M : Fin kk) (hJM : J ≠ M) (hJpos : 0 < ⟪v J, v J⟫) (t lam : ℝ)
    (hl : t * ⟪v M, v M⟫ = lam * ⟪v J, v J⟫)
    (hw : CellLe F U Dn (v J + t • v M))
    (hd : RobUni (fun i : ZMod k => y (c i) J + lam * y (c i) M)) :
    IsRupert (Finset.univ.image x) := by
  refine isRupert_of_closedCell hk F hx hc hcyc ha hw ?_
  have := robUni_affine hd hJpos ⟪p, v J + t • v M⟫
  convert this using 2 with i
  rw [hxy, wo_depth p v hv (y (c i)) J M hJM t lam hl]

/-- WO with a strictly unimodal profile. -/
theorem isRupert_of_wallOrtho_uni {k kk : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    (p : ℝ³) (v : Fin kk → ℝ³) (hv : ∀ a b, a ≠ b → ⟪v a, v b⟫ = 0)
    (y : Fin n → Fin kk → ℝ) (hxy : ∀ i, x i = p + ∑ e, y i e • v e)
    (J M : Fin kk) (hJM : J ≠ M) (hJpos : 0 < ⟪v J, v J⟫) (t lam : ℝ)
    (hl : t * ⟪v M, v M⟫ = lam * ⟪v J, v J⟫)
    (hw : CellLe F U Dn (v J + t • v M))
    (hd : Uni (fun i : ZMod k => y (c i) J + lam * y (c i) M)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_wallOrtho hk F hx hc hcyc ha p v hv y hxy J M hJM hJpos t lam hl hw
    (s0x_robUni_of_uni hd)

end Minimality.H21

