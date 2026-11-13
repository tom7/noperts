module

public import Minimality.Type29Cert
public import Minimality.Type21F2Weak

@[expose] public section

/-!
# Type 29: ties in the pair tests (`FEWER-FACES-PROOFS.md` §28, §18.4, §21.15)

* `pair_core`: **Corollary 13.3 with ties** for the pairs of K3a / K4a.  Two four-corner rims
  `Q₂` (the partner, at `v`) and `Q₁` (at `u`) whose diagonals cross along both views, with the
  signs `det(u, ·) det(v, ·) > 0` for `Q₁` and `< 0` for `Q₂`.  With at most one tie at each of
  `u`, `v` and no tie at one of them, either `Q₂` is robustly unimodal, or `Q₁` is and
  `⟪u, v⟫ ≤ 0` (the partner is preferred, so `Q₁`'s certificate carries the closed fact, as
  type 21's `VQuadCone`).
* `robust_of_view_nhds`: a rim with at most one tie is robustly unimodal if the unimodality
  criterion holds for all views near the given one (the tie is broken both ways by perturbing
  the view).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Ties at a multiple of a view are ties at the view. -/
theorem OneTieAt.of_smul {K : Finset ℝ³} {w : ℝ³} (h : OneTieAt K w) {c : ℝ} (hc : c ≠ 0) :
    OneTieAt K (c • w) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  simp only [real_inner_smul_right] at e1 e2
  exact h s hs t ht s' hs' t' ht' hst hst' (mul_left_cancel₀ hc e1) (mul_left_cancel₀ hc e2)

theorem NoTieAt.of_smul {K : Finset ℝ³} {w : ℝ³} (h : NoTieAt K w) {c : ℝ} (hc : c ≠ 0) :
    NoTieAt K (c • w) := by
  intro s hs t ht hst e
  simp only [real_inner_smul_right] at e
  exact h s hs t ht hst (mul_left_cancel₀ hc e)

theorem OneTieAt.of_eq_smul {K : Finset ℝ³} {w u : ℝ³} (h : OneTieAt K w) {c : ℝ}
    (e : u = c • w) (hc : c ≠ 0) : OneTieAt K u := e ▸ h.of_smul hc

theorem NoTieAt.of_eq_smul {K : Finset ℝ³} {w u : ℝ³} (h : NoTieAt K w) {c : ℝ}
    (e : u = c • w) (hc : c ≠ 0) : NoTieAt K u := e ▸ h.of_smul hc

theorem OneTieAt.neg {K : Finset ℝ³} {w : ℝ³} (h : OneTieAt K w) : OneTieAt K (-w) :=
  h.of_eq_smul (neg_one_smul ℝ w).symm (by norm_num)

theorem NoTieAt.neg {K : Finset ℝ³} {w : ℝ³} (h : NoTieAt K w) : NoTieAt K (-w) :=
  h.of_eq_smul (neg_one_smul ℝ w).symm (by norm_num)

variable {x : Fin 7 → ℝ³}

/-! ### The tie hypothesis of the covers -/

/-- The combined pairs with a tie at both views allowed when the two tied pairs are independent
(`IndepF`; the sign-product route `pair_core_ie`, `shared_core_ie`): `P14`, `P11`, `{Xa, T2}`,
`P13`, tier (A) `(V, Y)`, its `σ`-image `(T2, Y')` and tier (B2) `(W, Z)`.  (`{Y1, Y2}` needs no
such clause: `cert_k3_Yp` uses only one tie at each view.) -/
def pairViewsGO29 : Finset (View29 × View29) :=
  {(.inr 0, .inr 1), (.inr 0, .inr 3), (.inl (0, 5), .inr 1), (.inr 3, .inr 1),
    (.inr 2, .inl (3, 5)), (.inr 1, .inl (3, 4)), (.inl (0, 3), .inr 6)}

/-- **The ties allowed in the covers** (the codimension-2 hypothesis): at most one tied pair at
each nonzero named view; and for the pairs `pairViewsGO29` the tied pairs at the two views (one at
each, if both views have a tie) are independent (`IndepF`; a second tie that is dependent would be
a second equation on the shape). -/
structure Tie29 (x : Fin 7 → ℝ³) : Prop where
  one : OneTie29 x
  indep : ∀ p ∈ pairViewsGO29, view29 x p.1 ≠ 0 → view29 x p.2 ≠ 0 →
    IndepF (univ.image x) (view29 x p.1) (view29 x p.2)

theorem Tie29.edge {x : Fin 7 → ℝ³} (hx : Function.Injective x) (ht : Tie29 x) {i j : Fin 7}
    (hij : i ≠ j) : OneTieAt (univ.image x) (x j - x i) :=
  ht.one (.inl (i, j)) (sub_ne_zero.mpr (hx.ne hij.symm))

variable {x : Fin 7 → ℝ³}

end Minimality

end
