module

public import Minimality.Type08S.P2SCX1
public import Minimality.Type08S.P2SCX2
public import Minimality.Type08S.P2SCX3
public import Minimality.Type08S.P2SCX4
public import Minimality.Type08S.P2SCX5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma SC-X (package 8): chord-end HDN at the apex `x`, frame form (sp08f §3)

`ClassX5` is the frame-coordinate form of "the persistent HDN's foot is `x̄`" (the HDN classification, package P-G,
is taken as this hypothesis).  Five sub-cases: `x̄` in the open top side; `x̄ = t̄` for a top vertex `g`, a top
vertex `r`, the near end `g` or the far end `r` of a top side.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Class SC-X** (chord end at the apex), frame form.  The last component of each clause is robustness
(`f` on one side / opposite sides of `z_x`), and `x ∉ Π'` where needed (`hPi`-clauses). -/
def ClassX5 (σ L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  -- `x̄` in the open top side
  (Yg = Yr ∧ Xg < 0 ∧ 0 < Xr ∧ (zg - zx) * Xr = (zr - zx) * Xg ∧ 0 < (zf - zx) * (zr - zx) ∧
      0 < σ * ((zr - zx) * L - (zf - zx) * Xr)) ∨
  -- top vertex `g` over `x̄`
  (Yr < Yg ∧ Xg = 0 ∧ zg = zx ∧ 0 < (zf - zx) * (zr - zx)) ∨
  -- top vertex `r` over `x̄`
  (Yg < Yr ∧ Xr = 0 ∧ zr = zx ∧ (zf - zx) * (zg - zx) < 0) ∨
  -- near end `g` of the top side over `x̄`
  (Yg = Yr ∧ Xg = 0 ∧ zg = zx ∧ 0 < (zf - zx) * (zr - zx) ∧
      0 < σ * ((zr - zx) * L - (zf - zx) * Xr)) ∨
  -- far end `r` of the top side over `x̄`
  (Yg = Yr ∧ Xr = 0 ∧ zr = zx ∧ (zf - zx) * (zg - zx) < 0)

/-- **Lemma SC-X.** -/
theorem lemmaSCX (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassX5 σ L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩
  · exact lemmaSCX_open hF o E hL hzx hYr h1 h2 h3 h4 h5 h6 hE
  · exact lemmaSCX_gvert hF o E hL hzx hcr hYr h1 hcg h2 h3 h4 hE
  · exact lemmaSCX_rvert hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 hE
  · exact lemmaSCX_gend hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 h5 hE
  · exact lemmaSCX_rend hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 hE

section
variable {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}

/-- **Theorem 08.SC-c for N2's `K_c`, frame form.**  `x' = a'`, `x = c` (over `q`), `f = b`,
`r = c'`, `g = b'`; `d` is the middle over the `F`-side (strictly above the line `a' b`), `a`
lies strictly inside the screen triangle `(a', b, b')`. -/
theorem sc08_N2_Kx (hF : Fr e1 e2 e3) (o : ℝ³)
    {Xd zd Xa Ya za : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassX5 σ L zx zf Xr Yr zr Xg Yg zg)
    (hXd0 : 0 < Xd) (hXdL : Xd < L) (hd : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd))
    (hT : 0 < L * Yg) (hc1 : 0 < L * Ya) (hc2 : 0 < (Xg - L) * Ya - Yg * (Xa - L))
    (hc3 : 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 Xa Ya za}) := by
  refine lemmaSCX (σ := σ) hF o _ hL hzx hcr hYr hYg hcg hc (Eventually.of_forall fun s y hy => ?_)
  have m1 : o + pc e1 e2 e3 0 0 zp ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 Xa Ya za} := by simp [rim5]
  have m2 : o + pc e1 e2 e3 L 0 zf ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 Xa Ya za} := by simp [rim5]
  have m3 : o + pc e1 e2 e3 Xg Yg zg ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 Xa Ya za} := by simp [rim5]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact triCert_midF hF o _ hL hYg hXd0 hXdL m1 m2 m3 hd
  · exact triCert_int hF o _ m1 m2 m3 hT hc1 hc2 hc3

end

/-- **Theorem 08.SC-c for T4's `K_b`, frame form.**  `x' = 2`, `x = b`, `f = c`, `r = b'`,
`g = c'`; `a'` is the middle over the `F`-side (strictly above the line `2 c`), `a` the lower
middle over the `G`-side, at `λ (Xg, Yg)`, strictly below the chord from `x` to `g`. -/
theorem sc08_T4_Kx (hF : Fr e1 e2 e3) (o : ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd lam za : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassX5 σ L zx zf Xr Yr zr Xg Yg zg)
    (hXd0 : 0 < Xd) (hXdL : Xd < L) (hd : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd))
    (hl0 : 0 < lam) (hl1 : lam < 1) (hab : σ * (za - ((1 - lam) * zx + lam * zg)) < 0) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za}) := by
  refine lemmaSCX (σ := σ) hF o _ hL hzx hcr hYr hYg hcg hc ?_
  filter_upwards [ev_of_eq (P := fun s => Xg + s * Yg) Yg Xg 0 (Or.inl hYg) (fun s hs => by ring)]
    with s hs y hy
  have m1 : o + pc e1 e2 e3 0 0 zp ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za} := by simp [rim5]
  have m2 : o + pc e1 e2 e3 L 0 zf ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za} := by simp [rim5]
  have m3 : o + pc e1 e2 e3 Xg Yg zg ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za} := by simp [rim5]
  have m4 : o + pc e1 e2 e3 0 0 zx ∈ rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za} := by simp [rim5]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact triCert_midF hF o _ hL hYg hXd0 hXdL m1 m2 m3 hd
  · exact triCert_midG hF o _ hL hYg hl0 hl1 hs m3 m4 m2 hab

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.lemmaSCX
#print axioms Minimality.Type08Sp.sc08_N2_Kx
#print axioms Minimality.Type08Sp.sc08_T4_Kx
