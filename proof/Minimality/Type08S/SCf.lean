module

public import Minimality.Type08S.SCe

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- Class (c) package: the top vertex (the higher of `r`, `g` on the screen) projects to the open
chord `x̄ f̄` of the `F`-plane, `f` lies on the other side of its depth from `x`, and the
remaining corner of the closing is on the side it must be (robustness, Lemma 2.1(c)). -/
def ClassC5 (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  (Yr < Yg ∧ 0 < Xg ∧ Xg < L ∧ (zg - zx) * L = (zf - zx) * Xg ∧ (zx - zg) * (zf - zg) < 0 ∧
      (zx - zg) * (zr - zg) < 0) ∨
  (Yg < Yr ∧ 0 < Xr ∧ Xr < L ∧ (zr - zx) * L = (zf - zx) * Xr ∧ (zx - zr) * (zf - zr) < 0 ∧
      0 < (zx - zr) * (zg - zr))

/-- **Corollary SC-c for the five-corner closing `(x', f, r, g, x)`**, any additional vertices `E`. -/
theorem lemmaSCc (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassC5 L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact lemmaSCc_g hF o E hL hzx hcr hYr h1 hcg h2 h3 h4 h5 h6 hE
  · exact lemmaSCc_r hF o E hL hzx hcr hYr hYg h1 hcg h2 h3 h4 h5 h6 hE

section
variable {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}

/-- **Theorem 08.SC-c for N2's `K_c`, frame form.**  `x' = a'`, `x = c` (over `q`), `f = b`,
`r = c'`, `g = b'`; `d` is the middle over the `F`-side (strictly above the line `a' b`), `a`
lies strictly inside the screen triangle `(a', b, b')`. -/
theorem sc08_N2_Kc (hF : Fr e1 e2 e3) (o : ℝ³)
    {Xd zd Xa Ya za : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassC5 L zx zf Xr Yr zr Xg Yg zg)
    (hXd0 : 0 < Xd) (hXdL : Xd < L) (hd : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd))
    (hT : 0 < L * Yg) (hc1 : 0 < L * Ya) (hc2 : 0 < (Xg - L) * Ya - Yg * (Xa - L))
    (hc3 : 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 Xa Ya za}) := by
  refine lemmaSCc (σ := σ) hF o _ hL hzx hcr hYr hYg hcg hc (Eventually.of_forall fun s y hy => ?_)
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

/-- **Theorem 08.SC-c for T4's `K_b`, frame form.**  `x' = 2`, `x = b`, `f = c`, `r = b'`,
`g = c'`; `a'` is the middle over the `F`-side (strictly above the line `2 c`), `a` the lower
middle over the `G`-side, at `λ (Xg, Yg)`, strictly below the chord from `x` to `g`. -/
theorem sc08_T4_Kb (hF : Fr e1 e2 e3) (o : ℝ³)
    {Xd zd lam za : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : ClassC5 L zx zf Xr Yr zr Xg Yg zg)
    (hXd0 : 0 < Xd) (hXdL : Xd < L) (hd : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd))
    (hl0 : 0 < lam) (hl1 : lam < 1) (hab : σ * (za - ((1 - lam) * zx + lam * zg)) < 0) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za}) := by
  refine lemmaSCc (σ := σ) hF o _ hL hzx hcr hYr hYg hcg hc ?_
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

end

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.sc08_N2_Kc
#print axioms Minimality.Type08Sp.sc08_T4_Kb
