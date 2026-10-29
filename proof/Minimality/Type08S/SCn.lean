module

public import Minimality.Type08S.SCk
public import Minimality.Type08S.SCd

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

/-- **Class (d) package** (top side `r g` parallel to the F-side, `Yg = Yr`, `σ = 1`): the line
`z = σ0 + m X` through the projections of `r`, `g` crosses the open chord (`zp < σ0 < zx`, (D)), and
a level `z0` as in Corollary SC-d (case I or II). -/
def ClassD5 (zp L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ∃ σ0 m Xx z0 : ℝ, Yg = Yr ∧ Xg < Xr ∧ zp < zx ∧ σ0 = zg - m * Xg ∧ zr - zg = m * (Xr - Xg) ∧
    zp < σ0 ∧ σ0 < zx ∧ 0 < Xx ∧ Xx < L ∧ zx * L + (zf - zx) * Xx = (σ0 + m * Xx) * L ∧
    ((zf < z0 ∧ zr < z0 ∧ z0 < zg ∧ z0 < zx ∧ z0 < σ0) ∨ (z0 < zf ∧ z0 < zr ∧ zg < z0 ∧ zx < z0))

/-- Top-vertex class: class (c) (any `σ`), or class (d) (with `σ = 1`). -/
def Top5 (σ zp L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ClassC5 L zx zf Xr Yr zr Xg Yg zg ∨ (σ = 1 ∧ ClassD5 zp L zx zf Xr Yr zr Xg Yg zg)

theorem lemmaSCtop (hF : Fr e1 e2 e3) (o : ℝ³) (E : Finset ℝ³)
    {σ zp L zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : Top5 σ zp L zx zf Xr Yr zr Xg Yg zg)
    (hE : ∀ᶠ s : ℝ in atTop, ∀ y ∈ E, TriCert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E)
      (pc e1 e2 e3 0 0 1) (pc e1 e2 e3 (σ * s) (-σ) 0) y) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg E) := by
  rcases hc with hc | ⟨rfl, σ0, m, Xx, z0, hYY, hXrg, hzz, hσ0, hm, hD1, hD2, hX0, hXL, hch, hz | hz⟩
  · exact lemmaSCc (σ := σ) hF o E hL hzx hcr hYr hYg hcg hc hE
  · subst hYY
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    exact lemmaSCd_I hF o E hL hzz hYr hXrg hσ0 hm hD1 hD2 hX0 hXL hch h1 h2 h3 h4 h5 hE
  · subst hYY
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact lemmaSCd_II hF o E hL hzz hYr hXrg hσ0 hm hD1 hD2 hX0 hXL hch h1 h2 h3 h4 hE

section
variable {σ L zp zx zf Xr Yr zr Xg Yg zg : ℝ}

/-- **Theorem 08.SC-c for N2's `K_c`, frame form.**  `x' = a'`, `x = c` (over `q`), `f = b`,
`r = c'`, `g = b'`; `d` is the middle over the `F`-side (strictly above the line `a' b`), `a`
lies strictly inside the screen triangle `(a', b, b')`. -/
theorem sc08_N2_Ktop (hF : Fr e1 e2 e3) (o : ℝ³)
    {Xd zd Xa Ya za : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : Top5 σ zp L zx zf Xr Yr zr Xg Yg zg)
    (hXd0 : 0 < Xd) (hXdL : Xd < L) (hd : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd))
    (hT : 0 < L * Yg) (hc1 : 0 < L * Ya) (hc2 : 0 < (Xg - L) * Ya - Yg * (Xa - L))
    (hc3 : 0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 Xa Ya za}) := by
  refine lemmaSCtop (σ := σ) hF o _ hL hzx hcr hYr hYg hcg hc (Eventually.of_forall fun s y hy => ?_)
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
theorem sc08_T4_Ktop (hF : Fr e1 e2 e3) (o : ℝ³)
    {Xd zd lam za : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hc : Top5 σ zp L zx zf Xr Yr zr Xg Yg zg)
    (hXd0 : 0 < Xd) (hXdL : Xd < L) (hd : 0 < σ * (L * (zd - zp) - (zf - zp) * Xd))
    (hl0 : 0 < lam) (hl1 : lam < 1) (hab : σ * (za - ((1 - lam) * zx + lam * zg)) < 0) :
    IsRupert (rim5 e1 e2 e3 o L zp zx zf Xr Yr zr Xg Yg zg
      {o + pc e1 e2 e3 Xd 0 zd, o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za}) := by
  refine lemmaSCtop (σ := σ) hF o _ hL hzx hcr hYr hYg hcg hc ?_
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


def SCfN2' (u a a' b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 o : ℝ³) (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd Xa Ya za κ : ℝ),
    Fr e1 e2 e3 ∧ κ ≠ 0 ∧ u = κ • e3 ∧
    a' = o + pc e1 e2 e3 0 0 zp ∧ c = o + pc e1 e2 e3 0 0 zx ∧ b = o + pc e1 e2 e3 L 0 zf ∧
    c' = o + pc e1 e2 e3 Xr Yr zr ∧ b' = o + pc e1 e2 e3 Xg Yg zg ∧
    d = o + pc e1 e2 e3 Xd 0 zd ∧ a = o + pc e1 e2 e3 Xa Ya za ∧
    0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ Top5 σ zp L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < L * Yg ∧ 0 < L * Ya ∧ 0 < (Xg - L) * Ya - Yg * (Xa - L) ∧
    0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)

/-- **Frame data of the T4 single-circle closings** `K_b` (`x' = d`, `x = b`) and `K_2`
(`x' = b`, `x = d`): `xp, x, f, r, g` the 5-corner rim, `p` the F-middle, `q` the G-middle. -/
def SCfT4' (u xp x f r g p q : ℝ³) : Prop :=
  ∃ (e1 e2 e3 o : ℝ³) (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd lam za κ : ℝ),
    Fr e1 e2 e3 ∧ κ ≠ 0 ∧ u = κ • e3 ∧
    xp = o + pc e1 e2 e3 0 0 zp ∧ x = o + pc e1 e2 e3 0 0 zx ∧ f = o + pc e1 e2 e3 L 0 zf ∧
    r = o + pc e1 e2 e3 Xr Yr zr ∧ g = o + pc e1 e2 e3 Xg Yg zg ∧
    p = o + pc e1 e2 e3 Xd 0 zd ∧ q = o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za ∧
    0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ Top5 σ zp L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < lam ∧ lam < 1 ∧ σ * (za - ((1 - lam) * zx + lam * zg)) < 0


theorem rupert_SCfN2' {u a a' b b' c c' d : ℝ³} (h : SCfN2' u a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, σ, L, zp, zx, zf, Xr, Yr, zr, Xg, Yg, zg, Xd, zd, Xa, Ya, za, κ, hF, -, -,
    ha', hc, hb, hc', hb', hd, ha, hL, hzx, hcr, hYr, hYg, hcg, hcl, hX0, hXL, hdd, hT, h1, h2, h3⟩ := h
  have := sc08_N2_Ktop (σ := σ) (L := L) (zp := zp) (zx := zx) (zf := zf) (Xr := Xr) (Yr := Yr) (zr := zr) (Xg := Xg) (Yg := Yg) (zg := zg) (Xd := Xd) (zd := zd) (Xa := Xa) (Ya := Ya) (za := za) hF o hL hzx hcr hYr hYg hcg hcl hX0 hXL hdd hT h1 h2 h3
  convert this using 1
  subst ha' hc hb hc' hb' hd ha
  ext y; simp only [rim5, mem_insert, mem_singleton, mem_union]; tauto

theorem rupert_SCfT4' {u xp x f r g p q : ℝ³} (h : SCfT4' u xp x f r g p q) :
    IsRupert ({xp, x, f, r, g, p, q} : Finset ℝ³) := by
  obtain ⟨e1, e2, e3, o, σ, L, zp, zx, zf, Xr, Yr, zr, Xg, Yg, zg, Xd, zd, lam, za, κ, hF, -, -,
    h1, h2, h3, h4, h5, h6, h7, hL, hzx, hcr, hYr, hYg, hcg, hcl, hX0, hXL, hdd, hl0, hl1, hab⟩ := h
  have := sc08_T4_Ktop (σ := σ) (L := L) (zp := zp) (zx := zx) (zf := zf) (Xr := Xr) (Yr := Yr) (zr := zr) (Xg := Xg) (Yg := Yg) (zg := zg) (Xd := Xd) (zd := zd) (lam := lam) (za := za) hF o hL hzx hcr hYr hYg hcg hcl hX0 hXL hdd hl0 hl1 hab
  convert this using 1
  subst h1 h2 h3 h4 h5 h6 h7
  ext y; simp only [rim5, mem_insert, mem_singleton, mem_union]; tauto


/-- Inequality part of `SCfN2'` (frame numbers). -/
def N2Nums' (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd Xa Ya za : ℝ) : Prop :=
  0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ Top5 σ zp L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < L * Yg ∧ 0 < L * Ya ∧ 0 < (Xg - L) * Ya - Yg * (Xa - L) ∧
    0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)

/-- **Frame dictionary for N2 `K_c`** (item 1a): in any right-handed frame with `u = κ e3`, the
seven points have coordinates `⟪· - a', e_i⟫` (so `a'` is the origin, `zp = 0`), and `SCfN2'`
holds as soon as the inequalities `N2Nums'` hold for these coordinates. -/
theorem SCfN2'_of_frame {u a a' b b' c c' d : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0)
    (hu : u = κ • e3) (σ : ℝ)
    (H : N2Nums' σ ⟪b - a', e1⟫ 0 ⟪c - a', e3⟫ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫
      ⟪b' - a', e1⟫ ⟪b' - a', e2⟫ ⟪b' - a', e3⟫ ⟪d - a', e1⟫ ⟪d - a', e3⟫ ⟪a - a', e1⟫
      ⟪a - a', e2⟫ ⟪a - a', e3⟫)
    (hc0 : ⟪c - a', e1⟫ = 0) (hc2 : ⟪c - a', e2⟫ = 0) (hb2 : ⟪b - a', e2⟫ = 0)
    (hd2 : ⟪d - a', e2⟫ = 0) :
    SCfN2' u a a' b b' c c' d := by
  refine ⟨e1, e2, e3, a', σ, ⟪b - a', e1⟫, 0, ⟪c - a', e3⟫, ⟪b - a', e3⟫, ⟪c' - a', e1⟫, ⟪c' - a', e2⟫,
    ⟪c' - a', e3⟫, ⟪b' - a', e1⟫, ⟪b' - a', e2⟫, ⟪b' - a', e3⟫, ⟪d - a', e1⟫, ⟪d - a', e3⟫,
    ⟪a - a', e1⟫, ⟪a - a', e2⟫, ⟪a - a', e3⟫, κ, hF, hκ, hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H⟩
  · have := pc_coords hF a' a'; simp at this; simp [pc]
  · have := pc_coords hF a' c; rw [hc0, hc2] at this; exact this
  · have := pc_coords hF a' b; rw [hb2] at this; exact this
  · exact pc_coords hF a' c'
  · exact pc_coords hF a' b'
  · have := pc_coords hF a' d; rw [hd2] at this; exact this
  · exact pc_coords hF a' a

/-- Inequality part of `SCfT4'` (frame numbers). -/
def T4Nums' (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd lam za : ℝ) : Prop :=
  0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ Top5 σ zp L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < lam ∧ lam < 1 ∧ σ * (za - ((1 - lam) * zx + lam * zg)) < 0

/-- **Frame dictionary for T4 (`K_b`, `K_2`)**: origin `xp`, coordinates `⟪· - xp, e_i⟫`; `x - xp`
is along `e3`, `f - xp` and `p - xp` are edge-on (`e2`-coordinate 0), and the G-middle `q` lies
over the point `lam * (g - xp)` of the screen. -/
theorem SCfT4'_of_frame {u xp x f r g p q : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hκ : κ ≠ 0)
    (hu : u = κ • e3) (σ lam : ℝ)
    (H : T4Nums' σ ⟪f - xp, e1⟫ 0 ⟪x - xp, e3⟫ ⟪f - xp, e3⟫ ⟪r - xp, e1⟫ ⟪r - xp, e2⟫ ⟪r - xp, e3⟫
      ⟪g - xp, e1⟫ ⟪g - xp, e2⟫ ⟪g - xp, e3⟫ ⟪p - xp, e1⟫ ⟪p - xp, e3⟫ lam ⟪q - xp, e3⟫)
    (hx1 : ⟪x - xp, e1⟫ = 0) (hx2 : ⟪x - xp, e2⟫ = 0) (hf2 : ⟪f - xp, e2⟫ = 0)
    (hp2 : ⟪p - xp, e2⟫ = 0) (hq1 : ⟪q - xp, e1⟫ = lam * ⟪g - xp, e1⟫)
    (hq2 : ⟪q - xp, e2⟫ = lam * ⟪g - xp, e2⟫) :
    SCfT4' u xp x f r g p q := by
  refine ⟨e1, e2, e3, xp, σ, ⟪f - xp, e1⟫, 0, ⟪x - xp, e3⟫, ⟪f - xp, e3⟫, ⟪r - xp, e1⟫, ⟪r - xp, e2⟫,
    ⟪r - xp, e3⟫, ⟪g - xp, e1⟫, ⟪g - xp, e2⟫, ⟪g - xp, e3⟫, ⟪p - xp, e1⟫, ⟪p - xp, e3⟫, lam,
    ⟪q - xp, e3⟫, κ, hF, hκ, hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H⟩
  · have := pc_coords hF xp xp; simp at this; simp [pc]
  · have := pc_coords hF xp x; rw [hx1, hx2] at this; exact this
  · have := pc_coords hF xp f; rw [hf2] at this; exact this
  · exact pc_coords hF xp r
  · exact pc_coords hF xp g
  · have := pc_coords hF xp p; rw [hp2] at this; exact this
  · have := pc_coords hF xp q; rw [hq1, hq2] at this; exact this


end Type08Sp
end Minimality
