module

public import Minimality.Type08S.SCh

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- **Frame data of the N2 `K_c` single-circle closing** (view `u`): the seven points
`a' = x'`, `c = x`, `b = f`, `c' = r`, `b' = g`, `d` (F-middle), `a` (interior of the screen
triangle `(a', b, b')`) in an orthonormal frame with `u = κ e3`, with all hypotheses of
`sc08_N2_Kc` (class (c) rim). -/
def SCfN2 (u a a' b b' c c' d : ℝ³) : Prop :=
  ∃ (e1 e2 e3 o : ℝ³) (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd Xa Ya za κ : ℝ),
    Fr e1 e2 e3 ∧ κ ≠ 0 ∧ u = κ • e3 ∧
    a' = o + pc e1 e2 e3 0 0 zp ∧ c = o + pc e1 e2 e3 0 0 zx ∧ b = o + pc e1 e2 e3 L 0 zf ∧
    c' = o + pc e1 e2 e3 Xr Yr zr ∧ b' = o + pc e1 e2 e3 Xg Yg zg ∧
    d = o + pc e1 e2 e3 Xd 0 zd ∧ a = o + pc e1 e2 e3 Xa Ya za ∧
    0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ ClassC5 L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < L * Yg ∧ 0 < L * Ya ∧ 0 < (Xg - L) * Ya - Yg * (Xa - L) ∧
    0 < -Xg * (Ya - Yg) + Yg * (Xa - Xg)

/-- **Frame data of the T4 single-circle closings** `K_b` (`x' = d`, `x = b`) and `K_2`
(`x' = b`, `x = d`): `xp, x, f, r, g` the 5-corner rim, `p` the F-middle, `q` the G-middle. -/
def SCfT4 (u xp x f r g p q : ℝ³) : Prop :=
  ∃ (e1 e2 e3 o : ℝ³) (σ L zp zx zf Xr Yr zr Xg Yg zg Xd zd lam za κ : ℝ),
    Fr e1 e2 e3 ∧ κ ≠ 0 ∧ u = κ • e3 ∧
    xp = o + pc e1 e2 e3 0 0 zp ∧ x = o + pc e1 e2 e3 0 0 zx ∧ f = o + pc e1 e2 e3 L 0 zf ∧
    r = o + pc e1 e2 e3 Xr Yr zr ∧ g = o + pc e1 e2 e3 Xg Yg zg ∧
    p = o + pc e1 e2 e3 Xd 0 zd ∧ q = o + pc e1 e2 e3 (lam * Xg) (lam * Yg) za ∧
    0 < L ∧ 0 < σ * (zx - zp) ∧
    0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr) ∧ 0 < Yr ∧ 0 < Yg ∧
    0 < Yg * Xr - Xg * Yr ∧ ClassC5 L zx zf Xr Yr zr Xg Yg zg ∧
    0 < Xd ∧ Xd < L ∧ 0 < σ * (L * (zd - zp) - (zf - zp) * Xd) ∧
    0 < lam ∧ lam < 1 ∧ σ * (za - ((1 - lam) * zx + lam * zg)) < 0

/-- **The single-circle closing `t ∈ SC08` is of class SC-c** (Lemma SC / Corollary SC-c in
frame coordinates at its view): N2 `K_c`, T4 `K_b`, `K_2`. -/
def SCcl (a a' b b' c c' d : ℝ³) (t : Fin 3 × Bool × Bool) : Prop :=
  let u := (test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)
  (t.1 = 0 ∧ t.2.2 = true ∧ SCfN2 u a a' b b' c c' d) ∨
  (t.1 = 1 ∧ t.2.2 = true ∧ SCfT4 u d b c b' c' a' a) ∨
  (t.1 = 1 ∧ t.2.2 = false ∧ SCfT4 u b d c b' c' a' a)

theorem rupert_SCfN2 {u a a' b b' c c' d : ℝ³} (h : SCfN2 u a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  obtain ⟨e1, e2, e3, o, σ, L, zp, zx, zf, Xr, Yr, zr, Xg, Yg, zg, Xd, zd, Xa, Ya, za, κ, hF, -, -,
    ha', hc, hb, hc', hb', hd, ha, hL, hzx, hcr, hYr, hYg, hcg, hcl, hX0, hXL, hdd, hT, h1, h2, h3⟩ := h
  have := sc08_N2_Kc (σ := σ) (L := L) (zp := zp) (zx := zx) (zf := zf) (Xr := Xr) (Yr := Yr) (zr := zr) (Xg := Xg) (Yg := Yg) (zg := zg) (Xd := Xd) (zd := zd) (Xa := Xa) (Ya := Ya) (za := za) hF o hL hzx hcr hYr hYg hcg hcl hX0 hXL hdd hT h1 h2 h3
  convert this using 1
  subst ha' hc hb hc' hb' hd ha
  ext y; simp only [rim5, mem_insert, mem_singleton, mem_union]; tauto

theorem rupert_SCfT4 {u xp x f r g p q : ℝ³} (h : SCfT4 u xp x f r g p q) :
    IsRupert ({xp, x, f, r, g, p, q} : Finset ℝ³) := by
  obtain ⟨e1, e2, e3, o, σ, L, zp, zx, zf, Xr, Yr, zr, Xg, Yg, zg, Xd, zd, lam, za, κ, hF, -, -,
    h1, h2, h3, h4, h5, h6, h7, hL, hzx, hcr, hYr, hYg, hcg, hcl, hX0, hXL, hdd, hl0, hl1, hab⟩ := h
  have := sc08_T4_Kb (σ := σ) (L := L) (zp := zp) (zx := zx) (zf := zf) (Xr := Xr) (Yr := Yr) (zr := zr) (Xg := Xg) (Yg := Yg) (zg := zg) (Xd := Xd) (zd := zd) (lam := lam) (za := za) hF o hL hzx hcr hYr hYg hcg hcl hX0 hXL hdd hl0 hl1 hab
  convert this using 1
  subst h1 h2 h3 h4 h5 h6 h7
  ext y; simp only [rim5, mem_insert, mem_singleton, mem_union]; tauto

/-- Soundness: a closing of class SC-c gives Rupert. -/
theorem rupert_of_SCcl {a a' b b' c c' d : ℝ³} {t : Fin 3 × Bool × Bool}
    (h : SCcl a a' b b' c c' d t) : IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact rupert_SCfN2 h
  · have := rupert_SCfT4 h
    convert this using 1
    ext y; simp only [mem_insert, mem_singleton]; tauto
  · have := rupert_SCfT4 h
    convert this using 1
    ext y; simp only [mem_insert, mem_singleton]; tauto

/-- **Refined limit theorem.**  Rupert, or a single-circle closing `t` whose limit rim is
certified (robust unimodal), with an HDN at its view, and which is not of class SC-c. -/
theorem isRupert_type08_limit_hdn' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0)
    (hind : TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hnt : ¬ Touch a a' b b' c c' d)
    (hTco : IsT a' b c d → ¬ CoT2 a a' b b' c c' d)
    (hT'co : IsT' a b c' d → ¬ CoT'2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08,
        (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k),
          RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
            ((test08 t.1 t.2.1 t.2.2).lab ∘ σ)) ∧
        ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
          ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) ∧
        ¬ SCcl a a' b b' c c' d t := by
  classical
  rcases isRupert_type08_limit_hdn_rim N hq ties hties hind hcover hnt hTco hT'co with h | ⟨t, ht, hr, hn⟩
  · exact Or.inl h
  · by_cases hs : SCcl a a' b b' c c' d t
    · exact Or.inl (rupert_of_SCcl hs)
    · exact Or.inr ⟨t, ht, hr, hn, hs⟩

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.isRupert_type08_limit_hdn'
