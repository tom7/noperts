module

public import Minimality.Type10

@[expose] public section

/-!
# `TriGenPar` or `TriGenFarP` for a pair of facets one of which is a triangle

FEWER-FACES-PROOFS.md Proposition 23.19 (2), (3) and Proposition 24.12.  For two facets `Q1`,
`Q2` of `V` meeting in the vertex `v`, with no three points of `V` collinear and one of the two
facets a triangle, **one of the two general positions `TriGenPar`, `TriGenFarP` always holds**:

* a segment of `V` parallel to the line of the two planes lies in a single facet, or outside
  both (a functional of either facet takes equal values at its ends, so the ends lie in the same
  facets); inside a facet `Q1` the second functional is constant along it, so both ends are far
  ends of `Q1` or neither is (the pair is then a `MidPair`);
* so if `TriGenPar` fails, some facet, say `Q1`, has two far ends, i.e. a vertical far edge,
  at every view of the line (the functionals of a facet are unique up to a positive factor);
* then `FarDepthOKT` holds at every view: a tie of far ends is a tie where the face `Q1` has a
  vertical far edge, which `FarDepthOKT` allows (the rectangle too, as one face is a triangle).

The proof of the last step is by contradiction: a tie violating `FarDepthOKT` makes the far set
of each face a single depth at that view, but the two far ends of `Q1` have different depths,
because the segment joining them is parallel to the line of the planes.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-- The inner product in coordinates. -/
theorem inner_coords (u e : ℝ³) : ⟪u, e⟫ = u 0 * e 0 + u 1 * e 1 + u 2 * e 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- Two vectors of the kernel of two independent functionals are parallel: if `e ≠ 0` and `u`
both satisfy the two linear equations (normals `n1 = (α1, β1, γ1)`, `n2`), and there are test
vectors `a`, `b` showing that the normals are independent, then `u` is a multiple of `e`. -/
theorem ker_line (α1 β1 γ1 α2 β2 γ2 u0 u1 u2 e0 e1 e2 a0 a1 a2 b0 b1 b2 : ℝ)
    (hu1 : α1 * u0 + β1 * u1 + γ1 * u2 = 0) (hu2 : α2 * u0 + β2 * u1 + γ2 * u2 = 0)
    (he1 : α1 * e0 + β1 * e1 + γ1 * e2 = 0) (he2 : α2 * e0 + β2 * e1 + γ2 * e2 = 0)
    (ha1 : α1 * a0 + β1 * a1 + γ1 * a2 = 0) (ha2 : α2 * a0 + β2 * a1 + γ2 * a2 ≠ 0)
    (hb1 : α1 * b0 + β1 * b1 + γ1 * b2 ≠ 0) (hne : e0 ≠ 0 ∨ e1 ≠ 0 ∨ e2 ≠ 0) :
    ∃ t : ℝ, u0 = t * e0 ∧ u1 = t * e1 ∧ u2 = t * e2 := by
  set N0 := β1 * γ2 - γ1 * β2 with hN0
  set N1 := γ1 * α2 - α1 * γ2 with hN1
  set N2 := α1 * β2 - β1 * α2 with hN2
  have hN : N0 ≠ 0 ∨ N1 ≠ 0 ∨ N2 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h0, h1, h2⟩ := h
    have k0 : α1 * (α2 * a0 + β2 * a1 + γ2 * a2) = 0 := by
      linear_combination α2 * ha1 + a1 * h2 - a2 * h1
    have k1 : β1 * (α2 * a0 + β2 * a1 + γ2 * a2) = 0 := by
      linear_combination β2 * ha1 - a0 * h2 + a2 * h0
    have k2 : γ1 * (α2 * a0 + β2 * a1 + γ2 * a2) = 0 := by
      linear_combination γ2 * ha1 + a0 * h1 - a1 * h0
    have c0 := (mul_eq_zero.mp k0).resolve_right ha2
    have c1 := (mul_eq_zero.mp k1).resolve_right ha2
    have c2 := (mul_eq_zero.mp k2).resolve_right ha2
    exact hb1 (by rw [c0, c1, c2]; ring)
  set Nsq := N0 ^ 2 + N1 ^ 2 + N2 ^ 2 with hNsq
  have hNpos : 0 < Nsq := by
    rcases hN with h | h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  -- `Nsq • w = (w · N) • N` for `w` in the kernel
  have proj : ∀ w0 w1 w2 : ℝ, α1 * w0 + β1 * w1 + γ1 * w2 = 0 → α2 * w0 + β2 * w1 + γ2 * w2 = 0 →
      Nsq * w0 = (w0 * N0 + w1 * N1 + w2 * N2) * N0 ∧
      Nsq * w1 = (w0 * N0 + w1 * N1 + w2 * N2) * N1 ∧
      Nsq * w2 = (w0 * N0 + w1 * N1 + w2 * N2) * N2 := by
    intro w0 w1 w2 h1 h2
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (N1 * γ1 - N2 * β1) * h2 - (N1 * γ2 - N2 * β2) * h1
    · linear_combination (N2 * α1 - N0 * γ1) * h2 - (N2 * α2 - N0 * γ2) * h1
    · linear_combination (N0 * β1 - N1 * α1) * h2 - (N0 * β2 - N1 * α2) * h1
  obtain ⟨pu0, pu1, pu2⟩ := proj u0 u1 u2 hu1 hu2
  obtain ⟨pe0, pe1, pe2⟩ := proj e0 e1 e2 he1 he2
  set su := u0 * N0 + u1 * N1 + u2 * N2 with hsu
  set se := e0 * N0 + e1 * N1 + e2 * N2 with hse
  have hse0 : se ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at pe0 pe1 pe2
    have z0 : e0 = 0 := (mul_eq_zero.mp pe0).resolve_left hNpos.ne'
    have z1 : e1 = 0 := (mul_eq_zero.mp pe1).resolve_left hNpos.ne'
    have z2 : e2 = 0 := (mul_eq_zero.mp pe2).resolve_left hNpos.ne'
    rcases hne with h | h | h
    · exact h z0
    · exact h z1
    · exact h z2
  refine ⟨su / se, ?_, ?_, ?_⟩
  · field_simp
    apply mul_left_cancel₀ hNpos.ne'
    linear_combination se * pu0 - su * pe0
  · field_simp
    apply mul_left_cancel₀ hNpos.ne'
    linear_combination se * pu1 - su * pe1
  · field_simp
    apply mul_left_cancel₀ hNpos.ne'
    linear_combination se * pu2 - su * pe2

/-- Increments of an affine functional in coordinates. -/
theorem aff_dif (f : ℝ³ →ᵃ[ℝ] ℝ) : ∃ α β γ : ℝ, ∀ p q : ℝ³,
    f q - f p = α * (q 0 - p 0) + β * (q 1 - p 1) + γ * (q 2 - p 2) := by
  obtain ⟨K, α, β, γ, h⟩ := affine_xyz f
  exact ⟨α, β, γ, fun p q => by rw [h, h]; ring⟩

/-- A functional vanishing at `v` and at `v + e` is invariant under translation by multiples of
`e`. -/
theorem aff_shift (f : ℝ³ →ᵃ[ℝ] ℝ) {v e : ℝ³} (h0 : f v = 0) (h1 : f (v + e) = 0) (p : ℝ³)
    (c : ℝ) : f (p + c • e) = f p := by
  obtain ⟨α, β, γ, d⟩ := aff_dif f
  have d1 := d v (v + e)
  have d2 := d p (p + c • e)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at d1 d2
  rw [h0, h1] at d1
  have hl : α * e 0 + β * e 1 + γ * e 2 = 0 := by linear_combination -d1
  linear_combination d2 + c * hl

/-- Two functionals vanishing on a facet of at least three points of a set without three
collinear points, and negative at a point of the set off the facet, are positive multiples. -/
theorem aff_prop {V Q : Finset ℝ³} (hgen : NoThreeCollinear V) (hQV : Q ⊆ V) (h3 : 3 ≤ Q.card)
    (f g : ℝ³ →ᵃ[ℝ] ℝ) (zf : ∀ p ∈ Q, f p = 0) (nf : ∀ p ∈ V, p ∉ Q → f p < 0)
    (zg : ∀ p ∈ Q, g p = 0) (ng : ∀ p ∈ V, p ∉ Q → g p < 0) {w : ℝ³} (hw : w ∈ V) (hwQ : w ∉ Q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ y, g y = κ * f y := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < Q.card)
  have key := vanish3_ratio f g hab (hgen a (hQV ha) b (hQV hb) c (hQV hc) hab hac hbc)
    (zf a ha) (zf b hb) (zf c hc) (zg a ha) (zg b hb) (zg c hc)
  have fw := nf w hw hwQ
  have gw := ng w hw hwQ
  refine ⟨g w / f w, div_pos_of_neg_of_neg gw fw, fun y => ?_⟩
  have := key y w
  have fw0 : f w ≠ 0 := fw.ne
  rw [div_mul_eq_mul_div, eq_div_iff fw0]
  linear_combination -this

/-- A segment of `V` parallel to the line of the planes that is not a `MidPair` joins two far
ends of one facet. -/
theorem par_pair {V Q1 Q2 : Finset ℝ³} {v e p q : ℝ³} {c : ℝ} (hint : Q1 ∩ Q2 = {v})
    (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0) (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hc : q - p = c • e)
    (hnm : ¬ MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
      p q) :
    (p ∈ Q1 ∧ q ∈ Q1 ∧ (∀ x ∈ Q1, f2 p ≤ f2 x) ∧ (∀ x ∈ Q1, f2 q ≤ f2 x)) ∨
      (p ∈ Q2 ∧ q ∈ Q2 ∧ (∀ x ∈ Q2, f1 p ≤ f1 x) ∧ (∀ x ∈ Q2, f1 q ≤ f1 x)) := by
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ x ∈ Q1, x ∈ Q2 → x = v := by
    intro x h1 h2
    have : x ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have hq' : q = p + c • e := by rw [← hc]; abel
  have s1 : f1 q = f1 p := by rw [hq']; exact aff_shift f1 (z1 v hv1) e1 p c
  have s2 : f2 q = f2 p := by rw [hq']; exact aff_shift f2 (z2 v hv2) e2 p c
  have m1 : p ∈ Q1 → q ∈ Q1 := fun h => by
    by_contra hn; have := n1 q hq hn; rw [s1, z1 p h] at this; exact lt_irrefl _ this
  have m1' : q ∈ Q1 → p ∈ Q1 := fun h => by
    by_contra hn; have := n1 p hp hn; rw [← s1, z1 q h] at this; exact lt_irrefl _ this
  have m2 : p ∈ Q2 → q ∈ Q2 := fun h => by
    by_contra hn; have := n2 q hq hn; rw [s2, z2 p h] at this; exact lt_irrefl _ this
  have m2' : q ∈ Q2 → p ∈ Q2 := fun h => by
    by_contra hn; have := n2 p hp hn; rw [← s2, z2 q h] at this; exact lt_irrefl _ this
  by_cases a1 : p ∈ Q1
  · have b1 := m1 a1
    have a2 : p ∉ Q2 := fun h => hpq (by rw [only p a1 h, only q b1 (m2 h)])
    have farp : ∀ x ∈ Q1, f2 p ≤ f2 x := by
      by_contra hfp
      apply hnm
      exact Or.inl ⟨a1, b1, hfp, fun h => hfp (fun x hx => by have := h x hx; rwa [s2] at this)⟩
    exact Or.inl ⟨a1, b1, farp, fun x hx => by rw [s2]; exact farp x hx⟩
  · have b1 : q ∉ Q1 := fun h => a1 (m1' h)
    by_cases a2 : p ∈ Q2
    · have b2 := m2 a2
      have farp : ∀ x ∈ Q2, f1 p ≤ f1 x := by
        by_contra hfp
        apply hnm
        exact Or.inr (Or.inl ⟨a2, b2, hfp,
          fun h => hfp (fun x hx => by have := h x hx; rwa [s1] at this)⟩)
      exact Or.inr ⟨a2, b2, farp, fun x hx => by rw [s1]; exact farp x hx⟩
    · exact absurd (Or.inr (Or.inr ⟨a1, a2, b1, fun h => a2 (m2' h)⟩)) hnm

/-- **A failure of `FarDepthOKT` with a triangle face makes the far set of each face a single
depth** (the far ends of each face have the same depth at that view). -/
theorem farUniform {Q1 Q2 : Finset ℝ³} {far1 far2 : ℝ³ → Prop} {d : ℝ³ → ℝ}
    (hcard : Q1.card = 3 ∨ Q2.card = 3) (h : ¬ FarDepthOKT Q1 Q2 far1 far2 d) :
    (∃ p0 ∈ Q1, far1 p0 ∧ ∀ p' ∈ Q1, far1 p' → d p' = d p0) ∧
      (∃ q0 ∈ Q2, far2 q0 ∧ ∀ q' ∈ Q2, far2 q' → d q' = d q0) := by
  by_contra hU
  apply h
  intro p hp q hq hpq f1 f2 hd
  by_cases u1 : ∀ p' ∈ Q1, far1 p' → d p' = d p
  · by_cases u2 : ∀ q' ∈ Q2, far2 q' → d q' = d q
    · exact absurd ⟨⟨p, hp, f1, u1⟩, ⟨q, hq, f2, u2⟩⟩ hU
    · push Not at u2
      obtain ⟨q', hq', fq', dq'⟩ := u2
      exact Or.inr (Or.inl ⟨u1, q', hq', fq', dq'⟩)
  · push Not at u1
    obtain ⟨p', hp', fp', dp'⟩ := u1
    by_cases u2 : ∀ q' ∈ Q2, far2 q' → d q' = d q
    · exact Or.inl ⟨⟨p', hp', fp', dp'⟩, u2⟩
    · push Not at u2
      obtain ⟨q', hq', fq', dq'⟩ := u2
      exact Or.inr (Or.inr ⟨⟨p', hp', fp', dp'⟩, ⟨q', hq', fq', dq'⟩, Or.inr hcard⟩)

/-- **The core.** A vertical far edge `p q` of the facet `Q1` (both far for the functional `f2`
of the other facet) contradicts the uniform far depth of `Q1` at another view line `e`: the two
functionals of that view vanish on `q - p`, which is therefore parallel to `e`. -/
theorem par_core {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (hgen : NoThreeCollinear V) (h1V : Q1 ⊆ V)
    (h2V : Q2 ⊆ V)
    (hint : Q1 ∩ Q2 = {v}) (hc1 : 2 ≤ Q1.card) (h3 : 3 ≤ Q2.card) {w : ℝ³} (hw : w ∈ V)
    (hwQ : w ∉ Q2) (f2 : ℝ³ →ᵃ[ℝ] ℝ) (zf : ∀ p ∈ Q2, f2 p = 0) (nf : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (g1 g2 : ℝ³ →ᵃ[ℝ] ℝ) (zg1 : ∀ p ∈ Q1, g1 p = 0) (ng1 : ∀ p ∈ V, p ∉ Q1 → g1 p < 0)
    (zg2 : ∀ p ∈ Q2, g2 p = 0) (ng2 : ∀ p ∈ V, p ∉ Q2 → g2 p < 0) {e : ℝ³} (he : e ≠ 0)
    (eg1 : g1 (v + e) = 0) (eg2 : g2 (v + e) = 0)
    (hU : ∃ p0 ∈ Q1, (∀ x ∈ Q1, g2 p0 ≤ g2 x) ∧
      ∀ p' ∈ Q1, (∀ x ∈ Q1, g2 p' ≤ g2 x) → ⟪p', e⟫ = ⟪p0, e⟫)
    {p q : ℝ³} (hp : p ∈ Q1) (hq : q ∈ Q1) (hpq : p ≠ q) (fp : ∀ x ∈ Q1, f2 p ≤ f2 x)
    (fq : ∀ x ∈ Q1, f2 q ≤ f2 x) : False := by
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ x ∈ Q1, x ∈ Q2 → x = v := by
    intro x h1 h2
    have : x ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨κ, hκ, hg⟩ := aff_prop hgen h2V h3 f2 g2 zf nf zg2 ng2 hw hwQ
  obtain ⟨p0, hp0, -, hunif⟩ := hU
  have gp : ∀ x ∈ Q1, g2 p ≤ g2 x := fun x hx => by
    rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fp x hx) hκ.le
  have gq : ∀ x ∈ Q1, g2 q ≤ g2 x := fun x hx => by
    rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fq x hx) hκ.le
  have dp := hunif p hp gp
  have dq := hunif q hq gq
  have hgpq : g2 q = g2 p := by
    rw [hg, hg]; congr 1; exact le_antisymm (fq p hp) (fp q hq)
  obtain ⟨α1, β1, γ1, d1⟩ := aff_dif g1
  obtain ⟨α2, β2, γ2, d2⟩ := aff_dif g2
  have hu1 : α1 * (q 0 - p 0) + β1 * (q 1 - p 1) + γ1 * (q 2 - p 2) = 0 := by
    rw [← d1 p q, zg1 p hp, zg1 q hq]; ring
  have hu2 : α2 * (q 0 - p 0) + β2 * (q 1 - p 1) + γ2 * (q 2 - p 2) = 0 := by
    rw [← d2 p q, hgpq]; ring
  have he1 : α1 * e 0 + β1 * e 1 + γ1 * e 2 = 0 := by
    have := d1 v (v + e)
    simp only [PiLp.add_apply] at this
    rw [eg1, zg1 v hv1] at this
    linear_combination -this
  have he2 : α2 * e 0 + β2 * e 1 + γ2 * e 2 = 0 := by
    have := d2 v (v + e)
    simp only [PiLp.add_apply] at this
    rw [eg2, zg2 v hv2] at this
    linear_combination -this
  obtain ⟨a, ha, hav⟩ := Finset.exists_mem_ne (by omega : 1 < Q1.card) v
  obtain ⟨b, hb, hbv⟩ := Finset.exists_mem_ne (by omega : 1 < Q2.card) v
  have haQ : a ∉ Q2 := fun h => hav (only a ha h)
  have hbQ : b ∉ Q1 := fun h => hbv (only b h hb)
  have ha1 : α1 * (a 0 - v 0) + β1 * (a 1 - v 1) + γ1 * (a 2 - v 2) = 0 := by
    rw [← d1 v a, zg1 a ha, zg1 v hv1]; ring
  have ha2 : α2 * (a 0 - v 0) + β2 * (a 1 - v 1) + γ2 * (a 2 - v 2) ≠ 0 := by
    rw [← d2 v a, zg2 v hv2]
    have := ng2 a (h1V ha) haQ
    linarith
  have hb1 : α1 * (b 0 - v 0) + β1 * (b 1 - v 1) + γ1 * (b 2 - v 2) ≠ 0 := by
    rw [← d1 v b, zg1 v hv1]
    have := ng1 b (h2V hb) hbQ
    linarith
  have hne : e 0 ≠ 0 ∨ e 1 ≠ 0 ∨ e 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply he
    ext i
    fin_cases i
    · exact hcon.1
    · exact hcon.2.1
    · exact hcon.2.2
  obtain ⟨t, h0, h1, h2⟩ := ker_line α1 β1 γ1 α2 β2 γ2 (q 0 - p 0) (q 1 - p 1) (q 2 - p 2)
    (e 0) (e 1) (e 2) (a 0 - v 0) (a 1 - v 1) (a 2 - v 2) (b 0 - v 0) (b 1 - v 1) (b 2 - v 2)
    hu1 hu2 he1 he2 ha1 ha2 hb1 hne
  have hsum : t * (e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2) = 0 := by
    have := dq.trans dp.symm
    rw [inner_coords, inner_coords] at this
    linear_combination this - e 0 * h0 - e 1 * h1 - e 2 * h2
  have hpos : 0 < e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 := by
    rcases hne with h | h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (e 1), sq_nonneg (e 2)]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (e 0), sq_nonneg (e 2)]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (e 0), sq_nonneg (e 1)]
  have ht : t = 0 := (mul_eq_zero.mp hsum).resolve_right hpos.ne'
  subst ht
  apply hpq
  ext i
  fin_cases i
  · show p 0 = q 0
    linarith
  · show p 1 = q 1
    linarith
  · show p 2 = q 2
    linarith

/-- **`TriGenPar` or `TriGenFarP` for a pair of facets with a triangle** (FEWER-FACES-PROOFS.md
Proposition 23.19 (2), (3) and Proposition 24.12): for two facets `Q1`, `Q2` of `V`, no three
points of `V` collinear, meeting in `v`, one of them a triangle, either no segment parallel to the
line of the planes is a vertical far edge (`TriGenPar`: every parallel segment is a `MidPair`),
or some facet has a vertical far edge at the view and `TriGenFarP` holds. -/
theorem triGenPar_or_farP {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (hgen : NoThreeCollinear V)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (h1 : 3 ≤ Q1.card) (h2 : 3 ≤ Q2.card)
    (hcard : Q1.card = 3 ∨ Q2.card = 3) (hout1 : ∃ w ∈ V, w ∉ Q1) (hout2 : ∃ w ∈ V, w ∉ Q2) :
    TriGenPar V Q1 Q2 v ∨ TriGenFarP V Q1 Q2 v := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hP, hF⟩ := hcon
  obtain ⟨w1, hw1, hw1Q⟩ := hout1
  obtain ⟨w2, hw2, hw2Q⟩ := hout2
  have hP' : ∃ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → f1 p < 0) ∧
      (∀ p ∈ Q2, f2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → f2 p < 0) ∧ ∃ e : ℝ³, e ≠ 0 ∧ f1 (v + e) = 0 ∧
      f2 (v + e) = 0 ∧ ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ ∃ c : ℝ, q - p = c • e ∧
        ¬ MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
          p q := by
    by_contra hc
    apply hP
    intro f1 f2 z1 n1 z2 n2 e he e1 e2 p hp q hq hpq c hc'
    by_contra hnm
    exact hc ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, p, hp, q, hq, hpq, c, hc', hnm⟩
  have hF' : ∃ g1 g2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, g1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → g1 p < 0) ∧
      (∀ p ∈ Q2, g2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → g2 p < 0) ∧ ∃ e : ℝ³, e ≠ 0 ∧ g1 (v + e) = 0 ∧
      g2 (v + e) = 0 ∧ ¬ FarDepthOKT Q1 Q2 (fun p => ∀ p' ∈ Q1, g2 p ≤ g2 p')
        (fun q => ∀ q' ∈ Q2, g1 q ≤ g1 q') (fun p => ⟪p, e⟫) := by
    by_contra hc
    apply hF
    intro g1 g2 z1 n1 z2 n2 e he e1 e2
    by_contra hnm
    exact hc ⟨g1, g2, z1, n1, z2, n2, e, he, e1, e2, hnm⟩
  obtain ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, p, hp, q, hq, hpq, c, hc, hnm⟩ := hP'
  obtain ⟨g1, g2, y1, m1, y2, m2, e', he', e1', e2', hnF⟩ := hF'
  obtain ⟨⟨p0, hp0, hf0, hu0⟩, ⟨q0, hq0, hf0', hu0'⟩⟩ := farUniform hcard hnF
  rcases par_pair hint f1 f2 z1 n1 z2 n2 e1 e2 hp hq hpq hc hnm with
    ⟨hpQ, hqQ, fp, fq⟩ | ⟨hpQ, hqQ, fp, fq⟩
  · exact par_core hgen h1V h2V hint (by omega) h2 hw2 hw2Q f2 z2 n2 g1 g2 y1 m1 y2 m2 he' e1' e2'
      ⟨p0, hp0, hf0, hu0⟩ hpQ hqQ hpq fp fq
  · exact par_core hgen h2V h1V (by rw [Finset.inter_comm]; exact hint) (by omega) h1 hw1 hw1Q
      f1 z1 n1 g2 g1 y2 m2 y1 m1 he' e2' e1' ⟨q0, hq0, hf0', hu0'⟩ hpQ hqQ hpq fp fq

/-- `triGenPar_or_farP` for labelled points: two facets `A`, `B` of the labelled seven points
(each with at most six labels), meeting in the label `v`, one of them a triangle. -/
theorem triGenPar_or_farP_idx {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x)) (A B : Finset (Fin 7)) (v : Fin 7)
    (hint : A ∩ B = {v}) (hA : 3 ≤ A.card) (hB : 3 ≤ B.card) (hAB : A.card = 3 ∨ B.card = 3)
    (hA7 : A.card < 7) (hB7 : B.card < 7) :
    TriGenPar (Finset.univ.image x) (A.image x) (B.image x) (x v) ∨
      TriGenFarP (Finset.univ.image x) (A.image x) (B.image x) (x v) := by
  classical
  have hV : (Finset.univ.image x).card = 7 := by
    rw [Finset.card_image_of_injective _ hx]; simp
  have cA : (A.image x).card = A.card := Finset.card_image_of_injective _ hx
  have cB : (B.image x).card = B.card := Finset.card_image_of_injective _ hx
  refine triGenPar_or_farP hgen (Finset.image_subset_image (Finset.subset_univ A))
    (Finset.image_subset_image (Finset.subset_univ B))
    (by rw [← Finset.image_inter _ _ hx, hint, Finset.image_singleton])
    (by omega) (by omega) (by omega) ?_ ?_
  · obtain ⟨w, hw, hwA⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := A.image x)
      (t := Finset.univ.image x) (by omega)
    exact ⟨w, hw, hwA⟩
  · obtain ⟨w, hw, hwB⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := B.image x)
      (t := Finset.univ.image x) (by omega)
    exact ⟨w, hw, hwB⟩

end Minimality

end
