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

/-- **A failure of `FarDepthOKT` where the rectangle is allowed (`RectOK`) makes the far set of
each face a single depth** (the far ends of each face have the same depth at that view). -/
theorem farUniform {Q1 Q2 : Finset ℝ³} {far1 far2 : ℝ³ → Prop} {d : ℝ³ → ℝ}
    (hcard : RectOK Q1 Q2 far1 far2 d) (h : ¬ FarDepthOKT Q1 Q2 far1 far2 d) :
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

/-- **A failure of `FarDepthOKT` is a uniform far depth on both faces, or a rectangle where the
rectangle is not allowed.**  Either the far ends of each face all have one depth, or both faces
have two far ends at different depths (`p`, `p'` and `q`, `q'`), which tie crosswise
(`d p = d q`, `d p' = d q'`) while `RectOK` fails. -/
theorem farRect_of_not {Q1 Q2 : Finset ℝ³} {far1 far2 : ℝ³ → Prop} {d : ℝ³ → ℝ}
    (h : ¬ FarDepthOKT Q1 Q2 far1 far2 d) :
    ((∃ p0 ∈ Q1, far1 p0 ∧ ∀ p' ∈ Q1, far1 p' → d p' = d p0) ∧
      (∃ q0 ∈ Q2, far2 q0 ∧ ∀ q' ∈ Q2, far2 q' → d q' = d q0)) ∨
    (∃ p ∈ Q1, ∃ p' ∈ Q1, ∃ q ∈ Q2, ∃ q' ∈ Q2, far1 p ∧ far1 p' ∧ far2 q ∧ far2 q' ∧
      d p = d q ∧ d p' = d q' ∧ d p ≠ d p' ∧ ¬ RectOK Q1 Q2 far1 far2 d) := by
  classical
  by_contra hcon
  apply h
  intro p hp q hq hpq f1 f2 hd
  by_cases u1 : ∀ p' ∈ Q1, far1 p' → d p' = d p
  · by_cases u2 : ∀ q' ∈ Q2, far2 q' → d q' = d q
    · exact absurd (Or.inl ⟨⟨p, hp, f1, u1⟩, ⟨q, hq, f2, u2⟩⟩) hcon
    · push Not at u2
      obtain ⟨q', hq', fq', dq'⟩ := u2
      exact Or.inr (Or.inl ⟨u1, q', hq', fq', dq'⟩)
  · push Not at u1
    obtain ⟨p', hp', fp', dp'⟩ := u1
    by_cases u2 : ∀ q' ∈ Q2, far2 q' → d q' = d q
    · exact Or.inl ⟨⟨p', hp', fp', dp'⟩, u2⟩
    · push Not at u2
      obtain ⟨q', hq', fq', dq'⟩ := u2
      refine Or.inr (Or.inr ⟨⟨p', hp', fp', dp'⟩, ⟨q', hq', fq', dq'⟩, ?_⟩)
      by_cases hR : RectOK Q1 Q2 far1 far2 d
      · exact Or.inr hR
      · left
        intro p'' hp'' f'' dp'' q'' hq'' g'' dq'' nq e
        exact hcon (Or.inr ⟨p, hp, p'', hp'', q, hq, q'', hq'', f1, f'', f2, g'', hd, e,
          fun h => dp'' h.symm, hR⟩)

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
  obtain ⟨⟨p0, hp0, hf0, hu0⟩, ⟨q0, hq0, hf0', hu0'⟩⟩ :=
    farUniform (hcard.elim Or.inl fun h => Or.inr (Or.inl h)) hnF
  rcases par_pair hint f1 f2 z1 n1 z2 n2 e1 e2 hp hq hpq hc hnm with
    ⟨hpQ, hqQ, fp, fq⟩ | ⟨hpQ, hqQ, fp, fq⟩
  · exact par_core hgen h1V h2V hint (by omega) h2 hw2 hw2Q f2 z2 n2 g1 g2 y1 m1 y2 m2 he' e1' e2'
      ⟨p0, hp0, hf0, hu0⟩ hpQ hqQ hpq fp fq
  · exact par_core hgen h2V h1V (by rw [Finset.inter_comm]; exact hint) (by omega) h1 hw1 hw1Q
      f1 z1 n1 g2 g1 y2 m2 y1 m1 he' e2' e1' ⟨q0, hq0, hf0', hu0'⟩ hpQ hqQ hpq fp fq

/-- **The residual position of two quadrilaterals** (FEWER-FACES-PROOFS.md Proposition 24.12 and
Theorem 24.5 (a)).  At a view `e` along the line of the planes of the facets `Q1`, `Q2` (functionals
`f1`, `f2`) the far ends of `Q1` include two points `p`, `p'` at different depths (a vertical far
edge: minimizers of `f2` over `Q1`), those of `Q2` two points `q`, `q'`, and the depths tie
crosswise (`p ~ q`, `p' ~ q'`, the rectangle); and the shared vertex `v` has the depth of a far
end, with every vertex of both faces on one side of it (the triple tie with both faces one-sided).
For two quadrilaterals this is, besides a segment parallel to the line with an endpoint at a far
end that is not covered by the rectangle, the only position that `Minimality.TriGenFarP` excludes
(`RectOK`). -/
def QuadTripleRect (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∃ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → f1 p < 0) ∧
    (∀ p ∈ Q2, f2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → f2 p < 0) ∧
    ∃ e : ℝ³, e ≠ 0 ∧ f1 (v + e) = 0 ∧ f2 (v + e) = 0 ∧
      ∃ p ∈ Q1, ∃ p' ∈ Q1, ∃ q ∈ Q2, ∃ q' ∈ Q2,
        (∀ x ∈ Q1, f2 p ≤ f2 x) ∧ (∀ x ∈ Q1, f2 p' ≤ f2 x) ∧
        (∀ x ∈ Q2, f1 q ≤ f1 x) ∧ (∀ x ∈ Q2, f1 q' ≤ f1 x) ∧
        ⟪p, e⟫ = ⟪q, e⟫ ∧ ⟪p', e⟫ = ⟪q', e⟫ ∧ ⟪p, e⟫ ≠ ⟪p', e⟫ ∧
        ((∃ w ∈ Q1, (∀ x ∈ Q1, f2 w ≤ f2 x) ∧ ⟪w, e⟫ = ⟪v, e⟫) ∨
          (∃ w ∈ Q2, (∀ x ∈ Q2, f1 w ≤ f1 x) ∧ ⟪w, e⟫ = ⟪v, e⟫)) ∧
        ((∀ x ∈ Q1 ∪ Q2, ⟪v, e⟫ ≤ ⟪x, e⟫) ∨ (∀ x ∈ Q1 ∪ Q2, ⟪x, e⟫ ≤ ⟪v, e⟫))

/-- **`TriGenPar`, `TriGenFarP` or the residual position, for two quadrilaterals.**  For two
facets `Q1`, `Q2` of `V` meeting in `v`, with no three points of `V` collinear, both
quadrilaterals: either every segment parallel to the line of the two planes is a `MidPair`
(`TriGenPar`), or `TriGenFarP` holds, or `QuadTripleRect` holds.  (As `triGenPar_or_farP`, with the
rectangle also allowed for two quadrilaterals unless the shared vertex has the depth of a far end
and all vertices of both faces lie on one side of it.) -/
theorem triGenPar_or_farP_quad {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (hgen : NoThreeCollinear V)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (hc1 : Q1.card = 4)
    (hc2 : Q2.card = 4) (hout1 : ∃ w ∈ V, w ∉ Q1) (hout2 : ∃ w ∈ V, w ∉ Q2) :
    TriGenPar V Q1 Q2 v ∨ TriGenFarP V Q1 Q2 v ∨ QuadTripleRect V Q1 Q2 v := by
  classical
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hP, hF, hR⟩ := hcon
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
  rcases farRect_of_not hnF with ⟨⟨p0, hp0, hf0, hu0⟩, ⟨q0, hq0, hf0', hu0'⟩⟩ |
      ⟨a, ha, a', ha', b, hb, b', hb', fa, fa', fb, fb', t1, t2, t3, hnR⟩
  · rcases par_pair hint f1 f2 z1 n1 z2 n2 e1 e2 hp hq hpq hc hnm with
      ⟨hpQ, hqQ, fp, fq⟩ | ⟨hpQ, hqQ, fp, fq⟩
    · exact par_core hgen h1V h2V hint (by omega) (by omega) hw2 hw2Q f2 z2 n2 g1 g2 y1 m1 y2 m2
        he' e1' e2' ⟨p0, hp0, hf0, hu0⟩ hpQ hqQ hpq fp fq
    · exact par_core hgen h2V h1V (by rw [Finset.inter_comm]; exact hint) (by omega) (by omega)
        hw1 hw1Q f1 z1 n1 g2 g1 y2 m2 y1 m1 he' e2' e1' ⟨q0, hq0, hf0', hu0'⟩ hpQ hqQ hpq fp fq
  · apply hR
    have hnR' : ¬ ∀ w ∈ Q1 ∩ Q2, ((∃ p ∈ Q1, (∀ p' ∈ Q1, g2 p ≤ g2 p') ∧ ⟪p, e'⟫ = ⟪w, e'⟫) ∨
        (∃ q ∈ Q2, (∀ q' ∈ Q2, g1 q ≤ g1 q') ∧ ⟪q, e'⟫ = ⟪w, e'⟫)) →
        (∃ x ∈ Q1 ∪ Q2, ⟪x, e'⟫ < ⟪w, e'⟫) ∧ (∃ x ∈ Q1 ∪ Q2, ⟪w, e'⟫ < ⟪x, e'⟫) :=
      fun H => hnR (Or.inr (Or.inr ⟨hc1, hc2, H⟩))
    push Not at hnR'
    obtain ⟨w, hw, hties, hone⟩ := hnR'
    have hwv : w = v := by
      have : w ∈ ({v} : Finset ℝ³) := hint ▸ hw
      exact Finset.mem_singleton.mp this
    subst hwv
    refine ⟨g1, g2, y1, m1, y2, m2, e', he', e1', e2', a, ha, a', ha', b, hb, b', hb', fa, fa', fb,
      fb', t1, t2, t3, ?_, ?_⟩
    · rcases hties with ⟨x, hx, hxf, hxe⟩ | ⟨x, hx, hxf, hxe⟩
      · exact Or.inl ⟨x, hx, hxf, hxe⟩
      · exact Or.inr ⟨x, hx, hxf, hxe⟩
    · by_cases hlow : ∃ x ∈ Q1 ∪ Q2, ⟪x, e'⟫ < ⟪w, e'⟫
      · right
        exact hone hlow
      · left
        push Not at hlow
        exact hlow

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

/-- `triGenPar_or_farP_quad` for labelled points: two quadrilateral facets `A`, `B` of the labelled
seven points, meeting in the label `v`. -/
theorem triGenPar_or_farP_quad_idx {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x)) (A B : Finset (Fin 7)) (v : Fin 7)
    (hint : A ∩ B = {v}) (hA : A.card = 4) (hB : B.card = 4) :
    TriGenPar (Finset.univ.image x) (A.image x) (B.image x) (x v) ∨
      TriGenFarP (Finset.univ.image x) (A.image x) (B.image x) (x v) ∨
      QuadTripleRect (Finset.univ.image x) (A.image x) (B.image x) (x v) := by
  classical
  have hV : (Finset.univ.image x).card = 7 := by
    rw [Finset.card_image_of_injective _ hx]; simp
  have cA : (A.image x).card = A.card := Finset.card_image_of_injective _ hx
  have cB : (B.image x).card = B.card := Finset.card_image_of_injective _ hx
  refine triGenPar_or_farP_quad hgen (Finset.image_subset_image (Finset.subset_univ A))
    (Finset.image_subset_image (Finset.subset_univ B))
    (by rw [← Finset.image_inter _ _ hx, hint, Finset.image_singleton])
    (by omega) (by omega) ?_ ?_
  · obtain ⟨w, hw, hwA⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := A.image x)
      (t := Finset.univ.image x) (by omega)
    exact ⟨w, hw, hwA⟩
  · obtain ⟨w, hw, hwB⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := B.image x)
      (t := Finset.univ.image x) (by omega)
    exact ⟨w, hw, hwB⟩


/-! ### The edge views: `EdgePar` or `EdgeFarP` when a face at the edge is a triangle -/

/-- A segment of `V` parallel to the edge `v w` of two faces that is not a `MidPair` joins two far
ends of one facet (as `par_pair`, along an edge: both functionals vanish at `v` and `w`). -/
theorem edge_par_pair {V Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {c : ℝ} (hint : Q1 ∩ Q2 = {v, w})
    (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hp : p ∈ V) (hq : q ∈ V) (hc : q - p = c • (w - v))
    (hnm : ¬ MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
      p q) :
    (p ∈ Q1 ∧ q ∈ Q1 ∧ (∀ x ∈ Q1, f2 p ≤ f2 x) ∧ (∀ x ∈ Q1, f2 q ≤ f2 x)) ∨
      (p ∈ Q2 ∧ q ∈ Q2 ∧ (∀ x ∈ Q2, f1 p ≤ f1 x) ∧ (∀ x ∈ Q2, f1 q ≤ f1 x)) := by
  have hv : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hw : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  rw [Finset.mem_inter] at hv hw
  have e1 : f1 (v + (w - v)) = 0 := by rw [add_sub_cancel]; exact z1 w hw.1
  have e2 : f2 (v + (w - v)) = 0 := by rw [add_sub_cancel]; exact z2 w hw.2
  have hq' : q = p + c • (w - v) := by rw [← hc]; abel
  have s1 : f1 q = f1 p := by rw [hq']; exact aff_shift f1 (z1 v hv.1) e1 p c
  have s2 : f2 q = f2 p := by rw [hq']; exact aff_shift f2 (z2 v hv.2) e2 p c
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

/-- **A triangle face at an edge has a unique far end**: the points of the triangle `Qa` where
the functional `fb` of the other face `Qb` is least form a single point (the triangle's third
vertex lies off `Qb`, so `fb` is negative there). -/
theorem tri_far_unique {V Qa Qb : Finset ℝ³} {v w : ℝ³} (hvw : v ≠ w)
    (hint : Qa ∩ Qb = {v, w}) (hcard : Qa.card = 3) {b : ℝ³} (hb : b ∈ Qa) (hbQ : b ∉ Qb)
    (hbV : b ∈ V) (fb : ℝ³ →ᵃ[ℝ] ℝ) (zb : ∀ p ∈ Qb, fb p = 0)
    (nb : ∀ p ∈ V, p ∉ Qb → fb p < 0) {x y : ℝ³} (hx : x ∈ Qa) (hy : y ∈ Qa)
    (fx : ∀ z ∈ Qa, fb x ≤ fb z) (fy : ∀ z ∈ Qa, fb y ≤ fb z) : x = y := by
  classical
  by_contra hxy
  have hv : v ∈ Qa ∩ Qb := by rw [hint]; simp
  have hw : w ∈ Qa ∩ Qb := by rw [hint]; simp
  rw [Finset.mem_inter] at hv hw
  have nbb := nb b hbV hbQ
  have xQ : x ∉ Qb := fun h => by have := fx b hb; rw [zb x h] at this; linarith
  have yQ : y ∉ Qb := fun h => by have := fy b hb; rw [zb y h] at this; linarith
  have hxv : x ≠ v := fun h => xQ (h ▸ hv.2)
  have hxw : x ≠ w := fun h => xQ (h ▸ hw.2)
  have hyv : y ≠ v := fun h => yQ (h ▸ hv.2)
  have hyw : y ≠ w := fun h => yQ (h ▸ hw.2)
  have h4 : ({v, w, x, y} : Finset ℝ³) ⊆ Qa := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h | h
    · rw [h]; exact hv.1
    · rw [h]; exact hw.1
    · rw [h]; exact hx
    · rw [h]; exact hy
  have hc4 : ({v, w, x, y} : Finset ℝ³).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hxy]
    · simp [Ne.symm hxw, Ne.symm hyw]
    · simp [hvw, Ne.symm hxv, Ne.symm hyv]
  have := Finset.card_le_card h4
  omega

/-- **The core of the edge dichotomy.**  A non-`MidPair` parallel segment `p q` of the face `Qa`
(a vertical far edge for the functional `fb`), with a triangle among the two faces, makes the far
depths `FarDepthOK` (at any other pair of functionals `ga`, `gb`). -/
theorem edgeDich_core {V Qa Qb : Finset ℝ³} {v w : ℝ³} (hgen : NoThreeCollinear V)
    (haV : Qa ⊆ V) (hbV : Qb ⊆ V) (hvw : v ≠ w) (hint : Qa ∩ Qb = {v, w})
    (hnea : ∃ p ∈ Qa, p ∉ Qb) (hneb : ∃ p ∈ Qb, p ∉ Qa) (hcard : Qa.card = 3 ∨ Qb.card = 3)
    (fb ga gb : ℝ³ →ᵃ[ℝ] ℝ) (zb : ∀ p ∈ Qb, fb p = 0) (nb : ∀ p ∈ V, p ∉ Qb → fb p < 0)
    (zga : ∀ p ∈ Qa, ga p = 0) (nga : ∀ p ∈ V, p ∉ Qa → ga p < 0)
    (zgb : ∀ p ∈ Qb, gb p = 0) (ngb : ∀ p ∈ V, p ∉ Qb → gb p < 0)
    (hnF : ¬ FarDepthOK Qa Qb (fun p => ∀ p' ∈ Qa, gb p ≤ gb p')
      (fun q => ∀ q' ∈ Qb, ga q ≤ ga q') (fun p => ⟪p, w - v⟫))
    {p q : ℝ³} {c : ℝ} (hp : p ∈ Qa) (hq : q ∈ Qa) (hpq : p ≠ q)
    (fp : ∀ x ∈ Qa, fb p ≤ fb x) (fq : ∀ x ∈ Qa, fb q ≤ fb x) (hc : q - p = c • (w - v)) :
    False := by
  classical
  obtain ⟨b, hbA, hbB⟩ := hnea
  rcases hcard with h3 | h3
  · exact hpq (tri_far_unique hvw hint h3 hbA hbB (haV hbA) fb zb nb hp hq fp fq)
  · have hq' : q = p + c • (w - v) := by rw [← hc]; abel
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hpq; rw [hq']; simp
    have hne : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
    have hdep : ⟪p, w - v⟫ ≠ ⟪q, w - v⟫ := by
      rw [hq', inner_add_left, real_inner_smul_left]
      have : 0 < ⟪w - v, w - v⟫ := real_inner_self_pos.mpr hne
      intro h
      have : c * ⟪w - v, w - v⟫ = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hc0 h
      · linarith
    obtain ⟨κ, hκ, hg⟩ := aff_prop hgen hbV (by omega) fb gb zb nb zgb ngb (haV hbA) hbB
    have gp : ∀ x ∈ Qa, gb p ≤ gb x := fun x hx => by
      rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fp x hx) hκ.le
    have gq : ∀ x ∈ Qa, gb q ≤ gb x := fun x hx => by
      rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fq x hx) hκ.le
    have hb' : Qb ∩ Qa = {v, w} := by rw [Finset.inter_comm]; exact hint
    obtain ⟨b', hb'B, hb'A⟩ := hneb
    apply hnF
    intro p0 hp0 q0 hq0 hne0 f0 g0 hd
    refine Or.inl ⟨?_, ?_⟩
    · by_cases h0 : ⟪p, w - v⟫ = ⟪p0, w - v⟫
      · exact ⟨q, hq, gq, fun h => hdep (h0.trans h.symm)⟩
      · exact ⟨p, hp, gp, fun h => h0 h⟩
    · intro q' hq' g'
      rw [tri_far_unique (V := V) hvw hb' h3 hb'B hb'A (hbV hb'B) ga zga nga hq' hq0 g' g0]

/-- **`EdgePar` or `EdgeFarP` along an edge shared by two facets one of which is a triangle**
(FEWER-FACES-PROOFS.md Proposition 23.19 (1)–(3)).  A segment parallel to the edge that is not a
`MidPair` is a vertical far edge of one facet; the triangle has a unique far end, so the far
depths are then `FarDepthOK` (a tie has the triangle's single far end on one side and a vertical
far edge on the other).  No residual remains. -/
theorem edgePar_or_farP {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (hgen : NoThreeCollinear V)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1) (hcard : Q1.card = 3 ∨ Q2.card = 3) :
    EdgePar V Q1 Q2 v w ∨ EdgeFarP V Q1 Q2 v w := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hP, hF⟩ := hcon
  have hP' : ∃ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → f1 p < 0) ∧
      (∀ p ∈ Q2, f2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → f2 p < 0) ∧
      ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ ({p, q} : Finset ℝ³) ≠ {v, w} ∧ ∃ c : ℝ, q - p = c • (w - v) ∧
        ¬ MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
          p q := by
    by_contra hc
    apply hP
    intro f1 f2 z1 n1 z2 n2 p hp q hq hpq hpv c hc'
    by_contra hnm
    exact hc ⟨f1, f2, z1, n1, z2, n2, p, hp, q, hq, hpq, hpv, c, hc', hnm⟩
  have hF' : ∃ g1 g2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, g1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → g1 p < 0) ∧
      (∀ p ∈ Q2, g2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → g2 p < 0) ∧
      ¬ FarDepthOK Q1 Q2 (fun p => ∀ p' ∈ Q1, g2 p ≤ g2 p')
        (fun q => ∀ q' ∈ Q2, g1 q ≤ g1 q') (fun p => ⟪p, w - v⟫) := by
    by_contra hc
    apply hF
    intro g1 g2 z1 n1 z2 n2
    by_contra hnm
    exact hc ⟨g1, g2, z1, n1, z2, n2, hnm⟩
  obtain ⟨f1, f2, z1, n1, z2, n2, p, hp, q, hq, hpq, -, c, hc, hnm⟩ := hP'
  obtain ⟨g1, g2, y1, m1, y2, m2, hnF⟩ := hF'
  rcases edge_par_pair hint f1 f2 z1 n1 z2 n2 hp hq hc hnm with
    ⟨hpQ, hqQ, fp, fq⟩ | ⟨hpQ, hqQ, fp, fq⟩
  · exact edgeDich_core hgen h1V h2V hvw hint hne1 hne2 hcard f2 g1 g2 z2 n2 y1 m1 y2 m2 hnF
      hpQ hqQ hpq fp fq hc
  · exact edgeDich_core hgen h2V h1V hvw (by rw [Finset.inter_comm]; exact hint) hne2 hne1
      hcard.symm f1 g2 g1 z1 n1 y2 m2 y1 m1 (fun H => hnF H.symm) hpQ hqQ hpq fp fq hc

/-- `edgePar_or_farP` for labelled points: two facets `A`, `B` of the labelled seven points
(each with at most six labels), meeting in the edge `v w`, one of them a triangle. -/
theorem edgePar_or_farP_idx {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x)) (A B : Finset (Fin 7)) (v w : Fin 7)
    (hvw : v ≠ w) (hint : A ∩ B = {v, w}) (hA : ∃ i ∈ A, i ∉ B) (hB : ∃ i ∈ B, i ∉ A)
    (hAB : A.card = 3 ∨ B.card = 3) :
    EdgePar (Finset.univ.image x) (A.image x) (B.image x) (x v) (x w) ∨
      EdgeFarP (Finset.univ.image x) (A.image x) (B.image x) (x v) (x w) := by
  classical
  refine edgePar_or_farP hgen (Finset.image_subset_image (Finset.subset_univ A))
    (Finset.image_subset_image (Finset.subset_univ B)) (fun h => hvw (hx h))
    (by rw [← Finset.image_inter _ _ hx, hint, Finset.image_insert, Finset.image_singleton])
    ?_ ?_ ?_
  · obtain ⟨i, hi, hiB⟩ := hA
    exact ⟨x i, Finset.mem_image_of_mem x hi, fun h => hiB (by
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      rwa [hx hji] at hj)⟩
  · obtain ⟨i, hi, hiA⟩ := hB
    exact ⟨x i, Finset.mem_image_of_mem x hi, fun h => hiA (by
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      rwa [hx hji] at hj)⟩
  · rw [Finset.card_image_of_injective _ hx, Finset.card_image_of_injective _ hx]
    exact hAB


/-! ### Two quadrilaterals at an edge: the residual is the edge rectangle -/

/-- A segment of `V` parallel to the edge `v w` has different depths at its ends. -/
theorem inner_ne_of_par {v w p q : ℝ³} {c : ℝ} (hvw : v ≠ w) (hpq : p ≠ q)
    (hc : q - p = c • (w - v)) : ⟪p, w - v⟫ ≠ ⟪q, w - v⟫ := by
  have hq' : q = p + c • (w - v) := by rw [← hc]; abel
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hpq; rw [hq']; simp
  have hne : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
  rw [hq', inner_add_left, real_inner_smul_left]
  have : 0 < ⟪w - v, w - v⟫ := real_inner_self_pos.mpr hne
  intro h
  have : c * ⟪w - v, w - v⟫ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hc0 h
  · linarith

/-- A face of the pair has at least three points. -/
theorem three_le_card_of_inter {Q1 Q2 : Finset ℝ³} {v w b : ℝ³} (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w}) (hb : b ∈ Q2) (hbQ : b ∉ Q1) : 3 ≤ Q2.card := by
  classical
  have hv : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hw : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  rw [Finset.mem_inter] at hv hw
  have hvb : v ≠ b := fun h => hbQ (h ▸ hv.1)
  have hwb : w ≠ b := fun h => hbQ (h ▸ hw.1)
  have h3 : ({v, w, b} : Finset ℝ³).card = 3 := Finset.card_eq_three.mpr ⟨v, w, b, hvw, hvb, hwb, rfl⟩
  have hsub : ({v, w, b} : Finset ℝ³) ⊆ Q2 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h
    · rw [h]; exact hv.2
    · rw [h]; exact hw.2
    · rw [h]; exact hb
  have := Finset.card_le_card hsub
  omega

/-- **The edge rectangle**: the residual position of two faces at an edge `v w` for which neither
`EdgePar` nor `EdgeFarP` holds.  At the (unique up to scale) functionals `f1`, `f2` the far ends
of `Q1` include two points `p`, `p'` at different depths along `w - v` (a vertical far edge,
parallel to the edge) and those of `Q2` two points `q`, `q'`, and the depths tie crosswise
(`p ~ q`, `p' ~ q'`).  A triangle face has a single far end, so this needs two faces with at least
four points (`edgePar_or_farP`). -/
def EdgeRect (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  ∃ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → f1 p < 0) ∧
    (∀ p ∈ Q2, f2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → f2 p < 0) ∧
    ∃ p ∈ Q1, ∃ p' ∈ Q1, ∃ q ∈ Q2, ∃ q' ∈ Q2,
      (∀ x ∈ Q1, f2 p ≤ f2 x) ∧ (∀ x ∈ Q1, f2 p' ≤ f2 x) ∧
      (∀ x ∈ Q2, f1 q ≤ f1 x) ∧ (∀ x ∈ Q2, f1 q' ≤ f1 x) ∧
      ⟪p, w - v⟫ = ⟪q, w - v⟫ ∧ ⟪p', w - v⟫ = ⟪q', w - v⟫ ∧ ⟪p, w - v⟫ ≠ ⟪p', w - v⟫

theorem EdgeRect.swap {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h : EdgeRect V Q2 Q1 v w) :
    EdgeRect V Q1 Q2 v w := by
  obtain ⟨f1, f2, z1, n1, z2, n2, p, hp, p', hp', q, hq, q', hq', a, b, c, d, t1, t2, t3⟩ := h
  exact ⟨f2, f1, z2, n2, z1, n1, q, hq, q', hq', p, hp, p', hp', c, d, a, b, t1.symm, t2.symm,
    fun e => t3 (by rw [t1, t2, e])⟩

/-- **A vertical far edge on one face and a failure of `FarDepthOK` give the rectangle.** -/
theorem rect_of_nonuniform {Q1 Q2 : Finset ℝ³} {far1 far2 : ℝ³ → Prop} {d : ℝ³ → ℝ}
    (h : ¬ FarDepthOK Q1 Q2 far1 far2 d) {p q : ℝ³} (hp : p ∈ Q1) (hq : q ∈ Q1) (fp : far1 p)
    (fq : far1 q) (hd : d p ≠ d q) :
    ∃ p0 ∈ Q1, ∃ p' ∈ Q1, ∃ q0 ∈ Q2, ∃ q' ∈ Q2, far1 p0 ∧ far1 p' ∧ far2 q0 ∧ far2 q' ∧
      d p0 = d q0 ∧ d p' = d q' ∧ d p0 ≠ d p' := by
  by_contra hcon
  apply h
  intro p0 hp0 q0 hq0 hne f0 g0 hdd
  have hp1 : ∃ p1 ∈ Q1, far1 p1 ∧ d p1 ≠ d p0 := by
    by_cases h0 : d p = d p0
    · exact ⟨q, hq, fq, fun e => hd (h0.trans e.symm)⟩
    · exact ⟨p, hp, fp, h0⟩
  obtain ⟨p1, hp1Q, hp1f, hp1d⟩ := hp1
  by_cases u : ∀ q' ∈ Q2, far2 q' → d q' = d q0
  · exact Or.inl ⟨⟨p1, hp1Q, hp1f, hp1d⟩, u⟩
  · push Not at u
    obtain ⟨q1, hq1Q, hq1f, hq1d⟩ := u
    refine Or.inr (Or.inr ⟨⟨p1, hp1Q, hp1f, hp1d⟩, ⟨q1, hq1Q, hq1f, hq1d⟩, ?_⟩)
    intro p' hp' f' dp' q' hq' g' dq' ne e
    exact hcon ⟨p0, hp0, p', hp', q0, hq0, q', hq', f0, f', g0, g', hdd, e, fun h => dp' h.symm⟩

/-- Two points of the faces `Q1`, `Q2` with equal values of both functionals differ by a multiple
of the edge `w - v`. -/
theorem edge_dir {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0) {p p' : ℝ³}
    (e1 : f1 p' = f1 p) (e2 : f2 p' = f2 p) : ∃ t : ℝ, p' - p = t • (w - v) := by
  have hv : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hw : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  rw [Finset.mem_inter] at hv hw
  obtain ⟨α1, β1, γ1, d1⟩ := aff_dif f1
  obtain ⟨α2, β2, γ2, d2⟩ := aff_dif f2
  have hu1 : α1 * (p' 0 - p 0) + β1 * (p' 1 - p 1) + γ1 * (p' 2 - p 2) = 0 := by
    rw [← d1 p p', e1]; ring
  have hu2 : α2 * (p' 0 - p 0) + β2 * (p' 1 - p 1) + γ2 * (p' 2 - p 2) = 0 := by
    rw [← d2 p p', e2]; ring
  have he1 : α1 * (w 0 - v 0) + β1 * (w 1 - v 1) + γ1 * (w 2 - v 2) = 0 := by
    rw [← d1 v w, z1 v hv.1, z1 w hw.1]; ring
  have he2 : α2 * (w 0 - v 0) + β2 * (w 1 - v 1) + γ2 * (w 2 - v 2) = 0 := by
    rw [← d2 v w, z2 v hv.2, z2 w hw.2]; ring
  obtain ⟨a, ha, haQ⟩ := hne1
  obtain ⟨b, hb, hbQ⟩ := hne2
  have ha1 : α1 * (a 0 - v 0) + β1 * (a 1 - v 1) + γ1 * (a 2 - v 2) = 0 := by
    rw [← d1 v a, z1 a ha, z1 v hv.1]; ring
  have ha2 : α2 * (a 0 - v 0) + β2 * (a 1 - v 1) + γ2 * (a 2 - v 2) ≠ 0 := by
    rw [← d2 v a, z2 v hv.2]
    have := n2 a (h1V ha) haQ
    linarith
  have hb1 : α1 * (b 0 - v 0) + β1 * (b 1 - v 1) + γ1 * (b 2 - v 2) ≠ 0 := by
    rw [← d1 v b, z1 v hv.1]
    have := n1 b (h2V hb) hbQ
    linarith
  have hne : w 0 - v 0 ≠ 0 ∨ w 1 - v 1 ≠ 0 ∨ w 2 - v 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hvw
    ext i
    fin_cases i
    · show v 0 = w 0
      linarith [hcon.1]
    · show v 1 = w 1
      linarith [hcon.2.1]
    · show v 2 = w 2
      linarith [hcon.2.2]
  obtain ⟨t, h0, h1, h2⟩ := ker_line α1 β1 γ1 α2 β2 γ2 (p' 0 - p 0) (p' 1 - p 1) (p' 2 - p 2)
    (w 0 - v 0) (w 1 - v 1) (w 2 - v 2) (a 0 - v 0) (a 1 - v 1) (a 2 - v 2)
    (b 0 - v 0) (b 1 - v 1) (b 2 - v 2) hu1 hu2 he1 he2 ha1 ha2 hb1 hne
  refine ⟨t, ?_⟩
  ext i
  fin_cases i
  · show p' 0 - p 0 = t * (w 0 - v 0)
    linarith
  · show p' 1 - p 1 = t * (w 1 - v 1)
    linarith
  · show p' 2 - p 2 = t * (w 2 - v 2)
    linarith

/-- **`EdgePar`, `EdgeFarP` or the edge rectangle** (no assumption on the faces).  A non-`MidPair`
segment parallel to the edge is a vertical far edge of one face, so that face has far ends at two
depths; a failure of `FarDepthOK` is then a crosswise tie of two far ends of each face
(`EdgeRect`). -/
theorem edgePar_or_farP_rect {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (hgen : NoThreeCollinear V)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1) :
    EdgePar V Q1 Q2 v w ∨ EdgeFarP V Q1 Q2 v w ∨ EdgeRect V Q1 Q2 v w := by
  classical
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hP, hF, hR⟩ := hcon
  have hP' : ∃ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → f1 p < 0) ∧
      (∀ p ∈ Q2, f2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → f2 p < 0) ∧
      ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ ({p, q} : Finset ℝ³) ≠ {v, w} ∧ ∃ c : ℝ, q - p = c • (w - v) ∧
        ¬ MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
          p q := by
    by_contra hc
    apply hP
    intro f1 f2 z1 n1 z2 n2 p hp q hq hpq hpv c hc'
    by_contra hnm
    exact hc ⟨f1, f2, z1, n1, z2, n2, p, hp, q, hq, hpq, hpv, c, hc', hnm⟩
  have hF' : ∃ g1 g2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, g1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → g1 p < 0) ∧
      (∀ p ∈ Q2, g2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → g2 p < 0) ∧
      ¬ FarDepthOK Q1 Q2 (fun p => ∀ p' ∈ Q1, g2 p ≤ g2 p')
        (fun q => ∀ q' ∈ Q2, g1 q ≤ g1 q') (fun p => ⟪p, w - v⟫) := by
    by_contra hc
    apply hF
    intro g1 g2 z1 n1 z2 n2
    by_contra hnm
    exact hc ⟨g1, g2, z1, n1, z2, n2, hnm⟩
  obtain ⟨f1, f2, z1, n1, z2, n2, p, hp, q, hq, hpq, -, c, hc, hnm⟩ := hP'
  obtain ⟨g1, g2, y1, m1, y2, m2, hnF⟩ := hF'
  obtain ⟨b, hbA, hbB⟩ := hne1
  obtain ⟨b', hb'B, hb'A⟩ := hne2
  have c1 : 3 ≤ Q1.card :=
    three_le_card_of_inter hvw (by rw [Finset.inter_comm]; exact hint) hbA hbB
  have c2 : 3 ≤ Q2.card := three_le_card_of_inter hvw hint hb'B hb'A
  have hd := inner_ne_of_par hvw hpq hc
  rcases edge_par_pair hint f1 f2 z1 n1 z2 n2 hp hq hc hnm with
    ⟨hpQ, hqQ, fp, fq⟩ | ⟨hpQ, hqQ, fp, fq⟩
  · obtain ⟨κ, hκ, hg⟩ := aff_prop hgen h2V c2 f2 g2 z2 n2 y2 m2 (h1V hbA) hbB
    have gp : ∀ x ∈ Q1, g2 p ≤ g2 x := fun x hx => by
      rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fp x hx) hκ.le
    have gq : ∀ x ∈ Q1, g2 q ≤ g2 x := fun x hx => by
      rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fq x hx) hκ.le
    obtain ⟨p0, hp0, p', hp', q0, hq0, q', hq', a1, a2, a3, a4, t1, t2, t3⟩ :=
      rect_of_nonuniform hnF hpQ hqQ gp gq hd
    exact hR ⟨g1, g2, y1, m1, y2, m2, p0, hp0, p', hp', q0, hq0, q', hq', a1, a2, a3, a4,
      t1, t2, t3⟩
  · obtain ⟨κ, hκ, hg⟩ := aff_prop hgen h1V c1 f1 g1 z1 n1 y1 m1 (h2V hb'B) hb'A
    have gp : ∀ x ∈ Q2, g1 p ≤ g1 x := fun x hx => by
      rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fp x hx) hκ.le
    have gq : ∀ x ∈ Q2, g1 q ≤ g1 x := fun x hx => by
      rw [hg, hg]; exact mul_le_mul_of_nonneg_left (fq x hx) hκ.le
    obtain ⟨p0, hp0, p', hp', q0, hq0, q', hq', a1, a2, a3, a4, t1, t2, t3⟩ :=
      rect_of_nonuniform (fun H => hnF H.symm) hpQ hqQ gp gq hd
    exact hR (EdgeRect.swap ⟨g2, g1, y2, m2, y1, m1, p0, hp0, p', hp', q0, hq0, q', hq',
      a1, a2, a3, a4, t1, t2, t3⟩)

/-- **The edge rectangle is a parallelogram.**  The four far ends of the rectangle lie off the
other face, are distinct in pairs, and `p' - p = q' - q`: they are the vertices of a (planar)
parallelogram whose two sides `p p'`, `q q'` are parallel to the edge. -/
theorem EdgeRect.parallelogram {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (hvw : v ≠ w)
    (hint : Q1 ∩ Q2 = {v, w}) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hne1 : ∃ p ∈ Q1, p ∉ Q2)
    (hne2 : ∃ p ∈ Q2, p ∉ Q1) (h : EdgeRect V Q1 Q2 v w) :
    ∃ p ∈ Q1, ∃ p' ∈ Q1, ∃ q ∈ Q2, ∃ q' ∈ Q2, p ∉ Q2 ∧ p' ∉ Q2 ∧ q ∉ Q1 ∧ q' ∉ Q1 ∧
      p ≠ p' ∧ q ≠ q' ∧ p' - p = q' - q ∧ ⟪p, w - v⟫ = ⟪q, w - v⟫ ∧ ⟪p', w - v⟫ = ⟪q', w - v⟫ := by
  obtain ⟨f1, f2, z1, n1, z2, n2, p, hp, p', hp', q, hq, q', hq', fp, fp', fq, fq', t1, t2, t3⟩ :=
    h
  obtain ⟨b, hbA, hbB⟩ := hne1
  obtain ⟨b', hb'B, hb'A⟩ := hne2
  have nb := n2 b (h1V hbA) hbB
  have nb' := n1 b' (h2V hb'B) hb'A
  have pQ : p ∉ Q2 := fun h => by have := fp b hbA; rw [z2 p h] at this; linarith
  have p'Q : p' ∉ Q2 := fun h => by have := fp' b hbA; rw [z2 p' h] at this; linarith
  have qQ : q ∉ Q1 := fun h => by have := fq b' hb'B; rw [z1 q h] at this; linarith
  have q'Q : q' ∉ Q1 := fun h => by have := fq' b' hb'B; rw [z1 q' h] at this; linarith
  have hpp : p ≠ p' := fun h => t3 (by rw [h])
  have hqq : q ≠ q' := fun h => t3 (by rw [t1, t2, h])
  obtain ⟨s, hs⟩ := edge_dir hvw hint h1V h2V ⟨b, hbA, hbB⟩ ⟨b', hb'B, hb'A⟩ f1 f2 z1 n1 z2 n2
    (p := p) (p' := p') (by rw [z1 p hp, z1 p' hp'])
    (le_antisymm (fp' p hp) (fp p' hp'))
  obtain ⟨s', hs'⟩ := edge_dir hvw hint h1V h2V ⟨b, hbA, hbB⟩ ⟨b', hb'B, hb'A⟩ f1 f2 z1 n1 z2 n2
    (p := q) (p' := q') (le_antisymm (fq' q hq) (fq q' hq')) (by rw [z2 q hq, z2 q' hq'])
  have hpos : 0 < ⟪w - v, w - v⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hvw.symm)
  have e1 : ⟪p', w - v⟫ = ⟪p, w - v⟫ + s * ⟪w - v, w - v⟫ := by
    have : p' = p + s • (w - v) := by rw [← hs]; abel
    rw [this, inner_add_left, real_inner_smul_left]
  have e2 : ⟪q', w - v⟫ = ⟪q, w - v⟫ + s' * ⟪w - v, w - v⟫ := by
    have : q' = q + s' • (w - v) := by rw [← hs']; abel
    rw [this, inner_add_left, real_inner_smul_left]
  have hss : s = s' := by
    have : (s - s') * ⟪w - v, w - v⟫ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  exact ⟨p, hp, p', hp', q, hq, q', hq', pQ, p'Q, qQ, q'Q, hpp, hqq, by rw [hs, hs', hss], t1, t2⟩

/-- `EdgePar` gives `EdgeTieR` (the tie clause of `EdgeTieR`, `TieHER`, always holds: a tie of
the far ends is accepted). -/
theorem EdgePar.toTieR {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h : EdgePar V Q1 Q2 v w) :
    EdgeTieR V Q1 Q2 v w := by
  intro f1 f2 z1 n1 z2 n2
  refine ⟨fun p hp q hq hpq hne c hc => h f1 f2 z1 n1 z2 n2 p hp q hq hpq hne c hc, ?_⟩
  intro p _ q _ _ _ _
  by_cases e : ⟪p, w - v⟫ = ⟪q, w - v⟫
  · exact Or.inr e
  · exact Or.inl (Or.inl e)

/-- `edgePar_or_farP_rect` for labelled points, as `EdgeTieR` or `EdgeFarP` or the rectangle. -/
theorem edgeTieR_or_farP_rect_idx {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x)) (A B : Finset (Fin 7)) (v w : Fin 7)
    (hvw : v ≠ w) (hint : A ∩ B = {v, w}) (hA : ∃ i ∈ A, i ∉ B) (hB : ∃ i ∈ B, i ∉ A) :
    EdgeTieR (Finset.univ.image x) (A.image x) (B.image x) (x v) (x w) ∨
      EdgeFarP (Finset.univ.image x) (A.image x) (B.image x) (x v) (x w) ∨
      EdgeRect (Finset.univ.image x) (A.image x) (B.image x) (x v) (x w) := by
  classical
  rcases edgePar_or_farP_rect hgen (Finset.image_subset_image (Finset.subset_univ A))
    (Finset.image_subset_image (Finset.subset_univ B)) (fun h => hvw (hx h))
    (by rw [← Finset.image_inter _ _ hx, hint, Finset.image_insert, Finset.image_singleton])
    (by
      obtain ⟨i, hi, hiB⟩ := hA
      exact ⟨x i, Finset.mem_image_of_mem x hi, fun h => hiB (by
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
        rwa [hx hji] at hj)⟩)
    (by
      obtain ⟨i, hi, hiA⟩ := hB
      exact ⟨x i, Finset.mem_image_of_mem x hi, fun h => hiA (by
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
        rwa [hx hji] at hj)⟩) with h | h | h
  · exact Or.inl h.toTieR
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **Labelled form of the rectangle's parallelogram**: for two facets `A`, `B` of the labelled
points meeting in the edge `v w`, the edge rectangle gives labels `i i' ∈ A \ B`, `j j' ∈ B \ A`
with `i ≠ i'`, `j ≠ j'` and `x i' - x i = x j' - x j`. -/
theorem EdgeRect.labels {x : Fin 7 → ℝ³} (hx : Function.Injective x) (A B : Finset (Fin 7))
    (v w : Fin 7) (hvw : v ≠ w) (hint : A ∩ B = {v, w}) (hA : ∃ i ∈ A, i ∉ B)
    (hB : ∃ i ∈ B, i ∉ A)
    (h : EdgeRect (Finset.univ.image x) (A.image x) (B.image x) (x v) (x w)) :
    ∃ i ∈ A, ∃ i' ∈ A, ∃ j ∈ B, ∃ j' ∈ B, i ∉ B ∧ i' ∉ B ∧ j ∉ A ∧ j' ∉ A ∧ i ≠ i' ∧ j ≠ j' ∧
      x i' - x i = x j' - x j ∧ ⟪x i, x w - x v⟫ = ⟪x j, x w - x v⟫ ∧
      ⟪x i', x w - x v⟫ = ⟪x j', x w - x v⟫ := by
  classical
  have hmem : ∀ (S : Finset (Fin 7)) (y : ℝ³), y ∈ S.image x ↔ ∃ i ∈ S, x i = y := fun S y => by
    simp [Finset.mem_image]
  obtain ⟨p, hp, p', hp', q, hq, q', hq', pQ, p'Q, qQ, q'Q, hpp, hqq, hrel, ht1, ht2⟩ :=
    EdgeRect.parallelogram (V := Finset.univ.image x) (fun h => hvw (hx h))
      (by rw [← Finset.image_inter _ _ hx, hint, Finset.image_insert, Finset.image_singleton])
      (Finset.image_subset_image (Finset.subset_univ A))
      (Finset.image_subset_image (Finset.subset_univ B))
      (by
        obtain ⟨i, hi, hiB⟩ := hA
        exact ⟨x i, Finset.mem_image_of_mem x hi, fun h => hiB (by
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
          rwa [hx hji] at hj)⟩)
      (by
        obtain ⟨i, hi, hiA⟩ := hB
        exact ⟨x i, Finset.mem_image_of_mem x hi, fun h => hiA (by
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
          rwa [hx hji] at hj)⟩) h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hp'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hq'
  exact ⟨i, hi, i', hi', j, hj, j', hj', fun h => pQ (Finset.mem_image_of_mem x h),
    fun h => p'Q (Finset.mem_image_of_mem x h), fun h => qQ (Finset.mem_image_of_mem x h),
    fun h => q'Q (Finset.mem_image_of_mem x h), fun h => hpp (by rw [h]),
    fun h => hqq (by rw [h]), hrel, ht1, ht2⟩

/-- An affine functional takes equal increments on equal vector differences. -/
theorem aff_parallelogram (f : ℝ³ →ᵃ[ℝ] ℝ) {p p' q q' : ℝ³} (h : p' - p = q' - q) :
    f p' - f p = f q' - f q := by
  have h1 := f.linearMap_vsub p' p
  have h2 := f.linearMap_vsub q' q
  simp only [vsub_eq_sub] at h1 h2
  rw [← h1, ← h2, h]


/-! ### The edge rectangle at types 13 and 19 is refuted by a triangle facet -/

/-- Type 13: the edge rectangle at the edge `45` of the quadrilaterals `0145`, `2456` would make
`0, 1, 2, 6` a parallelogram, but the triangle `126` is a facet. -/
theorem not_edgeRect_type13 {x : Fin 7 → ℝ³} (hx : Function.Injective x) (f : ℝ³ →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → f (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → f (x i) < 0)) :
    ¬ EdgeRect (Finset.univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5) := by
  intro h
  obtain ⟨i, hiA, i', hi'A, j, hjB, j', hj'B, hiB, hi'B, hjA, hj'A, hii, hjj, hrel, -, -⟩ :=
    EdgeRect.labels hx {0, 1, 4, 5} {2, 4, 5, 6} 4 5 (by decide) (by decide) (by decide)
      (by decide) h
  have key := aff_parallelogram f hrel
  have hA : ∀ i ∈ ({0, 1, 4, 5} : Finset (Fin 7)), i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) →
      i = 0 ∨ i = 1 := by decide
  have hB : ∀ i ∈ ({2, 4, 5, 6} : Finset (Fin 7)), i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) →
      i = 2 ∨ i = 6 := by decide
  have f0 : f (x 0) < 0 := (hf 0).2 (by decide)
  have f1 : f (x 1) = 0 := (hf 1).1 (by decide)
  have f2 : f (x 2) = 0 := (hf 2).1 (by decide)
  have f6 : f (x 6) = 0 := (hf 6).1 (by decide)
  rcases hA i hiA hiB with rfl | rfl <;> rcases hA i' hi'A hi'B with rfl | rfl <;>
    rcases hB j hjB hjA with rfl | rfl <;> rcases hB j' hj'B hj'A with rfl | rfl <;>
    first | exact absurd rfl hii | exact absurd rfl hjj | linarith

/-- Type 19: the edge rectangle at the edge `35` of the quadrilaterals `0235`, `1356` would make
`0, 2, 1, 6` a parallelogram, but the triangle `026` is a facet. -/
theorem not_edgeRect_type19 {x : Fin 7 → ℝ³} (hx : Function.Injective x) (f : ℝ³ →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (i ∈ ({0, 2, 6} : Finset (Fin 7)) → f (x i) = 0) ∧
      (i ∉ ({0, 2, 6} : Finset (Fin 7)) → f (x i) < 0)) :
    ¬ EdgeRect (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5) := by
  intro h
  obtain ⟨i, hiA, i', hi'A, j, hjB, j', hj'B, hiB, hi'B, hjA, hj'A, hii, hjj, hrel, -, -⟩ :=
    EdgeRect.labels hx {0, 2, 3, 5} {1, 3, 5, 6} 3 5 (by decide) (by decide) (by decide)
      (by decide) h
  have key := aff_parallelogram f hrel
  have hA : ∀ i ∈ ({0, 2, 3, 5} : Finset (Fin 7)), i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) →
      i = 0 ∨ i = 2 := by decide
  have hB : ∀ i ∈ ({1, 3, 5, 6} : Finset (Fin 7)), i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) →
      i = 1 ∨ i = 6 := by decide
  have f0 : f (x 0) = 0 := (hf 0).1 (by decide)
  have f1 : f (x 1) < 0 := (hf 1).2 (by decide)
  have f2 : f (x 2) = 0 := (hf 2).1 (by decide)
  have f6 : f (x 6) = 0 := (hf 6).1 (by decide)
  rcases hA i hiA hiB with rfl | rfl <;> rcases hA i' hi'A hi'B with rfl | rfl <;>
    rcases hB j hjB hjA with rfl | rfl <;> rcases hB j' hj'B hj'A with rfl | rfl <;>
    first | exact absurd rfl hii | exact absurd rfl hjj | linarith

end Minimality

end
