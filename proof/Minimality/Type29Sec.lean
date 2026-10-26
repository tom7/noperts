module

public import Minimality.Type29Limit
public import Minimality.Type16Sector

@[expose] public section

/-!
# Type 29: no horizontal-double-normal exception at the two-triangle views (§22.2, §28)

Proposition 22.2 (`isRupert_of_tiltHides`) at the named views of type 29 where both faces seen
edge-on are triangles: the edges `03` (`023`, `035`), `05` (`015`, `035`), `24` (`124`, `234`),
`35` (`035`, `356`), `34` (`234`, `346`) and the vertex lines `015/124`, `015/356`, `124/346`,
`035/234`.  As for types 16 and 21 (`Type16Sector.lean`, `Type21Sector.lean`), every closing
there is realized on both face circles (a triangle has no middle on the far side of its chord),
so the limit rim of any certificate at such a view has a hiding tilt under (G1); with a
horizontal double normal at the view, (G1) fails only in codimension 2 (§22.4).

* `triEdge29`, `TriVtx29`, `Sec29`: the tilt alternative at a named view.
* `Sec29.tiltHides`: the limit rim of a certificate at a view with `Sec29` has a hiding tilt.
* `isRupert_of_certL_seq29_or`: Lemma 18.2 for one labelled certificate with "no horizontal
  double normal at the view, or `Sec29`".
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The five edges of type 29 between two triangles that carry certificates, `(v, w, a, b)` for
the edge `vw` between the triangles `vwa`, `vwb`: `03` (`023`, `035`), `05` (`015`, `035`),
`24` (`234`, `124`), `35` (`035`, `356`), `34` (`234`, `346`). -/
def triEdge29 : Fin 5 → Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  ![(0, 3, 2, 5), (0, 5, 1, 3), (2, 4, 3, 1), (3, 5, 0, 6), (3, 4, 2, 6)]

/-- The vertex lines of type 29 between two triangles: `015/124`, `015/356`, `124/346`,
`035/234` (`vtxLines29` 3, 4, 5, 6). -/
def TriVtx29 (t : Fin 7) : Prop := t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6

/-- **The tilt alternative at a named view of type 29**: a two-triangle edge or vertex line with
(G1). -/
def Sec29 (x : Fin 7 → ℝ³) : View29 → Prop
  | .inl (i, j) => ∃ e : Fin 5,
      (((triEdge29 e).1 = i ∧ (triEdge29 e).2.1 = j) ∨
        ((triEdge29 e).1 = j ∧ (triEdge29 e).2.1 = i)) ∧
      G1Edge (univ.image x) (x (triEdge29 e).1) (x (triEdge29 e).2.1) (x (triEdge29 e).2.2.1)
        (x (triEdge29 e).2.2.2)
  | .inr t => TriVtx29 t ∧
      G1Vtx (univ.image x) (vtxView29 x t) (x (vtxLines29 t).1.1) (x (vtxLines29 t).1.2.1)
        (x (vtxLines29 t).1.2.2) (x (vtxLines29 t).2.1) (x (vtxLines29 t).2.2.1)
        (x (vtxLines29 t).2.2.2)

variable {x : Fin 7 → ℝ³}

/-- The four points of a two-triangle edge are not coplanar (the octahedron faces `023`, `035`
and so on are distinct planes): the determinant is a signed inequality of `NF29`. -/
theorem triEdge29_det (N : NF29 x) (e : Fin 5) :
    det3 (x (triEdge29 e).2.1 - x (triEdge29 e).1) (x (triEdge29 e).2.2.1 - x (triEdge29 e).1)
      (x (triEdge29 e).2.2.2 - x (triEdge29 e).1) ≠ 0 := by
  fin_cases e <;> simp only [triEdge29, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> nf29_simp N <;>
    simp only [det3c] <;> refine mul_ne_zero ?_ N.hD
  · have := N.hE35; intro h; apply this.ne; linarith
  · have := N.ha0; intro h; linarith
  · have := N.hb2; intro h; linarith
  · have := N.d035; intro h; linarith
  · have := N.d234; intro h; linarith

theorem triEdge29_ne (e : Fin 5) :
    (triEdge29 e).1 ≠ (triEdge29 e).2.1 ∧ (triEdge29 e).2.1 ≠ (triEdge29 e).2.2.1 ∧
      (triEdge29 e).1 ≠ (triEdge29 e).2.2.1 ∧ (triEdge29 e).2.1 ≠ (triEdge29 e).2.2.2 ∧
      (triEdge29 e).1 ≠ (triEdge29 e).2.2.2 := by
  fin_cases e <;> decide

theorem triVtx29_ne {t : Fin 7} (ht : TriVtx29 t) :
    (vtxLines29 t).1.1 ≠ (vtxLines29 t).1.2.1 ∧ (vtxLines29 t).1.2.1 ≠ (vtxLines29 t).1.2.2 ∧
      (vtxLines29 t).1.1 ≠ (vtxLines29 t).1.2.2 ∧ (vtxLines29 t).2.1 ≠ (vtxLines29 t).2.2.1 ∧
      (vtxLines29 t).2.2.1 ≠ (vtxLines29 t).2.2.2 ∧ (vtxLines29 t).2.1 ≠ (vtxLines29 t).2.2.2 := by
  rcases ht with rfl | rfl | rfl | rfl <;> decide

/-- **The tilt alternative gives a hiding tilt for the limit rim** of a certificate at a view
with `Sec29` (Proposition 22.2). -/
theorem Sec29.tiltHides (N : NF29 x) {v : View29}
    (hv0 : view29 x v ≠ 0) (hsec : Sec29 x v) (ε : Bool) {k : ℕ} [NeZero k]
    {lab : ZMod k → Fin 7} {y : Fin 7 → ℝ³} (hy : RimCertAt y (sgnB ε • view29 y v) lab)
    (hleft : ∀ m i, 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i))
      (sgnB ε • view29 x v)) :
    ∃ d, TiltHides (univ.image x) (sgnB ε • view29 x v) d (fun i => x (lab i)) := by
  have hk := hy.three
  have hlab := hy.lab_injective
  have hσ := sgnB_cases ε
  have hs := sgnB_ne_zero ε
  rcases v with ⟨i, j⟩ | t
  · obtain ⟨e, he, hpar, hG⟩ := hsec
    obtain ⟨n1, n2, n3, n4, n5⟩ := triEdge29_ne e
    set v₀ := (triEdge29 e).1
    set w₀ := (triEdge29 e).2.1
    set a₀ := (triEdge29 e).2.2.1
    set b₀ := (triEdge29 e).2.2.2
    obtain ⟨c, hc, hview, hnot⟩ : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        sgnB ε • view29 x (.inl (i, j)) = c • (x w₀ - x v₀) ∧
        ∀ m : ZMod k, ¬ ((lab m = v₀ ∧ lab (m + 1) = w₀) ∨ (lab m = w₀ ∧ lab (m + 1) = v₀)) := by
      have hna := hy.not_axle (i₀ := i) (j₀ := j)
      rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · refine ⟨sgnB ε, hσ, by rw [← e1, ← e2]; rfl, fun m => ?_⟩
        rw [e1, e2]; exact hna m
      · refine ⟨-sgnB ε, by rcases hσ with h | h <;> rw [h] <;> norm_num, ?_, fun m => ?_⟩
        · show sgnB ε • (x j - x i) = _
          rw [← e1, ← e2, neg_smul, ← smul_neg, neg_sub]
        · rw [e1, e2]; exact fun h => hna m (Or.comm.mp h)
    rw [hview] at hleft ⊢
    refine exists_tiltHides_limit N.inj hk hlab (hpar.smul (by rcases hc with h | h <;> rw [h] <;>
      norm_num)) hnot (p₁ := x v₀) (q₁ := x w₀) (r₁ := x a₀) (p₂ := x v₀) (q₂ := x w₀)
      (r₂ := x b₀) ⟨N.inj.ne n1, N.inj.ne n2, N.inj.ne n3⟩ ⟨N.inj.ne n1, N.inj.ne n4, N.inj.ne n5⟩
      ?_ (hG.sigma hc) hleft
    rw [cross_cross_common]
    exact smul_ne_zero (triEdge29_det N e) (sub_ne_zero.mpr (N.inj.ne n1).symm)
  · obtain ⟨ht, hpar, hG⟩ := hsec
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := triVtx29_ne ht
    have hnot : ∀ m : ZMod k, ¬ ((lab m = (vtxLines29 t).1.1 ∧ lab (m + 1) = (vtxLines29 t).1.1) ∨
        (lab m = (vtxLines29 t).1.1 ∧ lab (m + 1) = (vtxLines29 t).1.1)) := by
      intro m h
      have e : lab m = lab (m + 1) := by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact zmod_ne_add_one (by omega) m (hlab e)
    refine exists_tiltHides_limit N.inj hk hlab (hpar.parOnly _ |>.smul hs) hnot
      ⟨N.inj.ne n1, N.inj.ne n2, N.inj.ne n3⟩ ⟨N.inj.ne n4, N.inj.ne n5, N.inj.ne n6⟩ ?_
      (hG.sigma hσ) hleft
    rw [← planeLine_eq_cross16]
    exact hv0

end Minimality

end
