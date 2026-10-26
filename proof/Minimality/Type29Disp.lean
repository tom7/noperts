module

public import Minimality.Type29TwoFace
public import Minimality.Type29EdgeE
public import Minimality.Type29Vtx

@[expose] public section

/-!
# Type 29: the dispatcher on the closings (`FEWER-FACES-PROOFS.md` §22, §28.5)

`Cond29 N ℓ` is the codimension-2 condition at the closing `ℓ` of the whitelists (Theorem 28.10):
* at a view between two triangles (`SecView29`: the edges `03`, `05`, `24`, `35`, `34`, the lines
  `015/124`, `015/356`, `124/346`, `035/234`): no horizontal double normal, or the tilt alternative
  `Sec29` (22.2: (G1) at the view);
* at `V`, `V′`, `T2` with the rim `(4, 3, 6)` (a triangle and the quad, realized on both
  circles) and `Y2` (the edge `46`): no horizontal double normal, or (G1) with no segment
  parallel to the view and distinct depths there (`TwoGen29`, `TwoEdgeGen29`);
* at the Lemma E edges `14`, `15`, `46`, `56` (eight edge pairs): no horizontal double normal, or
  `EdgeOK29` (`EdgeGen` for the two faces and the Lemma E planes);
* at `T1 = 012/1456` (P14, P11): no horizontal double normal, or `VtxGen` and not
  (`h2 = 1` and `θ = α`) (Lemma 28.7);
* at `T2 = 1456/234` with a four-corner rim: no horizontal double normal, or `VtxGen` and not
  (`h0 = 1` and `h2 = 1`) (Lemma 28.8); with the triangle rim `(4, 3, 5)`: or (G1) (22.6 (b)).
Every closing of the whitelists is in one of these classes (`Lab29.sec_or_special`).
`close29` closes one closing at the limit; `isRupert_of_cert_seq29_hdn` assembles them.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- The named views between two triangles: the edges `03`, `05`, `24`, `35`, `34` and the vertex
lines `015/124`, `015/356`, `124/346`, `035/234`. -/
def SecView29 : View29 → Prop
  | .inl (i, j) => ∃ e : Fin 5,
      ((triEdge29 e).1 = i ∧ (triEdge29 e).2.1 = j) ∨ ((triEdge29 e).1 = j ∧ (triEdge29 e).2.1 = i)
  | .inr t => TriVtx29 t

/-- `V = 035/1456` at `5`, rim `(5, 1, 2, 3)` (class A). -/
def lV29 : Lab29 := .inl (.inr 2, (5, 1, 2, 3), Ex29.none)

/-- `V′ = 1456/234` at `4`, rim `(4, 1, 0, 3)` (class B1). -/
def lV'29 : Lab29 := .inl (.inr 1, (4, 1, 0, 3), Ex29.none)

/-- `T2` with the triangle rim `(4, 3, 6)` (`T2c`). -/
def lT2c29 : Lab29 := .inr (.inr (.inl (.inr 1, (4, 3, 6), Ex29.t2)))

/-- `T2` with the triangle rim `(4, 3, 5)` (`T2b`, 0 hidden). -/
def lT2b29 : Lab29 := .inr (.inr (.inl (.inr 1, (4, 3, 5), Ex29.t2)))

/-- `Y2 = 1456/346-4`, the five-corner rim `(6, 3, 2, 0, 5)` at the segment `46`. -/
def lY229 : Lab29 := .inr (.inl (.inl (4, 6), (6, 3, 2, 0, 5)))

/-- `T1 = 012/1456` at `1`, the four-corner rim `(1, 2, 3, 6)` in the regions `P14`
(`θ ≥ α`, `h2 ≤ 1`, the partner `T2` failing) and `P11` (`1 ≤ h2`, the partner `T3` failing). -/
def lT1a : Lab29 := .inl (.inr 0, (1, 2, 3, 6), Ex29.t1)
def lT1b : Lab29 := .inl (.inr 0, (1, 2, 3, 6), Ex29.t1o)

/-- `T2 = 1456/234` at `4`, the four-corner rims `(4, 3, 0, 5)` (region `h0 ≤ h2 ≤ 1`, P14) and
`(4, 2, 0, 5)` (region `h0 ≤ 1 ≤ h2`, X and P13). -/
def lT2q1 : Lab29 := .inl (.inr 1, (4, 3, 0, 5), Ex29.t2)
def lT2q2 : Lab29 := .inl (.inr 1, (4, 2, 0, 5), Ex29.t2o)

/-- The edge pairs of Lemma E at the quadrilateral-triangle segments `14` (three), `15`
(three), `56` and `46`: `(4,1,5,2,3)`, `(4,1,6,2,3)`, `(1,4,2,5,0)`, `(1,5,4,0,2)`,
`(5,1,0,4,3)`, `(5,1,0,6,3)`, `(6,5,3,1,2)`, `(4,6,3,1,2)`. -/
def lE1 : Lab29 := .inr (.inr (.inr (4, 1, 5, 2, 3)))
def lE2 : Lab29 := .inr (.inr (.inr (4, 1, 6, 2, 3)))
def lE3 : Lab29 := .inr (.inr (.inr (1, 4, 2, 5, 0)))
def lE4 : Lab29 := .inr (.inr (.inr (1, 5, 4, 0, 2)))
def lE5 : Lab29 := .inr (.inr (.inr (5, 1, 0, 4, 3)))
def lE6 : Lab29 := .inr (.inr (.inr (5, 1, 0, 6, 3)))
def lE7 : Lab29 := .inr (.inr (.inr (6, 5, 3, 1, 2)))
def lE8 : Lab29 := .inr (.inr (.inr (4, 6, 3, 1, 2)))

/-- The closings with a condition of their own (not "no horizontal double normal"). -/
def Lab29.Special (ℓ : Lab29) : Prop :=
  ℓ = lV29 ∨ ℓ = lV'29 ∨ ℓ = lT1a ∨ ℓ = lT1b ∨ ℓ = lT2c29 ∨ ℓ = lT2b29 ∨ ℓ = lT2q1 ∨
    ℓ = lT2q2 ∨ ℓ = lY229 ∨ ℓ = lE1 ∨ ℓ = lE2 ∨ ℓ = lE3 ∨ ℓ = lE4 ∨
    ℓ = lE5 ∨ ℓ = lE6 ∨ ℓ = lE7 ∨ ℓ = lE8

/-- **The condition at one closing** (Theorem 28.10; §22.2 at two face circles, §22.3–22.8 at the
Lemma E edges and the one-circle vertex lines, Lemmas 28.7 and 28.8). -/
def Cond29 {x : Fin 7 → ℝ³} (N : NF29 x) (ℓ : Lab29) : Prop :=
  (SecView29 ℓ.view → NoHDNAt (univ.image x) (view29 x ℓ.view) ∨ Sec29 x ℓ.view) ∧
  (ℓ = lV29 → NoHDNAt (univ.image x) (view29 x (.inr 2)) ∨
    TwoGen29 (univ.image x) (view29 x (.inr 2)) (({0, 3, 5} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x)) ∧
  (ℓ = lV'29 → NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
    TwoGen29 (univ.image x) (view29 x (.inr 1)) (({2, 3, 4} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x)) ∧
  (ℓ = lT1a → NoHDNAt (univ.image x) (view29 x (.inr 0)) ∨
    (VtxGen (univ.image x) (view29 x (.inr 0)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({0, 1, 2} : Finset (Fin 7)).image x) N.f1456.N ∧
      ¬ (N.h2 = 1 ∧ -N.a2 * N.t + N.b2 * N.s = 0))) ∧
  (ℓ = lT1b → NoHDNAt (univ.image x) (view29 x (.inr 0)) ∨
    (VtxGen (univ.image x) (view29 x (.inr 0)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({0, 1, 2} : Finset (Fin 7)).image x) N.f1456.N ∧
      ¬ (N.h2 = 1 ∧ -N.a2 * N.t + N.b2 * N.s = 0))) ∧
  (ℓ = lT2c29 → NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
    TwoGen29 (univ.image x) (view29 x (.inr 1)) (({2, 3, 4} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x)) ∧
  (ℓ = lT2b29 → NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
    TwoGen29 (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x)) ∧
  (ℓ = lT2q1 → NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
    (VtxGen (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x) N.f1456.N ∧ ¬ (N.h0 = 1 ∧ N.h2 = 1))) ∧
  (ℓ = lT2q2 → NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
    (VtxGen (univ.image x) (view29 x (.inr 1)) (({1, 4, 5, 6} : Finset (Fin 7)).image x)
      (({2, 3, 4} : Finset (Fin 7)).image x) N.f1456.N ∧ ¬ (N.h0 = 1 ∧ N.h2 = 1))) ∧
  (ℓ = lY229 → NoHDNAt (univ.image x) (view29 x (.inl (4, 6))) ∨
    TwoEdgeGen29 (univ.image x) (view29 x (.inl (4, 6))) (x 4) (x 6)
      (({3, 4, 6} : Finset (Fin 7)).image x) (({1, 4, 5, 6} : Finset (Fin 7)).image x)) ∧
  (ℓ = lE1 → NoHDNAt (univ.image x) (view29 x (.inl (4, 1))) ∨
    EdgeOK29 x 4 1 5 2 3 {1, 4, 5, 6} {1, 2, 4}) ∧
  (ℓ = lE2 → NoHDNAt (univ.image x) (view29 x (.inl (4, 1))) ∨
    EdgeOK29 x 4 1 6 2 3 {1, 4, 5, 6} {1, 2, 4}) ∧
  (ℓ = lE3 → NoHDNAt (univ.image x) (view29 x (.inl (1, 4))) ∨
    EdgeOK29 x 1 4 2 5 0 {1, 2, 4} {1, 4, 5, 6}) ∧
  (ℓ = lE4 → NoHDNAt (univ.image x) (view29 x (.inl (1, 5))) ∨
    EdgeOK29 x 1 5 4 0 2 {1, 4, 5, 6} {0, 1, 5}) ∧
  (ℓ = lE5 → NoHDNAt (univ.image x) (view29 x (.inl (5, 1))) ∨
    EdgeOK29 x 5 1 0 4 3 {0, 1, 5} {1, 4, 5, 6}) ∧
  (ℓ = lE6 → NoHDNAt (univ.image x) (view29 x (.inl (5, 1))) ∨
    EdgeOK29 x 5 1 0 6 3 {0, 1, 5} {1, 4, 5, 6}) ∧
  (ℓ = lE7 → NoHDNAt (univ.image x) (view29 x (.inl (6, 5))) ∨
    EdgeOK29 x 6 5 3 1 2 {3, 5, 6} {1, 4, 5, 6}) ∧
  (ℓ = lE8 → NoHDNAt (univ.image x) (view29 x (.inl (4, 6))) ∨
    EdgeOK29 x 4 6 3 1 2 {3, 4, 6} {1, 4, 5, 6})

/-! ### The two-face closings -/

theorem close29_V (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (ε : Bool)
    (hH : NoHDNAt (univ.image x) (view29 x (.inr 2)) ∨
      TwoGen29 (univ.image x) (view29 x (.inr 2)) (({0, 3, 5} : Finset (Fin 7)).image x)
        (({1, 4, 5, 6} : Finset (Fin 7)).image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 2)) (quad 5 1 2 3) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  rcases hH with h | h
  · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl h) hc
  · exact isRupert_twoFaceVtx29 N (.inr 2) (N.view29_ne_zero _ (by simp)) ε (quad 5 1 2 3)
      N.f035 N.f1456 N.f015 (a := 3) (b := 5) (c := 0) (p := 5) (q := 1) (q₁ := 4) (q₂ := 6)
      (vv := 5) (e := 3) (jT := 1) (jQ := 0) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) K hK h hc

theorem close29_V' (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (ε : Bool)
    (hH : NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
      TwoGen29 (univ.image x) (view29 x (.inr 1)) (({2, 3, 4} : Finset (Fin 7)).image x)
        (({1, 4, 5, 6} : Finset (Fin 7)).image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 1)) (quad 4 1 0 3) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  rcases hH with h | h
  · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl h) hc
  · exact isRupert_twoFaceVtx29 N (.inr 1) (N.view29_ne_zero _ (by simp)) ε (quad 4 1 0 3)
      N.f234 N.f1456 N.f124 (a := 3) (b := 4) (c := 2) (p := 4) (q := 1) (q₁ := 5) (q₂ := 6)
      (vv := 4) (e := 3) (jT := 1) (jQ := 0) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) K hK h hc

theorem close29_T2c (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (ε : Bool)
    (hH : NoHDNAt (univ.image x) (view29 x (.inr 1)) ∨
      TwoGen29 (univ.image x) (view29 x (.inr 1)) (({2, 3, 4} : Finset (Fin 7)).image x)
        (({1, 4, 5, 6} : Finset (Fin 7)).image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inr 1)) (tri 4 3 6) ∧
      TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  rcases hH with h | h
  · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl h) hc
  · exact isRupert_twoFaceVtx29 N (.inr 1) (N.view29_ne_zero _ (by simp)) ε (tri 4 3 6)
      N.f234 N.f1456 N.f346 (a := 4) (b := 3) (c := 2) (p := 6) (q := 4) (q₁ := 1) (q₂ := 5)
      (vv := 4) (e := 3) (jT := 1) (jQ := 0) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) K hK h hc

theorem close29_Y2 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (ε : Bool)
    (hH : NoHDNAt (univ.image x) (view29 x (.inl (4, 6))) ∨
      TwoEdgeGen29 (univ.image x) (view29 x (.inl (4, 6))) (x 4) (x 6)
        (({3, 4, 6} : Finset (Fin 7)).image x) (({1, 4, 5, 6} : Finset (Fin 7)).image x))
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) (.inl (4, 6)))
      (quint 6 3 2 0 5) ∧ TiesAt29 x (K n)) : IsRupert (univ.image x) := by
  rcases hH with h | h
  · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl h) hc
  · exact isRupert_twoFaceEdge29 N (v := 4) (w := 6) (by decide) ε (quint 6 3 2 0 5)
      N.f346 N.f1456 N.f356 (a := 6) (b := 3) (c := 4) (p := 5) (q := 6) (q₁ := 1) (q₂ := 4)
      (vv := 4) (e := 3) (jT := 0) (jQ := 0) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) K hK h hc

instance : DecidablePred SecView29 := by
  intro v
  rcases v with ⟨i, j⟩ | t
  · unfold SecView29; infer_instance
  · unfold SecView29 TriVtx29; infer_instance

/-- **Every closing of the whitelists is at a two-triangle view or has a condition of its own.** -/
theorem Lab29.sec_or_special : ∀ ℓ : Lab29, ℓ.Ok → SecView29 ℓ.view ∨ ℓ.Special := by
  intro ℓ hℓ
  rcases ℓ with ⟨v, ⟨i₀, i₁, i₂, i₃⟩, e⟩ | ⟨v, ⟨i₀, i₁, i₂, i₃, i₄⟩⟩ | ⟨v, ⟨i₀, i₁, i₂⟩, e⟩ |
    ⟨v, w, a, b, c⟩
  · simp only [Lab29.Ok, quadLabels29, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hℓ
    rcases hℓ with ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ |
      ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ |
      ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ |
      ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ |
      ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ |
      ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ |
      ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ <;>
      first
      | exact Or.inl (by decide)
      | exact Or.inr (by simp [Lab29.Special, lV29, lV'29, lT1a, lT1b, lT2q1, lT2q2])
  · simp only [Lab29.Ok, quintLabels29, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hℓ
    rcases hℓ with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
      first
      | exact Or.inl (by decide)
      | exact Or.inr (by simp [Lab29.Special, lY229])
  · simp only [Lab29.Ok, triLabels29, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hℓ
    rcases hℓ with ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ <;>
      exact Or.inr (by simp [Lab29.Special, lT2b29, lT2c29])
  · simp only [Lab29.Ok, ePairLabels29, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hℓ
    rcases hℓ with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
      first
      | exact Or.inl (by decide)
      | exact Or.inr (by simp [Lab29.Special, lE1, lE2, lE3, lE4, lE5, lE6, lE7, lE8])

/-! ### One closing at the limit -/

theorem Lab29.not_special_quad {q : View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7) × Ex29}
    (h1 : (Sum.inl q : Lab29) ≠ lV29) (h2 : (Sum.inl q : Lab29) ≠ lV'29)
    (h3 : (Sum.inl q : Lab29) ≠ lT2q1) (h4 : (Sum.inl q : Lab29) ≠ lT2q2)
    (h5 : (Sum.inl q : Lab29) ≠ lT1a) (h6 : (Sum.inl q : Lab29) ≠ lT1b) :
    ¬ Lab29.Special (Sum.inl q) := by
  simp only [Lab29.Special, lT2c29, lT2b29, lY229, lE1, lE2, lE3, lE4, lE5, lE6, lE7, lE8,
    reduceCtorEq, false_or, or_false, not_or]
  exact ⟨h1, h2, h5, h6, h3, h4⟩

theorem Lab29.not_special_quint {q : View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)}
    (h : (Sum.inr (Sum.inl q) : Lab29) ≠ lY229) : ¬ Lab29.Special (Sum.inr (Sum.inl q)) := by
  simp only [Lab29.Special, lV29, lV'29, lT1a, lT1b, lT2c29, lT2b29, lT2q1, lT2q2, lE1, lE2, lE3,
    lE4, lE5, lE6, lE7, lE8, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq, false_or, or_false, not_or]
  exact h

theorem Lab29.not_special_tri {q : View29 × (Fin 7 × Fin 7 × Fin 7) × Ex29}
    (h : (Sum.inr (Sum.inr (Sum.inl q)) : Lab29) ≠ lT2c29)
    (h' : (Sum.inr (Sum.inr (Sum.inl q)) : Lab29) ≠ lT2b29) :
    ¬ Lab29.Special (Sum.inr (Sum.inr (Sum.inl q))) := by
  simp only [Lab29.Special, lV29, lV'29, lT1a, lT1b, lT2q1, lT2q2, lY229, lE1, lE2, lE3, lE4, lE5,
    lE6, lE7, lE8, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq, false_or, or_false, not_or]
  exact ⟨h, h'⟩

/-- **A frequent certificate of one closing** (Lemma 18.2 with §22): under `Cond29`, the limit
is Rupert. -/
theorem close29 (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (θs : ℕ → Fin 8 → ℝ)
    (hθs : Tendsto θs atTop (𝓝 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t]))
    (ℓ : Lab29) (hok : ℓ.Ok) (hH : Cond29 N ℓ)
    (hp : ∃ᶠ n in atTop, CertAt29 (K n) ℓ ∧ TiesAt29 x (K n) ∧
      ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, CertAt29 (K n) ℓ ∧ TiesAt29 x (K n) :=
    hp.mono fun n hn => ⟨hn.1, hn.2.1⟩
  obtain ⟨hsec, hV, hV', hT1a, hT1b, hT, hTb, hQ1, hQ2, hY, hE1, hE2, hE3, hE4, hE5, hE6, hE7,
    hE8⟩ := hH
  rcases ℓ with ⟨v, ⟨i₀, i₁, i₂, i₃⟩, e⟩ | ⟨v, ⟨i₀, i₁, i₂, i₃, i₄⟩⟩ | ⟨v, ⟨i₀, i₁, i₂⟩, e⟩ |
    ⟨v, w, a, b, c⟩
  · obtain ⟨ε, hε⟩ : ∃ ε : Bool, ∃ᶠ n in atTop,
        RimCertAt (K n) (sgnB ε • view29 (K n) v) (quad i₀ i₁ i₂ i₃) ∧ TiesAt29 x (K n) :=
      frequently_exists_of_finite (h.mono fun n hn => by
        obtain ⟨-, ε, hr⟩ := hn.1.quad_at
        exact ⟨ε, hr, hn.2⟩)
    by_cases hs : SecView29 v
    · exact isRupert_of_certL_seq29_or N K hK v ε _ (hsec hs) hε
    by_cases h1 : (Sum.inl (v, (i₀, i₁, i₂, i₃), e) : Lab29) = lV29
    · simp only [lV29, Sum.inl.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h1
      exact close29_V N K hK ε (hV rfl) hε
    by_cases h2 : (Sum.inl (v, (i₀, i₁, i₂, i₃), e) : Lab29) = lV'29
    · simp only [lV'29, Sum.inl.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h2
      exact close29_V' N K hK ε (hV' rfl) hε
    by_cases h3 : (Sum.inl (v, (i₀, i₁, i₂, i₃), e) : Lab29) = lT2q1
    · simp only [lT2q1, Sum.inl.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h3
      have hex : Ex29.lim N Ex29.t2 := Ex29.lim_of_freq N K hK θs hθs _
        (hp.mono fun n hn => ⟨hn.1.1, hn.2.2⟩)
      rcases hQ1 rfl with hn | ⟨hg, hne⟩
      · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl hn) hε
      · refine isRupert_T2quad29 N (b := 3) (m := 2) (by decide) (by decide) (by decide) ?_ K hK
          ε hg hε
        intro heq
        have h01 := N.f1456_eq heq
        simp only [Matrix.cons_val_zero, Matrix.cons_val] at h01
        exact hne ⟨by linarith, by obtain ⟨a, b⟩ := hex; linarith⟩
    by_cases h4 : (Sum.inl (v, (i₀, i₁, i₂, i₃), e) : Lab29) = lT2q2
    · simp only [lT2q2, Sum.inl.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h4
      have hex : Ex29.lim N Ex29.t2o := Ex29.lim_of_freq N K hK θs hθs _
        (hp.mono fun n hn => ⟨hn.1.1, hn.2.2⟩)
      rcases hQ2 rfl with hn | ⟨hg, hne⟩
      · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl hn) hε
      · refine isRupert_T2quad29 N (b := 2) (m := 3) (by decide) (by decide) (by decide) ?_ K hK
          ε hg hε
        intro heq
        have h01 := N.f1456_eq heq
        simp only [Matrix.cons_val_zero, Matrix.cons_val] at h01
        obtain ⟨a, b⟩ := hex
        exact hne ⟨by linarith, by linarith⟩
    by_cases h5 : (Sum.inl (v, (i₀, i₁, i₂, i₃), e) : Lab29) = lT1a
    · simp only [lT1a, Sum.inl.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h5
      have hex : Ex29.lim N Ex29.t1 := Ex29.lim_of_freq N K hK θs hθs _
        (hp.mono fun n hn => ⟨hn.1.1, hn.2.2⟩)
      rcases hT1a rfl with hn | ⟨hg, hne⟩
      · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl hn) hε
      · exact isRupert_T1_29 N K hK ε hg
          (fun hh => lt_of_le_of_ne hex.1.1 (fun e => hne ⟨hh, e.symm⟩))
          (fun hh => T1_esc_P14 N hh hex.2) hε
    by_cases h6 : (Sum.inl (v, (i₀, i₁, i₂, i₃), e) : Lab29) = lT1b
    · simp only [lT1b, Sum.inl.injEq, Prod.mk.injEq] at h6
      obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h6
      have hex : Ex29.lim N Ex29.t1o := Ex29.lim_of_freq N K hK θs hθs _
        (hp.mono fun n hn => ⟨hn.1.1, hn.2.2⟩)
      rcases hT1b rfl with hn | ⟨hg, hne⟩
      · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl hn) hε
      · exact isRupert_T1_29 N K hK ε hg
          (fun hh => lt_of_le_of_ne hex.1.1 (fun e => hne ⟨hh, e.symm⟩))
          (fun hh => T1_esc_P11 N hex.2) hε
    exact absurd ((Lab29.sec_or_special _ hok).resolve_left hs)
      (Lab29.not_special_quad h1 h2 h3 h4 h5 h6)
  · obtain ⟨ε, hε⟩ : ∃ ε : Bool, ∃ᶠ n in atTop,
        RimCertAt (K n) (sgnB ε • view29 (K n) v) (quint i₀ i₁ i₂ i₃ i₄) ∧ TiesAt29 x (K n) :=
      frequently_exists_of_finite (h.mono fun n hn => by
        obtain ⟨ε, hr⟩ := hn.1.quint_at
        exact ⟨ε, hr, hn.2⟩)
    by_cases hs : SecView29 v
    · exact isRupert_of_certL_seq29_or N K hK v ε _ (hsec hs) hε
    by_cases h1 : (Sum.inr (Sum.inl (v, (i₀, i₁, i₂, i₃, i₄))) : Lab29) = lY229
    · simp only [lY229, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
      exact close29_Y2 N K hK ε (hY rfl) hε
    exact absurd ((Lab29.sec_or_special _ hok).resolve_left hs) (Lab29.not_special_quint h1)
  · obtain ⟨ε, hε⟩ : ∃ ε : Bool, ∃ᶠ n in atTop,
        RimCertAt (K n) (sgnB ε • view29 (K n) v) (tri i₀ i₁ i₂) ∧ TiesAt29 x (K n) :=
      frequently_exists_of_finite (h.mono fun n hn => by
        obtain ⟨-, ε, hr⟩ := hn.1.tri_at
        exact ⟨ε, hr, hn.2⟩)
    by_cases hs : SecView29 v
    · exact isRupert_of_certL_seq29_or N K hK v ε _ (hsec hs) hε
    by_cases h1 : (Sum.inr (Sum.inr (Sum.inl (v, (i₀, i₁, i₂), e))) : Lab29) = lT2c29
    · simp only [lT2c29, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := h1
      exact close29_T2c N K hK ε (hT rfl) hε
    by_cases h2 : (Sum.inr (Sum.inr (Sum.inl (v, (i₀, i₁, i₂), e))) : Lab29) = lT2b29
    · simp only [lT2b29, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := h2
      rcases hTb rfl with hn | hg
      · exact isRupert_of_certL_seq29_or N K hK _ ε _ (Or.inl hn) hε
      · exact isRupert_T2tri29 N K hK ε hg hε
    exact absurd ((Lab29.sec_or_special _ hok).resolve_left hs) (Lab29.not_special_tri h1 h2)
  · -- an edge pair: at a two-triangle segment by the tilt, at a quadrilateral-triangle segment
    -- by Lemma E at the limit
    have key : (NoHDNAt (univ.image x) (view29 x (.inl (v, w))) ∨ Sec29 x (.inl (v, w))) →
        IsRupert (univ.image x) := fun hsec' => by
      obtain ⟨⟨ε, L⟩, hL⟩ : ∃ q : Bool × ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
          ∃ᶠ n in atTop, CertL29 (K n) (.inl (v, w)) q.1 q.2 ∧ TiesAt29 x (K n) :=
        frequently_exists_of_finite (h.mono fun n hn => by
          obtain ⟨ε, L, hL⟩ := hn.1.epair_at
          exact ⟨(ε, L), hL, hn.2⟩)
      rcases L with lab | lab | lab
      · exact isRupert_of_certL_seq29_or N K hK _ ε lab hsec' hL
      · exact isRupert_of_certL_seq29_or N K hK _ ε lab hsec' hL
      · exact isRupert_of_certL_seq29_or N K hK _ ε lab hsec' hL
    by_cases hs : SecView29 (.inl (v, w))
    · exact key (hsec hs)
    have hf := h.mono fun n hn => hn.1
    simp only [Lab29.Ok, ePairLabels29, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hok
    rcases hok with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd ⟨1, Or.inl ⟨rfl, rfl⟩⟩ hs
    · exact absurd ⟨2, Or.inl ⟨rfl, rfl⟩⟩ hs
    · rcases hE1 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f1456 N.f124 (by decide) (by decide) (by decide) hg hf
    · rcases hE2 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f1456 N.f124 (by decide) (by decide) (by decide) hg hf
    · rcases hE4 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f1456 N.f015 (by decide) (by decide) (by decide) hg hf
    · rcases hE5 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f015 N.f1456 (by decide) (by decide) (by decide) hg hf
    · rcases hE6 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f015 N.f1456 (by decide) (by decide) (by decide) hg hf
    · exact absurd ⟨0, Or.inl ⟨rfl, rfl⟩⟩ hs
    · rcases hE3 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f124 N.f1456 (by decide) (by decide) (by decide) hg hf
    · rcases hE7 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f356 N.f1456 (by decide) (by decide) (by decide) hg hf
    · rcases hE8 rfl with hn | hg
      · exact key (Or.inl hn)
      · exact closeE29 N K hK N.f346 N.f1456 (by decide) (by decide) (by decide) hg hf

/-- **A frequent type-29 certificate** (Lemma 18.2 with the finitely many closings), under
`Cond29` at every closing of the whitelists. -/
theorem isRupert_of_cert_seq29_hdn (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (θs : ℕ → Fin 8 → ℝ)
    (hθs : Tendsto θs atTop (𝓝 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t]))
    (H : ∀ ℓ : Lab29, ℓ.Ok → Cond29 N ℓ)
    (hc : ∃ᶠ n in atTop, Cert29 (K n) ∧ TiesAt29 x (K n) ∧
      ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ ℓ : {ℓ : Lab29 // ℓ.Ok}, CertAt29 (K n) ℓ.1 ∧ TiesAt29 x (K n) ∧
      ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n :=
    hc.mono fun n hn => by
      obtain ⟨ℓ, hok, h⟩ := (cert29_iff _).mp hn.1
      exact ⟨⟨ℓ, hok⟩, h, hn.2⟩
  obtain ⟨ℓ, hℓ⟩ := frequently_exists_of_finite h
  exact close29 N K hK θs hθs ℓ.1 ℓ.2 (H ℓ.1 ℓ.2) hℓ

end Minimality

end
