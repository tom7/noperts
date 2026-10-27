module

public import Minimality.Type02CaseC
public import Minimality.EdgeLimit
public import Minimality.Type16Edge
public import Minimality.Type16Main
public import Minimality.Type16Edge2
public import Minimality.TriBridge

@[expose] public section

/-!
# Type 02 at the edge `34`: horizontal double normals (`FEWER-FACES-PROOFS.md` §22, §24 item 6)

Lemma 23.12 closes the edge `34` of type 02 by Lemma E at the rims `(3, a, 2, b)`
(`Type02CaseC`), but needs no horizontal double normal (HDN) at the view `x 4 - x 3` for either
closing (`Type02EdgeGen'`).  Here an HDN is allowed where the conditions of §22.4 hold
(`Type02HDNOK`, `Type02EdgeGen''`); this is the paper's item 6 (§24, "Type 02: the 34-view"):
the closings are realized on the face circles of `0134`, `3456` (Lemma 22.1), so the closing of an
edge pair is `EdgeConf.isRupert_edgeClosing` (Proposition 22.2 for the planar rims `(0,5)`,
`(1,6)`, realized on both circles; Lemmas 22.3, 22.4, 22.8 for `(0,6)`, `(1,5)`, realized on one).

* `isRupert_ePair_here`: an edge pair of Lemma E at the shape itself (not a limit) is Rupert under
  `EdgeGen`, whatever its HDNs (`isRupert_ePair_limit_facts` for a constant sequence, with the
  strict Lemma E replaced by its two uses `hEa`, `hEb`, so that planar rims are allowed).
* `rim_core_data'`: the coordinates of `Type02CaseC` give `EPairData` at the rim.
* `Type02HDNOK`: `EdgeGen` for the faces `0134`, `3456` plus `Type02Rim` at the far ends.
* `Type02EdgeGen''`: the HDN fields are "no HDN, or `Type02HDNOK`"; the ties are as before.
* `isRupert_type02_edge34''`, `type02_edge34_byGen''`: the skeleton form.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter
open Type02CaseC

set_option maxHeartbeats 1000000 in
/-- **An edge pair of Lemma E at a shape itself** (`isRupert_ePair_limit_facts` with the constant
sequence, and the strict Lemma E replaced by its two consequences `hEa`, `hEb`, used only where a far
edge is parallel to a face): the facts of the pair (`EPairFacts`) and the conditions of §22.4
(`EdgeGen`) make the shape Rupert, whatever its horizontal double normals. -/
theorem isRupert_ePair_here {n : ℕ} (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    {v w a b c : Fin n} (hvw : v ≠ w) {Sa Sb : Finset (Fin n)} {Na Nb : ℝ³} {κa κb : ℝ}
    (hfa : ∀ i, (i ∈ Sa → ⟪Na, x i⟫ = κa) ∧ (i ∉ Sa → ⟪Na, x i⟫ < κa))
    (hfb : ∀ i, (i ∈ Sb → ⟪Nb, x i⟫ = κb) ∧ (i ∉ Sb → ⟪Nb, x i⟫ < κb))
    (hSa : v ∈ Sa ∧ w ∈ Sa ∧ a ∈ Sa ∧ b ∉ Sa ∧ c ∉ Sa ∧ ∀ i ∈ Sa, ∀ j ∈ Sa,
      i ≠ v → i ≠ w → i ≠ a → j ≠ v → j ≠ w → j ≠ a → i = j)
    (hSb : v ∈ Sb ∧ w ∈ Sb ∧ b ∈ Sb ∧ a ∉ Sb ∧ c ∉ Sb ∧ ∀ i ∈ Sb, ∀ j ∈ Sb,
      i ≠ v → i ≠ w → i ≠ b → j ≠ v → j ≠ w → j ≠ b → i = j)
    (hfacts : EPairFacts (univ.image x) (x v) (x w) (x a) (x b) (x c))
    (hgen : EdgeGen (univ.image x) (x w - x v) (x v) (x w) (Sa.image x) (Sb.image x) Na Nb)
    (hEa : ⟪Na, x c⟫ = ⟪Na, x b⟫ → det3 (x c - x a) (x b - x a) (x v - x a) *
      det3 (x c - x a) (x b - x a) (x w - x a) < 0)
    (hEb : ⟪Nb, x c⟫ = ⟪Nb, x a⟫ → det3 (x c - x b) (x a - x b) (x v - x b) *
      det3 (x c - x b) (x a - x b) (x w - x b) < 0) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨hvA, hwA, haA, hbA, hcA, hA1⟩ := hSa
  obtain ⟨hvB, hwB, hbB, haB, hcB, hB1⟩ := hSb
  set V := univ.image x with hVdef
  have mem : ∀ i, x i ∈ V := fun i => mem_image_of_mem x (mem_univ i)
  set u := x w - x v with hudef
  have hu : u ≠ 0 := sub_ne_zero.mpr (hx.ne hvw.symm)
  have hleft : ∀ z ∈ V, 0 ≤ det3 (x a - x v) (z - x v) u ∧ 0 ≤ det3 (x c - x a) (z - x a) u ∧
      0 ≤ det3 (x b - x c) (z - x c) u ∧ 0 ≤ det3 (x v - x b) (z - x b) u := hfacts.1.1
  have hsupp : ∀ z ∈ V, SuppIn u (quad (x v) (x a) (x c) (x b)) z := hfacts.1.2.1
  -- the configuration
  set Ma := (Sa \ {v, w, a}).image x with hMadef
  set Mb := (Sb \ {v, w, b}).image x with hMbdef
  have memMa : ∀ z, z ∈ Ma ↔ ∃ i ∈ Sa, i ≠ v ∧ i ≠ w ∧ i ≠ a ∧ x i = z := by
    intro z
    simp only [hMadef, mem_image, Finset.mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, hi, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩
  have memMb : ∀ z, z ∈ Mb ↔ ∃ i ∈ Sb, i ≠ v ∧ i ≠ w ∧ i ≠ b ∧ x i = z := by
    intro z
    simp only [hMbdef, mem_image, Finset.mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩; exact ⟨i, hi, h1, h2, h3, rfl⟩
    · rintro ⟨i, hi, h1, h2, h3, rfl⟩; exact ⟨i, ⟨hi, h1, h2, h3⟩, rfl⟩
  have hSAeq : Sa.image x = insert (x v) (insert (x w) (insert (x a) Ma)) := by
    ext z
    simp only [mem_image, mem_insert, memMa]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h1 : i = v; · left; rw [h1]
      by_cases h2 : i = w; · right; left; rw [h2]
      by_cases h3 : i = a; · right; right; left; rw [h3]
      exact Or.inr (Or.inr (Or.inr ⟨i, hi, h1, h2, h3, rfl⟩))
    · rintro (rfl | rfl | rfl | ⟨i, hi, -, -, -, rfl⟩)
      exacts [⟨v, hvA, rfl⟩, ⟨w, hwA, rfl⟩, ⟨a, haA, rfl⟩, ⟨i, hi, rfl⟩]
  have hSBeq : Sb.image x = insert (x v) (insert (x w) (insert (x b) Mb)) := by
    ext z
    simp only [mem_image, mem_insert, memMb]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h1 : i = v; · left; rw [h1]
      by_cases h2 : i = w; · right; left; rw [h2]
      by_cases h3 : i = b; · right; right; left; rw [h3]
      exact Or.inr (Or.inr (Or.inr ⟨i, hi, h1, h2, h3, rfl⟩))
    · rintro (rfl | rfl | rfl | ⟨i, hi, -, -, -, rfl⟩)
      exacts [⟨v, hvB, rfl⟩, ⟨w, hwB, rfl⟩, ⟨b, hbB, rfl⟩, ⟨i, hi, rfl⟩]
  have notMa : ∀ j, j ∉ Sa → x j ∉ Ma := by
    intro j hj hm
    obtain ⟨i, hi, -, -, -, he⟩ := (memMa _).mp hm
    exact hj (hx he ▸ hi)
  have notMb : ∀ j, j ∉ Sb → x j ∉ Mb := by
    intro j hj hm
    obtain ⟨i, hi, -, -, -, he⟩ := (memMb _).mp hm
    exact hj (hx he ▸ hi)
  have ne : ∀ {i j : Fin n}, (i ∈ Sa ∧ j ∉ Sa) ∨ (i ∈ Sb ∧ j ∉ Sb) → x j ≠ x i := by
    rintro i j (⟨hi, hj⟩ | ⟨hi, hj⟩) e <;> exact hj (hx e ▸ hi)
  have E : EdgeConf V u (x v) (x w) (x a) (x b) (x c) 1 Na Nb κa κb Ma Mb := {
    hu := hu
    hh := one_ne_zero
    hw := by rw [one_smul, hudef]; abel
    hv := mem v
    hwV := mem w
    ha := mem a
    hb := mem b
    hc := mem c
    hMa := fun z hz => by obtain ⟨i, -, -, -, -, rfl⟩ := (memMa z).mp hz; exact mem i
    hMb := fun z hz => by obtain ⟨i, -, -, -, -, rfl⟩ := (memMb z).mp hz; exact mem i
    faceA := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · rintro (e | e | e | e)
        · rw [hx e]; exact (hfa v).1 hvA
        · rw [hx e]; exact (hfa w).1 hwA
        · rw [hx e]; exact (hfa a).1 haA
        · obtain ⟨j, hj, -, -, -, he⟩ := (memMa _).mp e
          rw [← he]; exact (hfa j).1 hj
      · intro he
        have hi : i ∈ Sa := by
          by_contra hi; exact absurd he ((hfa i).2 hi).ne
        by_cases h1 : i = v; · left; rw [h1]
        by_cases h2 : i = w; · right; left; rw [h2]
        by_cases h3 : i = a; · right; right; left; rw [h3]
        exact Or.inr (Or.inr (Or.inr ((memMa _).mpr ⟨i, hi, h1, h2, h3, rfl⟩)))
    faceA_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sa
      · exact ((hfa i).1 hi).le
      · exact ((hfa i).2 hi).le
    faceB := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      constructor
      · rintro (e | e | e | e)
        · rw [hx e]; exact (hfb v).1 hvB
        · rw [hx e]; exact (hfb w).1 hwB
        · rw [hx e]; exact (hfb b).1 hbB
        · obtain ⟨j, hj, -, -, -, he⟩ := (memMb _).mp e
          rw [← he]; exact (hfb j).1 hj
      · intro he
        have hi : i ∈ Sb := by
          by_contra hi; exact absurd he ((hfb i).2 hi).ne
        by_cases h1 : i = v; · left; rw [h1]
        by_cases h2 : i = w; · right; left; rw [h2]
        by_cases h3 : i = b; · right; right; left; rw [h3]
        exact Or.inr (Or.inr (Or.inr ((memMb _).mpr ⟨i, hi, h1, h2, h3, rfl⟩)))
    faceB_le := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := mem_image.mp hz
      by_cases hi : i ∈ Sb
      · exact ((hfb i).1 hi).le
      · exact ((hfb i).2 hi).le
    hbA := ⟨ne (Or.inl ⟨hvA, hbA⟩), ne (Or.inl ⟨hwA, hbA⟩), ne (Or.inl ⟨haA, hbA⟩),
      notMa b hbA⟩
    hcA := ⟨ne (Or.inl ⟨hvA, hcA⟩), ne (Or.inl ⟨hwA, hcA⟩), ne (Or.inl ⟨haA, hcA⟩),
      notMa c hcA⟩
    haB := ⟨ne (Or.inr ⟨hvB, haB⟩), ne (Or.inr ⟨hwB, haB⟩), notMb a haB⟩
    hcB := ⟨ne (Or.inr ⟨hbB, hcB⟩), notMb c hcB⟩
    hMa' := by
      intro z hz
      obtain ⟨i, -, h1, h2, h3, rfl⟩ := (memMa z).mp hz
      exact ⟨hx.ne h1, hx.ne h2, hx.ne h3⟩
    hMb' := by
      intro z hz
      obtain ⟨i, -, h1, h2, h3, rfl⟩ := (memMb z).mp hz
      exact ⟨hx.ne h1, hx.ne h2, hx.ne h3⟩
    left := hleft
    par := hgen.par
    g1 := by rw [← hSAeq, ← hSBeq]; exact hgen.g1
    noSeg := by
      intro p hp q hq y hy hyp hyq s hs0 hs1
      obtain ⟨i, -, rfl⟩ := mem_image.mp hp
      obtain ⟨j, -, rfl⟩ := mem_image.mp hq
      obtain ⟨m, -, rfl⟩ := mem_image.mp hy
      exact hseg i j m hyp hyq s hs0 hs1
    supp := hsupp }
  have hMa1 : ∀ m ∈ Ma, ∀ m' ∈ Ma, m = m' := by
    intro z hz z' hz'
    obtain ⟨i, hi, h1, h2, h3, rfl⟩ := (memMa z).mp hz
    obtain ⟨j, hj, k1, k2, k3, rfl⟩ := (memMa z').mp hz'
    rw [hA1 i hi j hj h1 h2 h3 k1 k2 k3]
  have hMb1 : ∀ m ∈ Mb, ∀ m' ∈ Mb, m = m' := by
    intro z hz z' hz'
    obtain ⟨i, hi, h1, h2, h3, rfl⟩ := (memMb z).mp hz
    obtain ⟨j, hj, k1, k2, k3, rfl⟩ := (memMb z').mp hz'
    rw [hB1 i hi j hj h1 h2 h3 k1 k2 k3]
  have imgA : ∀ i ∈ Sa, x i ∈ Sa.image x := fun i hi => mem_image_of_mem x hi
  have imgB : ∀ i ∈ Sb, x i ∈ Sb.image x := fun i hi => mem_image_of_mem x hi
  have nimA : ∀ i ∉ Sa, x i ∉ Sa.image x := fun i hi h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hi (hx he ▸ hj)
  have nimB : ∀ i ∉ Sb, x i ∉ Sb.image x := fun i hi h => by
    obtain ⟨j, hj, he⟩ := mem_image.mp h; exact hi (hx he ▸ hj)
  have fA := fun p (hp : p ∈ Sa) => footA_of_gen hgen.footA (imgA p hp) (imgA a haA) (mem c)
    (mem b) (nimA c hcA) (nimA b hbA)
  have fB := fun p (hp : p ∈ Sb) => footA_of_gen hgen.footB (imgB p hp) (imgB b hbB) (mem c)
    (mem a) (nimB c hcB) (nimB a haB)
  rcases hfacts.1.2.2 with hz | hz
  · refine E.isRupert_edgeClosing hMa1 hMb1 ?_ hgen.dist hgen.one (fA v hvA) (fB v hvB)
      (fun h _ => hEa h) (fun h _ => hEb h)
    rw [quad_inner']
    exact hz.isRobustUnimodal
  · refine E.swap.isRupert_edgeClosing hMa1 hMb1 ?_ hgen.dist hgen.one (fA w hwA) (fB w hwB)
      (fun h _ => by rw [mul_comm]; exact hEa h) (fun h _ => by rw [mul_comm]; exact hEb h)
    rw [quad_inner']
    exact hz.isRobustUnimodal

/-- **Lemma E in coordinates: the data of an edge pair** (as `Type02CaseC.rim_core`, positive
orientation, without doubles): `EPairData` at the rim `(v, a, c, b)`. -/
theorem rim_core_data (V : Finset ℝ³) {v w a b c E1 E2 : ℝ³}
    (hD : 0 < det3 E1 E2 (w - v)) {tA tB ζa ζb α β γ : ℝ}
    (ha : a = v + tA • E1 + ζa • (w - v)) (hb : b = v + tB • E2 + ζb • (w - v))
    (hc : c = v + α • E1 + β • E2 + γ • (w - v))
    (htA : 0 < tA) (htB : 0 < tB) (hα : 0 < α) (hβ : 0 < β)
    (hch : tA * tB < α * tB + β * tA)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z) :
    EPairData V 1 v w a b c := by
  set u := w - v with hu
  have e1 : a - v = tA • E1 + (0 : ℝ) • E2 + ζa • u := by rw [ha]; module
  have e2 : c - v = α • E1 + β • E2 + γ • u := by rw [hc]; module
  have e4 : c - a = (α - tA) • E1 + β • E2 + (γ - ζa) • u := by rw [hc, ha]; module
  have e5 : b - a = (-tA) • E1 + tB • E2 + (ζb - ζa) • u := by rw [hb, ha]; module
  have e6 : b - c = (-α) • E1 + (tB - β) • E2 + (ζb - γ) • u := by rw [hb, hc]; module
  have e7 : v - c = (-α) • E1 + (-β) • E2 + (-γ) • u := by rw [hc]; module
  have e8 : v - b = (0 : ℝ) • E1 + (-tB) • E2 + (-ζb) • u := by rw [hb]; module
  have e9 : a - b = tA • E1 + (-tB) • E2 + (ζa - ζb) • u := by rw [hb, ha]; module
  have q₁ : 0 < det3 (a - v) (c - v) u := by
    rw [e1, e2, det3_coord_u]; nlinarith [mul_pos hD (mul_pos htA hβ)]
  have q₂ : 0 < det3 (c - a) (b - a) u := by
    rw [e4, e5, det3_coord_u]
    have : 0 < α * tB + β * tA - tA * tB := by linarith
    nlinarith [mul_pos hD this]
  have q₃ : 0 < det3 (b - c) (v - c) u := by
    rw [e6, e7, det3_coord_u]; nlinarith [mul_pos hD (mul_pos hα htB)]
  have q₄ : 0 < det3 (v - b) (a - b) u := by
    rw [e8, e9, det3_coord_u]; nlinarith [mul_pos hD (mul_pos htA htB)]
  refine ⟨Or.inl rfl, by rw [one_mul]; exact q₁, by rw [one_mul]; exact q₂,
    by rw [one_mul]; exact q₃, by rw [one_mul]; exact q₄, hE, h3, fun z hz => ?_⟩
  rcases hV z hz with h | h | h | h | h | h
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
    Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))]

/-- `rim_core_data`, either orientation: the pair is `(a, b)` or `(b, a)`. -/
theorem rim_core_data' (V : Finset ℝ³) {v w a b c E1 E2 : ℝ³}
    (hD : det3 E1 E2 (w - v) ≠ 0) {tA tB ζa ζb α β γ : ℝ}
    (ha : a = v + tA • E1 + ζa • (w - v)) (hb : b = v + tB • E2 + ζb • (w - v))
    (hc : c = v + α • E1 + β • E2 + γ • (w - v))
    (htA : 0 < tA) (htB : 0 < tB) (hα : 0 < α) (hβ : 0 < β)
    (hch : tA * tB < α * tB + β * tA)
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z) :
    EPairData V 1 v w a b c ∨ EPairData V 1 v w b a c := by
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hD' : 0 < det3 E2 E1 (w - v) := by
      have : det3 E2 E1 (w - v) = - det3 E1 E2 (w - v) := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [this]; linarith
    refine Or.inr (rim_core_data V (a := b) (b := a) hD' hb ha (by rw [hc]; module) htB htA hβ hα
      (by linarith) ?_ ?_ ?_)
    · rw [Type02CaseC.hE_swap a b c v, Type02CaseC.hE_swap a b c w]; nlinarith [hE]
    · exact fun ⟨h1, h2⟩ => h3 ⟨h2.symm, h1.symm⟩
    · intro z hz
      rcases hV z hz with h | h | h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Type02CaseC.edgeMid_symm h)))))]
  · exact Or.inl (rim_core_data V hpos ha hb hc htA htB hα hβ hch hE h3 hV)

/-! ### The conditions of §22.4 at the edge `34` and the closing by an edge pair -/

/-- **Lemma E strict at the rim `(3, a, 2, b)`, where a far edge is parallel to a face**: for the
normals `NA` of `0134` and `NB` of `3456`, if `x 2` and `x b` are at one level of `NA` (the far edge
`2 b` parallel to the face `0134`), resp. `x 2`, `x a` at one level of `NB`, then `3`, `4` lie
strictly on opposite sides of the plane `a 2 b`.  (A planar rim has `3` or `4` on the plane, so
there the two levels must be different.) -/
def Type02Rim (x : Fin 7 → ℝ³) (NA NB : ℝ³) (a b : Fin 7) : Prop :=
  (⟪NA, x 2⟫ = ⟪NA, x b⟫ → det3 (x 2 - x a) (x b - x a) (x 3 - x a) *
      det3 (x 2 - x a) (x b - x a) (x 4 - x a) < 0) ∧
  (⟪NB, x 2⟫ = ⟪NB, x a⟫ → det3 (x 2 - x b) (x a - x b) (x 3 - x b) *
      det3 (x 2 - x b) (x a - x b) (x 4 - x b) < 0)

/-- **The codimension-2 conditions of §22.4 at the edge `34` of type 02** (the escape of a
horizontal double normal there, `FEWER-FACES-PROOFS.md` §24 item 6 with §22): for the normals `NA`
of the face `0134` and `NB` of `3456`,

* `EdgeGen` at the view `x 4 - x 3` with the axle `3 4` and the two faces: only the axle seen
  end-on (no other segment parallel to `34`; in particular no vertical far edge `01`, `56`), (G1),
  all seven depths distinct, at most one direction of horizontal double normals, and no double
  normal perpendicular to a face from one of its vertices (each a coincidence of the shape);
* for the far ends of the rim, `Type02Rim` (a far edge parallel to a face is the only place where
  Lemma E is used strictly). -/
def Type02HDNOK (x : Fin 7 → ℝ³) : Prop :=
  ∀ NA NB : ℝ³, NA ≠ 0 → ⟪NA, x 4 - x 3⟫ = 0 → ⟪NA, x 0 - x 3⟫ = 0 →
    NB ≠ 0 → ⟪NB, x 4 - x 3⟫ = 0 → ⟪NB, x 5 - x 3⟫ = 0 →
    EdgeGen (Finset.univ.image x) (x 4 - x 3) (x 3) (x 4)
        (({0, 1, 3, 4} : Finset (Fin 7)).image x) (({3, 4, 5, 6} : Finset (Fin 7)).image x)
        NA NB ∧
      (Type02FarEnd x 0 1 → Type02FarEnd x 5 6 → Type02Rim x NA NB 0 5) ∧
      (Type02FarEnd x 0 1 → Type02FarEnd x 6 5 → Type02Rim x NA NB 0 6) ∧
      (Type02FarEnd x 1 0 → Type02FarEnd x 5 6 → Type02Rim x NA NB 1 5) ∧
      (Type02FarEnd x 1 0 → Type02FarEnd x 6 5 → Type02Rim x NA NB 1 6)

/-- **The closing of an edge pair at the edge `34` of type 02**, whatever the horizontal double
normals (Proposition 22.2 for the planar rims `(0, 5)`, `(1, 6)`, which are realized on both face
circles; §22.3, 22.4, 22.8 for the others, `EdgeConf.isRupert_edgeClosing`). -/
theorem type02_close_ePair {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (F1 : Face16 x {0, 1, 3, 4}) (F2 : Face16 x {3, 4, 5, 6}) {a b : Fin 7}
    (ha : a = 0 ∨ a = 1) (hb : b = 5 ∨ b = 6)
    (hG : EdgeGen (Finset.univ.image x) (x 4 - x 3) (x 3) (x 4)
      (({0, 1, 3, 4} : Finset (Fin 7)).image x) (({3, 4, 5, 6} : Finset (Fin 7)).image x)
      F1.N F2.N)
    (hR : Type02Rim x F1.N F2.N a b)
    (hE : EPairData (Finset.univ.image x) 1 (x 3) (x 4) (x a) (x b) (x 2) ∨
      EPairData (Finset.univ.image x) 1 (x 3) (x 4) (x b) (x a) (x 2)) :
    IsRupert (Finset.univ.image x) := by
  have mem : ∀ i, x i ∈ Finset.univ.image x := fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  have hSa : (3 : Fin 7) ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ (4 : Fin 7) ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧
      a ∈ ({0, 1, 3, 4} : Finset (Fin 7)) ∧ b ∉ ({0, 1, 3, 4} : Finset (Fin 7)) ∧
      (2 : Fin 7) ∉ ({0, 1, 3, 4} : Finset (Fin 7)) ∧
      ∀ i ∈ ({0, 1, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4} : Finset (Fin 7)),
        i ≠ 3 → i ≠ 4 → i ≠ a → j ≠ 3 → j ≠ 4 → j ≠ a → i = j := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  have hSb : (3 : Fin 7) ∈ ({3, 4, 5, 6} : Finset (Fin 7)) ∧ (4 : Fin 7) ∈ ({3, 4, 5, 6} : Finset (Fin 7)) ∧
      b ∈ ({3, 4, 5, 6} : Finset (Fin 7)) ∧ a ∉ ({3, 4, 5, 6} : Finset (Fin 7)) ∧
      (2 : Fin 7) ∉ ({3, 4, 5, 6} : Finset (Fin 7)) ∧
      ∀ i ∈ ({3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ 3 → i ≠ 4 → i ≠ b → j ≠ 3 → j ≠ 4 → j ≠ b → i = j := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  rcases hE with h | h
  · exact isRupert_ePair_here x hx hseg (v := 3) (w := 4) (a := a) (b := b) (c := 2)
      (by decide) (F1.hf (i₀ := 3) (by decide)) (F2.hf (i₀ := 3) (by decide)) hSa hSb
      ⟨ePair_facts h (mem 3) (mem 4) (mem a) (mem b) (mem 2), h.2.2.2.2.2.1⟩ hG hR.1 hR.2
  · exact isRupert_ePair_here x hx hseg (v := 3) (w := 4) (a := b) (b := a) (c := 2)
      (by decide) (F2.hf (i₀ := 3) (by decide)) (F1.hf (i₀ := 3) (by decide)) hSb hSa
      ⟨ePair_facts h (mem 3) (mem 4) (mem b) (mem a) (mem 2), h.2.2.2.2.2.1⟩ hG.swapF hR.2 hR.1

/-- No three of the seven points collinear gives the segment form used above. -/
theorem seg_of_noThreeCollinear {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (h : NoThreeCollinear (Finset.univ.image x)) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) := by
  intro i j m hmi hmj s hs0 hs1 heq
  by_cases hij : x i = x j
  · apply hmi; rw [heq, hij]; simp
  · refine h (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i)) (x j)
      (Finset.mem_image_of_mem x (Finset.mem_univ j)) (x m)
      (Finset.mem_image_of_mem x (Finset.mem_univ m)) hij (Ne.symm hmi) (Ne.symm hmj) s ?_
    rw [heq]; abel

/-- A vertical far edge is excluded by `EdgeGen`: the only segment parallel to `34` is `34`. -/
theorem EdgeGen.not_vertical {x : Fin 7 → ℝ³} (hx : Function.Injective x) {i j : Fin 7}
    (hij : i ≠ j) (hi3 : i ≠ 3) (hi4 : i ≠ 4)
    {SA SB : Finset ℝ³} {NA NB : ℝ³}
    (hG : EdgeGen (Finset.univ.image x) (x 4 - x 3) (x 3) (x 4) SA SB NA NB) (c : ℝ) :
    x j - x i ≠ c • (x 4 - x 3) := by
  intro h
  have hc := hG.par (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i)) (x j)
    (Finset.mem_image_of_mem x (Finset.mem_univ j)) (hx.ne hij) (by
      rw [h]; ext k; fin_cases k <;> simp [cross] <;> ring)
  rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hi3 (hx h1)
  · exact hi4 (hx h1)

/-- The vertex classification of Lemma E without doubles (`Type02CaseC.hV_mk`). -/
theorem hV_mk' (x : Fin 7 → ℝ³) (ia ib m1 m2 : Fin 7)
    (hcov : ∀ i : Fin 7, i = 3 ∨ i = 4 ∨ i = ia ∨ i = ib ∨ i = 2 ∨ i = m1 ∨ i = m2)
    (h1 : EdgeMid (x 3) (x 4) (x ia) (x ib) (x m1))
    (h2 : EdgeMid (x 3) (x 4) (x ia) (x ib) (x m2)) :
    ∀ z ∈ Finset.univ.image x, z = x 3 ∨ z = x 4 ∨ z = x ia ∨ z = x ib ∨ z = x 2 ∨
      EdgeMid (x 3) (x 4) (x ia) (x ib) z := by
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  rcases hcov i with h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2))))

/-- **The general position at the edge `34` of type 02, with the escape of a horizontal double
normal.**  As `Type02EdgeGen'`, but a horizontal double normal at the view `x 4 - x 3` of a closing
is allowed when the codimension-2 conditions of §22.4 hold there (`Type02HDNOK`): the failures are
an HDN together with one more coincidence. -/
structure Type02EdgeGen'' (x : Fin 7 → ℝ³) : Prop where
  hdn4 : NoHDNAt ((Finset.univ.image x).erase (x 4)) (x 4 - x 3) ∨ Type02HDNOK x
  hdn3 : NoHDNAt ((Finset.univ.image x).erase (x 3)) (x 4 - x 3) ∨ Type02HDNOK x
  t05 : Type02FarEnd' x 0 1 → Type02FarEnd' x 5 6 → ¬ Type02Tie x 0 5
  t06 : Type02FarEnd' x 0 1 → Type02FarEnd x 6 5 → ¬ Type02Tie x 0 6
  t15 : Type02FarEnd x 1 0 → Type02FarEnd' x 5 6 → ¬ Type02Tie x 1 5
  t16 : Type02FarEnd x 1 0 → Type02FarEnd x 6 5 → ¬ Type02Tie x 1 6

theorem Type02EdgeGen'.toGen'' {x : Fin 7 → ℝ³} (h : Type02EdgeGen' x) : Type02EdgeGen'' x :=
  ⟨Or.inl h.hdn4, Or.inl h.hdn3, h.t05, h.t06, h.t15, h.t16⟩

/-- Either both closings have no horizontal double normal, or the conditions of §22.4 hold. -/
theorem Type02EdgeGen''.ok_or {x : Fin 7 → ℝ³} (h : Type02EdgeGen'' x) :
    (NoHDNAt ((Finset.univ.image x).erase (x 4)) (x 4 - x 3) ∧
      NoHDNAt ((Finset.univ.image x).erase (x 3)) (x 4 - x 3)) ∨ Type02HDNOK x := by
  rcases h.hdn4 with h4 | h4
  · rcases h.hdn3 with h3 | h3
    · exact Or.inl ⟨h4, h3⟩
    · exact Or.inr h3
  · exact Or.inr h4

theorem Type02HDNOK.use {x : Fin 7 → ℝ³} (h : Type02HDNOK x) (F1 : Face16 x {0, 1, 3, 4})
    (F2 : Face16 x {3, 4, 5, 6}) :
    EdgeGen (Finset.univ.image x) (x 4 - x 3) (x 3) (x 4)
        (({0, 1, 3, 4} : Finset (Fin 7)).image x) (({3, 4, 5, 6} : Finset (Fin 7)).image x)
        F1.N F2.N ∧
      (Type02FarEnd x 0 1 → Type02FarEnd x 5 6 → Type02Rim x F1.N F2.N 0 5) ∧
      (Type02FarEnd x 0 1 → Type02FarEnd x 6 5 → Type02Rim x F1.N F2.N 0 6) ∧
      (Type02FarEnd x 1 0 → Type02FarEnd x 5 6 → Type02Rim x F1.N F2.N 1 5) ∧
      (Type02FarEnd x 1 0 → Type02FarEnd x 6 5 → Type02Rim x F1.N F2.N 1 6) :=
  h F1.N F2.N (F1.N_ne (i := 0) (j := 2) (by decide) (by decide))
    (F1.inner_sub (by decide) (by decide)) (F1.inner_sub (by decide) (by decide))
    (F2.N_ne (i := 3) (j := 0) (by decide) (by decide))
    (F2.inner_sub (by decide) (by decide)) (F2.inner_sub (by decide) (by decide))


open Type02CaseC in
set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 2000000 in
theorem isRupert_type02_edge34'' (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hseg : ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hF1 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧ f (x 0) = 0 ∧ f (x 1) = 0 ∧ f (x 4) = 0 ∧
      f (x 2) < 0 ∧ f (x 5) < 0 ∧ f (x 6) < 0)
    (hF2 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧ f (x 5) = 0 ∧ f (x 6) = 0 ∧ f (x 4) = 0 ∧
      f (x 0) < 0 ∧ f (x 1) < 0 ∧ f (x 2) < 0)
    (hF3 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 3) = 0 ∧ f (x 0) = 0 ∧ f (x 2) = 0 ∧ f (x 5) = 0 ∧
      f (x 1) < 0 ∧ f (x 4) < 0 ∧ f (x 6) < 0)
    (hF4 : ∃ f : ℝ³ →ᵃ[ℝ] ℝ, f (x 4) = 0 ∧ f (x 1) = 0 ∧ f (x 2) = 0 ∧ f (x 6) = 0 ∧
      f (x 0) < 0 ∧ f (x 3) < 0 ∧ f (x 5) < 0)
    (hgen : Type02EdgeGen'' x) : IsRupert (Finset.univ.image x) := by
  classical
  obtain ⟨f1, a3, a0, a1, a4, a2, a5, a6⟩ := hF1
  obtain ⟨f2, b3, b5, b6, b4, b0, b1, b2⟩ := hF2
  obtain ⟨f3, c3, c0, c2, c5, c1, c4, c6⟩ := hF3
  obtain ⟨f4, d4, d1, d2, d6, d0, d3, d5⟩ := hF4
  have hf1 : ∀ i, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → f1 (x i) < 0) := by
    intro i; fin_cases i <;> simp <;> assumption
  have hf2 : ∀ i, (i ∈ ({3, 4, 5, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({3, 4, 5, 6} : Finset (Fin 7)) → f2 (x i) < 0) := by
    intro i; fin_cases i <;> simp <;> assumption
  let F1 : Face16 x {0, 1, 3, 4} := Face16.ofAffine f1 hf1
  let F2 : Face16 x {3, 4, 5, 6} := Face16.ofAffine f2 hf2
  obtain ⟨e0, he0⟩ : ∃ e0 : ℝ³, e0 = x 0 - x 3 := ⟨_, rfl⟩
  obtain ⟨e5, he5⟩ : ∃ e5 : ℝ³, e5 = x 5 - x 3 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ³, u = x 4 - x 3 := ⟨_, rfl⟩
  have hx0 : x 0 = x 3 + e0 := by rw [he0]; abel
  have hx5 : x 5 = x 3 + e5 := by rw [he5]; abel
  have hx4 : x 4 = x 3 + u := by rw [hu]; abel
  -- the values of the linear parts
  have l1e0 : f1.linear e0 = 0 := by rw [he0, lin_sub]; linarith
  have l1u : f1.linear u = 0 := by rw [hu, lin_sub]; linarith
  have l1e5 : f1.linear e5 < 0 := by rw [he5, lin_sub]; linarith
  have l2e5 : f2.linear e5 = 0 := by rw [he5, lin_sub]; linarith
  have l2u : f2.linear u = 0 := by rw [hu, lin_sub]; linarith
  have l2e0 : f2.linear e0 < 0 := by rw [he0, lin_sub]; linarith
  have l3e0 : f3.linear e0 = 0 := by rw [he0, lin_sub]; linarith
  have l3e5 : f3.linear e5 = 0 := by rw [he5, lin_sub]; linarith
  have l3u : f3.linear u < 0 := by rw [hu, lin_sub]; linarith
  have hD := det_ne_zero e0 e5 u f1.linear f2.linear f3.linear l1e0 l1e5.ne l2e0.ne
    l3e0 l3e5 l3u.ne
  obtain ⟨α1, β1, γ1, h1⟩ := exists_coords hD (x 1) (x 3)
  obtain ⟨α2, β2, γ2, h2⟩ := exists_coords hD (x 2) (x 3)
  obtain ⟨α6, β6, γ6, h6⟩ := exists_coords hD (x 6) (x 3)
  have F : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (p : ℝ³) (α β γ : ℝ), p = x 3 + α • e0 + β • e5 + γ • u →
      f p = f (x 3) + α * f.linear e0 + β * f.linear e5 + γ * f.linear u := by
    intro f p α β γ h; subst h; exact aff_comb f (x 3) e0 e5 u α β γ
  -- facet 0134: the second coordinate
  have A1 := F f1 (x 1) α1 β1 γ1 h1
  have A2 := F f1 (x 2) α2 β2 γ2 h2
  have A6 := F f1 (x 6) α6 β6 γ6 h6
  simp only [a3, a1, l1e0, l1u, mul_zero, add_zero, zero_add] at A1 A2 A6
  have hβ1 : β1 = 0 := by
    rcases mul_eq_zero.mp A1.symm with h | h
    · exact h
    · exact absurd h l1e5.ne
  have hβ2 : 0 < β2 := pos_of_mul_neg' l1e5 (by rw [← A2]; exact a2)
  have hβ6 : 0 < β6 := pos_of_mul_neg' l1e5 (by rw [← A6]; exact a6)
  -- facet 3456: the first coordinate
  have B1 := F f2 (x 1) α1 β1 γ1 h1
  have B2 := F f2 (x 2) α2 β2 γ2 h2
  have B6 := F f2 (x 6) α6 β6 γ6 h6
  simp only [b3, b6, l2e5, l2u, mul_zero, add_zero, zero_add] at B1 B2 B6
  have hα6 : α6 = 0 := by
    rcases mul_eq_zero.mp B6.symm with h | h
    · exact h
    · exact absurd h l2e0.ne
  have hα1 : 0 < α1 := pos_of_mul_neg' l2e0 (by rw [← B1]; exact b1)
  have hα2 : 0 < α2 := pos_of_mul_neg' l2e0 (by rw [← B2]; exact b2)
  -- facet 0235: the third coordinate
  have C1 := F f3 (x 1) α1 β1 γ1 h1
  have C2 := F f3 (x 2) α2 β2 γ2 h2
  have C6 := F f3 (x 6) α6 β6 γ6 h6
  simp only [c3, c2, l3e0, l3e5, mul_zero, add_zero, zero_add] at C1 C2 C6
  have hγ2 : γ2 = 0 := by
    rcases mul_eq_zero.mp C2.symm with h | h
    · exact h
    · exact absurd h l3u.ne
  have hγ1 : 0 < γ1 := pos_of_mul_neg' l3u (by rw [← C1]; exact c1)
  have hγ6 : 0 < γ6 := pos_of_mul_neg' l3u (by rw [← C6]; exact c6)
  subst hβ1 hα6 hγ2
  -- facet 1246: the plane `z = 1 - p0 x - p5 y`
  have hg : 0 < f4.linear u := by rw [hu, lin_sub]; linarith
  have l4g : f4 (x 3) = - f4.linear u := by rw [hu, lin_sub]; linarith
  have l4e0 : f4.linear e0 < f4.linear u := by rw [he0, hu, lin_sub, lin_sub]; linarith
  have l4e5 : f4.linear e5 < f4.linear u := by rw [he5, hu, lin_sub, lin_sub]; linarith
  obtain ⟨p0, hp0⟩ : ∃ p0 : ℝ, f4.linear e0 = p0 * f4.linear u :=
    ⟨f4.linear e0 / f4.linear u, by field_simp⟩
  obtain ⟨p5, hp5⟩ : ∃ p5 : ℝ, f4.linear e5 = p5 * f4.linear u :=
    ⟨f4.linear e5 / f4.linear u, by field_simp⟩
  have hp0' : p0 < 1 := by
    by_contra h; push Not at h
    rw [hp0] at l4e0
    have := mul_nonneg (sub_nonneg.2 h) hg.le
    linarith only [this, l4e0]
  have hp5' : p5 < 1 := by
    by_contra h; push Not at h
    rw [hp5] at l4e5
    have := mul_nonneg (sub_nonneg.2 h) hg.le
    linarith only [this, l4e5]
  have D1 := F f4 (x 1) α1 0 γ1 (by rw [h1])
  have D2 := F f4 (x 2) α2 β2 0 h2
  have D6 := F f4 (x 6) 0 β6 γ6 h6
  rw [d1, l4g, hp0, hp5] at D1
  rw [d2, l4g, hp0, hp5] at D2
  rw [d6, l4g, hp0, hp5] at D6
  have N1 : γ1 = 1 - α1 * p0 := by
    have : f4.linear u * (γ1 - 1 + α1 * p0) = 0 := by linear_combination -D1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg.ne'
    · linarith
  have N6 : γ6 = 1 - β6 * p5 := by
    have : f4.linear u * (γ6 - 1 + β6 * p5) = 0 := by linear_combination -D6
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg.ne'
    · linarith
  have N2 : α2 * p0 + β2 * p5 = 1 := by
    have : f4.linear u * (α2 * p0 + β2 * p5 - 1) = 0 := by linear_combination -D2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg.ne'
    · linarith
  have hu' : x 4 - x 3 = u := hu.symm
  have hD' : det3 e0 e5 (x 4 - x 3) ≠ 0 := by rw [hu']; exact hD
  have mem : ∀ i, x i ∈ Finset.univ.image x :=
    fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  have e1 : x 1 = x 3 + α1 • e0 + γ1 • u := by rw [h1]; module
  have e6 : x 6 = x 3 + β6 • e5 + γ6 • u := by rw [h6]; module
  have e2 : x 2 = x 3 + α2 • e0 + β2 • e5 := by rw [h2]; module
  have q1 : α1 * p0 < 1 := by rw [N1] at hγ1; linarith
  have q6 : β6 * p5 < 1 := by rw [N6] at hγ6; linarith
  -- the far-end witnesses
  have fe01 : α1 ≤ 1 → Type02FarEnd' x 0 1 := fun hle => by
    rcases hle.lt_or_eq with hlt | h
    · exact Or.inl ⟨α1, γ1, hα1, hlt, by rw [← he0, hu', e1]⟩
    · exact Or.inr ⟨γ1, by rw [e1, hx0, hu', h]; module⟩
  have fe56 : β6 ≤ 1 → Type02FarEnd' x 5 6 := fun hle => by
    rcases hle.lt_or_eq with hlt | h
    · exact Or.inl ⟨β6, γ6, hβ6, hlt, by rw [← he5, hu', e6]⟩
    · exact Or.inr ⟨γ6, by rw [e6, hx5, hu', h]; module⟩
  have fe10 : 1 < α1 → Type02FarEnd x 1 0 := fun hgt =>
    ⟨1 / α1, -γ1 / α1, by positivity, by rw [div_lt_one hα1]; exact hgt, by
      rw [e1, hx0, hu']
      match_scalars <;> field_simp <;> ring⟩
  have fe65 : 1 < β6 → Type02FarEnd x 6 5 := fun hgt =>
    ⟨1 / β6, -γ6 / β6, by positivity, by rw [div_lt_one hβ6]; exact hgt, by
      rw [e6, hx5, hu']
      match_scalars <;> field_simp <;> ring⟩
  have hc : x 2 = x 3 + α2 • e0 + β2 • e5 + (0 : ℝ) • (x 4 - x 3) := by rw [e2]; module
  have hγa : 0 < γ1 - 1 + α1 := by
    have : γ1 - 1 + α1 = α1 * (1 - p0) := by rw [N1]; ring
    rw [this]; exact mul_pos hα1 (sub_pos.2 hp0')
  have hγb : 0 < γ6 - 1 + β6 := by
    have : γ6 - 1 + β6 = β6 * (1 - p5) := by rw [N6]; ring
    rw [this]; exact mul_pos hβ6 (sub_pos.2 hp5')
  have m1 : x 1 = x 3 + α1 • e0 + γ1 • (x 4 - x 3) := by rw [hu']; exact e1
  have m6 : x 6 = x 3 + β6 • e5 + γ6 • (x 4 - x 3) := by rw [hu']; exact e6
  have m0 : x 0 = x 3 + (1 : ℝ) • e0 + (0 : ℝ) • (x 4 - x 3) := by rw [hx0]; module
  have m5 : x 5 = x 3 + (1 : ℝ) • e5 + (0 : ℝ) • (x 4 - x 3) := by rw [hx5]; module
  have ha0 : x 0 = x 3 + (1 : ℝ) • e0 + (0 : ℝ) • e5 + (0 : ℝ) • u := by rw [hx0]; module
  have hb5 : x 5 = x 3 + (0 : ℝ) • e0 + (1 : ℝ) • e5 + (0 : ℝ) • u := by rw [hx5]; module
  have hc2 : x 2 = x 3 + α2 • e0 + β2 • e5 + (0 : ℝ) • u := by rw [e2]; module
  have ha1 : x 1 = x 3 + α1 • e0 + (0 : ℝ) • e5 + γ1 • u := by rw [e1]; module
  have hb6 : x 6 = x 3 + (0 : ℝ) • e0 + β6 • e5 + γ6 • u := by rw [e6]; module
  -- the middle `1` over the side `0`: a middle, or a double over `0` (a vertical far edge `01`)
  have mid1 : α1 ≤ 1 → ∀ b, EdgeMid (x 3) (x 4) (x 0) b (x 1) ∨
      EdgeDoubleOver (x 4 - x 3) (x 0) b (x 2) (x 1) := fun hle b => by
    rcases hle.lt_or_eq with hlt | h
    · exact Or.inl (mid_a_up hx0 hα1 hlt hγa m1 b)
    · exact Or.inr ⟨γ1, hγ1.ne', Or.inl (by rw [e1, hx0, hu', h]; module)⟩
  have mid6 : β6 ≤ 1 → ∀ a, EdgeMid (x 3) (x 4) a (x 5) (x 6) ∨
      EdgeDoubleOver (x 4 - x 3) a (x 5) (x 2) (x 6) := fun hle a => by
    rcases hle.lt_or_eq with hlt | h
    · exact Or.inl (mid_b_up hx5 hβ6 hlt hγb m6 a)
    · exact Or.inr ⟨γ6, hγ6.ne', Or.inr (Or.inl (by rw [e6, hx5, hu', h]; module))⟩
  have mid1' : (∀ c : ℝ, x 1 - x 0 ≠ c • (x 4 - x 3)) → α1 ≤ 1 → ∀ b,
      EdgeMid (x 3) (x 4) (x 0) b (x 1) := fun hnv hle b => by
    rcases hle.lt_or_eq with hlt | h
    · exact mid_a_up hx0 hα1 hlt hγa m1 b
    · exact absurd (by rw [e1, hx0, hu', h]; module : x 1 - x 0 = γ1 • (x 4 - x 3)) (hnv γ1)
  have mid6' : (∀ c : ℝ, x 6 - x 5 ≠ c • (x 4 - x 3)) → β6 ≤ 1 → ∀ a,
      EdgeMid (x 3) (x 4) a (x 5) (x 6) := fun hnv hle a => by
    rcases hle.lt_or_eq with hlt | h
    · exact mid_b_up hx5 hβ6 hlt hγb m6 a
    · exact absurd (by rw [e6, hx5, hu', h]; module : x 6 - x 5 = γ6 • (x 4 - x 3)) (hnv γ6)
  have fe01' : (∀ c : ℝ, x 1 - x 0 ≠ c • (x 4 - x 3)) → α1 ≤ 1 → Type02FarEnd x 0 1 :=
    fun hnv hle => (fe01 hle).resolve_right (fun ⟨c, hc⟩ => hnv c hc)
  have fe56' : (∀ c : ℝ, x 6 - x 5 ≠ c • (x 4 - x 3)) → β6 ≤ 1 → Type02FarEnd x 5 6 :=
    fun hnv hle => (fe56 hle).resolve_right (fun ⟨c, hc⟩ => hnv c hc)
  rcases hgen.ok_or with hn | hOK
  · -- no horizontal double normal: Lemma E with ties and doubles
    rcases le_or_gt α1 1 with hlt | hgt <;> rcases le_or_gt β6 1 with hlt6 | hgt6
    · -- (a, b) = (0, 5): planar rim `0235`
      have hch : (1 : ℝ) * 1 < α2 * 1 + β2 * 1 := by
        have := mul_lt_mul_of_pos_left hp0' hα2
        have := mul_lt_mul_of_pos_left hp5' hβ2
        linarith
      refine rim_core' _ hD' m0 m5 hc one_pos one_pos hα2 hβ2 hch (mem 3) (mem 4) (mem 0) (mem 5)
        (mem 2) ?_ (hgen.t05 (fe01 hlt) (fe56 hlt6)) ?_ hn.1 hn.2
      · rw [hx4]; exact hE_A (x 3) e0 e5 u (x 0) (x 5) (x 2) α2 β2 ha0 hb5 hc2
      · exact hV_mk x 0 5 1 6 (by decide)
          (mid1 hlt (x 5)) (mid6 hlt6 (x 0))
    · -- (a, b) = (0, 6): Lemma E
      have hch : (1 : ℝ) * β6 < α2 * β6 + β2 * 1 := by
        have e : β6 = α2 * β6 * p0 + β2 * (β6 * p5) := by linear_combination (-β6) * N2
        have t1 := mul_lt_mul_of_pos_left hp0' (mul_pos hα2 hβ6)
        have t2 := mul_lt_mul_of_pos_left q6 hβ2
        linarith
      refine rim_core' _ hD' m0 m6 hc one_pos hβ6 hα2 hβ2 hch (mem 3) (mem 4) (mem 0)
        (mem 6) (mem 2) ?_ (hgen.t06 (fe01 hlt) (fe65 hgt6)) ?_ hn.1 hn.2
      · rw [hx4]
        refine hE_C (x 3) e0 e5 u (x 0) (x 6) (x 2) α2 β2 β6 γ6 ha0 hb6 hc2 hγ6 hβ2 ?_
        have : γ6 * β2 - β2 - β6 * (α2 - 1) = -(β6 * α2 * (1 - p0)) := by
          rw [N6]; linear_combination (-β6) * N2
        rw [this]; exact neg_nonpos.2 (mul_pos (mul_pos hβ6 hα2) (sub_pos.2 hp0')).le
      · exact hV_mk x 0 6 1 5 (by decide)
          (mid1 hlt (x 6)) (Or.inl (mid_b_low hgt6 hγ6 m6 hx5 (x 0)))
    · -- (a, b) = (1, 5): Lemma E
      have hch : α1 * 1 < α2 * 1 + β2 * α1 := by
        have e : α1 = α2 * (α1 * p0) + β2 * α1 * p5 := by linear_combination (-α1) * N2
        have t1 := mul_lt_mul_of_pos_left q1 hα2
        have t2 := mul_lt_mul_of_pos_left hp5' (mul_pos hβ2 hα1)
        linarith
      refine rim_core' _ hD' m1 m5 hc hα1 one_pos hα2 hβ2 hch (mem 3) (mem 4) (mem 1)
        (mem 5) (mem 2) ?_ (hgen.t15 (fe10 hgt) (fe56 hlt6)) ?_ hn.1 hn.2
      · rw [hx4]
        refine hE_D (x 3) e0 e5 u (x 1) (x 5) (x 2) α2 β2 α1 γ1 ha1 hb5 hc2 hγ1 hα2 ?_
        have : γ1 * α2 - α2 - α1 * (β2 - 1) = -(α1 * β2 * (1 - p5)) := by
          rw [N1]; linear_combination (-α1) * N2
        rw [this]; exact neg_nonpos.2 (mul_pos (mul_pos hα1 hβ2) (sub_pos.2 hp5')).le
      · exact hV_mk x 1 5 0 6 (by decide)
          (Or.inl (mid_a_low hgt hγ1 m1 hx0 (x 5))) (mid6 hlt6 (x 1))
    · -- (a, b) = (1, 6): planar rim `1246`
      have hch : α1 * β6 < α2 * β6 + β2 * α1 := by
        have e : α1 * β6 = α2 * β6 * (α1 * p0) + β2 * α1 * (β6 * p5) := by
          linear_combination (-(α1 * β6)) * N2
        have t1 := mul_lt_mul_of_pos_left q1 (mul_pos hα2 hβ6)
        have t2 := mul_lt_mul_of_pos_left q6 (mul_pos hβ2 hα1)
        linarith
      refine rim_core' _ hD' m1 m6 hc hα1 hβ6 hα2 hβ2 hch (mem 3) (mem 4) (mem 1)
        (mem 6) (mem 2) ?_ (hgen.t16 (fe10 hgt) (fe65 hgt6)) ?_ hn.1 hn.2
      · rw [hx4]
        refine hE_B (x 3) e0 e5 u (x 1) (x 6) (x 2) α2 β2 α1 γ1 β6 γ6 ha1 hb6 hc2 ?_
        rw [N1, N6]; linear_combination (-(α1 * β6)) * N2
      · exact hV_mk x 1 6 0 5 (by decide)
          (Or.inl (mid_a_low hgt hγ1 m1 hx0 (x 6))) (Or.inl (mid_b_low hgt6 hγ6 m6 hx5 (x 1)))
  · -- a horizontal double normal: the conditions of §22.4 hold (`Type02HDNOK`)
    obtain ⟨hG, r05, r06, r15, r16⟩ := hOK.use F1 F2
    have nv01 := hG.not_vertical hx (i := 0) (j := 1) (by decide) (by decide) (by decide)
    have nv56 := hG.not_vertical hx (i := 5) (j := 6) (by decide) (by decide) (by decide)
    have h3 : ∀ i j : Fin 7, i ≠ 2 → j ≠ 2 → i ≠ j →
        ¬ (⟪x i, x 4 - x 3⟫ = ⟪x 2, x 4 - x 3⟫ ∧ ⟪x 2, x 4 - x 3⟫ = ⟪x j, x 4 - x 3⟫) :=
      fun i j hi hj _ h => hG.dist (x i) (mem i) (x 2) (mem 2) (hx.ne hi) h.1
    rcases le_or_gt α1 1 with hlt | hgt <;> rcases le_or_gt β6 1 with hlt6 | hgt6
    · -- (a, b) = (0, 5): planar rim `0235`
      have hch : (1 : ℝ) * 1 < α2 * 1 + β2 * 1 := by
        have := mul_lt_mul_of_pos_left hp0' hα2
        have := mul_lt_mul_of_pos_left hp5' hβ2
        linarith
      have hEc : det3 (x 5 - x 0) (x 2 - x 0) (x 3 - x 0) *
          det3 (x 5 - x 0) (x 2 - x 0) (x 4 - x 0) ≤ 0 := by
        rw [hx4]; exact hE_A (x 3) e0 e5 u (x 0) (x 5) (x 2) α2 β2 ha0 hb5 hc2
      have hd := rim_core_data' _ (v := x 3) (w := x 4) hD' m0 m5 hc one_pos one_pos hα2 hβ2 hch
        hEc (h3 0 5 (by decide) (by decide) (by decide))
        (hV_mk' x 0 5 1 6 (by decide) (mid1' nv01 hlt (x 5)) (mid6' nv56 hlt6 (x 0)))
      exact type02_close_ePair hx hseg F1 F2 (Or.inl rfl) (Or.inl rfl) hG
        (r05 (fe01' nv01 hlt) (fe56' nv56 hlt6)) hd
    · -- (a, b) = (0, 6): Lemma E
      have hch : (1 : ℝ) * β6 < α2 * β6 + β2 * 1 := by
        have e : β6 = α2 * β6 * p0 + β2 * (β6 * p5) := by linear_combination (-β6) * N2
        have t1 := mul_lt_mul_of_pos_left hp0' (mul_pos hα2 hβ6)
        have t2 := mul_lt_mul_of_pos_left q6 hβ2
        linarith
      have hEc : det3 (x 6 - x 0) (x 2 - x 0) (x 3 - x 0) *
          det3 (x 6 - x 0) (x 2 - x 0) (x 4 - x 0) ≤ 0 := by
        rw [hx4]
        refine hE_C (x 3) e0 e5 u (x 0) (x 6) (x 2) α2 β2 β6 γ6 ha0 hb6 hc2 hγ6 hβ2 ?_
        have : γ6 * β2 - β2 - β6 * (α2 - 1) = -(β6 * α2 * (1 - p0)) := by
          rw [N6]; linear_combination (-β6) * N2
        rw [this]; exact neg_nonpos.2 (mul_pos (mul_pos hβ6 hα2) (sub_pos.2 hp0')).le
      have hd := rim_core_data' _ (v := x 3) (w := x 4) hD' m0 m6 hc one_pos hβ6 hα2 hβ2 hch hEc
        (h3 0 6 (by decide) (by decide) (by decide))
        (hV_mk' x 0 6 1 5 (by decide) (mid1' nv01 hlt (x 6)) (mid_b_low hgt6 hγ6 m6 hx5 (x 0)))
      exact type02_close_ePair hx hseg F1 F2 (Or.inl rfl) (Or.inr rfl) hG
        (r06 (fe01' nv01 hlt) (fe65 hgt6)) hd
    · -- (a, b) = (1, 5): Lemma E
      have hch : α1 * 1 < α2 * 1 + β2 * α1 := by
        have e : α1 = α2 * (α1 * p0) + β2 * α1 * p5 := by linear_combination (-α1) * N2
        have t1 := mul_lt_mul_of_pos_left q1 hα2
        have t2 := mul_lt_mul_of_pos_left hp5' (mul_pos hβ2 hα1)
        linarith
      have hEc : det3 (x 5 - x 1) (x 2 - x 1) (x 3 - x 1) *
          det3 (x 5 - x 1) (x 2 - x 1) (x 4 - x 1) ≤ 0 := by
        rw [hx4]
        refine hE_D (x 3) e0 e5 u (x 1) (x 5) (x 2) α2 β2 α1 γ1 ha1 hb5 hc2 hγ1 hα2 ?_
        have : γ1 * α2 - α2 - α1 * (β2 - 1) = -(α1 * β2 * (1 - p5)) := by
          rw [N1]; linear_combination (-α1) * N2
        rw [this]; exact neg_nonpos.2 (mul_pos (mul_pos hα1 hβ2) (sub_pos.2 hp5')).le
      have hd := rim_core_data' _ (v := x 3) (w := x 4) hD' m1 m5 hc hα1 one_pos hα2 hβ2 hch hEc
        (h3 1 5 (by decide) (by decide) (by decide))
        (hV_mk' x 1 5 0 6 (by decide) (mid_a_low hgt hγ1 m1 hx0 (x 5)) (mid6' nv56 hlt6 (x 1)))
      exact type02_close_ePair hx hseg F1 F2 (Or.inr rfl) (Or.inl rfl) hG
        (r15 (fe10 hgt) (fe56' nv56 hlt6)) hd
    · -- (a, b) = (1, 6): planar rim `1246`
      have hch : α1 * β6 < α2 * β6 + β2 * α1 := by
        have e : α1 * β6 = α2 * β6 * (α1 * p0) + β2 * α1 * (β6 * p5) := by
          linear_combination (-(α1 * β6)) * N2
        have t1 := mul_lt_mul_of_pos_left q1 (mul_pos hα2 hβ6)
        have t2 := mul_lt_mul_of_pos_left q6 (mul_pos hβ2 hα1)
        linarith
      have hEc : det3 (x 6 - x 1) (x 2 - x 1) (x 3 - x 1) *
          det3 (x 6 - x 1) (x 2 - x 1) (x 4 - x 1) ≤ 0 := by
        rw [hx4]
        refine hE_B (x 3) e0 e5 u (x 1) (x 6) (x 2) α2 β2 α1 γ1 β6 γ6 ha1 hb6 hc2 ?_
        rw [N1, N6]; linear_combination (-(α1 * β6)) * N2
      have hd := rim_core_data' _ (v := x 3) (w := x 4) hD' m1 m6 hc hα1 hβ6 hα2 hβ2 hch hEc
        (h3 1 6 (by decide) (by decide) (by decide))
        (hV_mk' x 1 6 0 5 (by decide) (mid_a_low hgt hγ1 m1 hx0 (x 6))
          (mid_b_low hgt6 hγ6 m6 hx5 (x 1)))
      exact type02_close_ePair hx hseg F1 F2 (Or.inr rfl) (Or.inr rfl) hG
        (r16 (fe10 hgt) (fe65 hgt6)) hd


/-- **Type 02, case (c): Lemma E at the edge `34`, with the escape of horizontal double normals**
(Lemma 23.12, §24 item 6 and §22 of `FEWER-FACES-PROOFS.md`): a 7-point nopert whose labelling realizes
the faces `0134`, `0235`, `1246`, `3456` of type 02 satisfies `¬ Type02EdgeGen'' x`. -/
theorem type02_edge34_false'' {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (h3c : NoThreeCollinear (Finset.univ.image x)) (hN : IsNopert (Finset.univ.image x))
    {fs : List (Finset (Fin 7))} (hR : Minimality.RealizesFaces x fs)
    (h1 : ({0, 1, 3, 4} : Finset (Fin 7)) ∈ fs) (h2 : ({0, 2, 3, 5} : Finset (Fin 7)) ∈ fs)
    (h3 : ({1, 2, 4, 6} : Finset (Fin 7)) ∈ fs) (h4 : ({3, 4, 5, 6} : Finset (Fin 7)) ∈ fs)
    (hgen : Type02EdgeGen'' x) : False := by
  obtain ⟨f1, hf1⟩ := hR _ h1
  obtain ⟨f2, hf2⟩ := hR _ h4
  obtain ⟨f3, hf3⟩ := hR _ h2
  obtain ⟨f4, hf4⟩ := hR _ h3
  refine hN.2 (isRupert_type02_edge34'' x hx (seg_of_noThreeCollinear hx h3c) ?_ ?_ ?_ ?_ hgen)
  · exact ⟨f1, (hf1 3).1 (by decide), (hf1 0).1 (by decide), (hf1 1).1 (by decide),
      (hf1 4).1 (by decide), (hf1 2).2 (by decide), (hf1 5).2 (by decide),
      (hf1 6).2 (by decide)⟩
  · exact ⟨f2, (hf2 3).1 (by decide), (hf2 5).1 (by decide), (hf2 6).1 (by decide),
      (hf2 4).1 (by decide), (hf2 0).2 (by decide), (hf2 1).2 (by decide),
      (hf2 2).2 (by decide)⟩
  · exact ⟨f3, (hf3 3).1 (by decide), (hf3 0).1 (by decide), (hf3 2).1 (by decide),
      (hf3 5).1 (by decide), (hf3 1).2 (by decide), (hf3 4).2 (by decide),
      (hf3 6).2 (by decide)⟩
  · exact ⟨f4, (hf4 4).1 (by decide), (hf4 1).1 (by decide), (hf4 2).1 (by decide),
      (hf4 6).1 (by decide), (hf4 0).2 (by decide), (hf4 3).2 (by decide),
      (hf4 5).2 (by decide)⟩

/-- The skeleton form: `byGen1 (type02_edge34_byGen'' hx h3c hN hR) …` with
`hR : RealizesFaces x (sevenTypeFaces 1)` and `h3c : NoThreeCollinear (univ.image x)`. -/
theorem type02_edge34_byGen'' {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (h3c : NoThreeCollinear (Finset.univ.image x)) (hN : IsNopert (Finset.univ.image x))
    (hR : Minimality.RealizesFaces x (Minimality.sevenTypeFaces 1)) :
    Type02EdgeGen'' x → False :=
  type02_edge34_false'' hx h3c hN hR (by decide) (by decide) (by decide) (by decide)

end Minimality

end
