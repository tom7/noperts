module

public import Minimality.Type10

@[expose] public section

/-!
# The forced parallel edge at the special value

Proposition 23.16 of `FEWER-FACES-PROOFS.md` (the referee's two-line argument):
for the types 05, 10, 13, 17, 19, 23 and 27, where the dichotomy of two views
(`Type*.lean`) is decided by a number `s`, the special value `s = 1` puts three
vertices of one face on a line of the screen. So that face plane contains the
view direction, and an edge of the type is parallel to the line of the planes of
the vertex view where Lemma T′ applies:

| type | Lean view at the special value | parallel edge |
|---|---|---|
| 05 | `0123`, `246` at `2` | `01` |
| 10 | `023`, `1245` at `2` | `14` |
| 13 | `0145`, `123` at `1` | `45` |
| 17 | `136`, `2345` at `3` | `24` |
| 19 | `0235`, `046` at `0` | `35` |
| 23 | `014`, `156` at `1` | `04` |
| 27 | `025`, `046` at `0` | `25` |

Hence `TriGenFar` fails there (its first conjunct: no segment parallel to the
line), and the clause "`s = 1 → TriGenFar`" of the earlier statements of these
types excluded the whole hypersurface `s = 1`, of codimension 1. The statements
now ask for `EdgeFar` along the parallel edge at `s = 1` instead (Lemma T′ over
that edge, `EdgeChord.lean`), a condition of codimension 2 together with `s = 1`.

The theorems below record the parallel edge as an equality of a facet functional
at its two ends (the plane is parallel to the edge), and the failure of
`TriGenFar`.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-- `TriGenFar` fails when a segment `p q` of `V` is parallel to the line of the
two planes, i.e. both facet functionals take equal values at its ends. -/
theorem not_triGenFar_of_parallel {V Q1 Q2 : Finset ℝ³} {v p q : ℝ³} (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hv1 : v ∈ Q1) (hv2 : v ∈ Q2) (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (e1 : f1 q = f1 p) (e2 : f2 q = f2 p) : ¬ TriGenFar V Q1 Q2 v := by
  intro hT
  have shift : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f (v + (q - p)) = f v + (f q - f p) := by
    intro f
    obtain ⟨K, α, β, γ, h⟩ := affine_xyz f
    simp only [h, PiLp.add_apply, PiLp.sub_apply]; ring
  obtain ⟨hpar, -⟩ := hT f1 f2 z1 n1 z2 n2 (q - p) (sub_ne_zero.mpr hpq.symm)
    (by rw [shift, z1 v hv1, e1]; ring) (by rw [shift, z2 v hv2, e2]; ring)
  exact hpar p hp q hq hpq 1 (one_smul ℝ _).symm

/-- The barycentric value `fa y / ca + fb y / cb - 1`, as an affine map. -/
noncomputable def baryMap (fa fb : ℝ³ →ᵃ[ℝ] ℝ) (ca cb : ℝ) : ℝ³ →ᵃ[ℝ] ℝ :=
  ca⁻¹ • fa + cb⁻¹ • fb - AffineMap.const ℝ ℝ³ (1 : ℝ)

theorem baryMap_apply (fa fb : ℝ³ →ᵃ[ℝ] ℝ) (ca cb : ℝ) (y : ℝ³) :
    baryMap fa fb ca cb y = fa y / ca + fb y / cb - 1 := by
  simp [baryMap, div_eq_inv_mul]

/-- **The two-line argument, first form.** If the barycentric value is 1 at
three non-collinear points of the plane of `f`, then `f` is constant along any
segment on which the value is constant and `≠ 1`. -/
theorem eq_of_bary {f fa fb : ℝ³ →ᵃ[ℝ] ℝ} {ca cb : ℝ} {p q r : ℝ³} (hpq : p ≠ q)
    (hcol : ∀ c : ℝ, r - p ≠ c • (q - p)) (fp : f p = 0) (fq : f q = 0) (fr : f r = 0)
    (gp : fa p / ca + fb p / cb = 1) (gq : fa q / ca + fb q / cb = 1)
    (gr : fa r / ca + fb r / cb = 1) {y w : ℝ³}
    (hyw : fa y / ca + fb y / cb = fa w / ca + fb w / cb) (hw : fa w / ca + fb w / cb ≠ 1) :
    f y = f w := by
  have h := vanish3_ratio f (baryMap fa fb ca cb) hpq hcol fp fq fr
    (by rw [baryMap_apply, gp]; ring) (by rw [baryMap_apply, gq]; ring)
    (by rw [baryMap_apply, gr]; ring) y w
  rw [baryMap_apply, baryMap_apply, hyw] at h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hw) h

/-- **The two-line argument, second form.** If the barycentric value is 1 at
three non-collinear points of the plane of `f`, it is 1 on the whole plane. -/
theorem bary_eq_one_of_mem {f fa fb : ℝ³ →ᵃ[ℝ] ℝ} {ca cb : ℝ} {p q r : ℝ³} (hpq : p ≠ q)
    (hcol : ∀ c : ℝ, r - p ≠ c • (q - p)) (fp : f p = 0) (fq : f q = 0) (fr : f r = 0)
    (gp : fa p / ca + fb p / cb = 1) (gq : fa q / ca + fb q / cb = 1)
    (gr : fa r / ca + fb r / cb = 1) {y w : ℝ³} (fy : f y = 0) (fw : f w ≠ 0) :
    fa y / ca + fb y / cb = 1 := by
  have h := vanish3_ratio f (baryMap fa fb ca cb) hpq hcol fp fq fr
    (by rw [baryMap_apply, gp]; ring) (by rw [baryMap_apply, gq]; ring)
    (by rw [baryMap_apply, gr]; ring) y w
  rw [fy, zero_mul, baryMap_apply] at h
  have := (mul_eq_zero.mp h.symm).resolve_left fw
  linarith

theorem facet_zero_of_index {x : Fin 7 → ℝ³} {P : Finset (Fin 7)} {f : ℝ³ →ᵃ[ℝ] ℝ}
    (h : ∀ i, (i ∈ P → f (x i) = 0) ∧ (i ∉ P → f (x i) < 0)) : ∀ p ∈ P.image x, f p = 0 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact (h i).1 hi

theorem facet_neg_of_index {x : Fin 7 → ℝ³} {P : Finset (Fin 7)} {f : ℝ³ →ᵃ[ℝ] ℝ}
    (h : ∀ i, (i ∈ P → f (x i) = 0) ∧ (i ∉ P → f (x i) < 0)) :
    ∀ p ∈ univ.image x, p ∉ P.image x → f p < 0 := by
  intro p hp hpP
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  exact (h i).2 (fun hi => hpP (Finset.mem_image_of_mem x hi))

/-- Three distinct labelled points are not collinear. -/
theorem ncol_of_index {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ∀ c : ℝ, x k - x i ≠ c • (x j - x i) := by
  have hxV : ∀ i, x i ∈ univ.image x := fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  exact hgen (x i) (hxV i) (x j) (hxV j) (x k) (hxV k) (fun h => hij (hx h))
    (fun h => hik (hx h)) (fun h => hjk (hx h))


/-- **Type 05 at the special value**: if `fG x5 / fG x0 + fA x5 / fA x4 = 1`, the
plane of `246` is parallel to `01` (the plane of `0145` contains the line of the
planes of `0123` and `246`), so `01` is parallel to that line and `TriGenFar`
fails there. -/
theorem type05_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hs : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1) :
    fG (x 1) = fG (x 0) ∧
      ¬ TriGenFar (univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 2) := by
  have e : fG (x 1) = fG (x 0) := by
    have k := bary_eq_one_of_mem (f := fB) (fa := fG) (fb := fA) (p := x 0) (q := x 4) (r := x 5)
      (w := x 2) (fun h => by have := hx h; omega)
      (ncol_of_index hx hgen 0 4 5 (by decide) (by decide) (by decide))
      ((hB 0).1 (by decide)) ((hB 4).1 (by decide)) ((hB 5).1 (by decide))
      (by rw [(hA 0).1 (by decide), zero_div, add_zero, div_self ((hG 0).2 (by decide)).ne])
      (by rw [(hG 4).1 (by decide), zero_div, zero_add, div_self ((hA 4).2 (by decide)).ne]) hs
      ((hB 1).1 (by decide)) ((hB 2).2 (by decide)).ne
    rw [(hA 1).1 (by decide), zero_div, add_zero, div_eq_one_iff_eq ((hG 0).2 (by decide)).ne] at k
    exact k
  exact ⟨e, not_triGenFar_of_parallel fA fG (facet_zero_of_index hA) (facet_neg_of_index hA)
    (facet_zero_of_index hG) (facet_neg_of_index hG) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 0))
    (Finset.mem_image_of_mem x (Finset.mem_univ 1)) (fun h => by have := hx h; omega)
    (by rw [(hA 1).1 (by decide), (hA 0).1 (by decide)]) (e)⟩

/-- **Type 10 at the special value**: if `fB x0 / fB x2 + fA x0 / fA x3 = 1`, the
plane of `023` is parallel to `14`, so `14` is parallel to the line of the planes
of `023` and `1245`, and `TriGenFar` fails there. -/
theorem type10_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hs : fB (x 0) / fB (x 2) + fA (x 0) / fA (x 3) = 1) :
    fD (x 4) = fD (x 1) ∧
      ¬ TriGenFar (univ.image x) (({0, 2, 3} : Finset (Fin 7)).image x)
        (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 2) := by
  have e : fD (x 4) = fD (x 1) := by
    exact eq_of_bary (fa := fB) (fb := fA) (p := x 0) (q := x 2) (r := x 3)
      (fun h => by have := hx h; omega)
      (ncol_of_index hx hgen 0 2 3 (by decide) (by decide) (by decide))
      ((hD 0).1 (by decide)) ((hD 2).1 (by decide)) ((hD 3).1 (by decide)) hs
      (by rw [(hA 2).1 (by decide), zero_div, add_zero, div_self ((hB 2).2 (by decide)).ne])
      (by rw [(hB 3).1 (by decide), zero_div, zero_add, div_self ((hA 3).2 (by decide)).ne])
      (by rw [(hB 4).1 (by decide), (hA 4).1 (by decide), (hB 1).1 (by decide), (hA 1).1 (by decide)])
      (by rw [(hB 1).1 (by decide), (hA 1).1 (by decide)]; norm_num)
  exact ⟨e, not_triGenFar_of_parallel fD fA (facet_zero_of_index hD) (facet_neg_of_index hD)
    (facet_zero_of_index hA) (facet_neg_of_index hA) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 1))
    (Finset.mem_image_of_mem x (Finset.mem_univ 4)) (fun h => by have := hx h; omega)
    (e) (by rw [(hA 4).1 (by decide), (hA 1).1 (by decide)])⟩

/-- **Type 13 at the special value**: if `fB x3 / fB x1 + fA x3 / fA x2 = 1`, the
plane of `123` is parallel to `45`, so `45` is parallel to the line of the planes
of `0145` and `123`, and `TriGenFar` fails there. -/
theorem type13_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hs : fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1) :
    fD (x 5) = fD (x 4) ∧
      ¬ TriGenFar (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1) := by
  have e : fD (x 5) = fD (x 4) := by
    exact eq_of_bary (fa := fB) (fb := fA) (p := x 1) (q := x 2) (r := x 3)
      (fun h => by have := hx h; omega)
      (ncol_of_index hx hgen 1 2 3 (by decide) (by decide) (by decide))
      ((hD 1).1 (by decide)) ((hD 2).1 (by decide)) ((hD 3).1 (by decide))
      (by rw [(hA 1).1 (by decide), zero_div, add_zero, div_self ((hB 1).2 (by decide)).ne])
      (by rw [(hB 2).1 (by decide), zero_div, zero_add, div_self ((hA 2).2 (by decide)).ne]) hs
      (by rw [(hB 5).1 (by decide), (hA 5).1 (by decide), (hB 4).1 (by decide), (hA 4).1 (by decide)])
      (by rw [(hB 4).1 (by decide), (hA 4).1 (by decide)]; norm_num)
  exact ⟨e, not_triGenFar_of_parallel fA fD (facet_zero_of_index hA) (facet_neg_of_index hA)
    (facet_zero_of_index hD) (facet_neg_of_index hD) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 4))
    (Finset.mem_image_of_mem x (Finset.mem_univ 5)) (fun h => by have := hx h; omega)
    (by rw [(hA 5).1 (by decide), (hA 4).1 (by decide)]) (e)⟩

/-- **Type 17 at the special value**: if `fB x0 / fB x6 + fD x0 / fD x4 = 1`, the
plane of `136` is parallel to `24` (the plane of `0246` contains the line of the
planes of `136` and `2345`), so `24` is parallel to that line and `TriGenFar`
fails there. -/
theorem type17_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hs : fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1) :
    fD (x 4) = fD (x 2) ∧
      ¬ TriGenFar (univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) := by
  have e : fD (x 4) = fD (x 2) := by
    have k := bary_eq_one_of_mem (f := fA) (fa := fB) (fb := fD) (p := x 0) (q := x 4) (r := x 6)
      (w := x 3) (fun h => by have := hx h; omega)
      (ncol_of_index hx hgen 0 4 6 (by decide) (by decide) (by decide))
      ((hA 0).1 (by decide)) ((hA 4).1 (by decide)) ((hA 6).1 (by decide)) hs
      (by rw [(hB 4).1 (by decide), zero_div, zero_add, div_self ((hD 4).2 (by decide)).ne])
      (by rw [(hD 6).1 (by decide), zero_div, add_zero, div_self ((hB 6).2 (by decide)).ne])
      ((hA 2).1 (by decide)) ((hA 3).2 (by decide)).ne
    rw [(hB 2).1 (by decide), zero_div, zero_add, div_eq_one_iff_eq ((hD 4).2 (by decide)).ne] at k
    exact k.symm
  exact ⟨e, not_triGenFar_of_parallel fD fB (facet_zero_of_index hD) (facet_neg_of_index hD)
    (facet_zero_of_index hB) (facet_neg_of_index hB) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 2))
    (Finset.mem_image_of_mem x (Finset.mem_univ 4)) (fun h => by have := hx h; omega)
    (e) (by rw [(hB 4).1 (by decide), (hB 2).1 (by decide)])⟩

/-- **Type 19 at the special value**: if `fB x4 / fB x0 + fA x4 / fA x6 = 1`, the
plane of `046` is parallel to `35`, so `35` is parallel to the line of the planes
of `0235` and `046`, and `TriGenFar` fails there. -/
theorem type19_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hs : fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1) :
    fD (x 5) = fD (x 3) ∧
      ¬ TriGenFar (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) := by
  have e : fD (x 5) = fD (x 3) := by
    exact eq_of_bary (fa := fB) (fb := fA) (p := x 0) (q := x 4) (r := x 6)
      (fun h => by have := hx h; omega)
      (ncol_of_index hx hgen 0 4 6 (by decide) (by decide) (by decide))
      ((hD 0).1 (by decide)) ((hD 4).1 (by decide)) ((hD 6).1 (by decide))
      (by rw [(hA 0).1 (by decide), zero_div, add_zero, div_self ((hB 0).2 (by decide)).ne]) hs
      (by rw [(hB 6).1 (by decide), zero_div, zero_add, div_self ((hA 6).2 (by decide)).ne])
      (by rw [(hB 5).1 (by decide), (hA 5).1 (by decide), (hB 3).1 (by decide), (hA 3).1 (by decide)])
      (by rw [(hB 3).1 (by decide), (hA 3).1 (by decide)]; norm_num)
  exact ⟨e, not_triGenFar_of_parallel fA fD (facet_zero_of_index hA) (facet_neg_of_index hA)
    (facet_zero_of_index hD) (facet_neg_of_index hD) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 3))
    (Finset.mem_image_of_mem x (Finset.mem_univ 5)) (fun h => by have := hx h; omega)
    (by rw [(hA 5).1 (by decide), (hA 3).1 (by decide)]) (e)⟩

/-- **Type 23 at the special value**: if `fA x6 / fA x1 + fD x6 / fD x5 = 1`, the
plane of `156` is parallel to `04`, so `04` is parallel to the line of the planes
of `014` and `156`, and `TriGenFar` fails there. -/
theorem type23_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fD fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hs : fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5) = 1) :
    fH (x 4) = fH (x 0) ∧
      ¬ TriGenFar (univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
        (({1, 5, 6} : Finset (Fin 7)).image x) (x 1) := by
  have e : fH (x 4) = fH (x 0) := by
    exact eq_of_bary (fa := fA) (fb := fD) (p := x 1) (q := x 5) (r := x 6)
      (fun h => by have := hx h; omega)
      (ncol_of_index hx hgen 1 5 6 (by decide) (by decide) (by decide))
      ((hH 1).1 (by decide)) ((hH 5).1 (by decide)) ((hH 6).1 (by decide))
      (by rw [(hD 1).1 (by decide), zero_div, add_zero, div_self ((hA 1).2 (by decide)).ne])
      (by rw [(hA 5).1 (by decide), zero_div, zero_add, div_self ((hD 5).2 (by decide)).ne]) hs
      (by rw [(hA 4).1 (by decide), (hD 4).1 (by decide), (hA 0).1 (by decide), (hD 0).1 (by decide)])
      (by rw [(hA 0).1 (by decide), (hD 0).1 (by decide)]; norm_num)
  exact ⟨e, not_triGenFar_of_parallel fD fH (facet_zero_of_index hD) (facet_neg_of_index hD)
    (facet_zero_of_index hH) (facet_neg_of_index hH) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 0))
    (Finset.mem_image_of_mem x (Finset.mem_univ 4)) (fun h => by have := hx h; omega)
    (by rw [(hD 4).1 (by decide), (hD 0).1 (by decide)]) (e)⟩

/-- **Type 27 at the special value**: if `fG x2 / fG x5 = 1`, the plane of `046`
is parallel to `25`, so `25` is parallel to the line of the planes of `025` and
`046`, and `TriGenFar` fails there. -/
theorem type27_special_parallel (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (_hgen : NoThreeCollinear (univ.image x)) (fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hD : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hs : fG (x 2) / fG (x 5) = 1) :
    fG (x 5) = fG (x 2) ∧
      ¬ TriGenFar (univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) := by
  have e : fG (x 5) = fG (x 2) := by
    rw [div_eq_one_iff_eq ((hG 5).2 (by decide)).ne] at hs
    exact hs.symm
  exact ⟨e, not_triGenFar_of_parallel fD fG (facet_zero_of_index hD) (facet_neg_of_index hD)
    (facet_zero_of_index hG) (facet_neg_of_index hG) (Finset.mem_image_of_mem x (by decide))
    (Finset.mem_image_of_mem x (by decide)) (Finset.mem_image_of_mem x (Finset.mem_univ 2))
    (Finset.mem_image_of_mem x (Finset.mem_univ 5)) (fun h => by have := hx h; omega)
    (by rw [(hD 5).1 (by decide), (hD 2).1 (by decide)]) (e)⟩

end Minimality

end
