module

public import Minimality.SVCCells
public import Minimality.SilS0XD
public import Minimality.Type29Hole

@[expose] public section

/-!
# Type 29: the dominant SIGCHECK29 line pair F012xF015 + F124xF234 (PAIRLEAN29)

On the hole census (hl29 shapes) every closure of this line pair at the level of actual circuit
signs is already a SINGLE-view closure (no Gram coupling needed): the edge view `x 0 - x 1`
(line F012xF015) or the edge view `x 2 - x 4` (line F124xF234), each with one 5-point circuit
that is not facet-forced. Each circuit is stated as a determinant-sign hypothesis (two points on
the same / opposite sides of a plane through three vertices); in the normal form `NF29` they are
`a2 < 0` and `0 < b0`, i.e. the K1a sign pattern.

* `lexAny_e01`: facings `F234 -`, `F356 -` at `x 0 - x 1`, `Sep123_05`, distinct depths of
  `0, 1, 2, 3, 5` at `x 0 - x 1`  =>  `Gen.LexAny`.
* `lexAny_e24`: facings `F015 -`, `F035 -` at `x 2 - x 4`, `Sep013_24`, distinct depths of
  `0, 1, 2, 3, 4` at `x 2 - x 4`  =>  `Gen.LexAny`.
* `lexAny29_K1a_e01`, `lexAny29_K1a_e24`: the same for `s0x_fac29 N.facets` with the circuit
  hypothesis replaced by `N.a2 < 0` resp. `0 < N.b0`, conclusion `LexAny29`.

SINGLE29 (second part of this file): sixteen more single-view cells found by the single-view
census with actual circuit signs over all 36 facet-pair lines (14 edge views + 22 non-edge
lines). Fourteen are edge views, two are non-edge views `lv29 N X Y = cross N_X N_Y`. A
non-facet circuit enters through one hypothesis `PlaneSide x z a b i j` (sign of a product of
two determinants); in `NF29` all but two of them are K1 sign facts (`ps*_pos`, `ps*_neg`).
The two genuine shape conditions are `0 < PlaneSide x 2 5 6 0 1` (cell `e15a`, K1a) and
`PlaneSide x 2 4 6 0 1 < 0` (cell `e14b`, K1b); they stay as hypotheses.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC

namespace Minimality.PL29

/-! ### Generic helpers -/

/-- The facets of type 29 separate the vertices, so the vertices are distinct. -/
theorem inj29 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) : Function.Injective x := by
  intro i j h
  by_contra hne
  have key : ∀ i j : Fin 7, i ≠ j → ∃ t : Fin 9, i ∈ s0x_S29 t ∧ j ∉ s0x_S29 t := by decide
  obtain ⟨t, hi, hj⟩ := key i j hne
  have h1 := F.zero t i hi
  have h2 := F.neg t j hj
  rw [h] at h1; linarith

/-- An affine dependency evaluated on the affine function `det3 u v (· - z)`. -/
theorem det3_dep_sum {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (u v z : ℝ³) :
    ∑ i, mu i * det3 u v (y i - z) = 0 := by
  have h1 : ∀ i, mu i * det3 u v (y i - z) =
      mu i * ⟪cross u v, y i⟫ - mu i * ⟪cross u v, z⟫ := by
    intro i; simp only [det3, inner_sub_right]; ring
  simp only [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  have := congrArg (fun w => ⟪cross u v, w⟫) hdep
  simp only [inner_sum, real_inner_smul_right, inner_zero_right] at this
  exact this

/-- Plane relation: all weighted points but `i`, `j` on the plane `det3 u v (· - z) = 0`. -/
theorem plane_rel {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (u v z : ℝ³) {i j : Fin p} (hij : i ≠ j)
    (hon : ∀ l, l ≠ i → l ≠ j → det3 u v (y l - z) = 0) :
    mu i * det3 u v (y i - z) + mu j * det3 u v (y j - z) = 0 := by
  have h := det3_dep_sum y mu hsum hdep u v z
  rwa [Fintype.sum_eq_add i j hij (fun l hl => by rw [hon l hl.1 hl.2, mul_zero])] at h

theorem sign_rel_same {a b ga gb : ℝ} (h : a * ga + b * gb = 0) (hg : 0 < ga * gb) :
    SignType.sign a = -SignType.sign b := by
  have hgb : gb ≠ 0 := by rintro rfl; simp at hg
  have hsq : 0 < gb ^ 2 := by positivity
  have e : a * (ga * gb) = -(b * gb ^ 2) := by linear_combination gb * h
  have h1 : SignType.sign (a * (ga * gb)) = SignType.sign a := by
    rw [sign_mul, sign_pos hg, mul_one]
  have h2 : SignType.sign (-(b * gb ^ 2)) = -SignType.sign b := by
    rw [Left.sign_neg, sign_mul, sign_pos hsq, mul_one]
  rw [← h1, e, h2]

theorem sign_rel_opp {a b ga gb : ℝ} (h : a * ga + b * gb = 0) (hg : ga * gb < 0) :
    SignType.sign a = SignType.sign b := by
  have hgb : gb ≠ 0 := by rintro rfl; simp at hg
  have hsq : 0 < gb ^ 2 := by positivity
  have e : a * (ga * gb) = -(b * gb ^ 2) := by linear_combination gb * h
  have h1 : SignType.sign (a * (ga * gb)) = -SignType.sign a := by
    rw [sign_mul, sign_neg hg]; cases SignType.sign a <;> rfl
  have h2 : SignType.sign (-(b * gb ^ 2)) = -SignType.sign b := by
    rw [Left.sign_neg, sign_mul, sign_pos hsq, mul_one]
  have := h1.symm.trans (e ▸ h2)
  rw [neg_inj] at this
  exact this

theorem sgn_cases : ∀ a b : SignType, a ≠ 0 → b ≠ 0 → a * b = 1 ∨ a * b = -1 := by decide

/-- A nonzero dependency whose signs are `s` up to a common sign gives one with signs `s`. -/
theorem dep_normalize {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (hne : ∃ i, mu i ≠ 0) (s : Fin p → SignType) (k : Fin p)
    (hk : s k ≠ 0) (hrel : ∀ i, SignType.sign (mu i) = s i * s k * SignType.sign (mu k)) :
    ∃ mu' : Fin p → ℝ, ∑ i, mu' i = 0 ∧ ∑ i, mu' i • y i = 0 ∧
      ∀ i, SignType.sign (mu' i) = s i := by
  obtain ⟨i0, hi0⟩ := hne
  have hσ0 : SignType.sign (mu k) ≠ 0 := by
    intro h0; apply hi0; have := hrel i0; rw [h0, mul_zero] at this
    exact sign_eq_zero_iff.mp this
  rcases sgn_cases _ _ hk hσ0 with hc | hc
  · exact ⟨mu, hsum, hdep, fun i => by rw [hrel i, mul_assoc, hc, mul_one]⟩
  · refine ⟨fun i => -mu i, by rw [Finset.sum_neg_distrib, hsum, neg_zero],
      by simp only [neg_smul, Finset.sum_neg_distrib, hdep, neg_zero], fun i => ?_⟩
    rw [Left.sign_neg, hrel i, mul_assoc, hc]; cases s i <;> rfl

/-! ### The two circuit hypotheses -/

/-- `x 0` and `x 5` strictly on the same side of the plane through `x 1, x 2, x 3`
(circuit `{0,1,2,3,5}` with signs `0 1 3 +`, `2 5 -`; in `NF29`: `a2 < 0`). -/
def Sep123_05 (x : Fin 7 → ℝ³) : Prop :=
  0 < det3 (x 2 - x 1) (x 3 - x 1) (x 0 - x 1) * det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1)

/-- `x 2` and `x 4` strictly on opposite sides of the plane through `x 0, x 1, x 3`
(circuit `{0,1,2,3,4}` with signs `0 2 4 +`, `1 3 -`; in `NF29`: `0 < b0`). -/
def Sep013_24 (x : Fin 7 → ℝ³) : Prop :=
  det3 (x 0 - x 1) (x 3 - x 1) (x 2 - x 1) * det3 (x 0 - x 1) (x 3 - x 1) (x 4 - x 1) < 0

def PA : Fin 5 → Fin 7 := ![0, 1, 2, 3, 5]
def sA : Fin 5 → SignType := ![1, 1, -1, 1, -1]
def PB : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]
def sB : Fin 5 → SignType := ![1, -1, 1, -1, 1]

theorem depA {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) (hS : Sep123_05 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (PA i) = 0 ∧
      ∀ i, SignType.sign (mu i) = sA i := by
  have hP : Function.Injective (fun i => x (PA i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, -, hsum, hdep, hne⟩ := exists_dep PA hP Finset.univ (by simp)
  -- facet relations (012: 3|5, 023: 1|5, 035: 1|2)
  have r34 := facet_pair F PA mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 3 → l ≠ 4 → PA l ∈ s0x_S29 0) l h1 h2))
  have r14 := facet_pair F PA mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 1 → l ≠ 4 → PA l ∈ s0x_S29 2) l h1 h2))
  have r12 := facet_pair F PA mu hsum hdep 3 (i := 1) (j := 2) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 1 → l ≠ 2 → PA l ∈ s0x_S29 3) l h1 h2))
  -- the plane through 1, 2, 3: 0 and 5 on the same side
  have hpl := plane_rel (fun i => x (PA i)) mu hsum hdep (x 2 - x 1) (x 3 - x 1) (x 1)
    (i := 0) (j := 4) (by decide) (by
      intro l h1 h2
      fin_cases l
      · exact absurd rfl h1
      · show det3 (x 2 - x 1) (x 3 - x 1) (x 1 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · show det3 (x 2 - x 1) (x 3 - x 1) (x 2 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · show det3 (x 2 - x 1) (x 3 - x 1) (x 3 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · exact absurd rfl h2)
  have r04 := sign_rel_same hpl hS
  have e0 : SignType.sign (mu 0) = sA 0 * sA 4 * SignType.sign (mu 4) := by
    rw [r04]; cases SignType.sign (mu 4) <;> rfl
  have e1 : SignType.sign (mu 1) = sA 1 * sA 4 * SignType.sign (mu 4) := by
    rw [r14]; cases SignType.sign (mu 4) <;> rfl
  have e2 : SignType.sign (mu 2) = sA 2 * sA 4 * SignType.sign (mu 4) := by
    rw [← neg_neg (SignType.sign (mu 2)), ← r12, r14]; cases SignType.sign (mu 4) <;> rfl
  have e3 : SignType.sign (mu 3) = sA 3 * sA 4 * SignType.sign (mu 4) := by
    rw [r34]; cases SignType.sign (mu 4) <;> rfl
  have e4 : SignType.sign (mu 4) = sA 4 * sA 4 * SignType.sign (mu 4) := by
    cases SignType.sign (mu 4) <;> rfl
  exact dep_normalize _ mu hsum hdep hne sA 4 (by decide)
    (fun i => by fin_cases i <;> assumption)

theorem depB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) (hS : Sep013_24 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (PB i) = 0 ∧
      ∀ i, SignType.sign (mu i) = sB i := by
  have hP : Function.Injective (fun i => x (PB i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, -, hsum, hdep, hne⟩ := exists_dep PB hP Finset.univ (by simp)
  -- facet relations (012: 3|4, 234: 0|1, 124: 0|3)
  have r34 := facet_pair F PB mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 3 → l ≠ 4 → PB l ∈ s0x_S29 0) l h1 h2))
  have r01 := facet_pair F PB mu hsum hdep 6 (i := 0) (j := 1) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 0 → l ≠ 1 → PB l ∈ s0x_S29 6) l h1 h2))
  have r03 := facet_pair F PB mu hsum hdep 4 (i := 0) (j := 3) (by decide) (by decide)
    (by decide) (fun l h1 h2 => Or.inl
      ((by decide : ∀ l : Fin 5, l ≠ 0 → l ≠ 3 → PB l ∈ s0x_S29 4) l h1 h2))
  -- the plane through 0, 1, 3: 2 and 4 on opposite sides
  have hpl := plane_rel (fun i => x (PB i)) mu hsum hdep (x 0 - x 1) (x 3 - x 1) (x 1)
    (i := 2) (j := 4) (by decide) (by
      intro l h1 h2
      fin_cases l
      · show det3 (x 0 - x 1) (x 3 - x 1) (x 0 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · show det3 (x 0 - x 1) (x 3 - x 1) (x 1 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · exact absurd rfl h1
      · show det3 (x 0 - x 1) (x 3 - x 1) (x 3 - x 1) = 0
        simp only [det3_expand, PiLp.sub_apply]; ring
      · exact absurd rfl h2)
  have r24 := sign_rel_opp hpl hS
  have e3 : SignType.sign (mu 3) = sB 3 * sB 4 * SignType.sign (mu 4) := by
    rw [r34]; cases SignType.sign (mu 4) <;> rfl
  have e0 : SignType.sign (mu 0) = sB 0 * sB 4 * SignType.sign (mu 4) := by
    rw [r03, r34]; cases SignType.sign (mu 4) <;> rfl
  have e1 : SignType.sign (mu 1) = sB 1 * sB 4 * SignType.sign (mu 4) := by
    rw [← neg_neg (SignType.sign (mu 1)), ← r01, r03, r34]
    cases SignType.sign (mu 4) <;> rfl
  have e2 : SignType.sign (mu 2) = sB 2 * sB 4 * SignType.sign (mu 4) := by
    rw [r24]; cases SignType.sign (mu 4) <;> rfl
  have e4 : SignType.sign (mu 4) = sB 4 * sB 4 * SignType.sign (mu 4) := by
    cases SignType.sign (mu 4) <;> rfl
  exact dep_normalize _ mu hsum hdep hne sB 4 (by decide)
    (fun i => by fin_cases i <;> assumption)

/-! ### View `x 0 - x 1` (line F012xF015, facings `00++--?--`, F346 free) -/

def A_sw : Fin 9 → SignType := ![0, 0, 1, 1, -1, -1, -1, -1, -1]
def A_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 2, 3, 4], U := {2, 3}, Dn := {0, 1, 6, 8},
     sd := ![-1, -1, 0, 0, 0, 0, 0, 0, 0] },
   { k := 5, c := ![0, 1, 2, 3, 4], U := {0, 2, 3}, Dn := {1, 4, 6, 8},
     sd := ![1, -1, 0, 0, 0, 0, 0, 0, 0] },
   { k := 5, c := ![0, 1, 4, 3, 2], U := {1, 2, 3}, Dn := {0, 5, 6, 8},
     sd := ![-1, 1, 0, 0, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 2, 3, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![1, 1, 0, 0, 0, 0, 0, 0, 0] }]
def A_D : List (Fin 5 → SignType) := [sA]

theorem A_check : SVC.check s0x_S29 PA A_sw [(0, 1)] A_D A_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 1`** (the F012xF015 half of the dominant pair). -/
theorem lexAny_e01 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h234 : ⟪F.N 6, x 0 - x 1⟫ < 0) (h356 : ⟪F.N 8, x 0 - x 1⟫ < 0) (hS : Sep123_05 x)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ A_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ A_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 1⟫ = A_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg h356
  have hP : ∀ i, PA i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective PA := by decide
  refine svc_local F PA (x 0 - x 1) A_sw A_R hsw
    (hR_two F A_sw A_R 0 1 0 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [(0, 1)] ?_ A_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) A_check
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((inj29 F).ne (by decide))
  · intro s hs
    simp only [A_D, List.mem_singleton] at hs
    subst hs
    exact depA F hS

/-! ### View `x 2 - x 4` (line F124xF234, facings `+-+-0-0-?`, F356 free) -/

def B_sw : Fin 9 → SignType := ![1, -1, 1, -1, 0, -1, 0, -1, -1]
def B_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 2, 3], U := {0, 2}, Dn := {1, 3, 4, 6},
     sd := ![0, 0, 0, 0, -1, 0, -1, 0, 0] },
   { k := 5, c := ![0, 1, 4, 2, 3], U := {0, 2, 4}, Dn := {1, 3, 5, 6},
     sd := ![0, 0, 0, 0, 1, 0, -1, 0, 0] },
   { k := 5, c := ![0, 1, 2, 4, 3], U := {0, 2, 6}, Dn := {1, 3, 4, 7},
     sd := ![0, 0, 0, 0, -1, 0, 1, 0, 0] },
   { k := 4, c := ![0, 1, 4, 3], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, 0, 0, 0, 1, 0, 1, 0, 0] }]
def B_D : List (Fin 5 → SignType) := [sB]

theorem B_check : SVC.check s0x_S29 PB B_sw [(2, 4)] B_D B_R = true := by
  decide +kernel

/-- **Single view `x 2 - x 4`** (the F124xF234 half of the dominant pair). -/
theorem lexAny_e24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : ⟪F.N 1, x 2 - x 4⟫ < 0) (h035 : ⟪F.N 3, x 2 - x 4⟫ < 0) (hS : Sep013_24 x)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ B_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ B_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 4⟫ = B_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_neg h015
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_neg h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
  have hP : ∀ i, PB i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective PB := by decide
  refine svc_local F PB (x 2 - x 4) B_sw B_R hsw
    (hR_two F B_sw B_R 4 6 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [(2, 4)] ?_ B_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) B_check
  · intro ij hij
    simp only [List.mem_singleton] at hij
    subst hij
    exact forced_edge ((inj29 F).ne (by decide))
  · intro s hs
    simp only [B_D, List.mem_singleton] at hs
    subst hs
    exact depB F hS

/-! ### In the normal form: the circuit hypotheses are the K1a signs -/

theorem sep123_05_of_nf {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0) : Sep123_05 x := by
  have e1 : det3 (x 2 - x 1) (x 3 - x 1) (x 0 - x 1) =
      -(N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x0, N.x1, N.x2, N.x3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have e2 : det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) = N.a2 * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x1, N.x2, N.x3, N.x5]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have hD := N.hD
  have hD2 : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 := by positivity
  unfold Sep123_05
  rw [e1, e2, show -(N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ *
      (N.a2 * det3 N.E₁ N.E₂ N.E₃) =
      (-(N.a0 * N.b2 - N.a2 * N.b0) * N.a2) * det3 N.E₁ N.E₂ N.E₃ ^ 2 by ring]
  exact mul_pos (by nlinarith [N.hDD]) hD2

theorem sep013_24_of_nf {x : Fin 7 → ℝ³} (N : NF29 x) (hb0 : 0 < N.b0) : Sep013_24 x := by
  have e1 : det3 (x 0 - x 1) (x 3 - x 1) (x 2 - x 1) =
      (N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x0, N.x1, N.x2, N.x3]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have e2 : det3 (x 0 - x 1) (x 3 - x 1) (x 4 - x 1) = -N.b0 * det3 N.E₁ N.E₂ N.E₃ := by
    rw [N.x0, N.x1, N.x3, N.x4]; simp only [nfP_sub, det3_nfV, det3c]; ring
  have hD := N.hD
  have hD2 : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 := by positivity
  unfold Sep013_24
  rw [e1, e2, show (N.a0 * N.b2 - N.a2 * N.b0) * det3 N.E₁ N.E₂ N.E₃ *
      (-N.b0 * det3 N.E₁ N.E₂ N.E₃) =
      (-((N.a0 * N.b2 - N.a2 * N.b0) * N.b0)) * det3 N.E₁ N.E₂ N.E₃ ^ 2 by ring]
  have : 0 < (N.a0 * N.b2 - N.a2 * N.b0) * N.b0 := mul_pos N.hDD hb0
  nlinarith

/-- **K1a, view `x 0 - x 1`.** -/
theorem lexAny29_K1a_e01 {x : Fin 7 → ℝ³} (N : NF29 x) (ha2 : N.a2 < 0)
    (h234 : ⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0)
    (h356 : ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e01 _ h234 h356 (sep123_05_of_nf N ha2) hgen

/-- **K1a, view `x 2 - x 4`.** -/
theorem lexAny29_K1a_e24 {x : Fin 7 → ℝ³} (N : NF29 x) (hb0 : 0 < N.b0)
    (h015 : ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ < 0)
    (h035 : ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e24 _ h015 h035 (sep013_24_of_nf N hb0) hgen

/-- **Hole exclusion.** On `Hole29` in class K1a, neither single view of the dominant pair has
the facings of `lexAny_e01` / `lexAny_e24` with distinct depths. -/
theorem hole29_K1a_not_e01_e24 {x : Fin 7 → ℝ³} {N : NF29 x} (h : Minimality.H29.Hole29 x N)
    (hK1a : N.a2 < 0 ∧ 0 < N.b0) :
    ¬ ((⟪(s0x_fac29 N.facets).N 6, x 0 - x 1⟫ < 0 ∧ ⟪(s0x_fac29 N.facets).N 8, x 0 - x 1⟫ < 0 ∧
        ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
          i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫) ∨
      (⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫ < 0 ∧ ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫ < 0 ∧
        ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
          i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫)) := by
  have hnl := h.2.2.2.2.2.1
  rintro (⟨a, b, c⟩ | ⟨a, b, c⟩)
  · exact hnl (lexAny29_K1a_e01 N hK1a.1 a b c)
  · exact hnl (lexAny29_K1a_e24 N hK1a.2 a b c)


/-! ## SINGLE29: more single-view cells -/

/-- Product of the two plane-side determinants of `x i`, `x j` for the plane `x z, x a, x b`:
positive iff they are strictly on the same side. -/
noncomputable def PlaneSide (x : Fin 7 → ℝ³) (z a b i j : Fin 7) : ℝ :=
  det3 (x a - x z) (x b - x z) (x i - x z) * det3 (x a - x z) (x b - x z) (x j - x z)

/-- Plane relation, with points of weight zero allowed off the plane. -/
theorem plane_rel0 {p : ℕ} (y : Fin p → ℝ³) (mu : Fin p → ℝ) (hsum : ∑ i, mu i = 0)
    (hdep : ∑ i, mu i • y i = 0) (u v z : ℝ³) {i j : Fin p} (hij : i ≠ j)
    (hon : ∀ l, l ≠ i → l ≠ j → det3 u v (y l - z) = 0 ∨ mu l = 0) :
    mu i * det3 u v (y i - z) + mu j * det3 u v (y j - z) = 0 := by
  have h := det3_dep_sum y mu hsum hdep u v z
  rwa [Fintype.sum_eq_add i j hij (fun l hl => by
    rcases hon l hl.1 hl.2 with h | h
    · rw [h, mul_zero]
    · rw [h, zero_mul])] at h

/-! ### The plane-side hypotheses in the normal form `NF29` -/

section NF
variable {x : Fin 7 → ℝ³}

theorem ps23501_nf (N : NF29 x) : PlaneSide x 2 3 5 0 1 =
    (N.a2 * (1 - N.b0 - N.h0) - N.a0 * (1 - N.b2 - N.h2)) * N.a2 * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  unfold PlaneSide; rw [N.x0, N.x1, N.x2, N.x3, N.x5]; simp only [nfP_sub, det3_nfV, det3c]; ring

theorem ps13402_nf (N : NF29 x) : PlaneSide x 1 3 4 0 2 =
    N.b0 * N.b2 * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  unfold PlaneSide; rw [N.x0, N.x1, N.x2, N.x3, N.x4]; simp only [nfP_sub, det3_nfV, det3c]; ring

theorem ps13405_nf (N : NF29 x) : PlaneSide x 1 3 4 0 5 =
    N.b0 * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  unfold PlaneSide; rw [N.x0, N.x1, N.x3, N.x4, N.x5]; simp only [nfP_sub, det3_nfV, det3c]; ring

theorem ps23514_nf (N : NF29 x) : PlaneSide x 2 3 5 1 4 =
    -(N.a2 * (1 - N.a2 - N.b2 - N.h2)) * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  unfold PlaneSide; rw [N.x1, N.x2, N.x3, N.x4, N.x5]; simp only [nfP_sub, det3_nfV, det3c]; ring

theorem ps24501_nf (N : NF29 x) : PlaneSide x 2 4 5 0 1 =
    -(N.V * N.h2) * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  unfold PlaneSide NF29.V; rw [N.x0, N.x1, N.x2, N.x4, N.x5]; simp only [nfP_sub, det3_nfV, det3c]
  ring

theorem nf_D2 (N : NF29 x) : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  have := N.hD; positivity

/-- `[0235] > 0` (vertex 2 below facet 035). -/
theorem nf_q35 (N : NF29 x) : 0 < N.a2 * (1 - N.b0 - N.h0) - N.a0 * (1 - N.b2 - N.h2) := by
  nlinarith [N.hE35]

theorem ps23501_pos (N : NF29 x) (ha2 : 0 < N.a2) : 0 < PlaneSide x 2 3 5 0 1 := by
  rw [ps23501_nf]; exact mul_pos (mul_pos (nf_q35 N) ha2) (nf_D2 N)
theorem ps23501_neg (N : NF29 x) (ha2 : N.a2 < 0) : PlaneSide x 2 3 5 0 1 < 0 := by
  rw [ps23501_nf]; exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (nf_q35 N) ha2) (nf_D2 N)
theorem ps13402_pos (N : NF29 x) (hb0 : N.b0 < 0) : 0 < PlaneSide x 1 3 4 0 2 := by
  rw [ps13402_nf]; exact mul_pos (mul_pos_of_neg_of_neg hb0 N.hb2) (nf_D2 N)
theorem ps13402_neg (N : NF29 x) (hb0 : 0 < N.b0) : PlaneSide x 1 3 4 0 2 < 0 := by
  rw [ps13402_nf]; exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb0 N.hb2) (nf_D2 N)
theorem ps13405_pos (N : NF29 x) (hb0 : 0 < N.b0) : 0 < PlaneSide x 1 3 4 0 5 := by
  rw [ps13405_nf]; exact mul_pos hb0 (nf_D2 N)
theorem ps13405_neg (N : NF29 x) (hb0 : N.b0 < 0) : PlaneSide x 1 3 4 0 5 < 0 := by
  rw [ps13405_nf]; exact mul_neg_of_neg_of_pos hb0 (nf_D2 N)
theorem ps23514_pos (N : NF29 x) (ha2 : N.a2 < 0) : 0 < PlaneSide x 2 3 5 1 4 := by
  rw [ps23514_nf]
  have h := N.t345_2
  exact mul_pos (by nlinarith) (nf_D2 N)
theorem ps23514_neg (N : NF29 x) (ha2 : 0 < N.a2) : PlaneSide x 2 3 5 1 4 < 0 := by
  rw [ps23514_nf]
  have h := N.t345_2
  exact mul_neg_of_neg_of_pos (by nlinarith) (nf_D2 N)
theorem ps24501_pos (N : NF29 x) (hV : N.V < 0) : 0 < PlaneSide x 2 4 5 0 1 := by
  rw [ps24501_nf]; exact mul_pos (by nlinarith [N.hh2]) (nf_D2 N)
theorem ps24501_neg (N : NF29 x) (hV : 0 < N.V) : PlaneSide x 2 4 5 0 1 < 0 := by
  rw [ps24501_nf]; exact mul_neg_of_neg_of_pos (by nlinarith [N.hh2]) (nf_D2 N)

end NF

/-- The non-edge view along the line of facets `X`, `Y` (the cross product of their normals). -/
noncomputable def lv29 {x : Fin 7 → ℝ³} (N : NF29 x) (X Y : Fin 9) : ℝ³ :=
  cross ((s0x_fac29 N.facets).N X) ((s0x_fac29 N.facets).N Y)

/-! ### Cell `e05b`: line F015xF035 = edge view (x 0 - x 5), facings +0+0----- (rep K1b_1, census cover 144) -/

def e05b_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 5]
def e05b_s0 : Fin 5 → SignType := ![1, -1, 1, -1, 1]  -- circuit +-+-0+0

theorem e05b_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 2 3 5 0 1) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e05b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e05b_s0 i := by
  have hP : Function.Injective (fun i => x (e05b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e05b_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e05b_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e05b_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    )
  have r2 := facet_pair F e05b_P mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e05b_P mu hsum hdep 3 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_same (plane_rel0 (fun i => x (e05b_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v0 v1 v2 v3 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = -v2 → v0 = -v1 →
     v0 = e05b_s0 0 * e05b_s0 4 * v5 ∧ v1 = e05b_s0 1 * e05b_s0 4 * v5 ∧ v2 = e05b_s0 2 * e05b_s0 4 * v5 ∧ v3 = e05b_s0 3 * e05b_s0 4 * v5 ∧ v5 = e05b_s0 4 * e05b_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e05b_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e05b_sw : Fin 9 → SignType := ![1, 0, 1, 0, -1, -1, -1, 1, -1]
def e05b_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 2, 3], U := {0, 2}, Dn := {1, 3, 4, 6},
     sd := ![0, -1, 0, -1, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 2, 3, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![0, 1, 0, 1, 0, 0, 0, 0, 0] }]
def e05b_D : List (Fin 5 → SignType) := [e05b_s0]

theorem e05b_check : SVC.check s0x_S29 e05b_P e05b_sw [] e05b_D e05b_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 5`** (line F015xF035). -/
theorem lexAny_e05b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h124 : ⟪F.N 4, x 0 - x 5⟫ < 0)
    (h234 : ⟪F.N 6, x 0 - x 5⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 0 1)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 5⟫ ≠ ⟪x j, x 0 - x 5⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e05b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e05b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 5⟫ = e05b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 3 (by decide) (by decide))
    · exact sign_neg h124
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hP : ∀ i, e05b_P i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e05b_P := by decide
  refine svc_local F e05b_P (x 0 - x 5) e05b_sw e05b_R hsw
    (hR_two F e05b_sw e05b_R 1 3 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e05b_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e05b_check
  intro s hs
  simp only [e05b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e05b_dep0 F hS0


/-! ### Cell `e12b`: line F012xF124 = edge view (x 1 - x 2), facings 0+-+0+-++ (rep K1b_1, census cover 134) -/

def e12b_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]
def e12b_s0 : Fin 5 → SignType := ![1, -1, -1, -1, 1]  -- circuit +---+00

theorem e12b_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 1 3 4 0 2) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e12b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e12b_s0 i := by
  have hP : Function.Injective (fun i => x (e12b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e12b_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e12b_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e12b_P mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e12b_P mu hsum hdep 4 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e12b_P mu hsum hdep 6 (i := 0) (j := 1) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_same (plane_rel0 (fun i => x (e12b_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 2) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v0 v1 v2 v3 v4 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = -v1 → v0 = -v2 →
     v0 = e12b_s0 0 * e12b_s0 4 * v4 ∧ v1 = e12b_s0 1 * e12b_s0 4 * v4 ∧ v2 = e12b_s0 2 * e12b_s0 4 * v4 ∧ v3 = e12b_s0 3 * e12b_s0 4 * v4 ∧ v4 = e12b_s0 4 * e12b_s0 4 * v4 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e12b_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e12b_sw : Fin 9 → SignType := ![0, 1, -1, 1, 0, 1, -1, 1, 1]
def e12b_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 4, 3], U := {1, 3, 5, 7}, Dn := {0, 2, 4, 6},
     sd := ![-1, 0, 0, 0, -1, 0, 0, 0, 0] },
   { k := 4, c := ![0, 2, 4, 3], U := {0, 3, 4, 7}, Dn := {2, 6},
     sd := ![1, 0, 0, 0, 1, 0, 0, 0, 0] }]
def e12b_D : List (Fin 5 → SignType) := [e12b_s0]

theorem e12b_check : SVC.check s0x_S29 e12b_P e12b_sw [] e12b_D e12b_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 2`** (line F012xF124). -/
theorem lexAny_e12b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h035 : 0 < ⟪F.N 3, x 1 - x 2⟫)
    (h346 : 0 < ⟪F.N 7, x 1 - x 2⟫)
    (hS0 : 0 < PlaneSide x 1 3 4 0 2)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e12b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e12b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 2⟫ = e12b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_neg (edge_neg F 2 (by decide) (by decide))
    · exact sign_pos h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_pos (edge_pos F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_pos h346
  have hP : ∀ i, e12b_P i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e12b_P := by decide
  refine svc_local F e12b_P (x 1 - x 2) e12b_sw e12b_R hsw
    (hR_two F e12b_sw e12b_R 0 4 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e12b_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e12b_check
  intro s hs
  simp only [e12b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e12b_dep0 F hS0


/-! ### Cell `e02a`: line F012xF023 = edge view (x 0 - x 2), facings 0+0+-+-++ (rep K1aG_32, census cover 135) -/

def e02a_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]
def e02a_s0 : Fin 5 → SignType := ![1, -1, 1, -1, 1]  -- circuit +-+-+00

theorem e02a_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 1 3 4 0 2 < 0) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e02a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e02a_s0 i := by
  have hP : Function.Injective (fun i => x (e02a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e02a_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e02a_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e02a_P mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e02a_P mu hsum hdep 4 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e02a_P mu hsum hdep 6 (i := 0) (j := 1) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_opp (plane_rel0 (fun i => x (e02a_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 2) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v0 v1 v2 v3 v4 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = -v1 → v0 = v2 →
     v0 = e02a_s0 0 * e02a_s0 4 * v4 ∧ v1 = e02a_s0 1 * e02a_s0 4 * v4 ∧ v2 = e02a_s0 2 * e02a_s0 4 * v4 ∧ v3 = e02a_s0 3 * e02a_s0 4 * v4 ∧ v4 = e02a_s0 4 * e02a_s0 4 * v4 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e02a_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e02a_sw : Fin 9 → SignType := ![0, 1, 0, 1, -1, 1, -1, 1, 1]
def e02a_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 4, 3], U := {1, 3, 5, 7}, Dn := {0, 2, 4, 6},
     sd := ![-1, 0, -1, 0, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 2, 3, 4], U := {0, 2, 5, 7}, Dn := {4, 6},
     sd := ![1, 0, 1, 0, 0, 0, 0, 0, 0] }]
def e02a_D : List (Fin 5 → SignType) := [e02a_s0]

theorem e02a_check : SVC.check s0x_S29 e02a_P e02a_sw [] e02a_D e02a_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 2`** (line F012xF023). -/
theorem lexAny_e02a {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h1456 : 0 < ⟪F.N 5, x 0 - x 2⟫)
    (h346 : 0 < ⟪F.N 7, x 0 - x 2⟫)
    (hS0 : PlaneSide x 1 3 4 0 2 < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e02a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e02a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 2⟫ = e02a_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_pos h1456
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_pos h346
  have hP : ∀ i, e02a_P i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e02a_P := by decide
  refine svc_local F e02a_P (x 0 - x 2) e02a_sw e02a_R hsw
    (hR_two F e02a_sw e02a_R 0 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e02a_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e02a_check
  intro s hs
  simp only [e02a_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e02a_dep0 F hS0


/-! ### Cell `e15a`: line F015xF1456 = edge view (x 1 - x 5), facings +0--+0--- (rep K1aG_115, census cover 78) -/

def e15a_P : Fin 6 → Fin 7 := ![0, 1, 2, 4, 5, 6]
def e15a_s0 : Fin 6 → SignType := ![1, -1, -1, 1, -1, 0]  -- circuit +--0+-0
def e15a_s1 : Fin 6 → SignType := ![1, -1, -1, 0, -1, 1]  -- circuit +--00-+
def e15a_s2 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e15a_s3 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e15a_s4 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem e15a_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 2 4 5 0 1) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a_s0 i := by
  have hP : Function.Injective (fun i => x (e15a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e15a_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F e15a_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F e15a_P mu hsum hdep 4 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r3 := facet_pair F e15a_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_same (plane_rel0 (fun i => x (e15a_P i)) mu hsum hdep (x 4 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 4 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v2 v4 v5 : SignType, v4 = -v5 → v2 = -v4 → v0 = -v5 → v0 = -v2 → v0 = -v1 →
     v0 = e15a_s0 0 * e15a_s0 4 * v5 ∧ v1 = e15a_s0 1 * e15a_s0 4 * v5 ∧ v2 = e15a_s0 2 * e15a_s0 4 * v5 ∧ v4 = e15a_s0 3 * e15a_s0 4 * v5 ∧ v5 = e15a_s0 4 * e15a_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a_s0 5 * e15a_s0 4 * b) _

theorem e15a_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS1 : 0 < PlaneSide x 2 5 6 0 1) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a_s1 i := by
  have hP : Function.Injective (fun i => x (e15a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a_P hP ({0, 1, 2, 4, 5} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e15a_P mu hsum hdep 0 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e15a_P mu hsum hdep 1 (i := 2) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (e15a_P i)) mu hsum hdep (x 5 - x 2) (x 6 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 5 - x 2) (x 6 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · left; show det3 (x 5 - x 2) (x 6 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 5 - x 2) (x 6 - x 2) (x 6 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS1)
  have key : ∀ v0 v1 v2 v5 v6 : SignType, v5 = -v6 → v2 = -v6 → v0 = -v2 → v0 = -v1 →
     v0 = e15a_s1 0 * e15a_s1 5 * v6 ∧ v1 = e15a_s1 1 * e15a_s1 5 * v6 ∧ v2 = e15a_s1 2 * e15a_s1 5 * v6 ∧ v5 = e15a_s1 4 * e15a_s1 5 * v6 ∧ v6 = e15a_s1 5 * e15a_s1 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e15a_s1 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a_s1 3 * e15a_s1 5 * b) _
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a_s2 i := by
  have hP : Function.Injective (fun i => x (e15a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a_s2 0 * e15a_s2 5 * v6 ∧ v1 = e15a_s2 1 * e15a_s2 5 * v6 ∧ v4 = e15a_s2 3 * e15a_s2 5 * v6 ∧ v5 = e15a_s2 4 * e15a_s2 5 * v6 ∧ v6 = e15a_s2 5 * e15a_s2 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a_s2 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a_s2 2 * e15a_s2 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a_dep3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a_s3 i := by
  have hP : Function.Injective (fun i => x (e15a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a_s3 0 * e15a_s3 5 * v6 ∧ v1 = e15a_s3 1 * e15a_s3 5 * v6 ∧ v4 = e15a_s3 3 * e15a_s3 5 * v6 ∧ v5 = e15a_s3 4 * e15a_s3 5 * v6 ∧ v6 = e15a_s3 5 * e15a_s3 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a_s3 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a_s3 2 * e15a_s3 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a_dep4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a_s4 i := by
  have hP : Function.Injective (fun i => x (e15a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a_s4 0 * e15a_s4 5 * v6 ∧ v1 = e15a_s4 1 * e15a_s4 5 * v6 ∧ v4 = e15a_s4 3 * e15a_s4 5 * v6 ∧ v5 = e15a_s4 4 * e15a_s4 5 * v6 ∧ v6 = e15a_s4 5 * e15a_s4 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a_s4 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a_s4 2 * e15a_s4 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e15a_sw : Fin 9 → SignType := ![1, 0, -1, -1, 1, 0, -1, -1, -1]
def e15a_R : List (SVC.Rim 9 6) :=
  [{ k := 4, c := ![0, 1, 3, 2], U := {0, 4}, Dn := {1, 2, 5, 6},
     sd := ![0, -1, 0, 0, 0, -1, 0, 0, 0] },
   { k := 5, c := ![0, 2, 3, 5, 4], U := {0, 1, 4, 5}, Dn := {2, 3, 6, 7, 8},
     sd := ![0, 1, 0, 0, 0, 1, 0, 0, 0] }]
def e15a_D : List (Fin 6 → SignType) := [e15a_s0, e15a_s1, e15a_s2, e15a_s3, e15a_s4]

theorem e15a_check : SVC.check s0x_S29 e15a_P e15a_sw [] e15a_D e15a_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 5`** (line F015xF1456). -/
theorem lexAny_e15a {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : ⟪F.N 2, x 1 - x 5⟫ < 0)
    (h234 : ⟪F.N 6, x 1 - x 5⟫ < 0)
    (h346 : ⟪F.N 7, x 1 - x 5⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 4 5 0 1)
    (hS1 : 0 < PlaneSide x 2 5 6 0 1)
    (hgen : ∀ i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e15a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e15a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 5⟫ = e15a_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_neg h023
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg h234
    · exact sign_neg h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hP : ∀ i, e15a_P i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e15a_P := by decide
  refine svc_local F e15a_P (x 1 - x 5) e15a_sw e15a_R hsw
    (hR_two F e15a_sw e15a_R 1 5 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e15a_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e15a_check
  intro s hs
  simp only [e15a_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e15a_dep0 F hS0
  · exact e15a_dep1 F hS1
  · exact e15a_dep2 F
  · exact e15a_dep3 F
  · exact e15a_dep4 F


/-! ### Cell `e15a2`: line F015xF1456 = edge view (x 1 - x 5), facings +0+-+0++- (rep K1aN_36, census cover 45) -/

def e15a2_P : Fin 6 → Fin 7 := ![0, 1, 3, 4, 5, 6]
def e15a2_s0 : Fin 6 → SignType := ![1, -1, -1, 1, -1, 0]  -- circuit +-0-+-0
def e15a2_s1 : Fin 6 → SignType := ![1, 0, -1, -1, -1, 1]  -- circuit +00---+ (facet-forced)
def e15a2_s2 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e15a2_s3 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e15a2_s4 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem e15a2_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a2_s0 i := by
  have hP : Function.Injective (fun i => x (e15a2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a2_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e15a2_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F e15a2_P mu hsum hdep 3 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F e15a2_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (e15a2_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 4) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v3 v4 v5 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = -v5 →
     v0 = e15a2_s0 0 * e15a2_s0 4 * v5 ∧ v1 = e15a2_s0 1 * e15a2_s0 4 * v5 ∧ v3 = e15a2_s0 2 * e15a2_s0 4 * v5 ∧ v4 = e15a2_s0 3 * e15a2_s0 4 * v5 ∧ v5 = e15a2_s0 4 * e15a2_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e15a2_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a2_s0 5 * e15a2_s0 4 * b) _

theorem e15a2_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a2_s1 i := by
  have hP : Function.Injective (fun i => x (e15a2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a2_P hP ({0, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e15a2_P mu hsum hdep 3 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e15a2_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F e15a2_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e15a2_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v3 v4 v5 v6 : SignType, v4 = -v6 → v0 = -v3 → v0 = -v5 → v0 = -v4 →
     v0 = e15a2_s1 0 * e15a2_s1 5 * v6 ∧ v3 = e15a2_s1 2 * e15a2_s1 5 * v6 ∧ v4 = e15a2_s1 3 * e15a2_s1 5 * v6 ∧ v5 = e15a2_s1 4 * e15a2_s1 5 * v6 ∧ v6 = e15a2_s1 5 * e15a2_s1 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e15a2_s1 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a2_s1 1 * e15a2_s1 5 * b) _
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a2_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a2_s2 i := by
  have hP : Function.Injective (fun i => x (e15a2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a2_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a2_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a2_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a2_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a2_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a2_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a2_s2 0 * e15a2_s2 5 * v6 ∧ v1 = e15a2_s2 1 * e15a2_s2 5 * v6 ∧ v4 = e15a2_s2 3 * e15a2_s2 5 * v6 ∧ v5 = e15a2_s2 4 * e15a2_s2 5 * v6 ∧ v6 = e15a2_s2 5 * e15a2_s2 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a2_s2 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a2_s2 2 * e15a2_s2 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a2_dep3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a2_s3 i := by
  have hP : Function.Injective (fun i => x (e15a2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a2_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a2_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a2_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a2_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a2_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a2_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a2_s3 0 * e15a2_s3 5 * v6 ∧ v1 = e15a2_s3 1 * e15a2_s3 5 * v6 ∧ v4 = e15a2_s3 3 * e15a2_s3 5 * v6 ∧ v5 = e15a2_s3 4 * e15a2_s3 5 * v6 ∧ v6 = e15a2_s3 5 * e15a2_s3 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a2_s3 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a2_s3 2 * e15a2_s3 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a2_dep4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a2_s4 i := by
  have hP : Function.Injective (fun i => x (e15a2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a2_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a2_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a2_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a2_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a2_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a2_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a2_s4 0 * e15a2_s4 5 * v6 ∧ v1 = e15a2_s4 1 * e15a2_s4 5 * v6 ∧ v4 = e15a2_s4 3 * e15a2_s4 5 * v6 ∧ v5 = e15a2_s4 4 * e15a2_s4 5 * v6 ∧ v6 = e15a2_s4 5 * e15a2_s4 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a2_s4 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a2_s4 2 * e15a2_s4 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e15a2_sw : Fin 9 → SignType := ![1, 0, 1, -1, 1, 0, 1, 1, -1]
def e15a2_R : List (SVC.Rim 9 6) :=
  [{ k := 5, c := ![0, 1, 3, 5, 2], U := {0, 2, 4, 7}, Dn := {1, 3, 5, 8},
     sd := ![0, -1, 0, 0, 0, -1, 0, 0, 0] },
   { k := 4, c := ![0, 2, 5, 4], U := {1, 2, 5, 7}, Dn := {3, 8},
     sd := ![0, 1, 0, 0, 0, 1, 0, 0, 0] }]
def e15a2_D : List (Fin 6 → SignType) := [e15a2_s0, e15a2_s1, e15a2_s2, e15a2_s3, e15a2_s4]

theorem e15a2_check : SVC.check s0x_S29 e15a2_P e15a2_sw [] e15a2_D e15a2_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 5`** (line F015xF1456). -/
theorem lexAny_e15a2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 5⟫)
    (h346 : 0 < ⟪F.N 7, x 1 - x 5⟫)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5)
    (hgen : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e15a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e15a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 5⟫ = e15a2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_pos h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hP : ∀ i, e15a2_P i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e15a2_P := by decide
  refine svc_local F e15a2_P (x 1 - x 5) e15a2_sw e15a2_R hsw
    (hR_two F e15a2_sw e15a2_R 1 5 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e15a2_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e15a2_check
  intro s hs
  simp only [e15a2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e15a2_dep0 F hS0
  · exact e15a2_dep1 F
  · exact e15a2_dep2 F
  · exact e15a2_dep3 F
  · exact e15a2_dep4 F


/-! ### Cell `e02b`: line F012xF023 = edge view (x 0 - x 2), facings 0+0+----- (rep K1b_6, census cover 49) -/

def e02b_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 5]
def e02b_s0 : Fin 5 → SignType := ![1, -1, 1, -1, 1]  -- circuit +-+-0+0

theorem e02b_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 2 3 5 0 1) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e02b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e02b_s0 i := by
  have hP : Function.Injective (fun i => x (e02b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e02b_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e02b_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e02b_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    )
  have r2 := facet_pair F e02b_P mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e02b_P mu hsum hdep 3 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_same (plane_rel0 (fun i => x (e02b_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v0 v1 v2 v3 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = -v2 → v0 = -v1 →
     v0 = e02b_s0 0 * e02b_s0 4 * v5 ∧ v1 = e02b_s0 1 * e02b_s0 4 * v5 ∧ v2 = e02b_s0 2 * e02b_s0 4 * v5 ∧ v3 = e02b_s0 3 * e02b_s0 4 * v5 ∧ v5 = e02b_s0 4 * e02b_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e02b_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e02b_sw : Fin 9 → SignType := ![0, 1, 0, 1, -1, -1, -1, 1, -1]
def e02b_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 4, 3], U := {1, 3}, Dn := {0, 2, 5, 8},
     sd := ![-1, 0, -1, 0, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 2, 3, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![1, 0, 1, 0, 0, 0, 0, 0, 0] }]
def e02b_D : List (Fin 5 → SignType) := [e02b_s0]

theorem e02b_check : SVC.check s0x_S29 e02b_P e02b_sw [] e02b_D e02b_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 2`** (line F012xF023). -/
theorem lexAny_e02b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h1456 : ⟪F.N 5, x 0 - x 2⟫ < 0)
    (h356 : ⟪F.N 8, x 0 - x 2⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 0 1)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e02b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e02b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 2⟫ = e02b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr (edge_zero F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_pos (edge_pos F 3 (by decide) (by decide))
    · exact sign_neg (edge_neg F 4 (by decide) (by decide))
    · exact sign_neg h1456
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg h356
  have hP : ∀ i, e02b_P i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e02b_P := by decide
  refine svc_local F e02b_P (x 0 - x 2) e02b_sw e02b_R hsw
    (hR_two F e02b_sw e02b_R 0 2 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e02b_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e02b_check
  intro s hs
  simp only [e02b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e02b_dep0 F hS0


/-! ### Cell `e14b`: line F124xF1456 = edge view (x 1 - x 4), facings ++--00--- (rep K1b_25, census cover 29) -/

def e14b_P : Fin 6 → Fin 7 := ![0, 1, 2, 4, 5, 6]
def e14b_s0 : Fin 6 → SignType := ![1, 1, -1, 1, -1, 0]  -- circuit ++-0+-0
def e14b_s1 : Fin 6 → SignType := ![1, 1, -1, 1, 0, -1]  -- circuit ++-0+0-
def e14b_s2 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b_s3 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b_s4 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem e14b_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 2 4 5 0 1 < 0) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b_s0 i := by
  have hP : Function.Injective (fun i => x (e14b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e14b_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F e14b_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F e14b_P mu hsum hdep 4 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r3 := facet_pair F e14b_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_opp (plane_rel0 (fun i => x (e14b_P i)) mu hsum hdep (x 4 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 4 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 4 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v2 v4 v5 : SignType, v4 = -v5 → v2 = -v4 → v0 = -v5 → v0 = -v2 → v0 = v1 →
     v0 = e14b_s0 0 * e14b_s0 4 * v5 ∧ v1 = e14b_s0 1 * e14b_s0 4 * v5 ∧ v2 = e14b_s0 2 * e14b_s0 4 * v5 ∧ v4 = e14b_s0 3 * e14b_s0 4 * v5 ∧ v5 = e14b_s0 4 * e14b_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b_s0 5 * e14b_s0 4 * b) _

theorem e14b_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS1 : PlaneSide x 2 4 6 0 1 < 0) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b_s1 i := by
  have hP : Function.Injective (fun i => x (e14b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b_P hP ({0, 1, 2, 3, 5} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e14b_P mu hsum hdep 0 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e14b_P mu hsum hdep 4 (i := 0) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_opp (plane_rel0 (fun i => x (e14b_P i)) mu hsum hdep (x 4 - x 2) (x 6 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 4 - x 2) (x 6 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 4 - x 2) (x 6 - x 2) (x 4 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    · left; show det3 (x 4 - x 2) (x 6 - x 2) (x 6 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS1)
  have key : ∀ v0 v1 v2 v4 v6 : SignType, v4 = -v6 → v0 = -v6 → v0 = -v2 → v0 = v1 →
     v0 = e14b_s1 0 * e14b_s1 5 * v6 ∧ v1 = e14b_s1 1 * e14b_s1 5 * v6 ∧ v2 = e14b_s1 2 * e14b_s1 5 * v6 ∧ v4 = e14b_s1 3 * e14b_s1 5 * v6 ∧ v6 = e14b_s1 5 * e14b_s1 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e14b_s1 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b_s1 4 * e14b_s1 5 * b) _
  · exact hk.2.2.2.2

theorem e14b_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b_s2 i := by
  have hP : Function.Injective (fun i => x (e14b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e14b_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e14b_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e14b_s2 0 * e14b_s2 5 * v6 ∧ v1 = e14b_s2 1 * e14b_s2 5 * v6 ∧ v4 = e14b_s2 3 * e14b_s2 5 * v6 ∧ v5 = e14b_s2 4 * e14b_s2 5 * v6 ∧ v6 = e14b_s2 5 * e14b_s2 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b_s2 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b_s2 2 * e14b_s2 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b_dep3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b_s3 i := by
  have hP : Function.Injective (fun i => x (e14b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e14b_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e14b_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e14b_s3 0 * e14b_s3 5 * v6 ∧ v1 = e14b_s3 1 * e14b_s3 5 * v6 ∧ v4 = e14b_s3 3 * e14b_s3 5 * v6 ∧ v5 = e14b_s3 4 * e14b_s3 5 * v6 ∧ v6 = e14b_s3 5 * e14b_s3 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b_s3 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b_s3 2 * e14b_s3 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b_dep4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b_s4 i := by
  have hP : Function.Injective (fun i => x (e14b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e14b_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e14b_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e14b_s4 0 * e14b_s4 5 * v6 ∧ v1 = e14b_s4 1 * e14b_s4 5 * v6 ∧ v4 = e14b_s4 3 * e14b_s4 5 * v6 ∧ v5 = e14b_s4 4 * e14b_s4 5 * v6 ∧ v6 = e14b_s4 5 * e14b_s4 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b_s4 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b_s4 2 * e14b_s4 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e14b_sw : Fin 9 → SignType := ![1, 1, -1, -1, 0, 0, -1, -1, -1]
def e14b_R : List (SVC.Rim 9 6) :=
  [{ k := 4, c := ![0, 2, 1, 4], U := {0, 1}, Dn := {2, 3, 4, 5},
     sd := ![0, 0, 0, 0, -1, -1, 0, 0, 0] },
   { k := 5, c := ![0, 2, 3, 5, 4], U := {0, 1, 4, 5}, Dn := {2, 3, 6, 7, 8},
     sd := ![0, 0, 0, 0, 1, 1, 0, 0, 0] }]
def e14b_D : List (Fin 6 → SignType) := [e14b_s0, e14b_s1, e14b_s2, e14b_s3, e14b_s4]

theorem e14b_check : SVC.check s0x_S29 e14b_P e14b_sw [] e14b_D e14b_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 4`** (line F124xF1456). -/
theorem lexAny_e14b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : ⟪F.N 2, x 1 - x 4⟫ < 0)
    (h035 : ⟪F.N 3, x 1 - x 4⟫ < 0)
    (h356 : ⟪F.N 8, x 1 - x 4⟫ < 0)
    (hS0 : PlaneSide x 2 4 5 0 1 < 0)
    (hS1 : PlaneSide x 2 4 6 0 1 < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e14b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e14b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 4⟫ = e14b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_neg h023
    · exact sign_neg h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_neg h356
  have hP : ∀ i, e14b_P i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e14b_P := by decide
  refine svc_local F e14b_P (x 1 - x 4) e14b_sw e14b_R hsw
    (hR_two F e14b_sw e14b_R 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e14b_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e14b_check
  intro s hs
  simp only [e14b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e14b_dep0 F hS0
  · exact e14b_dep1 F hS1
  · exact e14b_dep2 F
  · exact e14b_dep3 F
  · exact e14b_dep4 F


/-! ### Cell `e14b2`: line F124xF1456 = edge view (x 1 - x 4), facings ++++00--+ (rep K1b_2, census cover 40) -/

def e14b2_P : Fin 6 → Fin 7 := ![1, 2, 3, 4, 5, 6]
def e14b2_s0 : Fin 6 → SignType := ![1, -1, 1, 1, -1, 0]  -- circuit 0+-++-0
def e14b2_s1 : Fin 6 → SignType := ![1, 0, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b2_s2 : Fin 6 → SignType := ![1, 0, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b2_s3 : Fin 6 → SignType := ![1, 0, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b2_s4 : Fin 6 → SignType := ![0, 1, -1, -1, -1, 1]  -- circuit 00+---+ (facet-forced)

theorem e14b2_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 2 3 5 1 4 < 0) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b2_s0 i := by
  have hP : Function.Injective (fun i => x (e14b2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b2_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e14b2_P mu hsum hdep 4 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F e14b2_P mu hsum hdep 5 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F e14b2_P mu hsum hdep 6 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r3 := (sign_rel_opp (plane_rel0 (fun i => x (e14b2_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 3) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v1 v2 v3 v4 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = v4 →
     v1 = e14b2_s0 0 * e14b2_s0 4 * v5 ∧ v2 = e14b2_s0 1 * e14b2_s0 4 * v5 ∧ v3 = e14b2_s0 2 * e14b2_s0 4 * v5 ∧ v4 = e14b2_s0 3 * e14b2_s0 4 * v5 ∧ v5 = e14b2_s0 4 * e14b2_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e14b2_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b2_s0 5 * e14b2_s0 4 * b) _

theorem e14b2_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b2_s1 i := by
  have hP : Function.Injective (fun i => x (e14b2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b2_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z2 : mu 1 = 0 := facet_zero F e14b2_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z2, sign_zero]
  have r1 := facet_pair F e14b2_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z2
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b2_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b2_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b2_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v2 v4 v5 v6 : SignType, v2 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = e14b2_s1 0 * e14b2_s1 5 * v6 ∧ v2 = e14b2_s1 1 * e14b2_s1 5 * v6 ∧ v4 = e14b2_s1 3 * e14b2_s1 5 * v6 ∧ v5 = e14b2_s1 4 * e14b2_s1 5 * v6 ∧ v6 = e14b2_s1 5 * e14b2_s1 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b2_s1 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b2_s1 2 * e14b2_s1 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b2_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b2_s2 i := by
  have hP : Function.Injective (fun i => x (e14b2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b2_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z2 : mu 1 = 0 := facet_zero F e14b2_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z2, sign_zero]
  have r1 := facet_pair F e14b2_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z2
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b2_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b2_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b2_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v2 v4 v5 v6 : SignType, v2 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = e14b2_s2 0 * e14b2_s2 5 * v6 ∧ v2 = e14b2_s2 1 * e14b2_s2 5 * v6 ∧ v4 = e14b2_s2 3 * e14b2_s2 5 * v6 ∧ v5 = e14b2_s2 4 * e14b2_s2 5 * v6 ∧ v6 = e14b2_s2 5 * e14b2_s2 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b2_s2 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b2_s2 2 * e14b2_s2 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b2_dep3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b2_s3 i := by
  have hP : Function.Injective (fun i => x (e14b2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b2_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z2 : mu 1 = 0 := facet_zero F e14b2_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z2, sign_zero]
  have r1 := facet_pair F e14b2_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z2
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b2_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b2_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b2_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v2 v4 v5 v6 : SignType, v2 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = e14b2_s3 0 * e14b2_s3 5 * v6 ∧ v2 = e14b2_s3 1 * e14b2_s3 5 * v6 ∧ v4 = e14b2_s3 3 * e14b2_s3 5 * v6 ∧ v5 = e14b2_s3 4 * e14b2_s3 5 * v6 ∧ v6 = e14b2_s3 5 * e14b2_s3 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b2_s3 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b2_s3 2 * e14b2_s3 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b2_dep4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b2_s4 i := by
  have hP : Function.Injective (fun i => x (e14b2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b2_P hP ({1, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e14b2_P mu hsum hdep 5 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r1 := facet_pair F e14b2_P mu hsum hdep 6 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b2_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e14b2_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v2 v3 v4 v5 v6 : SignType, v2 = -v3 → v5 = -v6 → v2 = -v5 → v2 = -v4 →
     v2 = e14b2_s4 1 * e14b2_s4 5 * v6 ∧ v3 = e14b2_s4 2 * e14b2_s4 5 * v6 ∧ v4 = e14b2_s4 3 * e14b2_s4 5 * v6 ∧ v5 = e14b2_s4 4 * e14b2_s4 5 * v6 ∧ v6 = e14b2_s4 5 * e14b2_s4 5 * v6 := by decide
  have hk := key (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e14b2_s4 5 (by decide) (fun i => ?_)
  fin_cases i
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b2_s4 0 * e14b2_s4 5 * b) _
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e14b2_sw : Fin 9 → SignType := ![1, 1, 1, 1, 0, 0, -1, -1, 1]
def e14b2_R : List (SVC.Rim 9 6) :=
  [{ k := 5, c := ![0, 1, 2, 5, 4], U := {0, 1, 2, 8}, Dn := {4, 5, 6, 7},
     sd := ![0, 0, 0, 0, -1, -1, 0, 0, 0] },
   { k := 4, c := ![1, 2, 5, 3], U := {2, 4, 5, 8}, Dn := {6, 7},
     sd := ![0, 0, 0, 0, 1, 1, 0, 0, 0] }]
def e14b2_D : List (Fin 6 → SignType) := [e14b2_s0, e14b2_s1, e14b2_s2, e14b2_s3, e14b2_s4]

theorem e14b2_check : SVC.check s0x_S29 e14b2_P e14b2_sw [] e14b2_D e14b2_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 4`** (line F124xF1456). -/
theorem lexAny_e14b2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 4⟫)
    (h356 : 0 < ⟪F.N 8, x 1 - x 4⟫)
    (hS0 : PlaneSide x 2 3 5 1 4 < 0)
    (hgen : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e14b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e14b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 4⟫ = e14b2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_pos h356
  have hP : ∀ i, e14b2_P i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e14b2_P := by decide
  refine svc_local F e14b2_P (x 1 - x 4) e14b2_sw e14b2_R hsw
    (hR_two F e14b2_sw e14b2_R 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e14b2_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e14b2_check
  intro s hs
  simp only [e14b2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e14b2_dep0 F hS0
  · exact e14b2_dep1 F
  · exact e14b2_dep2 F
  · exact e14b2_dep3 F
  · exact e14b2_dep4 F


/-! ### Cell `e15a3`: line F015xF1456 = edge view (x 1 - x 5), facings +0+-+0+-- (rep K1aN_98, census cover 19) -/

def e15a3_P : Fin 6 → Fin 7 := ![0, 1, 3, 4, 5, 6]
def e15a3_s0 : Fin 6 → SignType := ![1, -1, -1, 1, -1, 0]  -- circuit +-0-+-0
def e15a3_s1 : Fin 6 → SignType := ![1, 0, -1, -1, -1, 1]  -- circuit +00---+ (facet-forced)
def e15a3_s2 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e15a3_s3 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e15a3_s4 : Fin 6 → SignType := ![0, 1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem e15a3_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a3_s0 i := by
  have hP : Function.Injective (fun i => x (e15a3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a3_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e15a3_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F e15a3_P mu hsum hdep 3 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · right; exact hz _ (by decide)
    )
  have r2 := facet_pair F e15a3_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (e15a3_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 4) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v0 v1 v3 v4 v5 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = -v5 →
     v0 = e15a3_s0 0 * e15a3_s0 4 * v5 ∧ v1 = e15a3_s0 1 * e15a3_s0 4 * v5 ∧ v3 = e15a3_s0 2 * e15a3_s0 4 * v5 ∧ v4 = e15a3_s0 3 * e15a3_s0 4 * v5 ∧ v5 = e15a3_s0 4 * e15a3_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e15a3_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a3_s0 5 * e15a3_s0 4 * b) _

theorem e15a3_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a3_s1 i := by
  have hP : Function.Injective (fun i => x (e15a3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a3_P hP ({0, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e15a3_P mu hsum hdep 3 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e15a3_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F e15a3_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e15a3_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v3 v4 v5 v6 : SignType, v4 = -v6 → v0 = -v3 → v0 = -v5 → v0 = -v4 →
     v0 = e15a3_s1 0 * e15a3_s1 5 * v6 ∧ v3 = e15a3_s1 2 * e15a3_s1 5 * v6 ∧ v4 = e15a3_s1 3 * e15a3_s1 5 * v6 ∧ v5 = e15a3_s1 4 * e15a3_s1 5 * v6 ∧ v6 = e15a3_s1 5 * e15a3_s1 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e15a3_s1 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a3_s1 1 * e15a3_s1 5 * b) _
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a3_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a3_s2 i := by
  have hP : Function.Injective (fun i => x (e15a3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a3_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a3_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a3_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a3_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a3_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a3_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a3_s2 0 * e15a3_s2 5 * v6 ∧ v1 = e15a3_s2 1 * e15a3_s2 5 * v6 ∧ v4 = e15a3_s2 3 * e15a3_s2 5 * v6 ∧ v5 = e15a3_s2 4 * e15a3_s2 5 * v6 ∧ v6 = e15a3_s2 5 * e15a3_s2 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a3_s2 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a3_s2 2 * e15a3_s2 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a3_dep3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a3_s3 i := by
  have hP : Function.Injective (fun i => x (e15a3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a3_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a3_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a3_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a3_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a3_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a3_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a3_s3 0 * e15a3_s3 5 * v6 ∧ v1 = e15a3_s3 1 * e15a3_s3 5 * v6 ∧ v4 = e15a3_s3 3 * e15a3_s3 5 * v6 ∧ v5 = e15a3_s3 4 * e15a3_s3 5 * v6 ∧ v6 = e15a3_s3 5 * e15a3_s3 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a3_s3 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a3_s3 2 * e15a3_s3 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e15a3_dep4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e15a3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e15a3_s4 i := by
  have hP : Function.Injective (fun i => x (e15a3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e15a3_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z0 : mu 0 = 0 := facet_zero F e15a3_P mu hsum hdep 5 (i := 0) (by decide) (by
    intro l h1
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 0) = 0 := by rw [z0, sign_zero]
  have r1 := facet_pair F e15a3_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e15a3_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e15a3_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e15a3_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact z0
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v0 v1 v4 v5 v6 : SignType, v0 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v0 = e15a3_s4 0 * e15a3_s4 5 * v6 ∧ v1 = e15a3_s4 1 * e15a3_s4 5 * v6 ∧ v4 = e15a3_s4 3 * e15a3_s4 5 * v6 ∧ v5 = e15a3_s4 4 * e15a3_s4 5 * v6 ∧ v6 = e15a3_s4 5 * e15a3_s4 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e15a3_s4 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e15a3_s4 2 * e15a3_s4 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e15a3_sw : Fin 9 → SignType := ![1, 0, 1, -1, 1, 0, 1, -1, -1]
def e15a3_R : List (SVC.Rim 9 6) :=
  [{ k := 4, c := ![0, 1, 3, 2], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, -1, 0, 0, 0, -1, 0, 0, 0] },
   { k := 5, c := ![0, 2, 3, 5, 4], U := {1, 2, 5, 6}, Dn := {3, 7, 8},
     sd := ![0, 1, 0, 0, 0, 1, 0, 0, 0] }]
def e15a3_D : List (Fin 6 → SignType) := [e15a3_s0, e15a3_s1, e15a3_s2, e15a3_s3, e15a3_s4]

theorem e15a3_check : SVC.check s0x_S29 e15a3_P e15a3_sw [] e15a3_D e15a3_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 5`** (line F015xF1456). -/
theorem lexAny_e15a3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 5⟫)
    (h234 : 0 < ⟪F.N 6, x 1 - x 5⟫)
    (h346 : ⟪F.N 7, x 1 - x 5⟫ < 0)
    (hS0 : 0 < PlaneSide x 1 3 4 0 5)
    (hgen : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e15a3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e15a3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 5⟫ = e15a3_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_pos h234
    · exact sign_neg h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hP : ∀ i, e15a3_P i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e15a3_P := by decide
  refine svc_local F e15a3_P (x 1 - x 5) e15a3_sw e15a3_R hsw
    (hR_two F e15a3_sw e15a3_R 1 5 1 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e15a3_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e15a3_check
  intro s hs
  simp only [e15a3_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e15a3_dep0 F hS0
  · exact e15a3_dep1 F
  · exact e15a3_dep2 F
  · exact e15a3_dep3 F
  · exact e15a3_dep4 F


/-! ### Cell `e14b3`: line F124xF1456 = edge view (x 1 - x 4), facings ++++00--- (rep K1b_20, census cover 61) -/

def e14b3_P : Fin 6 → Fin 7 := ![1, 2, 3, 4, 5, 6]
def e14b3_s0 : Fin 6 → SignType := ![1, -1, 1, 1, -1, 0]  -- circuit 0+-++-0
def e14b3_s1 : Fin 6 → SignType := ![1, 0, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b3_s2 : Fin 6 → SignType := ![1, 0, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b3_s3 : Fin 6 → SignType := ![1, 0, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def e14b3_s4 : Fin 6 → SignType := ![0, 1, -1, -1, -1, 1]  -- circuit 00+---+ (facet-forced)

theorem e14b3_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 2 3 5 1 4 < 0) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b3_s0 i := by
  have hP : Function.Injective (fun i => x (e14b3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b3_P hP ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e14b3_P mu hsum hdep 4 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r1 := facet_pair F e14b3_P mu hsum hdep 5 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F e14b3_P mu hsum hdep 6 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · right; exact hz _ (by decide)
    )
  have r3 := (sign_rel_opp (plane_rel0 (fun i => x (e14b3_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 3) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · right; exact hz _ (by decide)
    )) hS0)
  have key : ∀ v1 v2 v3 v4 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = v4 →
     v1 = e14b3_s0 0 * e14b3_s0 4 * v5 ∧ v2 = e14b3_s0 1 * e14b3_s0 4 * v5 ∧ v3 = e14b3_s0 2 * e14b3_s0 4 * v5 ∧ v4 = e14b3_s0 3 * e14b3_s0 4 * v5 ∧ v5 = e14b3_s0 4 * e14b3_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e14b3_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b3_s0 5 * e14b3_s0 4 * b) _

theorem e14b3_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b3_s1 i := by
  have hP : Function.Injective (fun i => x (e14b3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b3_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z2 : mu 1 = 0 := facet_zero F e14b3_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z2, sign_zero]
  have r1 := facet_pair F e14b3_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z2
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b3_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b3_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b3_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v2 v4 v5 v6 : SignType, v2 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = e14b3_s1 0 * e14b3_s1 5 * v6 ∧ v2 = e14b3_s1 1 * e14b3_s1 5 * v6 ∧ v4 = e14b3_s1 3 * e14b3_s1 5 * v6 ∧ v5 = e14b3_s1 4 * e14b3_s1 5 * v6 ∧ v6 = e14b3_s1 5 * e14b3_s1 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b3_s1 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b3_s1 2 * e14b3_s1 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b3_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b3_s2 i := by
  have hP : Function.Injective (fun i => x (e14b3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b3_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z2 : mu 1 = 0 := facet_zero F e14b3_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z2, sign_zero]
  have r1 := facet_pair F e14b3_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z2
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b3_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b3_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b3_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v2 v4 v5 v6 : SignType, v2 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = e14b3_s2 0 * e14b3_s2 5 * v6 ∧ v2 = e14b3_s2 1 * e14b3_s2 5 * v6 ∧ v4 = e14b3_s2 3 * e14b3_s2 5 * v6 ∧ v5 = e14b3_s2 4 * e14b3_s2 5 * v6 ∧ v6 = e14b3_s2 5 * e14b3_s2 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b3_s2 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b3_s2 2 * e14b3_s2 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b3_dep3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b3_s3 i := by
  have hP : Function.Injective (fun i => x (e14b3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b3_P hP ({0, 1, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have z2 : mu 1 = 0 := facet_zero F e14b3_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z2, sign_zero]
  have r1 := facet_pair F e14b3_P mu hsum hdep 1 (i := 3) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z2
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b3_P mu hsum hdep 4 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · right; exact hz _ (by decide)
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e14b3_P mu hsum hdep 7 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F e14b3_P mu hsum hdep 8 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · right; exact z2
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v2 v4 v5 v6 : SignType, v2 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = e14b3_s3 0 * e14b3_s3 5 * v6 ∧ v2 = e14b3_s3 1 * e14b3_s3 5 * v6 ∧ v4 = e14b3_s3 3 * e14b3_s3 5 * v6 ∧ v5 = e14b3_s3 4 * e14b3_s3 5 * v6 ∧ v6 = e14b3_s3 5 * e14b3_s3 5 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e14b3_s3 5 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b3_s3 2 * e14b3_s3 5 * b) _
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem e14b3_dep4 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 6 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e14b3_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e14b3_s4 i := by
  have hP : Function.Injective (fun i => x (e14b3_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e14b3_P hP ({1, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have r0 := facet_pair F e14b3_P mu hsum hdep 5 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r1 := facet_pair F e14b3_P mu hsum hdep 6 (i := 4) (j := 5) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e14b3_P mu hsum hdep 7 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e14b3_P mu hsum hdep 8 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · right; exact hz _ (by decide)
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v2 v3 v4 v5 v6 : SignType, v2 = -v3 → v5 = -v6 → v2 = -v5 → v2 = -v4 →
     v2 = e14b3_s4 1 * e14b3_s4 5 * v6 ∧ v3 = e14b3_s4 2 * e14b3_s4 5 * v6 ∧ v4 = e14b3_s4 3 * e14b3_s4 5 * v6 ∧ v5 = e14b3_s4 4 * e14b3_s4 5 * v6 ∧ v6 = e14b3_s4 5 * e14b3_s4 5 * v6 := by decide
  have hk := key (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) (SignType.sign (mu 5)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e14b3_s4 5 (by decide) (fun i => ?_)
  fin_cases i
  · rw [hz _ (by decide), sign_zero]; exact (by decide : ∀ b : SignType, (0 : SignType) = e14b3_s4 0 * e14b3_s4 5 * b) _
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e14b3_sw : Fin 9 → SignType := ![1, 1, 1, 1, 0, 0, -1, -1, -1]
def e14b3_R : List (SVC.Rim 9 6) :=
  [{ k := 4, c := ![0, 1, 2, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![0, 0, 0, 0, -1, -1, 0, 0, 0] },
   { k := 5, c := ![1, 2, 4, 5, 3], U := {2, 3, 4, 5}, Dn := {6, 7, 8},
     sd := ![0, 0, 0, 0, 1, 1, 0, 0, 0] }]
def e14b3_D : List (Fin 6 → SignType) := [e14b3_s0, e14b3_s1, e14b3_s2, e14b3_s3, e14b3_s4]

theorem e14b3_check : SVC.check s0x_S29 e14b3_P e14b3_sw [] e14b3_D e14b3_R = true := by
  decide +kernel

/-- **Single view `x 1 - x 4`** (line F124xF1456). -/
theorem lexAny_e14b3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h023 : 0 < ⟪F.N 2, x 1 - x 4⟫)
    (h035 : 0 < ⟪F.N 3, x 1 - x 4⟫)
    (h356 : ⟪F.N 8, x 1 - x 4⟫ < 0)
    (hS0 : PlaneSide x 2 3 5 1 4 < 0)
    (hgen : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e14b3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e14b3_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 1 - x 4⟫ = e14b3_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_pos h023
    · exact sign_pos h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 5 (by decide) (by decide))
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_neg h356
  have hP : ∀ i, e14b3_P i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e14b3_P := by decide
  refine svc_local F e14b3_P (x 1 - x 4) e14b3_sw e14b3_R hsw
    (hR_two F e14b3_sw e14b3_R 4 5 1 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e14b3_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e14b3_check
  intro s hs
  simp only [e14b3_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact e14b3_dep0 F hS0
  · exact e14b3_dep1 F
  · exact e14b3_dep2 F
  · exact e14b3_dep3 F
  · exact e14b3_dep4 F


/-! ### Cell `e24a2`: line F124xF234 = edge view (x 2 - x 4), facings ++++0-0-- (rep K1aG_155, census cover 65) -/

def e24a2_P : Fin 5 → Fin 7 := ![1, 2, 3, 4, 5]
def e24a2_s0 : Fin 5 → SignType := ![1, -1, 1, -1, -1]  -- circuit 0+-+--0

theorem e24a2_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 2 3 5 1 4) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e24a2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e24a2_s0 i := by
  have hP : Function.Injective (fun i => x (e24a2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e24a2_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e24a2_P mu hsum hdep 4 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e24a2_P mu hsum hdep 5 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have r2 := facet_pair F e24a2_P mu hsum hdep 6 (i := 0) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r3 := (sign_rel_same (plane_rel0 (fun i => x (e24a2_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 3) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v1 v2 v3 v4 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = -v4 →
     v1 = e24a2_s0 0 * e24a2_s0 4 * v5 ∧ v2 = e24a2_s0 1 * e24a2_s0 4 * v5 ∧ v3 = e24a2_s0 2 * e24a2_s0 4 * v5 ∧ v4 = e24a2_s0 3 * e24a2_s0 4 * v5 ∧ v5 = e24a2_s0 4 * e24a2_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e24a2_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e24a2_sw : Fin 9 → SignType := ![1, 1, 1, 1, 0, -1, 0, -1, -1]
def e24a2_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 2, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![0, 0, 0, 0, -1, 0, -1, 0, 0] },
   { k := 4, c := ![0, 3, 2, 4], U := {1, 3, 4, 6}, Dn := {5, 7, 8},
     sd := ![0, 0, 0, 0, 1, 0, 1, 0, 0] }]
def e24a2_D : List (Fin 5 → SignType) := [e24a2_s0]

theorem e24a2_check : SVC.check s0x_S29 e24a2_P e24a2_sw [] e24a2_D e24a2_R = true := by
  decide +kernel

/-- **Single view `x 2 - x 4`** (line F124xF234). -/
theorem lexAny_e24a2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : 0 < ⟪F.N 1, x 2 - x 4⟫)
    (h035 : 0 < ⟪F.N 3, x 2 - x 4⟫)
    (h356 : ⟪F.N 8, x 2 - x 4⟫ < 0)
    (hS0 : 0 < PlaneSide x 2 3 5 1 4)
    (hgen : ∀ i ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e24a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e24a2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 4⟫ = e24a2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos h015
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_pos h035
    · exact sign_eq_zero_iff.mpr (edge_zero F 4 (by decide) (by decide))
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
    · exact sign_neg h356
  have hP : ∀ i, e24a2_P i ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e24a2_P := by decide
  refine svc_local F e24a2_P (x 2 - x 4) e24a2_sw e24a2_R hsw
    (hR_two F e24a2_sw e24a2_R 4 6 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e24a2_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e24a2_check
  intro s hs
  simp only [e24a2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e24a2_dep0 F hS0


/-! ### Cell `e05b2`: line F015xF035 = edge view (x 0 - x 5), facings +0+0+-+-- (rep K1b_42, census cover 13) -/

def e05b2_P : Fin 5 → Fin 7 := ![0, 1, 3, 4, 5]
def e05b2_s0 : Fin 5 → SignType := ![1, -1, -1, 1, 1]  -- circuit +-0-++0

theorem e05b2_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 1 3 4 0 5 < 0) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e05b2_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e05b2_s0 i := by
  have hP : Function.Injective (fun i => x (e05b2_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e05b2_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e05b2_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    )
  have r1 := facet_pair F e05b2_P mu hsum hdep 3 (i := 1) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r2 := facet_pair F e05b2_P mu hsum hdep 5 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have r3 := (sign_rel_opp (plane_rel0 (fun i => x (e05b2_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 4) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    )) hS0)
  have key : ∀ v0 v1 v3 v4 v5 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = v5 →
     v0 = e05b2_s0 0 * e05b2_s0 4 * v5 ∧ v1 = e05b2_s0 1 * e05b2_s0 4 * v5 ∧ v3 = e05b2_s0 2 * e05b2_s0 4 * v5 ∧ v4 = e05b2_s0 3 * e05b2_s0 4 * v5 ∧ v5 = e05b2_s0 4 * e05b2_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3
  refine dep_normalize _ mu hsum hdep hne e05b2_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e05b2_sw : Fin 9 → SignType := ![1, 0, 1, 0, 1, -1, 1, -1, -1]
def e05b2_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 3, 2], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, -1, 0, -1, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 3, 2, 4], U := {1, 3, 4, 6}, Dn := {5, 7, 8},
     sd := ![0, 1, 0, 1, 0, 0, 0, 0, 0] }]
def e05b2_D : List (Fin 5 → SignType) := [e05b2_s0]

theorem e05b2_check : SVC.check s0x_S29 e05b2_P e05b2_sw [] e05b2_D e05b2_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 5`** (line F015xF035). -/
theorem lexAny_e05b2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h124 : 0 < ⟪F.N 4, x 0 - x 5⟫)
    (h234 : 0 < ⟪F.N 6, x 0 - x 5⟫)
    (h346 : ⟪F.N 7, x 0 - x 5⟫ < 0)
    (hS0 : PlaneSide x 1 3 4 0 5 < 0)
    (hgen : ∀ i ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 5⟫ ≠ ⟪x j, x 0 - x 5⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e05b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e05b2_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 5⟫ = e05b2_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 1 (by decide) (by decide))
    · exact sign_pos (edge_pos F 2 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 3 (by decide) (by decide))
    · exact sign_pos h124
    · exact sign_neg (edge_neg F 5 (by decide) (by decide))
    · exact sign_pos h234
    · exact sign_neg h346
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hP : ∀ i, e05b2_P i ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e05b2_P := by decide
  refine svc_local F e05b2_P (x 0 - x 5) e05b2_sw e05b2_R hsw
    (hR_two F e05b2_sw e05b2_R 1 3 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e05b2_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e05b2_check
  intro s hs
  simp only [e05b2_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e05b2_dep0 F hS0


/-! ### Cell `e03a`: line F023xF035 = edge view (x 0 - x 3), facings ++00----- (rep K1aN_2, census cover 20) -/

def e03a_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 5]
def e03a_s0 : Fin 5 → SignType := ![1, 1, -1, 1, -1]  -- circuit ++-+0-0

theorem e03a_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : PlaneSide x 2 3 5 0 1 < 0) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e03a_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e03a_s0 i := by
  have hP : Function.Injective (fun i => x (e03a_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e03a_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e03a_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e03a_P mu hsum hdep 1 (i := 2) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    )
  have r2 := facet_pair F e03a_P mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r3 := facet_pair F e03a_P mu hsum hdep 3 (i := 1) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_opp (plane_rel0 (fun i => x (e03a_P i)) mu hsum hdep (x 3 - x 2) (x 5 - x 2) (x 2) (i := 0) (j := 1) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 2 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 3 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 2) (x 5 - x 2) (x 5 - x 2) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v0 v1 v2 v3 v5 : SignType, v3 = -v5 → v2 = -v3 → v1 = -v5 → v1 = -v2 → v0 = v1 →
     v0 = e03a_s0 0 * e03a_s0 4 * v5 ∧ v1 = e03a_s0 1 * e03a_s0 4 * v5 ∧ v2 = e03a_s0 2 * e03a_s0 4 * v5 ∧ v3 = e03a_s0 3 * e03a_s0 4 * v5 ∧ v5 = e03a_s0 4 * e03a_s0 4 * v5 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e03a_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e03a_sw : Fin 9 → SignType := ![1, 1, 0, 0, -1, -1, -1, 1, -1]
def e03a_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 2, 1, 4], U := {0, 1}, Dn := {2, 3, 4, 5},
     sd := ![0, 0, -1, -1, 0, 0, 0, 0, 0] },
   { k := 4, c := ![1, 2, 3, 4], U := {0, 1, 2, 3}, Dn := {4, 5, 6, 8},
     sd := ![0, 0, 1, 1, 0, 0, 0, 0, 0] }]
def e03a_D : List (Fin 5 → SignType) := [e03a_s0]

theorem e03a_check : SVC.check s0x_S29 e03a_P e03a_sw [] e03a_D e03a_R = true := by
  decide +kernel

/-- **Single view `x 0 - x 3`** (line F023xF035). -/
theorem lexAny_e03a {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h124 : ⟪F.N 4, x 0 - x 3⟫ < 0)
    (h1456 : ⟪F.N 5, x 0 - x 3⟫ < 0)
    (hS0 : PlaneSide x 2 3 5 0 1 < 0)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 3⟫ ≠ ⟪x j, x 0 - x 3⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e03a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e03a_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 0 - x 3⟫ = e03a_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_pos (edge_pos F 1 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_eq_zero_iff.mpr (edge_zero F 3 (by decide) (by decide))
    · exact sign_neg h124
    · exact sign_neg h1456
    · exact sign_neg (edge_neg F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 8 (by decide) (by decide))
  have hP : ∀ i, e03a_P i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e03a_P := by decide
  refine svc_local F e03a_P (x 0 - x 3) e03a_sw e03a_R hsw
    (hR_two F e03a_sw e03a_R 2 3 0 5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e03a_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e03a_check
  intro s hs
  simp only [e03a_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e03a_dep0 F hS0


/-! ### Cell `e23b`: line F023xF234 = edge view (x 2 - x 3), facings +-0-+-0-- (rep K1b_2, census cover 31) -/

def e23b_P : Fin 5 → Fin 7 := ![0, 1, 2, 3, 4]
def e23b_s0 : Fin 5 → SignType := ![1, -1, -1, -1, 1]  -- circuit +---+00

theorem e23b_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (hS0 : 0 < PlaneSide x 1 3 4 0 2) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (e23b_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = e23b_s0 i := by
  have hP : Function.Injective (fun i => x (e23b_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep e23b_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have r0 := facet_pair F e23b_P mu hsum hdep 0 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · left; decide
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r1 := facet_pair F e23b_P mu hsum hdep 2 (i := 1) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F e23b_P mu hsum hdep 4 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r3 := facet_pair F e23b_P mu hsum hdep 6 (i := 0) (j := 1) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · exact absurd rfl h2
    · left; decide
    · left; decide
    · left; decide
    )
  have r4 := (sign_rel_same (plane_rel0 (fun i => x (e23b_P i)) mu hsum hdep (x 3 - x 1) (x 4 - x 1) (x 1) (i := 0) (j := 2) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 1 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · exact absurd rfl h2
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 3 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    · left; show det3 (x 3 - x 1) (x 4 - x 1) (x 4 - x 1) = 0
      simp only [det3_expand, PiLp.sub_apply]; ring
    )) hS0)
  have key : ∀ v0 v1 v2 v3 v4 : SignType, v3 = -v4 → v1 = -v4 → v0 = -v3 → v0 = -v1 → v0 = -v2 →
     v0 = e23b_s0 0 * e23b_s0 4 * v4 ∧ v1 = e23b_s0 1 * e23b_s0 4 * v4 ∧ v2 = e23b_s0 2 * e23b_s0 4 * v4 ∧ v3 = e23b_s0 3 * e23b_s0 4 * v4 ∧ v4 = e23b_s0 4 * e23b_s0 4 * v4 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne e23b_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def e23b_sw : Fin 9 → SignType := ![1, -1, 0, -1, 1, -1, 0, -1, 1]
def e23b_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![0, 1, 4, 2], U := {0, 4}, Dn := {1, 2, 5, 6},
     sd := ![0, 0, -1, 0, 0, 0, -1, 0, 0] },
   { k := 4, c := ![0, 1, 4, 3], U := {0, 2, 4, 6}, Dn := {1, 3, 5, 7},
     sd := ![0, 0, 1, 0, 0, 0, 1, 0, 0] }]
def e23b_D : List (Fin 5 → SignType) := [e23b_s0]

theorem e23b_check : SVC.check s0x_S29 e23b_P e23b_sw [] e23b_D e23b_R = true := by
  decide +kernel

/-- **Single view `x 2 - x 3`** (line F023xF234). -/
theorem lexAny_e23b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (h015 : ⟪F.N 1, x 2 - x 3⟫ < 0)
    (h1456 : ⟪F.N 5, x 2 - x 3⟫ < 0)
    (hS0 : 0 < PlaneSide x 1 3 4 0 2)
    (hgen : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 3⟫ ≠ ⟪x j, x 2 - x 3⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ e23b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ e23b_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, x 2 - x 3⟫ = e23b_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos (edge_pos F 0 (by decide) (by decide))
    · exact sign_neg h015
    · exact sign_eq_zero_iff.mpr (edge_zero F 2 (by decide) (by decide))
    · exact sign_neg (edge_neg F 3 (by decide) (by decide))
    · exact sign_pos (edge_pos F 4 (by decide) (by decide))
    · exact sign_neg h1456
    · exact sign_eq_zero_iff.mpr (edge_zero F 6 (by decide) (by decide))
    · exact sign_neg (edge_neg F 7 (by decide) (by decide))
  have hP : ∀ i, e23b_P i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective e23b_P := by decide
  refine svc_local F e23b_P (x 2 - x 3) e23b_sw e23b_R hsw
    (hR_two F e23b_sw e23b_R 2 6 2 4 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) e23b_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) e23b_check
  intro s hs
  simp only [e23b_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact e23b_dep0 F hS0


/-! ### Cell `l1456x234`: line F1456xF234 (non-edge view), facings -----00++ (rep K1aN_104, census cover 49) -/

def l1456x234_P : Fin 5 → Fin 7 := ![1, 3, 4, 5, 6]
def l1456x234_s0 : Fin 5 → SignType := ![1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def l1456x234_s1 : Fin 5 → SignType := ![1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def l1456x234_s2 : Fin 5 → SignType := ![1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem l1456x234_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (l1456x234_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = l1456x234_s0 i := by
  have hP : Function.Injective (fun i => x (l1456x234_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep l1456x234_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z3 : mu 1 = 0 := facet_zero F l1456x234_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z3, sign_zero]
  have r1 := facet_pair F l1456x234_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F l1456x234_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F l1456x234_P mu hsum hdep 7 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F l1456x234_P mu hsum hdep 8 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v3 v4 v5 v6 : SignType, v3 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = l1456x234_s0 0 * l1456x234_s0 4 * v6 ∧ v3 = l1456x234_s0 1 * l1456x234_s0 4 * v6 ∧ v4 = l1456x234_s0 2 * l1456x234_s0 4 * v6 ∧ v5 = l1456x234_s0 3 * l1456x234_s0 4 * v6 ∧ v6 = l1456x234_s0 4 * l1456x234_s0 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne l1456x234_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem l1456x234_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (l1456x234_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = l1456x234_s1 i := by
  have hP : Function.Injective (fun i => x (l1456x234_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep l1456x234_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z3 : mu 1 = 0 := facet_zero F l1456x234_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z3, sign_zero]
  have r1 := facet_pair F l1456x234_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F l1456x234_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F l1456x234_P mu hsum hdep 7 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F l1456x234_P mu hsum hdep 8 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v3 v4 v5 v6 : SignType, v3 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = l1456x234_s1 0 * l1456x234_s1 4 * v6 ∧ v3 = l1456x234_s1 1 * l1456x234_s1 4 * v6 ∧ v4 = l1456x234_s1 2 * l1456x234_s1 4 * v6 ∧ v5 = l1456x234_s1 3 * l1456x234_s1 4 * v6 ∧ v6 = l1456x234_s1 4 * l1456x234_s1 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne l1456x234_s1 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem l1456x234_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (l1456x234_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = l1456x234_s2 i := by
  have hP : Function.Injective (fun i => x (l1456x234_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep l1456x234_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z3 : mu 1 = 0 := facet_zero F l1456x234_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z3, sign_zero]
  have r1 := facet_pair F l1456x234_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F l1456x234_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F l1456x234_P mu hsum hdep 7 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F l1456x234_P mu hsum hdep 8 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v3 v4 v5 v6 : SignType, v3 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = l1456x234_s2 0 * l1456x234_s2 4 * v6 ∧ v3 = l1456x234_s2 1 * l1456x234_s2 4 * v6 ∧ v4 = l1456x234_s2 2 * l1456x234_s2 4 * v6 ∧ v5 = l1456x234_s2 3 * l1456x234_s2 4 * v6 ∧ v6 = l1456x234_s2 4 * l1456x234_s2 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne l1456x234_s2 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def l1456x234_sw : Fin 9 → SignType := ![1, -1, 1, -1, -1, 0, 0, 1, 1]
def l1456x234_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![1, 2, 4, 3], U := {7, 8}, Dn := {3, 5, 6},
     sd := ![0, 0, 0, 0, 0, -1, -1, 0, 0] },
   { k := 4, c := ![0, 2, 1, 3], U := {5, 7, 8}, Dn := {1, 3, 4, 6},
     sd := ![0, 0, 0, 0, 0, 1, -1, 0, 0] }]
def l1456x234_D : List (Fin 5 → SignType) := [l1456x234_s0, l1456x234_s1, l1456x234_s2]

theorem l1456x234_check : SVC.check s0x_S29 l1456x234_P l1456x234_sw [] l1456x234_D l1456x234_R = true := by
  decide +kernel

/-- **Single view `w`** (line F1456xF234). -/
theorem lexAny_l1456x234 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w : ℝ³) (h1456 : ⟪F.N 5, w⟫ = 0) (h234 : ⟪F.N 6, w⟫ = 0)
    (h015 : ⟪F.N 1, w⟫ < 0)
    (h035 : ⟪F.N 3, w⟫ < 0)
    (h124 : ⟪F.N 4, w⟫ < 0)
    (h346 : 0 < ⟪F.N 7, w⟫)
    (h356 : 0 < ⟪F.N 8, w⟫)
    (hgen : ∀ i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, w⟫ ≠ ⟪x j, w⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ l1456x234_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({1, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ l1456x234_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, w⟫ = l1456x234_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_neg h015
    · exact sign_neg h035
    · exact sign_neg h124
    · exact sign_eq_zero_iff.mpr h1456
    · exact sign_eq_zero_iff.mpr h234
    · exact sign_pos h346
    · exact sign_pos h356
  have hP : ∀ i, l1456x234_P i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective l1456x234_P := by decide
  refine svc_local F l1456x234_P w l1456x234_sw l1456x234_R hsw
    (hR_two F l1456x234_sw l1456x234_R 5 6 4 2 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) l1456x234_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) l1456x234_check
  intro s hs
  simp only [l1456x234_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact l1456x234_dep0 F
  · exact l1456x234_dep1 F
  · exact l1456x234_dep2 F


/-! ### Cell `l035x1456`: line F035xF1456 (non-edge view), facings ---0-0-++ (rep K1aN_58, census cover 48) -/

def l035x1456_P : Fin 5 → Fin 7 := ![1, 3, 4, 5, 6]
def l035x1456_s0 : Fin 5 → SignType := ![1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def l035x1456_s1 : Fin 5 → SignType := ![1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)
def l035x1456_s2 : Fin 5 → SignType := ![1, 0, -1, -1, 1]  -- circuit 0+00--+ (facet-forced)

theorem l035x1456_dep0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (l035x1456_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = l035x1456_s0 i := by
  have hP : Function.Injective (fun i => x (l035x1456_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep l035x1456_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z3 : mu 1 = 0 := facet_zero F l035x1456_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z3, sign_zero]
  have r1 := facet_pair F l035x1456_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F l035x1456_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F l035x1456_P mu hsum hdep 7 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F l035x1456_P mu hsum hdep 8 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v3 v4 v5 v6 : SignType, v3 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = l035x1456_s0 0 * l035x1456_s0 4 * v6 ∧ v3 = l035x1456_s0 1 * l035x1456_s0 4 * v6 ∧ v4 = l035x1456_s0 2 * l035x1456_s0 4 * v6 ∧ v5 = l035x1456_s0 3 * l035x1456_s0 4 * v6 ∧ v6 = l035x1456_s0 4 * l035x1456_s0 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne l035x1456_s0 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem l035x1456_dep1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (l035x1456_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = l035x1456_s1 i := by
  have hP : Function.Injective (fun i => x (l035x1456_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep l035x1456_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z3 : mu 1 = 0 := facet_zero F l035x1456_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z3, sign_zero]
  have r1 := facet_pair F l035x1456_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F l035x1456_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F l035x1456_P mu hsum hdep 7 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F l035x1456_P mu hsum hdep 8 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v3 v4 v5 v6 : SignType, v3 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = l035x1456_s1 0 * l035x1456_s1 4 * v6 ∧ v3 = l035x1456_s1 1 * l035x1456_s1 4 * v6 ∧ v4 = l035x1456_s1 2 * l035x1456_s1 4 * v6 ∧ v5 = l035x1456_s1 3 * l035x1456_s1 4 * v6 ∧ v6 = l035x1456_s1 4 * l035x1456_s1 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne l035x1456_s1 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

theorem l035x1456_dep2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) :
    ∃ mu : Fin 5 → ℝ, ∑ i, mu i = 0 ∧ ∑ i, mu i • x (l035x1456_P i) = 0 ∧
      ∀ i, SignType.sign (mu i) = l035x1456_s2 i := by
  have hP : Function.Injective (fun i => x (l035x1456_P i)) := (inj29 F).comp (by decide)
  obtain ⟨mu, hz, hsum, hdep, hne⟩ := exists_dep l035x1456_P hP ({0, 1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have z3 : mu 1 = 0 := facet_zero F l035x1456_P mu hsum hdep 5 (i := 1) (by decide) (by
    intro l h1
    fin_cases l
    · left; decide
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · left; decide
    )
  have r0 : SignType.sign (mu 1) = 0 := by rw [z3, sign_zero]
  have r1 := facet_pair F l035x1456_P mu hsum hdep 1 (i := 2) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    )
  have r2 := facet_pair F l035x1456_P mu hsum hdep 4 (i := 3) (j := 4) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · left; decide
    · right; exact z3
    · left; decide
    · exact absurd rfl h1
    · exact absurd rfl h2
    )
  have r3 := facet_pair F l035x1456_P mu hsum hdep 7 (i := 0) (j := 3) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · left; decide
    · exact absurd rfl h2
    · left; decide
    )
  have r4 := facet_pair F l035x1456_P mu hsum hdep 8 (i := 0) (j := 2) (by decide) (by decide) (by decide)
    (by
    intro l h1 h2
    fin_cases l
    · exact absurd rfl h1
    · left; decide
    · exact absurd rfl h2
    · left; decide
    · left; decide
    )
  have key : ∀ v1 v3 v4 v5 v6 : SignType, v3 = 0 → v4 = -v6 → v5 = -v6 → v1 = -v5 → v1 = -v4 →
     v1 = l035x1456_s2 0 * l035x1456_s2 4 * v6 ∧ v3 = l035x1456_s2 1 * l035x1456_s2 4 * v6 ∧ v4 = l035x1456_s2 2 * l035x1456_s2 4 * v6 ∧ v5 = l035x1456_s2 3 * l035x1456_s2 4 * v6 ∧ v6 = l035x1456_s2 4 * l035x1456_s2 4 * v6 := by decide
  have hk := key (SignType.sign (mu 0)) (SignType.sign (mu 1)) (SignType.sign (mu 2)) (SignType.sign (mu 3)) (SignType.sign (mu 4)) r0 r1 r2 r3 r4
  refine dep_normalize _ mu hsum hdep hne l035x1456_s2 4 (by decide) (fun i => ?_)
  fin_cases i
  · exact hk.1
  · exact hk.2.1
  · exact hk.2.2.1
  · exact hk.2.2.2.1
  · exact hk.2.2.2.2

def l035x1456_sw : Fin 9 → SignType := ![1, -1, 1, 0, -1, 0, -1, 1, 1]
def l035x1456_R : List (SVC.Rim 9 5) :=
  [{ k := 4, c := ![1, 2, 4, 3], U := {7, 8}, Dn := {3, 5, 6},
     sd := ![0, 0, 0, -1, 0, -1, 0, 0, 0] },
   { k := 4, c := ![0, 2, 1, 3], U := {5, 7, 8}, Dn := {1, 3, 4, 6},
     sd := ![0, 0, 0, -1, 0, 1, 0, 0, 0] }]
def l035x1456_D : List (Fin 5 → SignType) := [l035x1456_s0, l035x1456_s1, l035x1456_s2]

theorem l035x1456_check : SVC.check s0x_S29 l035x1456_P l035x1456_sw [] l035x1456_D l035x1456_R = true := by
  decide +kernel

/-- **Single view `w`** (line F035xF1456). -/
theorem lexAny_l035x1456 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x)
    (w : ℝ³) (h035 : ⟪F.N 3, w⟫ = 0) (h1456 : ⟪F.N 5, w⟫ = 0)
    (h015 : ⟪F.N 1, w⟫ < 0)
    (h124 : ⟪F.N 4, w⟫ < 0)
    (h234 : ⟪F.N 6, w⟫ < 0)
    (h346 : 0 < ⟪F.N 7, w⟫)
    (h356 : 0 < ⟪F.N 8, w⟫)
    (hgen : ∀ i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, w⟫ ≠ ⟪x j, w⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ l035x1456_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      t ∈ ({1, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ l035x1456_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn →
      SignType.sign ⟪F.N t, w⟫ = l035x1456_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_neg h015
    · exact sign_eq_zero_iff.mpr h035
    · exact sign_neg h124
    · exact sign_eq_zero_iff.mpr h1456
    · exact sign_neg h234
    · exact sign_pos h346
    · exact sign_pos h356
  have hP : ∀ i, l035x1456_P i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)) := by decide
  have hPi : Function.Injective l035x1456_P := by decide
  refine svc_local F l035x1456_P w l035x1456_sw l035x1456_R hsw
    (hR_two F l035x1456_sw l035x1456_R 3 5 5 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    [] (by simp) l035x1456_D ?_ (fun i j hij => hgen _ (hP i) _ (hP j) (hPi.ne hij)) l035x1456_check
  intro s hs
  simp only [l035x1456_D, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact l035x1456_dep0 F
  · exact l035x1456_dep1 F
  · exact l035x1456_dep2 F


/-! ### SINGLE29 cells in the normal form `NF29` -/

/-- **K1b, view `x 0 - x 5`** (cell `e05b`). -/
theorem lexAny29_K1b_e05 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : ⟪(s0x_fac29 N.facets).N 4, x 0 - x 5⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 6, x 0 - x 5⟫ < 0)
    (h4 : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 5⟫ ≠ ⟪x j, x 0 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e05b _ h2 h3 (ps23501_pos N h1) h4

/-- **K1b, view `x 1 - x 2`** (cell `e12b`). -/
theorem lexAny29_K1b_e12 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 2⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 7, x 1 - x 2⟫)
    (h4 : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e12b _ h2 h3 (ps13402_pos N h1) h4

/-- **K1a, view `x 0 - x 2`** (cell `e02a`). -/
theorem lexAny29_K1a_e02 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 5, x 0 - x 2⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 7, x 0 - x 2⟫)
    (h4 : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e02a _ h2 h3 (ps13402_neg N h1) h4

/-- **K1a, view `x 1 - x 5`** (cell `e15a`). -/
theorem lexAny29_K1a_e15 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.V < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 6, x 1 - x 5⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ < 0)
    (h5 : 0 < PlaneSide x 2 5 6 0 1)
    (h6 : ∀ i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e15a _ h2 h3 h4 (ps24501_pos N h1) h5 h6

/-- **K1a, view `x 1 - x 5`** (cell `e15a2`). -/
theorem lexAny29_K1a_e15_2 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫)
    (h4 : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e15a2 _ h2 h3 (ps13405_pos N h1) h4

/-- **K1b, view `x 0 - x 2`** (cell `e02b`). -/
theorem lexAny29_K1b_e02 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : ⟪(s0x_fac29 N.facets).N 5, x 0 - x 2⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 8, x 0 - x 2⟫ < 0)
    (h4 : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e02b _ h2 h3 (ps23501_pos N h1) h4

/-- **K1b, view `x 1 - x 4`** (cell `e14b`). -/
theorem lexAny29_K1b_e14 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.V)
    (h2 : ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 3, x 1 - x 4⟫ < 0)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ < 0)
    (h5 : PlaneSide x 2 4 6 0 1 < 0)
    (h6 : ∀ i ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e14b _ h2 h3 h4 (ps24501_neg N h1) h5 h6

/-- **K1b, view `x 1 - x 4`** (cell `e14b2`). -/
theorem lexAny29_K1b_e14_2 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫)
    (h4 : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e14b2 _ h2 h3 (ps23514_neg N h1) h4

/-- **K1a, view `x 1 - x 5`** (cell `e15a3`). -/
theorem lexAny29_K1a_e15_3 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.b0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 5⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 6, x 1 - x 5⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 7, x 1 - x 5⟫ < 0)
    (h5 : ∀ i ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 5⟫ ≠ ⟪x j, x 1 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e15a3 _ h2 h3 h4 (ps13405_pos N h1) h5

/-- **K1b, view `x 1 - x 4`** (cell `e14b3`). -/
theorem lexAny29_K1b_e14_3 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : 0 < N.a2)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 2, x 1 - x 4⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 3, x 1 - x 4⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 1 - x 4⟫ < 0)
    (h5 : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 1 - x 4⟫ ≠ ⟪x j, x 1 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e14b3 _ h2 h3 h4 (ps23514_neg N h1) h5

/-- **K1a, view `x 2 - x 4`** (cell `e24a2`). -/
theorem lexAny29_K1a_e24_2 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.a2 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 1, x 2 - x 4⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 3, x 2 - x 4⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 8, x 2 - x 4⟫ < 0)
    (h5 : ∀ i ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)), ∀ j ∈ ({1, 2, 3, 4, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 4⟫ ≠ ⟪x j, x 2 - x 4⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e24a2 _ h2 h3 h4 (ps23514_pos N h1) h5

/-- **K1b, view `x 0 - x 5`** (cell `e05b2`). -/
theorem lexAny29_K1b_e05_2 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : 0 < ⟪(s0x_fac29 N.facets).N 4, x 0 - x 5⟫)
    (h3 : 0 < ⟪(s0x_fac29 N.facets).N 6, x 0 - x 5⟫)
    (h4 : ⟪(s0x_fac29 N.facets).N 7, x 0 - x 5⟫ < 0)
    (h5 : ∀ i ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 3, 4, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 5⟫ ≠ ⟪x j, x 0 - x 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e05b2 _ h2 h3 h4 (ps13405_neg N h1) h5

/-- **K1a, view `x 0 - x 3`** (cell `e03a`). -/
theorem lexAny29_K1a_e03 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.a2 < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 4, x 0 - x 3⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 5, x 0 - x 3⟫ < 0)
    (h4 : ∀ i ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 5} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 0 - x 3⟫ ≠ ⟪x j, x 0 - x 3⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e03a _ h2 h3 (ps23501_neg N h1) h4

/-- **K1b, view `x 2 - x 3`** (cell `e23b`). -/
theorem lexAny29_K1b_e23 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : N.b0 < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 1, x 2 - x 3⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 5, x 2 - x 3⟫ < 0)
    (h4 : ∀ i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)),
      i ≠ j → ⟪x i, x 2 - x 3⟫ ≠ ⟪x j, x 2 - x 3⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_e23b _ h2 h3 (ps13402_pos N h1) h4

/-- **NF29, view `cross N1456 N234`** (cell `l1456x234`). -/
theorem lexAny29_l1456x234 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : ⟪(s0x_fac29 N.facets).N 1, lv29 N 5 6⟫ < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 3, lv29 N 5 6⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 4, lv29 N 5 6⟫ < 0)
    (h4 : 0 < ⟪(s0x_fac29 N.facets).N 7, lv29 N 5 6⟫)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 8, lv29 N 5 6⟫)
    (h6 : ∀ i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, lv29 N 5 6⟫ ≠ ⟪x j, lv29 N 5 6⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_l1456x234 _ _ (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h1 h2 h3 h4 h5 h6

/-- **NF29, view `cross N035 N1456`** (cell `l035x1456`). -/
theorem lexAny29_l035x1456 {x : Fin 7 → ℝ³} (N : NF29 x)
    (h1 : ⟪(s0x_fac29 N.facets).N 1, lv29 N 3 5⟫ < 0)
    (h2 : ⟪(s0x_fac29 N.facets).N 4, lv29 N 3 5⟫ < 0)
    (h3 : ⟪(s0x_fac29 N.facets).N 6, lv29 N 3 5⟫ < 0)
    (h4 : 0 < ⟪(s0x_fac29 N.facets).N 7, lv29 N 3 5⟫)
    (h5 : 0 < ⟪(s0x_fac29 N.facets).N 8, lv29 N 3 5⟫)
    (h6 : ∀ i ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({1, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j → ⟪x i, lv29 N 3 5⟫ ≠ ⟪x j, lv29 N 3 5⟫) :
    Minimality.H29.LexAny29 (s0x_fac29 N.facets) :=
  lexAny_l035x1456 _ _ (by rw [real_inner_comm]; exact Minimality.inner_cross_left _ _) (by rw [real_inner_comm]; exact Minimality.inner_cross_right _ _) h1 h2 h3 h4 h5 h6

end Minimality.PL29
