module

public import Minimality.Type24EPQuad

/-!
# A strict 4-rim with a level edge is an Edge-Plane view (up to perturbation)

Job L4LEV (Carbon A76 Theorem 1.1, level-edge case of the `k = 4` Empty-Arc Theorem).  A strict quadrilateral rim
`lab : ZMod 4 → Fin n` of a view `w₀` with `⟪E_a, w₀⟫ = 0` (rim edge `a` level) gives `Gen.EdgePlaneAny x`.

Proof.  Write `E_a`, `E_{a+1}` for consecutive edges; they span `w₀^⊥`.  Choose `v` with `ε⟪E_a, v⟫ > 0`,
`ε⟪E_{a+1}, v⟫ > 0`, `ε = ±1` the sign of `⟪E_{a+1}, w₀⟫` (`ε = 1` if it is `≥ 0`), generic with respect to finitely
many planes (`exists_avoid_kernels`).  For `w = w₀ + s v`, small `s > 0`, the consecutive depth steps
`⟪E_a, w⟫ = s⟪E_a, v⟫` and `⟪E_{a+1}, w⟫` have the same sign, so the 4-cycle of depths is not alternating
(`pat_exists`), and `sr4_exists` gives `SplitRows`; the generic planes make all depths distinct, the determinants
`T_r` nonzero, `hnd` true, and (hypothesis `hdiag`) every non-rim point lies strictly inside one of the four
triangles of rim vertices.  Then `Split.EV.epRows_of_splitRows`.

Extra hypotheses (both unavoidable): `hnp` (no two opposite rim edges parallel; with parallel opposite edges the
heights over the edge tie and `SplitRows` of this shape does not exist) and `hdiag` (no non-rim point lies on both
diagonal lines of the rim; otherwise the statement is false, see `edgePlaneAny_of_strictRim4_level`).
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.Rim4

variable {n : ℕ}

/-- The rim edge `a → a+1`. -/
noncomputable def ev (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (a : ZMod 4) : ℝ³ :=
  x (lab (a + 1)) - x (lab a)

/-- The component of `x (lab c) - x (lab a)` orthogonal to the edge `ev a`. -/
noncomputable def rv (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (a c : ZMod 4) : ℝ³ :=
  (x (lab c) - x (lab a)) -
    (⟪x (lab c) - x (lab a), ev x lab a⟫ / ⟪ev x lab a, ev x lab a⟫) • ev x lab a

theorem hnd_of {A C E w : ℝ³} (hE : E ≠ 0) (hEw : ⟪E, w⟫ ≠ 0)
    (h : ⟪(C - A) - (⟪C - A, E⟫ / ⟪E, E⟫) • E, w⟫ ≠ 0) :
    ⟪A + (⟪C - A, w⟫ / ⟪E, w⟫) • E - C, E⟫ ≠ 0 := by
  have hdd : 0 < ⟪E, E⟫ := real_inner_self_pos.2 hE
  intro h0
  apply h
  have e : ⟪A + (⟪C - A, w⟫ / ⟪E, w⟫) • E - C, E⟫ =
      (⟪C - A, w⟫ / ⟪E, w⟫) * ⟪E, E⟫ - ⟪C - A, E⟫ := by
    have : A + (⟪C - A, w⟫ / ⟪E, w⟫) • E - C = (⟪C - A, w⟫ / ⟪E, w⟫) • E - (C - A) := by abel
    rw [this, inner_sub_left, real_inner_smul_left]
  rw [e] at h0
  have ht : (⟪C - A, w⟫ / ⟪E, w⟫) * ⟪E, w⟫ = ⟪C - A, w⟫ := div_mul_cancel₀ _ hEw
  have h1 : ⟪C - A, E⟫ / ⟪E, E⟫ = ⟪C - A, w⟫ / ⟪E, w⟫ := by
    rw [div_eq_iff hdd.ne']; linarith
  rw [inner_sub_left, real_inner_smul_left, h1]
  linarith

theorem z4facts : (∀ i : ZMod 4, i + 1 + 1 = i + 2) ∧ (∀ i : ZMod 4, i + 2 + 1 = i + 3) ∧
    (∀ i : ZMod 4, i + 3 + 1 = i) ∧ (∀ i : ZMod 4, i + 2 ≠ i) ∧ (∀ i : ZMod 4, i + 2 ≠ i + 1) ∧
    (∀ i : ZMod 4, i + 3 ≠ i) ∧ (∀ i : ZMod 4, i + 3 ≠ i + 2) ∧ (∀ i : ZMod 4, i + 1 ≠ i) ∧
    (∀ i : ZMod 4, i + 3 ≠ i + 1) ∧ (∀ i : ZMod 4, i + 2 ≠ i + 3) := by
  decide

/-- A non-rim point off the diagonal line `X_i X_{i+2}` (at the view `w`) lies strictly inside one of the
triangles `X_i X_{i+1} X_{i+2}`, `X_i X_{i+2} X_{i+3}`. -/
theorem hidden_of_diag (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (hinj : Function.Injective lab) (w : ℝ³)
    (hR : StrictRimN x w lab) (m : Fin n) (hm : ∀ i, m ≠ lab i) (i : ZMod 4)
    (hf : det3 (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) w ≠ 0) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < det3 (q - p) (r - p) w ∧ 0 < det3 (q - p) (x m - p) w ∧
      0 < det3 (r - q) (x m - q) w ∧ 0 < det3 (p - r) (x m - r) w := by
  obtain ⟨f1, f2, f3, g1, g2, g3, g4, g5, g6, g7⟩ := z4facts
  have tAB := hR m i (hm i) (hm (i + 1))
  have tBC := hR m (i + 1) (hm (i + 1)) (by rw [f1 i]; exact hm _)
  rw [f1 i] at tBC
  have tCD := hR m (i + 2) (hm _) (by rw [f2 i]; exact hm _)
  rw [f2 i] at tCD
  have tDA := hR m (i + 3) (hm _) (by rw [f3 i]; exact hm _)
  rw [f3 i] at tDA
  have mem : ∀ j, x (lab j) ∈ univ.image x := fun j => mem_image_of_mem _ (mem_univ _)
  rcases lt_or_gt_of_ne hf with hneg | hpos
  · have t3 := hR (lab (i + 2)) i (fun h => g1 i (hinj h)) (fun h => g2 i (hinj h))
    refine ⟨x (lab i), mem i, x (lab (i + 1)), mem _, x (lab (i + 2)), mem _, t3, tAB, tBC, ?_⟩
    rw [det3_flip]
    linarith
  · have t3 := hR (lab (i + 2)) (i + 3) (fun h => g4 i (hinj h).symm) (by
      rw [f3 i]; exact fun h => g1 i (hinj h))
    rw [f3 i] at t3
    refine ⟨x (lab i), mem i, x (lab (i + 2)), mem _, x (lab (i + 3)), mem _, ?_, hpos, tCD, tDA⟩
    have e : det3 (x (lab (i + 2)) - x (lab i)) (x (lab (i + 3)) - x (lab i)) w =
        det3 (x (lab i) - x (lab (i + 3))) (x (lab (i + 2)) - x (lab (i + 3))) w := by
      simp only [det3, PiLp.sub_apply]; ring
    rw [e]; exact t3

/-- **Generic core.**  A strict quadrilateral rim at a view `w` where all depths are distinct, the `T`-determinants
and `rv`-planes are avoided, every non-rim point is off one diagonal line, and the depth cycle is not alternating. -/
theorem edgePlaneAny_core4 (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (hinj : Function.Injective lab)
    (w : ℝ³) (hR : StrictRimN x w lab)
    (hT : ∀ r : ZMod 4, det3 (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) w ≠ 0)
    (hz : ∀ i j : ZMod 4, i ≠ j → ⟪x (lab i), w⟫ ≠ ⟪x (lab j), w⟫)
    (hre : ∀ a c : ZMod 4, c ≠ a → c ≠ a + 1 → ⟪rv x lab a c, w⟫ ≠ 0)
    (hh : ∀ m, (∀ i, m ≠ lab i) → ∃ i : ZMod 4, det3 (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) w ≠ 0)
    (hn1 : ¬ (⟪x (lab 0), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 0), w⟫ < ⟪x (lab 3), w⟫ ∧
      ⟪x (lab 2), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 2), w⟫ < ⟪x (lab 3), w⟫))
    (hn2 : ¬ (⟪x (lab 1), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 1), w⟫ < ⟪x (lab 2), w⟫ ∧
      ⟪x (lab 3), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 3), w⟫ < ⟪x (lab 2), w⟫)) :
    Gen.EdgePlaneAny x := by
  obtain ⟨f1, f2, f3, g1, g2, g3, g4, g5, g6, g7⟩ := z4facts
  have hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) w :=
    fun i j h1 h2 => hR (lab j) i (fun h => h1 (hinj h)) (fun h => h2 (hinj h))
  have hpat := T24.EPQ.pat_exists (hz 0 1 (by decide)) (hz 0 2 (by decide)) (hz 0 3 (by decide))
    (hz 1 2 (by decide)) (hz 1 3 (by decide)) (hz 2 3 (by decide)) hn1 hn2
  obtain ⟨a, c, σ, hca, hca1, hS⟩ := T24.EPQ.sr4_exists (X := fun i => x (lab i)) (w := w) hcyc
    (fun r => hT r) hpat
  have hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 := by
    rw [inner_sub_left]; exact sub_ne_zero.2 (hz _ _ (g5 a).symm.symm)
  have hE : ev x lab a ≠ 0 := by
    intro h0
    have := hcyc a (a + 2) (g1 a) (g2 a)
    have h' : x (lab (a + 1)) - x (lab a) = 0 := h0
    rw [h'] at this
    simp [det3] at this
  have hnd : ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c), x (lab (a + 1)) - x (lab a)⟫ ≠ 0 :=
    hnd_of (A := x (lab a)) (C := x (lab c)) hE hD (hre a c hca hca1)
  have hcv : det3 (x (lab (c + 1)) - x (lab c)) (x (lab (c - 1)) - x (lab c)) w ≠ 0 := by
    have e1 : c - 1 ≠ c := (by decide : ∀ c : ZMod 4, c - 1 ≠ c) c
    have e2 : c - 1 ≠ c + 1 := (by decide : ∀ c : ZMod 4, c - 1 ≠ c + 1) c
    exact (hcyc c (c - 1) e1 e2).ne'
  have hhid : HiddenInTriangles x w lab := by
    intro m hm
    obtain ⟨i, hi⟩ := hh m hm
    exact hidden_of_diag x lab hinj w hR m hm i hi
  obtain ⟨s, α, μ, hrow⟩ := EV.epRows_of_splitRows (k := 4) (by norm_num)
    (fun i => x (lab i)) w a c σ hca hca1 hS hD hnd hcv
  exact ⟨4, inferInstance, lab, w, a, s, α, μ, by norm_num, hinj, hR, hhid, hD, hrow⟩

theorem ev_ne (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (w : ℝ³)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) w) (a : ZMod 4) :
    ev x lab a ≠ 0 := by
  obtain ⟨f1, f2, f3, g1, g2, g3, g4, g5, g6, g7⟩ := z4facts
  intro h0
  have := hcyc a (a + 2) (g1 a) (g2 a)
  have h' : x (lab (a + 1)) - x (lab a) = 0 := h0
  rw [h'] at this
  simp [det3] at this

theorem diag_ne (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (w : ℝ³)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) w) (a : ZMod 4) :
    x (lab (a + 2)) - x (lab a) ≠ 0 := by
  obtain ⟨f1, f2, f3, g1, g2, g3, g4, g5, g6, g7⟩ := z4facts
  intro h0
  have := hcyc a (a + 2) (g1 a) (g2 a)
  rw [h0] at this
  simp [det3] at this

theorem rv_ne (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (w : ℝ³)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) w) (a c : ZMod 4)
    (h1 : c ≠ a) (h2 : c ≠ a + 1) : rv x lab a c ≠ 0 := by
  intro h0
  have h := hcyc a c h1 h2
  have e : x (lab c) - x (lab a) =
      (⟪x (lab c) - x (lab a), ev x lab a⟫ / ⟪ev x lab a, ev x lab a⟫) • ev x lab a := by
    rw [← sub_eq_zero]; exact h0
  have e2 : x (lab (a + 1)) - x (lab a) = ev x lab a := rfl
  rw [e2, e, det3_smul2, det3_self, mul_zero] at h
  exact lt_irrefl _ h

theorem v0_inner (E0 E1 w : ℝ³) :
    ⟪E0, cross E1 w + cross w E0⟫ = det3 E0 E1 w ∧ ⟪E1, cross E1 w + cross w E0⟫ = det3 E0 E1 w := by
  constructor <;> simp only [inner3, cross_0, cross_1, cross_2, det3, PiLp.add_apply] <;> ring

/-- The level case with the level edge `0 → 1`. -/
theorem level0 (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hR : StrictRimN x w₀ lab)
    (hnp : ∀ r : ZMod 4, cross (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) ≠ 0)
    (hdiag : ∀ m, (∀ i, m ≠ lab i) → ∃ i : ZMod 4, cross (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) ≠ 0)
    (hlev : ⟪x (lab 1) - x (lab 0), w₀⟫ = 0) : Gen.EdgePlaneAny x := by
  obtain ⟨f1, f2, f3, g1, g2, g3, g4, g5, g6, g7⟩ := z4facts
  have hcyc : ∀ w : ℝ³, StrictRimN x w lab → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) w :=
    fun w hw i j h1 h2 => hw (lab j) i (fun h => h1 (hinj h)) (fun h => h2 (hinj h))
  have hD : 0 < det3 (x (lab 1) - x (lab 0)) (x (lab 2) - x (lab 1)) w₀ := by
    have := hcyc w₀ hR 0 2 (by decide) (by decide)
    have e : ((0 : ZMod 4) + 1) = 1 := by decide
    rw [e] at this
    have e2 : det3 (x (lab 1) - x (lab 0)) (x (lab 2) - x (lab 1)) w₀ =
        det3 (x (lab 1) - x (lab 0)) (x (lab 2) - x (lab 0)) w₀ := by
      simp only [det3, PiLp.sub_apply]; ring
    linarith
  -- the sign
  obtain ⟨ε, hε, hεε, hεP⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ε * ε = 1 ∧
      0 ≤ ε * ⟪x (lab 2) - x (lab 1), w₀⟫ := by
    by_cases hP : 0 ≤ ⟪x (lab 2) - x (lab 1), w₀⟫
    · exact ⟨1, Or.inl rfl, by norm_num, by simpa using hP⟩
    · exact ⟨-1, Or.inr rfl, by norm_num, by push Not at hP; linarith⟩
  set E0 : ℝ³ := x (lab 1) - x (lab 0) with hE0
  set E1 : ℝ³ := x (lab 2) - x (lab 1) with hE1
  let v0 : ℝ³ := ε • (cross E1 w₀ + cross w₀ E0)
  have hv0 : 0 < ε * ⟪E0, v0⟫ ∧ 0 < ε * ⟪E1, v0⟫ := by
    obtain ⟨i0, i1⟩ := v0_inner E0 E1 w₀
    simp only [v0, real_inner_smul_right, i0, i1]
    constructor <;> nlinarith
  let U : Set ℝ³ := {v | 0 < ε * ⟪E0, v⟫ ∧ 0 < ε * ⟪E1, v⟫}
  have hU : IsOpen U := by
    have h1 : IsOpen {v : ℝ³ | 0 < ε * ⟪E0, v⟫} := isOpen_lt continuous_const (by fun_prop)
    have h2 : IsOpen {v : ℝ³ | 0 < ε * ⟪E1, v⟫} := isOpen_lt continuous_const (by fun_prop)
    exact h1.inter h2
  -- the vectors
  let vecA : ZMod 4 × Fin 5 → ℝ³ := fun p =>
    ![cross (x (lab (2 + p.1)) - x (lab (1 + p.1))) (x (lab (0 + p.1)) - x (lab (3 + p.1))),
      ev x lab p.1, x (lab (p.1 + 2)) - x (lab p.1), rv x lab p.1 (p.1 + 2), rv x lab p.1 (p.1 + 3)] p.2
  let mS : Type _ := {m : Fin n // ∀ i, m ≠ lab i}
  let ic : mS → ZMod 4 := fun m => Classical.choose (hdiag m.1 m.2)
  let vecB : mS → ℝ³ := fun m =>
    cross (x (lab (ic m + 2)) - x (lab (ic m))) (x m.1 - x (lab (ic m)))
  let vec : (ZMod 4 × Fin 5) ⊕ mS → ℝ³ := Sum.elim vecA vecB
  have hnz : ∀ p, vec p ≠ 0 := by
    rintro (⟨r, k⟩ | m)
    · fin_cases k
      · exact hnp r
      · exact ev_ne x lab w₀ (hcyc w₀ hR) r
      · exact diag_ne x lab w₀ (hcyc w₀ hR) r
      · exact rv_ne x lab w₀ (hcyc w₀ hR) r (r + 2) (g1 r) (g2 r)
      · exact rv_ne x lab w₀ (hcyc w₀ hR) r (r + 3) (g3 r) (g6 r)
    · exact Classical.choose_spec (hdiag m.1 m.2)
  have : Finite ((ZMod 4 × Fin 5) ⊕ mS) := inferInstance
  obtain ⟨v, hvU, hv⟩ := Minimality.exists_avoid_kernels (ι := (ZMod 4 × Fin 5) ⊕ mS)
    (fun p => innerₗ ℝ³ (vec p))
    (fun p hy => by
      have h1 := LinearMap.congr_fun hy (vec p)
      simp only [innerₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at h1
      exact hnz p h1) hU ⟨v0, hv0⟩
  have hK : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ p, ⟪vec p, w₀⟫ + s * ⟪vec p, v⟫ ≠ 0 :=
    eventually_all.2 fun p => Minimality.eventually_affine_ne fun _ => by simpa using hv p
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ := (((strictRim_ev hR v).and hK).and self_mem_nhdsWithin).exists
  have hs : 0 < s := hs0
  have key : ∀ (y : ℝ³), ⟪y, w₀⟫ + s * ⟪y, v⟫ = ⟪y, w₀ + s • v⟫ := by
    intro y; rw [inner_add_right, real_inner_smul_right]
  set w := w₀ + s • v with hw
  have hw' : ∀ p, ⟪vec p, w⟫ ≠ 0 := fun p => by rw [← key]; exact hs2 p
  -- depth steps
  have hE0w : 0 < ε * ⟪E0, w⟫ := by
    have : ⟪E0, w⟫ = s * ⟪E0, v⟫ := by rw [← key, hlev]; ring
    rw [this]; nlinarith [hvU.1]
  have hE1w : 0 < ε * ⟪E1, w⟫ := by
    have : ⟪E1, w⟫ = ⟪E1, w₀⟫ + s * ⟪E1, v⟫ := by rw [← key]
    rw [this]; nlinarith [hvU.2]
  have d01 : ⟪x (lab 1), w⟫ - ⟪x (lab 0), w⟫ = ⟪E0, w⟫ := (inner_sub_left _ _ _).symm
  have d12 : ⟪x (lab 2), w⟫ - ⟪x (lab 1), w⟫ = ⟪E1, w⟫ := (inner_sub_left _ _ _).symm
  have hn1 : ¬ (⟪x (lab 0), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 0), w⟫ < ⟪x (lab 3), w⟫ ∧
      ⟪x (lab 2), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 2), w⟫ < ⟪x (lab 3), w⟫) := by
    rintro ⟨h1, -, h3, -⟩
    rcases hε with rfl | rfl <;> linarith
  have hn2 : ¬ (⟪x (lab 1), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 1), w⟫ < ⟪x (lab 2), w⟫ ∧
      ⟪x (lab 3), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 3), w⟫ < ⟪x (lab 2), w⟫) := by
    rintro ⟨h1, h2, -, -⟩
    rcases hε with rfl | rfl <;> linarith
  refine edgePlaneAny_core4 x lab hinj w hs1 ?_ ?_ ?_ ?_ hn1 hn2
  · intro r
    have := hw' (Sum.inl (r, 0))
    simp only [vec, vecA, Sum.elim_inl, Matrix.cons_val_zero] at this
    rwa [← det3_eq_inner_cross] at this
  · intro i j hij h
    have hsub : ⟪x (lab i) - x (lab j), w⟫ = 0 := by rw [inner_sub_left, h, sub_self]
    rcases T24.EPQ.zmod4_ne_cases i j hij with rfl | rfl | rfl
    · apply hw' (Sum.inl (i, 1))
      show ⟪x (lab (i + 1)) - x (lab i), w⟫ = 0
      rw [← neg_sub, inner_neg_left, hsub, neg_zero]
    · apply hw' (Sum.inl (i, 2))
      show ⟪x (lab (i + 2)) - x (lab i), w⟫ = 0
      rw [← neg_sub, inner_neg_left, hsub, neg_zero]
    · apply hw' (Sum.inl (j, 1))
      show ⟪x (lab (j + 1)) - x (lab j), w⟫ = 0
      exact hsub
  · intro a c h1 h2
    rcases (by decide : ∀ a c : ZMod 4, c ≠ a → c ≠ a + 1 → c = a + 2 ∨ c = a + 3) a c h1 h2 with
      rfl | rfl
    · exact hw' (Sum.inl (a, 3))
    · exact hw' (Sum.inl (a, 4))
  · intro m hm
    refine ⟨ic ⟨m, hm⟩, ?_⟩
    have := hw' (Sum.inr ⟨m, hm⟩)
    simp only [vec, vecB, Sum.elim_inr] at this
    rwa [← det3_eq_inner_cross] at this

/-- **L4LEV (Carbon A76 Theorem 1.1, level edge of a strict 4-rim).**  A strict quadrilateral rim `lab` of a view
`w₀` for which the rim edge `a → a+1` is level (`⟪x (lab (a+1)) - x (lab a), w₀⟫ = 0`) carries an Edge-Plane
certificate at a nearby view: `Gen.EdgePlaneAny x`.  No facets, no injectivity of `x`.

Hypotheses beyond the statement of the brief, both necessary:
* `hnp`: no two opposite rim edges are parallel (as in `T24.EPQ.edgePlaneAny_of_strictRim4`; for a parallelogram
  the two far vertices have equal height over every rim edge and the `SplitRows` shape used here does not exist);
* `hdiag`: no non-rim point lies on both diagonal lines of the rim.  Without it the statement is false: for
  `x = (0,0,0), (4,0,0), (3,3,0), (0,2,0)` and the diagonal crossing `(4/3, 4/3, 0)`, `w₀ = (0,0,1)`, `a = 0`, all
  hypotheses of the brief hold, but every strict rim of every view is the quadrilateral and the fifth point lies on
  both projected diagonals, so it is in no open triangle of `HiddenInTriangles`. -/
theorem edgePlaneAny_of_strictRim4_level (x : Fin n → ℝ³) (lab : ZMod 4 → Fin n)
    (hinj : Function.Injective lab) (w₀ : ℝ³) (hR : StrictRimN x w₀ lab)
    (hnp : ∀ r : ZMod 4,
      cross (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) ≠ 0)
    (hdiag : ∀ m, (∀ i, m ≠ lab i) →
      ∃ i : ZMod 4, cross (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) ≠ 0)
    (a : ZMod 4) (hlev : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0) : Gen.EdgePlaneAny x := by
  let lab' : ZMod 4 → Fin n := fun i => lab (i + a)
  have hinj' : Function.Injective lab' := fun i j h => add_right_cancel (hinj h)
  have hR' : StrictRimN x w₀ lab' := by
    intro m i h1 h2
    have e : i + 1 + a = i + a + 1 := by ring
    have := hR m (i + a) h1 (by simpa only [lab', e] using h2)
    simpa only [lab', e] using this
  refine level0 x lab' hinj' w₀ hR' (fun r => ?_) (fun m hm => ?_) ?_
  · simpa only [lab', add_assoc] using hnp (r + a)
  · obtain ⟨i, hi⟩ := hdiag m (fun i => by simpa [lab'] using hm (i - a))
    refine ⟨i - a, ?_⟩
    have e1 : i - a + 2 + a = i + 2 := by ring
    have e2 : i - a + a = i := by ring
    simpa only [lab', e1, e2] using hi
  · have e1 : (1 : ZMod 4) + a = a + 1 := add_comm _ _
    have e0 : (0 : ZMod 4) + a = a := zero_add _
    simpa only [lab', e1, e0] using hlev

end Minimality.Split.Rim4
