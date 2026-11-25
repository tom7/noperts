module

public import Minimality.SplitRows
public import Minimality.EdgePlane
public import Minimality.SplitLeaf
public import Minimality.GenericLeaves

/-!
# EV (Hydrogen Task EV, from Carbon A71 Theorem 1.1): a non-degenerate SplitRows view carries an Edge-Plane certificate (Carbon A71 Theorem 1.1)

Proves `epRows_of_splitRows`: under `SplitRows X w a c σ`, `hD : ⟪X (a + 1) - X a, w⟫ ≠ 0`,
`hnd : ⟪levelPoint X w a c - X c, X (a + 1) - X a⟫ ≠ 0`, and
`hcv : det3 (X (c + 1) - X c) (X (c - 1) - X c) w ≠ 0`, there exist `(s, α, μ)` satisfying
`EPRows X w a s α μ` at the same `w` and base edge `a`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.Split.EV

/-- The Edge-Plane rows of `freeAt_of_edgePlane` for base edge `a`. -/
def EPRows {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k) (s α μ : ℝ) : Prop :=
  ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
    0 < (α + μ * ⟪X j - X a, w⟫) * det3 (X (i + 1) - X i) (X (a + 1) - X a) w + s * edgePlaneSpin X w a i j

/-- **A71 Theorem 1.1.**  A non-degenerate `SplitRows` view carries an Edge-Plane certificate
at the same `w` and base edge `a`. -/
theorem epRows_of_splitRows {k : ℕ} [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³)
    (a c : ZMod k) (σ : ℝ)
    (hca : c ≠ a) (hca1 : c ≠ a + 1) (hS : SplitRows X w a c σ)
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0)
    (hnd : ⟪levelPoint X w a c - X c, X (a + 1) - X a⟫ ≠ 0)
    (hcv : det3 (X (c + 1) - X c) (X (c - 1) - X c) w ≠ 0) :
    ∃ s α μ : ℝ, EPRows X w a s α μ := by
  let _ := hca
  have hcm1_ne_c : c - 1 ≠ c := by
    intro h
    have h1 : (1 : ZMod k) = 0 := by
      have : c - (c - 1) = 0 := by rw [h, sub_self]
      simpa using this
    have hf : Fact (1 < k) := ⟨by omega⟩
    exact one_ne_zero h1
  have hcm1a : c - 1 ≠ a := fun h => hca1 (by linear_combination h)
  have hw0 : w ≠ 0 := by
    intro hw
    apply hcv
    simp [hw, det3]
  have hww : ⟪w, w⟫ ≠ 0 := ne_of_gt (real_inner_self_pos.2 hw0)
  set d := X (a + 1) - X a
  set D := ⟪d, w⟫
  set sc := ⟪X c - X a, w⟫ / D
  set q := levelPoint X w a c
  set h := q - X c
  set A := X (c + 1) - X c
  set B := X (c - 1) - X c
  have hD' : D ≠ 0 := hD
  have hhw : ⟪h, w⟫ = 0 := by
    dsimp [h, q, levelPoint]
    rw [inner_sub_left, inner_add_left, real_inner_smul_left]
    change ⟪X a, w⟫ + (⟪X c - X a, w⟫ / D) * D - ⟪X c, w⟫ = 0
    rw [div_mul_cancel₀ _ hD']
    simp only [inner3, PiLp.sub_apply]; ring
  have hspin_eq : ∀ E : ℝ³,
      det3 E (cross w (X c - X a)) w + (⟪X c - X a, w⟫ / D) * det3 E (cross d w) w =
        -⟪w, w⟫ * ⟪E, h⟫ := by
    intro E
    have e1 : det3 E (cross w (X c - X a)) w = ⟪w, w⟫ * ⟪X c - X a, E⟫ - ⟪X c - X a, w⟫ * ⟪E, w⟫ := by
      simp only [det3, inner3, cross_0, cross_1, cross_2]; ring
    have e2 : det3 E (cross d w) w = D * ⟪E, w⟫ - ⟪w, w⟫ * ⟪E, d⟫ := by
      dsimp [D]
      simp only [det3, inner3, cross_0, cross_1, cross_2]; ring
    rw [e1, e2]
    have hmul : (⟪X c - X a, w⟫ / D) * (D * ⟪E, w⟫ - ⟪w, w⟫ * ⟪E, d⟫) =
        ⟪X c - X a, w⟫ * ⟪E, w⟫ - ⟪w, w⟫ * ((⟪X c - X a, w⟫ / D) * ⟪E, d⟫) := by
      rw [mul_sub, ← mul_assoc, div_mul_cancel₀ _ hD']
      ring
    rw [hmul]
    have hEh : ⟪E, h⟫ = -⟪X c - X a, E⟫ + (⟪X c - X a, w⟫ / D) * ⟪E, d⟫ := by
      change ⟪E, X a + (⟪X c - X a, w⟫ / D) • d - X c⟫ = _
      simp only [inner_sub_left, inner_sub_right, inner_add_right, real_inner_smul_right]
      rw [real_inner_comm E (X a), real_inner_comm E (X c)]
      ring
    rw [hEh]
    ring
  set A_prev := det3 (X (c - 1 + 1) - X (c - 1)) d w
  set A_curr := det3 (X (c + 1) - X c) d w
  set S_prev := edgePlaneSpin X w a (c - 1) c
  set S_curr := edgePlaneSpin X w a c c
  have hc_prev : c - 1 + 1 = c := by ring
  have hA_prev_eq : A_prev = -det3 B d w := by
    dsimp [A_prev, B]
    rw [hc_prev]
    simp only [det3, PiLp.sub_apply]; ring
  have hA_curr_eq : A_curr = det3 A d w := rfl
  have hS_prev_eq : S_prev = ⟪w, w⟫ * ⟪B, h⟫ := by
    dsimp [S_prev, edgePlaneSpin]
    rw [hc_prev]
    have hE : det3 (X c - X (c - 1)) (cross w (X c - X a)) w +
        (⟪X c - X a, w⟫ / D) * det3 (X c - X (c - 1)) (cross d w) w =
        -⟪w, w⟫ * ⟪X c - X (c - 1), h⟫ := hspin_eq (X c - X (c - 1))
    dsimp [d, D] at hE
    rw [hE]
    simp only [B, inner3, PiLp.sub_apply]; ring
  have hS_curr_eq : S_curr = -⟪w, w⟫ * ⟪A, h⟫ := by
    dsimp [S_curr, edgePlaneSpin]
    have hE := hspin_eq A
    dsimp [A, d, D] at hE
    rw [hE]
  set Δ := A_prev * S_curr - A_curr * S_prev
  have hΔ_eq : Δ = -⟪w, w⟫ * det3 A B w * ⟪h, d⟫ := by
    have hid : det3 B d w * ⟪A, h⟫ - det3 A d w * ⟪B, h⟫ =
        det3 A B d * ⟪h, w⟫ - det3 A B w * ⟪h, d⟫ := by
      simp only [det3, inner3]; ring
    dsimp [Δ]
    rw [hA_prev_eq, hA_curr_eq, hS_prev_eq, hS_curr_eq]
    have : (-det3 B d w) * (-⟪w, w⟫ * ⟪A, h⟫) - det3 A d w * (⟪w, w⟫ * ⟪B, h⟫) =
        ⟪w, w⟫ * (det3 B d w * ⟪A, h⟫ - det3 A d w * ⟪B, h⟫) := by ring
    rw [this, hid, hhw, mul_zero, zero_sub]
    ring
  have hΔ_ne : Δ ≠ 0 := by
    rw [hΔ_eq]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hww) hcv) hnd
  set ρc := (S_curr - S_prev) / Δ
  set s := (A_prev - A_curr) / Δ
  have hrow_prev : A_prev * ρc + S_prev * s = 1 := by
    dsimp [ρc, s]
    field_simp [hΔ_ne]
    dsimp [Δ]; ring
  have hrow_curr : A_curr * ρc + S_curr * s = 1 := by
    dsimp [ρc, s]
    field_simp [hΔ_ne]
    dsimp [Δ]; ring
  let J : ZMod k × Bool → ZMod k := fun t => if t.2 then t.1 + 1 else t.1
  let p : ZMod k × Bool → ℝ := fun t =>
    if t.1 = a then 1 else if J t = c then 0 else
      σ * (⟪X (J t) - X c, w⟫ * det3 (X (t.1 + 1) - X t.1) d w)
  let q_coeff : ZMod k × Bool → ℝ := fun t =>
    if t.1 = a then 1 else ρc * det3 (X (t.1 + 1) - X t.1) d w + s * edgePlaneSpin X w a t.1 (J t)
  obtain ⟨L, hL⟩ := exists_large p q_coeff (by
    rintro ⟨i, b⟩
    by_cases hi : i = a
    · left; simp [p, hi]
    · by_cases hJc : J (i, b) = c
      · right
        refine ⟨by simp [p, hi, hJc], ?_⟩
        dsimp [q_coeff]
        simp only [hi, hJc, ite_false]
        cases b
        · simp only [J, Bool.false_eq_true, ↓reduceIte] at hJc
          rw [hJc]
          rw [show ρc * det3 (X (c + 1) - X c) d w + s * edgePlaneSpin X w a c c =
              A_curr * ρc + S_curr * s by dsimp [A_curr, S_curr]; ring, hrow_curr]
          norm_num
        · simp only [J, ↓reduceIte] at hJc
          have hic : i = c - 1 := by linear_combination hJc
          rw [hic]
          rw [show ρc * det3 (X (c - 1 + 1) - X (c - 1)) d w + s * edgePlaneSpin X w a (c - 1) c =
              A_prev * ρc + S_prev * s by dsimp [A_prev, S_prev]; ring, hrow_prev]
          norm_num
      · left
        dsimp [p]
        simp only [hi, hJc, ite_false]
        have hj : J (i, b) = i ∨ J (i, b) = i + 1 := by cases b <;> simp [J]
        exact hS i (J (i, b)) hi hj hJc)
  refine ⟨s, ρc - L * σ * ⟪X c - X a, w⟫, L * σ, ?_⟩
  intro i j hia hj
  let b : Bool := decide (j = i + 1)
  have hJb : J (i, b) = j := by
    dsimp [J, b]
    rcases hj with rfl | rfl
    · by_cases h1 : j = j + 1
      · change (if decide (j = j + 1) then j + 1 else j) = j
        rw [decide_eq_true h1]; exact h1.symm
      · change (if decide (j = j + 1) then j + 1 else j) = j
        rw [decide_eq_false h1]; rfl
    · change (if decide (i + 1 = i + 1) then i + 1 else i) = i + 1
      rw [decide_eq_true rfl]; rfl
  have hrow := hL (i, b)
  dsimp [p, q_coeff] at hrow
  simp only [hia, hJb, ite_false] at hrow
  have hinner : ⟪X j - X a, w⟫ - ⟪X c - X a, w⟫ = ⟪X j - X c, w⟫ := by
    simp only [inner3, PiLp.sub_apply]; ring
  have hlin : (ρc - L * σ * ⟪X c - X a, w⟫ + L * σ * ⟪X j - X a, w⟫) *
      det3 (X (i + 1) - X i) d w + s * edgePlaneSpin X w a i j =
      L * (σ * (⟪X j - X c, w⟫ * det3 (X (i + 1) - X i) d w)) +
        (ρc * det3 (X (i + 1) - X i) d w + s * edgePlaneSpin X w a i j) := by
    linear_combination L * σ * det3 (X (i + 1) - X i) d w * hinner
  rw [hlin]
  by_cases hjc : j = c
  · simp only [hjc, ite_true, mul_zero, zero_add] at hrow
    rw [hjc, sub_self, inner_zero_left, zero_mul, mul_zero, mul_zero, zero_add]
    exact hrow
  · simp only [hjc, ite_false] at hrow
    exact hrow

/-! ### Gen-level consequence: `SplitAny` implies `EdgePlaneAny` -/

open scoped Topology
open Filter Minimality.H21

/-- Core of `split_core`, exposing the Edge-Plane data of the perturbed view. -/
theorem split_core_ep {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : NoBetween x) (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : StrictRimN x w₀ lab) (a c : ZMod k) (σ : ℝ) (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (hrows : SplitRows (fun i => x (lab i)) w₀ a c σ) :
    Gen.EdgePlaneAny x := by
  classical
  -- the candidate normals: `hD`, `hnd`, and the fan diagonals from `lab 0`
  let d : ℝ³ := x (lab (a + 1)) - x (lab a)
  let κ : ℝ := ⟪x (lab c) - x (lab a), d⟫ / ⟪d, d⟫
  let e : ℝ³ := x (lab c) - x (lab a) - κ • d
  let cands : Finset ℝ³ := insert d (insert e ((univ : Finset (Fin n × ZMod k)).image
    fun p => cross (x (lab p.2) - x (lab 0)) (x p.1 - x (lab 0))))
  let T := cands.filter (· ≠ 0)
  obtain ⟨v, -, hv⟩ := Minimality.exists_avoid_kernels (ι := T) (fun y => innerₗ ℝ³ (y : ℝ³))
    (fun y hy => by
      have h1 := LinearMap.congr_fun hy (y : ℝ³)
      simp only [innerₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at h1
      exact (mem_filter.1 y.2).2 h1) isOpen_univ Set.univ_nonempty
  have hK : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ y : T, ⟪(y : ℝ³), w₀⟫ + s * ⟪(y : ℝ³), v⟫ ≠ 0 :=
    eventually_all.2 fun y => Minimality.eventually_affine_ne fun _ => by simpa using hv y
  obtain ⟨s, hR, hS, hN⟩ := ((strictRim_ev hrim v).and ((splitRows_ev hrows v).and hK)).exists
  set w := w₀ + s • v with hw
  have hav : ∀ y ∈ cands, y ≠ 0 → ⟪y, w⟫ ≠ 0 := by
    intro y hy hy0
    have := hN ⟨y, mem_filter.2 ⟨hy, hy0⟩⟩
    rwa [hw, inner_add_right, real_inner_smul_right]
  have h10 : (1 : ZMod k) ≠ 0 := by
    intro h
    have h' : ((1 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'; omega
  have hd0 : d ≠ 0 := sub_ne_zero.2 fun h => h10 (by
    have := hinj (hx h); linear_combination this)
  have hD : ⟪d, w⟫ ≠ 0 := hav d (mem_insert_self _ _) hd0
  -- `e ≠ 0`: the corner `c` is off the line of the edge `a`
  have hcrim := hR (lab c) a (fun h => hca (hinj h)) (fun h => hca1 (hinj h))
  have he0 : e ≠ 0 := by
    intro h0
    have : x (lab c) - x (lab a) = κ • d := by
      rw [← sub_eq_zero]; exact h0
    rw [this, det3_smul2, det3_self, mul_zero] at hcrim
    exact lt_irrefl _ hcrim
  have hew : ⟪e, w⟫ ≠ 0 := hav e (mem_insert_of_mem (mem_insert_self _ _)) he0
  have hnd : ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c), x (lab (a + 1)) - x (lab a)⟫ ≠ 0 := by
    have hdd : 0 < ⟪d, d⟫ := real_inner_self_pos.2 hd0
    have e1 : levelPoint (fun i => x (lab i)) w a c - x (lab c) =
        (⟪x (lab c) - x (lab a), w⟫ / ⟪d, w⟫) • d - (x (lab c) - x (lab a)) := by
      simp only [levelPoint, d]; abel
    rw [e1]
    change ⟪_ - _, d⟫ ≠ 0
    rw [inner_sub_left, real_inner_smul_left]
    have hew' : ⟪x (lab c) - x (lab a), w⟫ - κ * ⟪d, w⟫ ≠ 0 := by
      have : ⟪e, w⟫ = ⟪x (lab c) - x (lab a), w⟫ - κ * ⟪d, w⟫ := by
        simp only [e]; rw [inner_sub_left, real_inner_smul_left]
      rwa [this] at hew
    have hC : ⟪x (lab c) - x (lab a), d⟫ = κ * ⟪d, d⟫ := by
      simp only [κ]; field_simp
    rw [hC]
    intro h
    apply hew'
    have h2 : (⟪x (lab c) - x (lab a), w⟫ / ⟪d, w⟫ - κ) * ⟪d, d⟫ = 0 := by rw [sub_mul]; exact h
    have h3 := (mul_eq_zero.1 h2).resolve_right hdd.ne'
    rw [sub_eq_zero, div_eq_iff hD] at h3
    linarith
  have hhid : HiddenInTriangles x w lab := by
    refine hidden_of_rim hk x hx hseg w lab hinj hR fun m hm j hj hcr => ?_
    rw [det3_eq_inner_cross]
    exact hav _ (mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ (mem_univ (m, j))))) hcr
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hcrim
    simp [det3] at hcrim
  have hcv : det3 (x (lab (c + 1)) - x (lab c)) (x (lab (c - 1)) - x (lab c)) w ≠ 0 := by
    have h1 : c - 1 ≠ c := by
      intro h
      have h1 : (1 : ZMod k) = 0 := by
        have : c - (c - 1) = 0 := by rw [h, sub_self]
        simpa using this
      exact h10 h1
    have h2 : c - 1 ≠ c + 1 := by
      intro h
      have h2 : (2 : ZMod k) = 0 := by linear_combination -h
      have h2' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h2
      rw [ZMod.natCast_eq_zero_iff] at h2'
      have := Nat.le_of_dvd (by norm_num) h2'; omega
    exact (hR (lab (c - 1)) c (fun h => h1 (hinj h)) (fun h => h2 (hinj h))).ne'
  obtain ⟨s, α, μ, hrow⟩ := epRows_of_splitRows hk (fun i => x (lab i)) w a c σ hca hca1 hS hD hnd hcv
  exact ⟨k, inferInstance, lab, w, a, s, α, μ, hk, hinj, hR, hhid, hD, hrow⟩

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- **Gen.splitAny_edgePlaneAny.**  A generic split-pair view yields an Edge-Plane view (the rim and
the nearby view are those of `split_core`).  Hypotheses as in `Gen.splitAny_isRupert`. -/
theorem _root_.Minimality.Gen.splitAny_edgePlaneAny (F : S0xFac m S x) (hx : Function.Injective x)
    (hsep : ∀ i j : Fin n, j ≠ i → ∃ t : Fin m, i ∈ S t ∧ j ∉ S t)
    (h : Gen.SplitAny F) : Gen.EdgePlaneAny x := by
  rcases h with ⟨k, hne, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
  have hseg := noBetween_of_fac F hsep
  have hF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictFac F pat (u + ε • v) := by
    refine eventually_all.2 fun t => ?_
    obtain ⟨h1, h2⟩ := hfac t
    by_cases hp : pat t = true
    · filter_upwards [Minimality.eventually_pos_affine (h1 hp)] with ε hε
      refine ⟨fun _ => ?_, fun h => absurd hp (by simp [h])⟩
      rw [inner_add_right, real_inner_smul_right]; exact hε
    · have hp' : pat t = false := by simpa using hp
      filter_upwards [Minimality.eventually_pos_affine (h2 hp')] with ε hε
      refine ⟨fun h => absurd h hp, fun _ => ?_⟩
      rw [inner_add_right, real_inner_smul_right]; linarith
  obtain ⟨ε, h1, h2⟩ := (hF.and (splitRows_ev hrows v)).exists
  rcases rim_of_fac F hx hc hk hcyc h1 with h | h
  · exact split_core_ep hk x hx hseg c hc _ h a cc σ hca hca1 h2
  · have hc' : Function.Injective fun i : ZMod k => c (-i) := fun i j h => neg_injective (hc h)
    exact split_core_ep hk x hx hseg _ hc' _ h (-a - 1) (-cc) σ
      (fun e => hca1 (by linear_combination -e)) (fun e => hca (by linear_combination -e))
      (splitRows_rev (X := fun i => x (c i)) h2)

end Minimality.Split.EV
