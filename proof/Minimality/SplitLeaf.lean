module

public import Mathlib
public import Minimality.SplitRows
public import Minimality.Type21SAT.Lex2
public import Minimality.ManyTies

/-!
# The split leaf (Theorem 8.10 rows) for the SAT bridges of types 16 and 29

Staged in nopert229/out/bottleneck/p29/sat/L29S/ (DESIGN.md there); not yet imported by
`Minimality` (no bridge uses it yet). Namespace `Minimality.Split`, next to the row machinery of
`Minimality.SplitRows`.

* `split_core`: a view `w₀` with a strict rim `lab` and strict split rows gives a free view nearby:
  a small perturbation `w₀ + s v` keeps the rim and the rows and avoids finitely many planes
  (the `hD` plane, the `hnd` plane and the collinearity planes of the fan from `lab 0`), so that
  `HiddenInTriangles` holds there, and `freeAt_of_splitRows` applies.
* `hidden_of_rim`: a strict rim plus "no hidden point on a fan diagonal from `lab 0`" gives
  `HiddenInTriangles` (fan triangulation, discrete intermediate value).
* `split_strict_rupert`: facet data with strict facings at `w₀` (the rim cycle, either orientation)
  and strict rows give `IsRupert`.
* `split_tope_rupert` (menu and line views): lex facings at `(u, v)`, rows strict at `u`.
* `split_lex2_rupert` (tie views): three-level lex facings at `(u, d, w)` as `s0x_lex2_rupert`,
  rows with lex depth sign at `(u, d)` and `Δ` strict at `u`.
* `NoBetween` (no point strictly between two others) is the one extra hypothesis; it follows from
  facet data by a decidable condition on the vertex sets (`noBetween_of_fac`).
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split

/-! ### `det3` algebra -/

theorem det3_add_smul (p q w v : ℝ³) (s : ℝ) :
    det3 p q (w + s • v) = det3 p q w + s * det3 p q v := by
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_smul2 (p q w : ℝ³) (t : ℝ) : det3 p (t • q) w = t * det3 p q w := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_self (p w : ℝ³) : det3 p p w = 0 := by
  simp only [det3]; ring

theorem det3_eq_inner_cross (p q w : ℝ³) : det3 p q w = ⟪cross p q, w⟫ := by
  rw [inner3]; simp only [det3, cross_0, cross_1, cross_2]

theorem det3_flip (p r y w : ℝ³) : det3 (p - r) (y - r) w = -det3 (r - p) (y - p) w := by
  simp only [det3, PiLp.sub_apply]; ring

theorem det3_fan (p q r y w : ℝ³) :
    det3 (q - p) (r - p) w = det3 (q - p) (y - p) w + det3 (r - q) (y - q) w + det3 (p - r) (y - r) w := by
  simp only [det3, PiLp.sub_apply]; ring

theorem det3_neg_neg (p q w : ℝ³) : det3 (-p) (-q) w = det3 p q w := by
  simp only [det3, PiLp.neg_apply]; ring

theorem det3_smul_cross (μ : ℝ) (A B y w : ℝ³) :
    det3 (μ • Minimality.cross A B) y w = μ * (⟪A, y⟫ * ⟪B, w⟫ - ⟪B, y⟫ * ⟪A, w⟫) := by
  rw [inner3, inner3, inner3, inner3]
  simp only [det3, Minimality.cross, PiLp.smul_apply, smul_eq_mul]
  simp
  ring

/-- `p × q = 0` with `p ≠ 0`: `q` is a multiple of `p`. -/
theorem cross_eq_zero_imp {p q : ℝ³} (h : cross p q = 0) (hp : p ≠ 0) : ∃ t : ℝ, q = t • p := by
  have h0 : cross p q 0 = 0 := by rw [h]; simp
  have h1 : cross p q 1 = 0 := by rw [h]; simp
  have h2 : cross p q 2 = 0 := by rw [h]; simp
  simp only [cross_0, cross_1, cross_2] at h0 h1 h2
  have hex : p 0 ≠ 0 ∨ p 1 ≠ 0 ∨ p 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hp
    ext i; fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2]
  rcases hex with a | a | a
  · refine ⟨q 0 / p 0, ?_⟩
    ext i; fin_cases i <;> simp <;> field_simp <;> linarith
  · refine ⟨q 1 / p 1, ?_⟩
    ext i; fin_cases i <;> simp <;> field_simp <;> linarith
  · refine ⟨q 2 / p 2, ?_⟩
    ext i; fin_cases i <;> simp <;> field_simp <;> linarith

/-! ### No point strictly between two others -/

/-- No point of `x` lies strictly inside the segment of two other points. -/
def NoBetween {n : ℕ} (x : Fin n → ℝ³) : Prop :=
  ∀ m p q : Fin n, p ≠ m → q ≠ m → ∀ t : ℝ, 0 < t → t < 1 → x m ≠ x p + t • (x q - x p)

/-- From facet data: every vertex `i` and every other point `j` have a facet through `i` missing `j`
(decidable on the vertex sets; `by decide` for a concrete type). -/
theorem noBetween_of_fac {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : Minimality.H21.S0xFac m S x) (hS : ∀ i j : Fin n, j ≠ i → ∃ T, i ∈ S T ∧ j ∉ S T) :
    NoBetween x := by
  intro i p q hp hq t ht0 ht1 he
  obtain ⟨T, hiT, hpT⟩ := hS i p hp
  have fi := F.zero T i hiT
  have fp := F.neg T p hpT
  have fq := F.le T q
  have e1 := F.hN T (x i) (x p)
  have e2 := F.hN T (x q) (x p)
  rw [he, add_sub_cancel_left, real_inner_smul_right, ← e2, ← he] at e1
  nlinarith

/-! ### Rows under reversal of the cycle -/

theorem splitRows_rev {k : ℕ} {X : ZMod k → ℝ³} {w : ℝ³} {a c : ZMod k} {σ : ℝ}
    (h : SplitRows X w a c σ) : SplitRows (fun i => X (-i)) w (-a - 1) (-c) σ := by
  intro i j hi hj hjc
  have hi' : -i - 1 ≠ a := fun e => hi (by rw [← e]; ring)
  have hj' : -j = -i - 1 ∨ -j = -i - 1 + 1 := by
    rcases hj with rfl | rfl
    · right; ring
    · left; ring
  have hjc' : -j ≠ c := fun e => hjc (by rw [← e]; ring)
  have := h (-i - 1) (-j) hi' hj' hjc'
  simp only
  rw [show -(i + 1) = -i - 1 by ring, show -(-a - 1 + 1) = a by ring, show -(-a - 1) = a + 1 by ring,
    show -(-c) = c by ring]
  rw [show -i - 1 + 1 = -i by ring] at this
  rw [show X (-i - 1) - X (-i) = -(X (-i) - X (-i - 1)) by abel,
    show X a - X (a + 1) = -(X (a + 1) - X a) by abel, det3_neg_neg]
  exact this

/-! ### Persistence along a line -/

theorem ev_pos_quad {A B C D σ : ℝ} (h : 0 < σ * (A * C)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < σ * ((A + s * B) * (C + s * D)) := by
  have hc : Continuous fun s : ℝ => σ * ((A + s * B) * (C + s * D)) := by fun_prop
  have h0 : 0 < (fun s : ℝ => σ * ((A + s * B) * (C + s * D))) 0 := by simpa using h
  exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds

theorem ev_imp {P : Prop} {q : ℝ → Prop} {l : Filter ℝ} (h : P → ∀ᶠ s in l, q s) :
    ∀ᶠ s in l, P → q s := by
  by_cases hP : P
  · exact (h hP).mono fun s hs _ => hs
  · exact Eventually.of_forall fun s h' => absurd h' hP

theorem splitRows_ev {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {u : ℝ³} {a c : ZMod k} {σ : ℝ}
    (h : SplitRows X u a c σ) (v : ℝ³) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), SplitRows X (u + s • v) a c σ := by
  refine eventually_all.2 fun i => eventually_all.2 fun j => ev_imp fun hi => ev_imp fun hj =>
    ev_imp fun hjc => ?_
  filter_upwards [ev_pos_quad (B := ⟪X j - X c, v⟫) (D := det3 (X (i + 1) - X i) (X (a + 1) - X a) v)
    (h i j hi hj hjc)] with s hs
  rw [inner_add_right, real_inner_smul_right, det3_add_smul]
  exact hs

theorem strictRim_ev {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : StrictRimN x u lab) (v : ℝ³) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), StrictRimN x (u + s • v) lab := by
  refine eventually_all.2 fun m => eventually_all.2 fun i => ev_imp fun h0 => ev_imp fun h1 => ?_
  filter_upwards [Minimality.eventually_pos_affine (Or.inl (h m i h0 h1))
    (B := det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) v)] with s hs
  rw [det3_add_smul]; exact hs

/-! ### `HiddenInTriangles` from a strict rim, off the fan diagonals -/

/-- At a strict rim, a hidden point is not on the line of `lab 0` and `lab j` (in space), unless it
lies strictly between them. -/
theorem cross_ne_of_rim {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : NoBetween x) (w : ℝ³) (lab : ZMod k → Fin n) (hinj : Function.Injective lab)
    (hrim : StrictRimN x w lab) (m : Fin n) (hm : ∀ i, m ≠ lab i) (j : ZMod k) (hj : j ≠ 0) :
    cross (x (lab j) - x (lab 0)) (x m - x (lab 0)) ≠ 0 := by
  intro h
  have hP : x (lab j) - x (lab 0) ≠ 0 := sub_ne_zero.2 fun e => hj (hinj (hx e))
  obtain ⟨t, hQ⟩ := cross_eq_zero_imp h hP
  -- edge 0 gives `0 < t`
  have ht0 : 0 < t := by
    have h0 := hrim m 0 (hm 0) (hm _)
    rw [hQ, det3_smul2] at h0
    by_cases hj1 : j = 0 + 1
    · rw [← hj1, det3_self, mul_zero] at h0; exact absurd h0 (lt_irrefl _)
    · have hpos := hrim (lab j) 0 (fun e => hj (hinj e)) (fun e => hj1 (hinj e))
      exact pos_of_mul_pos_left h0 hpos.le
  -- edge `j` gives `t < 1`
  have ht1 : t < 1 := by
    have h0 := hrim m j (hm _) (hm _)
    have e1 : x m - x (lab j) = (1 - t) • (x (lab 0) - x (lab j)) := by
      rw [sub_smul, one_smul, ← neg_sub (x (lab j)) (x (lab 0)), smul_neg, ← hQ]; abel
    rw [e1, det3_smul2] at h0
    by_cases hj1 : j + 1 = 0
    · rw [hj1, det3_self, mul_zero] at h0; exact absurd h0 (lt_irrefl _)
    · have hpos := hrim (lab 0) j (fun e => hj (hinj e).symm) (fun e => hj1 (hinj e).symm)
      have := pos_of_mul_pos_left h0 hpos.le
      linarith
  exact hseg m (lab 0) (lab j) (fun e => hm 0 e.symm) (fun e => hm j e.symm) t ht0 ht1
    (by rw [← hQ]; abel)

/-- **Fan lemma.**  A strict rim `lab` at `w`, and no hidden point on a projected diagonal from
`lab 0` (unless the diagonal's space direction is degenerate), give `HiddenInTriangles`. -/
theorem hidden_of_rim {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : NoBetween x) (w : ℝ³) (lab : ZMod k → Fin n) (hinj : Function.Injective lab)
    (hrim : StrictRimN x w lab)
    (hgen : ∀ m, (∀ i, m ≠ lab i) → ∀ j : ZMod k, j ≠ 0 →
      cross (x (lab j) - x (lab 0)) (x m - x (lab 0)) ≠ 0 →
      det3 (x (lab j) - x (lab 0)) (x m - x (lab 0)) w ≠ 0) :
    HiddenInTriangles x w lab := by
  intro m hm
  set g : ℕ → ℝ := fun s => det3 (x (lab (s : ZMod k)) - x (lab 0)) (x m - x (lab 0)) w with hg
  have cast_ne : ∀ s : ℕ, 0 < s → s < k → ((s : ℕ) : ZMod k) ≠ 0 := by
    intro s h0 h1 e
    rw [ZMod.natCast_eq_zero_iff] at e
    exact absurd (Nat.le_of_dvd h0 e) (by omega)
  have g1 : 0 < g 1 := by
    have := hrim m 0 (hm 0) (hm _)
    simpa [hg] using this
  have gk : g (k - 1) < 0 := by
    have e : (((k - 1 : ℕ) : ZMod k) + 1) = 0 := by
      have : ((k - 1 : ℕ) : ZMod k) + 1 = ((k - 1 + 1 : ℕ) : ZMod k) := by push_cast; ring
      rw [this, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
    have := hrim m ((k - 1 : ℕ) : ZMod k) (hm _) (hm _)
    rw [e, det3_flip] at this
    simp only [hg]; linarith
  have gne : ∀ s, 1 ≤ s → s < k → g s ≠ 0 := by
    intro s h1 h2
    exact hgen m hm _ (cast_ne s (by omega) h2)
      (cross_ne_of_rim x hx hseg w lab hinj hrim m hm _ (cast_ne s (by omega) h2))
  have hex : ∃ s, 1 ≤ s ∧ g (s + 1) < 0 := ⟨k - 2, by omega, by
    rw [show k - 2 + 1 = k - 1 by omega]; exact gk⟩
  classical
  set s := Nat.find hex with hs
  obtain ⟨hs1, hs2⟩ := Nat.find_spec hex
  have hsk : s + 1 ≤ k - 1 := by
    by_contra hc
    have := Nat.find_min' hex (show 1 ≤ k - 2 ∧ g (k - 2 + 1) < 0 from
      ⟨by omega, by rw [show k - 2 + 1 = k - 1 by omega]; exact gk⟩)
    omega
  have gs : 0 < g s := by
    by_cases h1 : s = 1
    · rw [h1]; exact g1
    · have hmin := Nat.find_min hex (show s - 1 < s by omega)
      have hge : 0 ≤ g s := by
        by_contra hc
        apply hmin
        refine ⟨by omega, ?_⟩
        rw [show s - 1 + 1 = s by omega]; linarith
      exact lt_of_le_of_ne hge (gne s (by omega) (by omega)).symm
  have hrs := hrim m (s : ZMod k) (hm _) (hm _)
  have e1 : ((s : ℕ) : ZMod k) + 1 = ((s + 1 : ℕ) : ZMod k) := by push_cast; ring
  rw [e1] at hrs
  have h3 : 0 < det3 (x (lab 0) - x (lab ((s + 1 : ℕ) : ZMod k)))
      (x m - x (lab ((s + 1 : ℕ) : ZMod k))) w := by
    rw [det3_flip]; simp only [hg] at hs2; linarith
  refine ⟨x (lab 0), mem_image_of_mem x (mem_univ _), x (lab (s : ZMod k)), mem_image_of_mem x (mem_univ _),
    x (lab ((s + 1 : ℕ) : ZMod k)), mem_image_of_mem x (mem_univ _), ?_, gs, hrs, h3⟩
  rw [det3_fan _ _ _ (x m)]
  have : 0 < det3 (x (lab (s : ZMod k)) - x (lab 0)) (x m - x (lab 0)) w := gs
  linarith

/-! ### The core: a strict rim with strict rows gives a free view nearby -/

theorem split_core {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (hx : Function.Injective x)
    (hseg : NoBetween x) (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : StrictRimN x w₀ lab) (a c : ZMod k) (σ : ℝ) (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (hrows : SplitRows (fun i => x (lab i)) w₀ a c σ) :
    ∃ w : ℝ³, w ≠ 0 ∧ FreeAt (univ.image x) w := by
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
  exact ⟨w, hw0, freeAt_of_splitRows hk x w lab hinj hR hhid a c σ hS hD hnd⟩


/-! ### Facet data: strict facings give a strict rim in one of the two orientations -/

section Leaf
open Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Strict facings of all facets at `w` with the pattern `pat`. -/
def StrictFac (F : S0xFac m S x) (pat : Fin m → Bool) (w : ℝ³) : Prop :=
  ∀ t, (pat t = true → 0 < ⟪F.N t, w⟫) ∧ (pat t = false → ⟪F.N t, w⟫ < 0)

theorem rim_of_fac {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    {c : ZMod k → Fin n} (hc : Function.Injective c) (hk : 3 ≤ k) {pat : Fin m → Bool}
    (hcyc : S0xCycOK S c pat) {w : ℝ³} (hfs : StrictFac F pat w) :
    StrictRimN x w c ∨ StrictRimN x w (fun i => c (-i)) := by
  have hfac : S0xFacOK F pat w 0 := fun t =>
    ⟨fun h => Or.inl ((hfs t).1 h), fun h => Or.inl (by linarith [(hfs t).2 h])⟩
  obtain ⟨D⟩ := s0x_silL (k := k) F hcyc hfac
  choose μ hμ0 hd using h21b_exists_mu hk hx hc D
  -- the bracket at an off-edge point is strictly positive
  have hK : ∀ i q, q ≠ c i → q ≠ c (i + 1) →
      0 < ⟪D.A i, x q - x (c i)⟫ * ⟪D.B i, w⟫ - ⟪D.B i, x q - x (c i)⟫ * ⟪D.A i, w⟫ := by
    intro i q h0 h1
    have eA : ⟪D.A i, x q - x (c i)⟫ = D.fA i (x q) := by rw [← D.hA, D.zA0, sub_zero]
    have eB : ⟪D.B i, x q - x (c i)⟫ = D.fB i (x q) := by rw [← D.hB, D.zB0, sub_zero]
    have hA : 0 < ⟪D.A i, w⟫ := by
      rcases D.up i with h | ⟨_, h⟩
      · exact h
      · simp at h
    have hB : ⟪D.B i, w⟫ < 0 := by
      rcases D.dn i with h | ⟨_, h⟩
      · linarith
      · simp at h
    rw [eA, eB]
    have na := D.nA i q
    have nb := D.nB i q
    rcases D.strict i q h0 h1 with h | h
    · nlinarith [mul_nonneg (neg_nonneg.2 nb) hA.le, mul_pos_of_neg_of_neg h hB]
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos na hB.le, mul_pos (neg_pos.2 h) hA]
  rcases h21b_sign_agree hk hx hc D μ hμ0 hd with hp | hn
  · left
    intro q i h0 h1
    rw [hd i, det3_smul_cross]
    exact mul_pos (hp i) (hK i q h0 h1)
  · right
    intro q i h0 h1
    obtain ⟨j, rfl⟩ : ∃ j, i = -j - 1 := ⟨-i - 1, by ring⟩
    simp only [show -(-j - 1 + 1) = j by ring, show -(-j - 1) = j + 1 by ring] at h0 h1 ⊢
    rw [det3_flip, hd j, det3_smul_cross]
    have := mul_neg_of_neg_of_pos (hn j) (hK j q h1 h0)
    linarith

/-- **Split leaf at a view with strict facings.** -/
theorem split_strict_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    (hseg : NoBetween x) {c : ZMod k → Fin n} (hc : Function.Injective c) (hk : 3 ≤ k)
    {pat : Fin m → Bool} (hcyc : S0xCycOK S c pat) {w₀ : ℝ³} (hfs : StrictFac F pat w₀)
    (a cc : ZMod k) (σ : ℝ) (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hrows : SplitRows (fun i => x (c i)) w₀ a cc σ) : IsRupert (univ.image x) := by
  rcases rim_of_fac F hx hc hk hcyc hfs with h | h
  · obtain ⟨w, hw, hf⟩ := split_core hk x hx hseg c hc w₀ h a cc σ hca hca1 hrows
    exact FreeAt.isRupert hw hf
  · have hc' : Function.Injective fun i : ZMod k => c (-i) := fun i j h => neg_injective (hc h)
    obtain ⟨w, hw, hf⟩ := split_core hk x hx hseg _ hc' w₀ h (-a - 1) (-cc) σ
      (fun e => hca1 (by linear_combination -e)) (fun e => hca (by linear_combination -e))
      (splitRows_rev (X := fun i => x (c i)) hrows)
    exact FreeAt.isRupert hw hf

/-- **Split leaf at a menu or line view `u`** (facings lex at `(u, v)`, as `s0x_tope_rupert`;
rows strict at `u`).  The actual view is `u + ε v`, then a further small perturbation. -/
theorem split_tope_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    (hseg : NoBetween x) {c : ZMod k → Fin n} {pat : Fin m → Bool} {u : ℝ³} (v : ℝ³)
    (hc : Function.Injective c) (hk : 3 ≤ k) (hcyc : S0xCycOK S c pat) (hfac : S0xFacOK F pat u v)
    (a cc : ZMod k) (σ : ℝ) (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hrows : SplitRows (fun i => x (c i)) u a cc σ) : IsRupert (univ.image x) := by
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
  exact split_strict_rupert F hx hseg hc hk hcyc h1 a cc σ hca hca1 h2

/-- The same with a tope witness (`S0xTope`), as `s0x_tope_rupert'`. -/
theorem split_tope_rupert' {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    (hseg : NoBetween x) {c : ZMod k → Fin n} {pat : Fin m → Bool} {u : ℝ³}
    (hc : Function.Injective c) (hk : 3 ≤ k) (hcyc : S0xCycOK S c pat) (ht : S0xTope F pat u)
    (a cc : ZMod k) (σ : ℝ) (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hrows : SplitRows (fun i => x (c i)) u a cc σ) : IsRupert (univ.image x) := by
  obtain ⟨v, hv⟩ := ht
  exact split_tope_rupert F hx hseg v hc hk hcyc hv a cc σ hca hca1 hrows

/-- Tie-view rows at `(u, d)`: for every row a sign `s` with the depth lex `s`-positive at `(u, d)`
(`h21b_LP`, as `ordD` of the tie rules) and the rise `Δ` strictly `σ s`-positive at `u`. -/
def LexRows {k : ℕ} (X : ZMod k → ℝ³) (u d : ℝ³) (a cc : ZMod k) (σ : ℝ) : Prop :=
  ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ cc → ∃ s : ℝ,
    h21b_LP (s * ⟪X j - X cc, u⟫) (s * ⟪X j - X cc, d⟫) ∧
      0 < σ * s * det3 (X (i + 1) - X i) (X (a + 1) - X a) u

theorem lexRows_ev {k : ℕ} [NeZero k] {X : ZMod k → ℝ³} {u d : ℝ³} {a cc : ZMod k} {σ : ℝ}
    (h : LexRows X u d a cc σ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), SplitRows X (u + ε • d) a cc σ := by
  refine eventually_all.2 fun i => eventually_all.2 fun j => ev_imp fun hi => ev_imp fun hj =>
    ev_imp fun hjc => ?_
  obtain ⟨s, hL, hΔ⟩ := h i j hi hj hjc
  have hs : s ≠ 0 := by
    rintro rfl
    rcases hL with h | ⟨_, h⟩ <;> simp at h
  filter_upwards [Minimality.eventually_pos_affine hL,
    Minimality.eventually_pos_affine (B := σ * s * det3 (X (i + 1) - X i) (X (a + 1) - X a) d)
      (Or.inl hΔ)] with ε h1 h2
  rw [inner_add_right, real_inner_smul_right, det3_add_smul]
  set A := ⟪X j - X cc, u⟫
  set B := ⟪X j - X cc, d⟫
  set C := det3 (X (i + 1) - X i) (X (a + 1) - X a) u
  set D := det3 (X (i + 1) - X i) (X (a + 1) - X a) d
  have key : s ^ 2 * (σ * ((A + ε * B) * (C + ε * D))) =
      (s * A + ε * (s * B)) * (σ * s * C + ε * (σ * s * D)) := by ring
  have hpos : 0 < s ^ 2 * (σ * ((A + ε * B) * (C + ε * D))) := by rw [key]; exact mul_pos h1 h2
  exact pos_of_mul_pos_right hpos (sq_nonneg s)

/-- **Split leaf at a tie view** (facings three-level lex at `(u, d, w)` as `s0x_lex2_rupert`;
depths lex at `(u, d)`, rises strict at `u`).  The actual view is `u + ε d`, then the menu leaf
with tilt `w`. -/
theorem split_lex2_rupert {k : ℕ} [NeZero k] (F : S0xFac m S x) (hx : Function.Injective x)
    (hseg : NoBetween x) {c : ZMod k → Fin n} {pat : Fin m → Bool} {u d w : ℝ³}
    (hc : Function.Injective c) (hk : 3 ≤ k) (hcyc : S0xCycOK S c pat)
    (hfac : ∀ t, (pat t = true → LP3 ⟪F.N t, u⟫ ⟪F.N t, d⟫ ⟪F.N t, w⟫) ∧
      (pat t = false → LP3 (-⟪F.N t, u⟫) (-⟪F.N t, d⟫) (-⟪F.N t, w⟫)))
    (a cc : ZMod k) (σ : ℝ) (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hrows : LexRows (fun i => x (c i)) u d a cc σ) : IsRupert (univ.image x) := by
  have e1 : ∀ ε : ℝ, ∀ p : ℝ³, ⟪p, u + ε • d⟫ = ⟪p, u⟫ + ε * ⟪p, d⟫ := by
    intro ε p; rw [inner_add_right, real_inner_smul_right]
  have hfacev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S0xFacOK F pat (u + ε • d) w := by
    refine eventually_all.2 fun t => ?_
    obtain ⟨h1, h2⟩ := hfac t
    by_cases hp : pat t = true
    · filter_upwards [lp3_ev (h1 hp)] with ε hε
      refine ⟨fun _ => by rw [e1]; exact hε, fun h => absurd hp (by simp [h])⟩
    · have hp' : pat t = false := by simpa using hp
      filter_upwards [lp3_ev (h2 hp')] with ε hε
      refine ⟨fun h => absurd h hp, fun _ => ?_⟩
      have : -⟪F.N t, u + ε • d⟫ = -⟪F.N t, u⟫ + ε * (-⟪F.N t, d⟫) := by rw [e1]; ring
      rw [this]; exact hε
  obtain ⟨ε, h1, h2⟩ := (hfacev.and (lexRows_ev hrows)).exists
  exact split_tope_rupert F hx hseg w hc hk hcyc h1 a cc σ hca hca1 h2

end Leaf

end Minimality.Split

#print axioms Minimality.Split.split_core
#print axioms Minimality.Split.split_strict_rupert
#print axioms Minimality.Split.split_tope_rupert'
#print axioms Minimality.Split.split_lex2_rupert
#print axioms Minimality.Split.noBetween_of_fac

#print axioms Minimality.Split.split_tope_rupert
#print axioms Minimality.Split.hidden_of_rim
