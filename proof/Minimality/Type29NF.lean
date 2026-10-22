module

public import Minimality.Type16Pairs
public import Minimality.Type29

@[expose] public section

/-!
# Type 29: normal coordinates (`FEWER-FACES-PROOFS.md` §21.0)

Lemma 21.1: an affine map fixing the plane `H = aff(1, 4, 5)` puts `1 = (0, 0, 0)`,
`4 = (1, 0, 0)`, `5 = (0, 1, 0)`, `3 = (0, 0, −1)`, `0 = (a0, b0, −h0)`, `2 = (a2, b2, −h2)` and
the cap `6 = (s, t, 0)`.  Rupertness is not affine-invariant, so the frame is kept, as for
type 16 (`Type16NF.lean`): `x i = nfP o E₁ E₂ E₃ α β γ` with `o = x 1`, `E₁ = x 4 − x 1`,
`E₂ = x 5 − x 1`, `E₃ = x 1 − x 3`; every orientation test is a polynomial in the eight
coordinates times `det3 E₁ E₂ E₃` (`det3_nfV`), and depths are inner products (every metric).

* `NF29`: the normal form with the inequalities of Lemma 21.1 (`O = K − 6` an octahedron with
  the faces `012, 015, 023, 035, 124, 145, 234, 345`) and of the region `Π` (`K` of type 29).
* `NF29.sigma`: the normal form of `x ∘ σ`, `σ = (0 2)(4 5)`:
  `(a0, b0, h0, a2, b2, h2, s, t) ↦ (b2, a2, h2, b0, a0, h0, t, s)`.
* Tools: `nf29_simp`, `nf29_vec`, `nf29_test` (as `nf_simp`, `nf_vec`, `nf_test` of type 16),
  a vertex-view triangle rim in either orientation (`isRupert_vtriσ`).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **The normal form of type 29** (§21.0, Lemma 21.1) in the frame `o; E₁, E₂, E₃`:
`x 1 = o`, `x 4 = o + E₁`, `x 5 = o + E₂`, `x 3 = o − E₃`, `x 0 = (a0, b0, −h0)`,
`x 2 = (a2, b2, −h2)`, `x 6 = (s, t, 0)`.  The octahedron inequalities (`O = K − 6` with the
opposite pairs `(0, 4)`, `(1, 3)`, `(2, 5)`): `h0, h2 > 0`, `a0 < 0`, `b2 < 0`, `0` and `2`
beneath `345`, `F4, F5, D, D + G4, D + G5 > 0`, `E35 < 0 < E24`; the cap (`6 ∈ Π`): `s, t > 0`,
`s + t > 1`, `δ023(6), δ035(6), δ234(6) > 0`. -/
structure NF29 (x : Fin 7 → ℝ³) where
  o : ℝ³
  E₁ : ℝ³
  E₂ : ℝ³
  E₃ : ℝ³
  inj : Function.Injective x
  a0 : ℝ
  b0 : ℝ
  h0 : ℝ
  a2 : ℝ
  b2 : ℝ
  h2 : ℝ
  s : ℝ
  t : ℝ
  x0 : x 0 = nfP o E₁ E₂ E₃ a0 b0 (-h0)
  x1 : x 1 = nfP o E₁ E₂ E₃ 0 0 0
  x2 : x 2 = nfP o E₁ E₂ E₃ a2 b2 (-h2)
  x3 : x 3 = nfP o E₁ E₂ E₃ 0 0 (-1)
  x4 : x 4 = nfP o E₁ E₂ E₃ 1 0 0
  x5 : x 5 = nfP o E₁ E₂ E₃ 0 1 0
  x6 : x 6 = nfP o E₁ E₂ E₃ s t 0
  hD : det3 E₁ E₂ E₃ ≠ 0
  hh0 : 0 < h0
  hh2 : 0 < h2
  ha0 : a0 < 0
  hb2 : b2 < 0
  t345_0 : a0 + b0 + h0 < 1
  t345_2 : a2 + b2 + h2 < 1
  hF4 : 0 < h2 * b0 - h0 * b2
  hF5 : 0 < h0 * a2 - h2 * a0
  hDD : 0 < a0 * b2 - a2 * b0
  hDG4 : 0 < a0 * b2 - a2 * b0 + (b0 * (1 - h2) - b2 * (1 - h0))
  hDG5 : 0 < a0 * b2 - a2 * b0 + (a2 * (1 - h0) - a0 * (1 - h2))
  hE35 : (b0 - 1 + h0) * a2 - a0 * b2 + a0 * (1 - h2) < 0
  hE24 : 0 < a0 * b2 + (1 - h2 - a2) * b0 - b2 * (1 - h0)
  hs : 0 < s
  ht : 0 < t
  hst : 1 < s + t
  d023 : 0 < a0 * b2 - a2 * b0 + s * (b0 * (1 - h2) - b2 * (1 - h0)) +
    t * (a2 * (1 - h0) - a0 * (1 - h2))
  d035 : 0 < -((b0 - 1 + h0) * s - a0 * t + a0)
  d234 : 0 < b2 * s + (1 - h2 - a2) * t - b2

/-- `σ = (0 2)(4 5)`. -/
def sigma29 : Fin 7 → Fin 7 := ![2, 1, 0, 3, 5, 4, 6]

theorem sigma29_inj : Function.Injective sigma29 := by decide

theorem image_sigma29 (x : Fin 7 → ℝ³) : univ.image (x ∘ sigma29) = univ.image x := by
  ext z
  simp only [mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    have h : ∀ j, sigma29 (sigma29 j) = j := by decide
    exact ⟨sigma29 i, congrArg x (h i)⟩

namespace NF29

variable {x : Fin 7 → ℝ³}

/-- The orientation of the frame. -/
noncomputable def D (N : NF29 x) : ℝ := det3 N.E₁ N.E₂ N.E₃

/-- **The normal form of `x ∘ σ`**, `σ = (0 2)(4 5)`: the frame `o; E₂, E₁, E₃` and the
coordinates `(b2, a2, h2, b0, a0, h0, t, s)`. -/
def sigma (N : NF29 x) : NF29 (x ∘ sigma29) where
  o := N.o
  E₁ := N.E₂
  E₂ := N.E₁
  E₃ := N.E₃
  inj := N.inj.comp sigma29_inj
  a0 := N.b2
  b0 := N.a2
  h0 := N.h2
  a2 := N.b0
  b2 := N.a0
  h2 := N.h0
  s := N.t
  t := N.s
  x0 := by show x 2 = _; rw [N.x2]; simp only [nfP]; module
  x1 := by show x 1 = _; rw [N.x1]; simp only [nfP]; module
  x2 := by show x 0 = _; rw [N.x0]; simp only [nfP]; module
  x3 := by show x 3 = _; rw [N.x3]; simp only [nfP]; module
  x4 := by show x 5 = _; rw [N.x5]; simp only [nfP]; module
  x5 := by show x 4 = _; rw [N.x4]; simp only [nfP]; module
  x6 := by show x 6 = _; rw [N.x6]; simp only [nfP]; module
  hD := by
    have e : det3 N.E₂ N.E₁ N.E₃ = -det3 N.E₁ N.E₂ N.E₃ := by simp only [det3_expand]; ring
    rw [e]; exact neg_ne_zero.mpr N.hD
  hh0 := N.hh2
  hh2 := N.hh0
  ha0 := N.hb2
  hb2 := N.ha0
  t345_0 := by linarith [N.t345_2]
  t345_2 := by linarith [N.t345_0]
  hF4 := by linarith [N.hF5]
  hF5 := by linarith [N.hF4]
  hDD := by linarith [N.hDD]
  hDG4 := by linarith [N.hDG5]
  hDG5 := by linarith [N.hDG4]
  hE35 := by linarith [N.hE24]
  hE24 := by linarith [N.hE35]
  hs := N.ht
  ht := N.hs
  hst := by linarith [N.hst]
  d023 := by linarith [N.d023]
  d035 := by linarith [N.d234]
  d234 := by linarith [N.d035]

theorem sigma_D (N : NF29 x) : N.sigma.D = -N.D := by
  simp only [D, sigma, det3_expand]; ring

end NF29

/-- Rewrite the points of a type-29 normal form and the frame determinants. -/
macro "nf29_simp " N:term:max : tactic =>
  `(tactic| simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    NF29.x0 $N, NF29.x1 $N, NF29.x2 $N, NF29.x3 $N, NF29.x4 $N, NF29.x5 $N,
    NF29.x6 $N, nfP_sub, det3_nfV])

/-- A vector identity of a type-29 normal form, checked coordinatewise. -/
macro "nf29_vec " N:term:max : tactic =>
  `(tactic| (nf29_simp $N; ext; simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, PiLp.neg_apply, PiLp.zero_apply, WithLp.ofLp_zero, Pi.zero_apply,
    smul_eq_mul]; ring))

/-- An orientation test of a type-29 normal form from the sign of its polynomial. -/
macro "nf29_test " N:term:max hσD:term:max h:term : tactic =>
  `(tactic| (nf29_simp $N; exact nf_pos $hσD $h (by simp only [det3c]; ring)))

/-- A vertex-view triangle rim `y₀ y₁ y₂` (orientation `σ`). -/
theorem isRupert_vtriσ (V M : Finset ℝ³) {u : ℝ³} (hu : u ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {y₀ y₁ y₂ : ℝ³} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) (h₂ : y₂ ∈ V)
    (n₀ : y₀ ∉ M) (n₁ : y₁ ∉ M) (n₂ : y₂ ∉ M)
    (c₁ : 0 < σ * det3 (y₁ - y₀) (y₂ - y₀) u) (c₂ : 0 < σ * det3 (y₂ - y₁) (y₀ - y₁) u)
    (c₃ : 0 < σ * det3 (y₀ - y₂) (y₁ - y₂) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ≠ y₀ → z ≠ y₁ → z ≠ y₂ →
      0 < σ * det3 (y₁ - y₀) (z - y₀) u ∧ 0 < σ * det3 (y₂ - y₁) (z - y₁) u ∧
        0 < σ * det3 (y₀ - y₂) (z - y₂) u)
    (hz : [⟪y₀, u⟫, ⟪y₁, u⟫, ⟪y₂, u⟫].Nodup) (hnd : NoHDNAt V u)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y₀ + s • (y₁ - y₀) + δ • u ∨ m = y₁ + s • (y₂ - y₁) + δ • u ∨
        m = y₂ + s • (y₀ - y₂) + δ • u)) : IsRupert V := by
  obtain ⟨a0, a1, a2⟩ := zmod3_add_one
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2⟩, z3, -⟩ := hz
  have hinj : Function.Injective (tri ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫) := by
    intro i j h
    rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
      simp only [tri_0, tri_1, tri_2] at h <;> first | rfl | (exfalso; tauto)
  have hzu : (fun i => ⟪tri y₀ y₁ y₂ i, u⟫) = tri ⟪y₀, u⟫ ⟪y₁, u⟫ ⟪y₂, u⟫ := by
    funext i; rcases zmod3_cases i with rfl | rfl | rfl <;> rfl
  refine isRupert_of_vertexViewσ V M u hu hσ (k := 3) (by norm_num) (tri y₀ y₁ y₂) ?_ ?_ ?_
    ?_ (by rw [hzu]; exact (isCyclicUnimodal_three hinj).isRobustUnimodal) hnd ?_
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [h₀, h₁, h₂]
  · intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [n₀, n₁, n₂]
  · intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, tri_0, tri_1, tri_2]
    exacts [c₁, c₂, c₃]
  · intro y hy hyM hyx i
    obtain ⟨r0, r1, r2⟩ := hrest y hy hyM (hyx 0) (hyx 1) (hyx 2)
    rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [a0, a1, a2, tri_0, tri_1, tri_2]
    exacts [r0, r1, r2]
  · intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, h | h | h⟩ := hM m hm
    · exact ⟨0, s, δ, hs0, hs1, hδ, by simp only [a0, tri_0, tri_1]; exact h⟩
    · exact ⟨1, s, δ, hs0, hs1, hδ, by simp only [a1, tri_1, tri_2]; exact h⟩
    · exact ⟨2, s, δ, hs0, hs1, hδ, by simp only [a2, tri_2, tri_0]; exact h⟩

end Minimality

end
