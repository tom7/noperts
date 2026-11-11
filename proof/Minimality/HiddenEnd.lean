module

public import Mathlib
public import Minimality.SplitRows

@[expose] public section

/-!
# The Hidden-End Lemma


The views are `u s = u₀ + s v₁ + s² v₂` (`tiltView`).  For a fixed motion `(ω, τ)` every
determinant of a `TiltCert` at `u s` is a quadratic `A + s B + s² C` in `s`; it is positive for
small `s > 0` when `(A, B, C)` is lexicographically positive (`LexPos3`).  So a lexicographic
`TiltCert` (`LexTiltCert`) at every point gives `FreeAt` at all small `s` (`freeAt_of_lexTilt`),
hence `IsRupert`.

The Hidden-End Lemma (`hel`, `hel_rupert`): at a corner `c` with ends `K, J, M`, `u₀ = k`,
`v₁ = -(α j + β m)`, `v₂ = -(γ j + δ m)` with `(α, γ)` and `(β, δ)` lexicographically positive
(this contains the HEL ray `k - s(α j + β m)` and the CSL / Corner-Limit family
`k - s α j - s² δ m`), the point `K` needs no certificate: it is proved hidden in the triangle
`c J M` (`lexTilt_K`).  Every other point needs a `LexTiltCert`.  Row lemmas turn the limit
rows of the sketch into such certificates:

* `lexTilt_of_tiltCert`: a strict `TiltCert` at `u₀` (rows (a): limit shadow vertices; strictly
  hidden points);
* `lexTilt_edge_exposed`: a limit edge point that the tilt pushes out, with its row (b);
* `lexTilt_edge_hidden`: a limit edge point that the tilt pushes in (no row);
* `lexTilt_wallJ`, `lexTilt_wallM`: wall points hidden by the tilt (the sketch's "hidden wall
  points", with the corrected criterion).

No convexity, no hull, no general-position hypothesis.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.HEL
open Minimality.Split
open Minimality (cross)

/-! ### Lexicographic positivity -/

/-- `(B, C)` is lexicographically positive. -/
def LexPos2 (B C : ℝ) : Prop := 0 < B ∨ (B = 0 ∧ 0 < C)

/-- `(A, B, C)` is lexicographically positive: `A + s B + s² C > 0` for small `s > 0`. -/
def LexPos3 (A B C : ℝ) : Prop := 0 < A ∨ (A = 0 ∧ LexPos2 B C)

theorem ev_pos_of_cont {g : ℝ → ℝ} (hg : Continuous g) (h : 0 < g 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < g s :=
  Filter.Eventually.filter_mono nhdsWithin_le_nhds ((hg.tendsto 0).eventually (lt_mem_nhds h))

theorem LexPos3.eventually {A B C : ℝ} (h : LexPos3 A B C) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < A + s * B + s ^ 2 * C := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact ev_pos_of_cont (g := fun s => A + s * B + s ^ 2 * C) (by fun_prop) (by simpa using h)
  · filter_upwards [ev_pos_of_cont (g := fun s => B + s * C) (by fun_prop) (by simpa using h),
      self_mem_nhdsWithin] with s hs hs0
    have : 0 + s * B + s ^ 2 * C = s * (B + s * C) := by ring
    rw [this]; exact mul_pos hs0 hs
  · filter_upwards [self_mem_nhdsWithin] with s hs0
    have : (0:ℝ) + s * 0 + s ^ 2 * C = s ^ 2 * C := by ring
    rw [this]; exact mul_pos (pow_pos hs0 2) h

theorem lexPos3_of_pos {A : ℝ} (B C : ℝ) (h : 0 < A) : LexPos3 A B C := Or.inl h

/-- `(0, β E, δ E)` with `E > 0` and `(β, δ)` lexicographically positive. -/
theorem lexPos3_zero_mul {A B C β δ E : ℝ} (hE : 0 < E) (h : LexPos2 β δ) (hA : A = 0)
    (hB : B = β * E) (hC : C = δ * E) : LexPos3 A B C := by
  refine Or.inr ⟨hA, ?_⟩
  rcases h with h | ⟨h0, h⟩
  · exact Or.inl (by rw [hB]; positivity)
  · exact Or.inr ⟨by rw [hB, h0, zero_mul], by rw [hC]; positivity⟩

/-! ### Tilted views and lexicographic certificates -/

/-- The view `u₀ + s v₁ + s² v₂`. -/
noncomputable def tiltView (u v₁ v₂ : ℝ³) (s : ℝ) : ℝ³ := u + s • v₁ + s ^ 2 • v₂

theorem det3_tiltView (a b u v₁ v₂ : ℝ³) (s : ℝ) :
    det3 a b (tiltView u v₁ v₂ s) = det3 a b u + s * det3 a b v₁ + s ^ 2 * det3 a b v₂ := by
  simp only [tiltView, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The determinant `det3 a b ·` is lexicographically positive along the views. -/
def LexDet (a b u v₁ v₂ : ℝ³) : Prop := LexPos3 (det3 a b u) (det3 a b v₁) (det3 a b v₂)

theorem LexDet.eventually {a b u v₁ v₂ : ℝ³} (h : LexDet a b u v₁ v₂) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < det3 a b (tiltView u v₁ v₂ s) := by
  filter_upwards [LexPos3.eventually h] with s hs
  rw [det3_tiltView]; exact hs

/-- `TiltCert` with every determinant lexicographically positive along the views
`u₀ + s v₁ + s² v₂`, for the fixed motion `(ω, τ)`. -/
def LexTiltCert (V : Finset ℝ³) (u v₁ v₂ ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, LexDet (y₁ - x) (y₀ - x) u v₁ v₂ ∧
      LexDet (y₁ - x) (cross ω x + τ) u v₁ v₂ ∧ LexDet (x - y₀) (cross ω x + τ) u v₁ v₂) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, LexDet (b - a) (c - a) u v₁ v₂ ∧ LexDet (b - a) (x - a) u v₁ v₂ ∧
      LexDet (c - b) (x - b) u v₁ v₂ ∧ LexDet (a - c) (x - c) u v₁ v₂)

theorem LexTiltCert.eventually {V : Finset ℝ³} {u v₁ v₂ ω τ x : ℝ³}
    (h : LexTiltCert V u v₁ v₂ ω τ x) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), TiltCert V (tiltView u v₁ v₂ s) ω τ x := by
  rcases h with ⟨y₀, h₀, y₁, h₁, d1, d2, d3⟩ | ⟨a, ha, b, hb, c, hc, d1, d2, d3, d4⟩
  · filter_upwards [d1.eventually, d2.eventually, d3.eventually] with s e1 e2 e3
    exact Or.inl ⟨y₀, h₀, y₁, h₁, e1, e2, e3⟩
  · filter_upwards [d1.eventually, d2.eventually, d3.eventually, d4.eventually] with s e1 e2 e3 e4
    exact Or.inr ⟨a, ha, b, hb, c, hc, e1, e2, e3, e4⟩

theorem TiltCert.ne_zero {V : Finset ℝ³} {w ω τ x : ℝ³} (h : TiltCert V w ω τ x) : w ≠ 0 := by
  rintro rfl
  rcases h with ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, _, _, h, -⟩ <;>
    simp [det3] at h

/-- **Lexicographic tilt lemma.**  A lexicographic `TiltCert` at every point, for one motion, gives
free views `u₀ + s v₁ + s² v₂` for all small `s > 0`. -/
theorem freeAt_of_lexTilt {ι : Type*} [Finite ι] (x : ι → ℝ³) (V : Finset ℝ³)
    (hV : ∀ y ∈ V, ∃ i, x i = y) (u v₁ v₂ ω τ : ℝ³)
    (h : ∀ i, LexTiltCert V u v₁ v₂ ω τ (x i)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt V (tiltView u v₁ v₂ s) := by
  filter_upwards [Filter.eventually_all.2 fun i => (h i).eventually] with s hs
  refine ⟨ω, τ, fun y hy => ?_⟩
  obtain ⟨i, rfl⟩ := hV y hy
  exact hs i

theorem isRupert_of_lexTilt {n : ℕ} (x : Fin n → ℝ³) (i₀ : Fin n) (u v₁ v₂ ω τ : ℝ³)
    (h : ∀ i, LexTiltCert (univ.image x) u v₁ v₂ ω τ (x i)) : IsRupert (univ.image x) := by
  have hF := freeAt_of_lexTilt x (univ.image x)
    (fun y hy => by obtain ⟨i, -, rfl⟩ := mem_image.1 hy; exact ⟨i, rfl⟩) u v₁ v₂ ω τ h
  obtain ⟨s, hs, hs'⟩ := ((h i₀).eventually.and hF).exists
  exact FreeAt.isRupert (TiltCert.ne_zero hs) hs'

/-! ### Row lemmas: from the limit system to lexicographic certificates -/

/-- A strict `TiltCert` at the limit view (rows (a), strictly hidden points). -/
theorem lexTilt_of_tiltCert {V : Finset ℝ³} {u v₁ v₂ ω τ x : ℝ³} (h : TiltCert V u ω τ x) :
    LexTiltCert V u v₁ v₂ ω τ x := by
  rcases h with ⟨y₀, h₀, y₁, h₁, d1, d2, d3⟩ | ⟨a, ha, b, hb, c, hc, d1, d2, d3, d4⟩
  · exact Or.inl ⟨y₀, h₀, y₁, h₁, Or.inl d1, Or.inl d2, Or.inl d3⟩
  · exact Or.inr ⟨a, ha, b, hb, c, hc, Or.inl d1, Or.inl d2, Or.inl d3, Or.inl d4⟩

syntax "hel_simp" : tactic
macro_rules
  | `(tactic| hel_simp) => `(tactic| simp only [det3, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul])

/-- A limit edge point: `x - q = λ (r - q) + μ u₀` with `0 < λ < 1` (in the shadow along `u₀`,
`x` is inside the edge from `q` to `r`; `μ` its depth offset).  If the tilt pushes it out
(`(-μ det3 (r - q) u₀ v₁, -μ det3 (r - q) u₀ v₂)` lexicographically positive), its limit row (b)
`det3 (r - q) (V x) u₀ > 0` gives a certificate (the angle `q x r`). -/
theorem lexTilt_edge_exposed {V : Finset ℝ³} {u v₁ v₂ ω τ x q r : ℝ³} (hq : q ∈ V) (hr : r ∈ V)
    (l μ : ℝ) (hx : x - q = l • (r - q) + μ • u) (hl0 : 0 < l) (hl1 : l < 1)
    (hout : LexPos2 (-(μ * det3 (r - q) u v₁)) (-(μ * det3 (r - q) u v₂)))
    (hrow : 0 < det3 (r - q) (cross ω x + τ) u) :
    LexTiltCert V u v₁ v₂ ω τ x := by
  have hx' : x = q + (l • (r - q) + μ • u) := by rw [← hx]; abel
  subst hx'
  have e1 : ∀ w : ℝ³, det3 (r - (q + (l • (r - q) + μ • u))) (q - (q + (l • (r - q) + μ • u))) w
      = -(μ * det3 (r - q) u w) := fun w => by hel_simp; ring
  refine Or.inl ⟨q, hq, r, hr, ?_, ?_, ?_⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [e1]; simp only [det3]; ring
    · rw [e1, e1]; exact hout
  · refine Or.inl ?_
    have : ∀ W : ℝ³, det3 (r - (q + (l • (r - q) + μ • u))) W u = (1 - l) * det3 (r - q) W u :=
      fun W => by hel_simp; ring
    rw [this]; exact mul_pos (by linarith) hrow
  · refine Or.inl ?_
    have : ∀ W : ℝ³, det3 (q + (l • (r - q) + μ • u) - q) W u = l * det3 (r - q) W u :=
      fun W => by hel_simp; ring
    rw [this]; exact mul_pos hl0 hrow

/-- A limit edge point that the tilt pushes in (`(μ det3 (r - q) u₀ v₁, μ det3 (r - q) u₀ v₂)`
lexicographically positive), with `s` strictly on the inner side of the edge `q → r`: hidden in
the triangle `q r s`, no row needed. -/
theorem lexTilt_edge_hidden {V : Finset ℝ³} {u v₁ v₂ ω τ x q r s : ℝ³} (hq : q ∈ V) (hr : r ∈ V)
    (hs : s ∈ V) (l μ : ℝ) (hx : x - q = l • (r - q) + μ • u) (hl0 : 0 < l) (hl1 : l < 1)
    (hin : LexPos2 (μ * det3 (r - q) u v₁) (μ * det3 (r - q) u v₂))
    (hT : 0 < det3 (r - q) (s - q) u) :
    LexTiltCert V u v₁ v₂ ω τ x := by
  have hx' : x = q + (l • (r - q) + μ • u) := by rw [← hx]; abel
  subst hx'
  have e1 : ∀ w : ℝ³, det3 (r - q) (q + (l • (r - q) + μ • u) - q) w = μ * det3 (r - q) u w :=
    fun w => by hel_simp; ring
  refine Or.inr ⟨q, hq, r, hr, s, hs, Or.inl hT, Or.inr ⟨?_, ?_⟩, Or.inl ?_, Or.inl ?_⟩
  · rw [e1]; simp only [det3]; ring
  · rw [e1, e1]; exact hin
  · have : det3 (s - r) (q + (l • (r - q) + μ • u) - r) u = (1 - l) * det3 (r - q) (s - q) u := by
      hel_simp; ring
    rw [this]; exact mul_pos (by linarith) hT
  · have : det3 (q - s) (q + (l • (r - q) + μ • u) - s) u = l * det3 (r - q) (s - q) u := by
      hel_simp; ring
    rw [this]; exact mul_pos hl0 hT

/-! ### The corner: `K` and the wall points are hidden -/

section Corner
variable {n : ℕ} (x : Fin n → ℝ³) (c K J M : Fin n) (α β γ δ : ℝ)

/-- The view direction `u₀ = k`. -/
noncomputable abbrev hk : ℝ³ := x K - x c
/-- `v₁ = -(α j + β m)`. -/
noncomputable abbrev hv₁ : ℝ³ := -(α • (x J - x c) + β • (x M - x c))
/-- `v₂ = -(γ j + δ m)`. -/
noncomputable abbrev hv₂ : ℝ³ := -(γ • (x J - x c) + δ • (x M - x c))

/-- `D = det3 j m k`, the orientation of the corner. -/
noncomputable abbrev hD : ℝ := det3 (x J - x c) (x M - x c) (x K - x c)

/-- **`K` is hidden** in the triangle `c J M` at every small view of the hiding family. -/
theorem lexTilt_K (ω τ : ℝ³) (hD0 : 0 < hD x c K J M) (hαγ : LexPos2 α γ) (hβδ : LexPos2 β δ) :
    LexTiltCert (univ.image x) (hk x c K) (hv₁ x c J M α β) (hv₂ x c J M γ δ) ω τ (x K) := by
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  refine Or.inr ⟨x c, mem c, x J, mem J, x M, mem M, Or.inl ?_, ?_, Or.inl ?_, ?_⟩
  · simpa using hD0
  · exact lexPos3_zero_mul hD0 hβδ (by simp only [hk, det3]; ring)
      (by simp only [hv₁, hD]; hel_simp; ring) (by simp only [hv₂, hD]; hel_simp; ring)
  · have : det3 (x M - x J) (x K - x J) (hk x c K) = hD x c K J M := by
      simp only [hk, hD]; hel_simp; ring
    rw [this]; exact hD0
  · exact lexPos3_zero_mul hD0 hαγ (by simp only [hk]; hel_simp; ring)
      (by simp only [hv₁, hD]; hel_simp; ring) (by simp only [hv₂, hD]; hel_simp; ring)

/-- **Wall points of `W_J = (c, K, J)` hidden by the tilt.**  `x p - x c = a k + b j` and
`x P - x c = a' k + b' j` (`P` e.g. the far end of the wall in the limit shadow, or `J` itself:
`a' = 0`, `b' = 1`).  If `0 < b < b'` and `a' b < b' a` (`p` lies on the `K` side of the line
`c P` in the wall), then `p` is hidden in the triangle `c P M`. -/
theorem lexTilt_wallJ (ω τ : ℝ³) (p P : Fin n) (a b a' b' : ℝ)
    (hp : x p - x c = a • (x K - x c) + b • (x J - x c))
    (hP : x P - x c = a' • (x K - x c) + b' • (x J - x c))
    (hD0 : 0 < hD x c K J M) (hβδ : LexPos2 β δ)
    (hb : 0 < b) (hbb : b < b') (hab : a' * b < b' * a) :
    LexTiltCert (univ.image x) (hk x c K) (hv₁ x c J M α β) (hv₂ x c J M γ δ) ω τ (x p) := by
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hp' : x p = x c + (a • (x K - x c) + b • (x J - x c)) := by rw [← hp]; abel
  have hP' : x P = x c + (a' • (x K - x c) + b' • (x J - x c)) := by rw [← hP]; abel
  have hE : 0 < (b' * a - a' * b) * hD x c K J M := mul_pos (by linarith) hD0
  refine Or.inr ⟨x c, mem c, x P, mem P, x M, mem M, Or.inl ?_, ?_, Or.inl ?_, Or.inl ?_⟩
  · have : det3 (x P - x c) (x M - x c) (hk x c K) = b' * hD x c K J M := by
      rw [hP']; simp only [hk, hD]; hel_simp; ring
    rw [this]; exact mul_pos (by linarith) hD0
  · refine lexPos3_zero_mul hE hβδ ?_ ?_ ?_ <;> rw [hP', hp'] <;>
      simp only [hk, hv₁, hv₂, hD] <;> hel_simp <;> ring
  · have : det3 (x M - x P) (x p - x P) (hk x c K) = (b' - b) * hD x c K J M := by
      rw [hP', hp']; simp only [hk, hD]; hel_simp; ring
    rw [this]; exact mul_pos (by linarith) hD0
  · have : det3 (x c - x M) (x p - x M) (hk x c K) = b * hD x c K J M := by
      rw [hp']; simp only [hk, hD]; hel_simp; ring
    rw [this]; exact mul_pos hb hD0

/-- **Wall points of `W_M = (c, K, M)` hidden by the tilt** (mirror of `lexTilt_wallJ`):
`x p - x c = a k + b m`, `x P - x c = a' k + b' m`, `0 < b < b'`, `a' b < b' a`; hidden in the
triangle `c J P`. -/
theorem lexTilt_wallM (ω τ : ℝ³) (p P : Fin n) (a b a' b' : ℝ)
    (hp : x p - x c = a • (x K - x c) + b • (x M - x c))
    (hP : x P - x c = a' • (x K - x c) + b' • (x M - x c))
    (hD0 : 0 < hD x c K J M) (hαγ : LexPos2 α γ)
    (hb : 0 < b) (hbb : b < b') (hab : a' * b < b' * a) :
    LexTiltCert (univ.image x) (hk x c K) (hv₁ x c J M α β) (hv₂ x c J M γ δ) ω τ (x p) := by
  have mem : ∀ j, x j ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ j)
  have hp' : x p = x c + (a • (x K - x c) + b • (x M - x c)) := by rw [← hp]; abel
  have hP' : x P = x c + (a' • (x K - x c) + b' • (x M - x c)) := by rw [← hP]; abel
  have hE : 0 < (b' * a - a' * b) * hD x c K J M := mul_pos (by linarith) hD0
  refine Or.inr ⟨x c, mem c, x J, mem J, x P, mem P, Or.inl ?_, Or.inl ?_, Or.inl ?_, ?_⟩
  · have : det3 (x J - x c) (x P - x c) (hk x c K) = b' * hD x c K J M := by
      rw [hP']; simp only [hk, hD]; hel_simp; ring
    rw [this]; exact mul_pos (by linarith) hD0
  · have : det3 (x J - x c) (x p - x c) (hk x c K) = b * hD x c K J M := by
      rw [hp']; simp only [hk, hD]; hel_simp; ring
    rw [this]; exact mul_pos hb hD0
  · have : det3 (x P - x J) (x p - x J) (hk x c K) = (b' - b) * hD x c K J M := by
      rw [hP', hp']; simp only [hk, hD]; hel_simp; ring
    rw [this]; exact mul_pos (by linarith) hD0
  · refine lexPos3_zero_mul hE hαγ ?_ ?_ ?_ <;> rw [hP', hp'] <;>
      simp only [hk, hv₁, hv₂, hD] <;> hel_simp <;> ring

/-- **Hidden-End Lemma.**  `c` a point with `K, J, M` (the corner edge `cK` and the two other edge
ends), `D = det3 (x J - x c) (x M - x c) (x K - x c) > 0` (swap `J, M` otherwise).  Views
`u s = k - s (α j + β m) - s² (γ j + δ m)` with `(α, γ)` and `(β, δ)` lexicographically positive
(the hiding cone: `K` is hidden behind `c`).  If one motion `(ω, τ)` has a lexicographic
`TiltCert` at every point other than `K` (the limit system), then all small views are free. -/
theorem hel (ω τ : ℝ³) (hD0 : 0 < hD x c K J M) (hαγ : LexPos2 α γ) (hβδ : LexPos2 β δ)
    (hcert : ∀ i, i ≠ K →
      LexTiltCert (univ.image x) (hk x c K) (hv₁ x c J M α β) (hv₂ x c J M γ δ) ω τ (x i)) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), FreeAt (univ.image x)
      (x K - x c - s • (α • (x J - x c) + β • (x M - x c)) -
        s ^ 2 • (γ • (x J - x c) + δ • (x M - x c))) := by
  have hall : ∀ i, LexTiltCert (univ.image x) (hk x c K) (hv₁ x c J M α β)
      (hv₂ x c J M γ δ) ω τ (x i) := by
    intro i
    by_cases hi : i = K
    · rw [hi]; exact lexTilt_K x c K J M α β γ δ ω τ hD0 hαγ hβδ
    · exact hcert i hi
  filter_upwards [freeAt_of_lexTilt x (univ.image x)
    (fun y hy => by obtain ⟨i, -, rfl⟩ := mem_image.1 hy; exact ⟨i, rfl⟩) _ _ _ ω τ hall] with s hs
  convert hs using 1
  simp only [tiltView, hk, hv₁, hv₂, smul_neg]; abel

theorem hel_rupert (ω τ : ℝ³) (hD0 : 0 < hD x c K J M) (hαγ : LexPos2 α γ) (hβδ : LexPos2 β δ)
    (hcert : ∀ i, i ≠ K →
      LexTiltCert (univ.image x) (hk x c K) (hv₁ x c J M α β) (hv₂ x c J M γ δ) ω τ (x i)) :
    IsRupert (univ.image x) :=
  isRupert_of_lexTilt x K _ _ _ ω τ fun i => by
    by_cases hi : i = K
    · rw [hi]; exact lexTilt_K x c K J M α β γ δ ω τ hD0 hαγ hβδ
    · exact hcert i hi

end Corner

end Minimality.Split.HEL

