module

public import Minimality.Type08S.P2LXrim
public import Minimality.Type08S.P2SC2V4

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma LX (ii) in SC2-V's frame (package K): the case `h_{x'} > h_f`

Frame as in `lemmaSC2V` (rim `(x', f, r, g, x)`, `x' = (0,0,zp)`, `x = (0,0,zx)`, `f = (L,0,zf)`), `h = σ z`,
`h_x > h_{x'}` (`hzx`), and now `h_f < h_{x'}` (`hlo : σ(zf - zp) < 0`).  K_x = (x, f, r, g) has the SC2-V
shape (`ClassV2tail`: a top vertex over `f̄` / `f̄ = ḡ`, robust).  The lexicographic sector cycle of `Σ2`
(depth `h + s·c`, `c = S X - Y`, `S` large) is `x'` inserted strictly between `f` and `x` (Fact I (b)):
unimodal, so Theorem 24.1 (`isRupert_of_tilted_unimodal_σ`) gives Rupert.  No exception: R* needs `x' <_d f`,
which is excluded by `hlo` (strictly).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

def five {α : Type*} (p₀ p₁ p₂ p₃ p₄ : α) : ZMod 5 → α := ![p₀, p₁, p₂, p₃, p₄]
theorem five_0 {α : Type*} {p₀ p₁ p₂ p₃ p₄ : α} : five p₀ p₁ p₂ p₃ p₄ 0 = p₀ := rfl
theorem five_1 {α : Type*} {p₀ p₁ p₂ p₃ p₄ : α} : five p₀ p₁ p₂ p₃ p₄ 1 = p₁ := rfl
theorem five_2 {α : Type*} {p₀ p₁ p₂ p₃ p₄ : α} : five p₀ p₁ p₂ p₃ p₄ 2 = p₂ := rfl
theorem five_3 {α : Type*} {p₀ p₁ p₂ p₃ p₄ : α} : five p₀ p₁ p₂ p₃ p₄ 3 = p₃ := rfl
theorem five_4 {α : Type*} {p₀ p₁ p₂ p₃ p₄ : α} : five p₀ p₁ p₂ p₃ p₄ 4 = p₄ := rfl

theorem z5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  revert i; decide
theorem z5_add_one : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide
theorem z5_sub_one : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧
    (3 : ZMod 5) - 1 = 2 ∧ (4 : ZMod 5) - 1 = 3 := by decide

/-- Lexicographic `(a, c) < (b, d)`. -/
def LL (a c b d : ℝ) : Prop := a < b ∨ (a = b ∧ c < d)

theorem lex_ev {a c b d : ℝ} (h : LL a c b d) : ∀ᶠ s in 𝓝[>] (0 : ℝ), a + s * c < b + s * d := by
  have h' : 0 < (b - a) ∨ ((b - a) = 0 ∧ 0 < (d - c)) := by
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  filter_upwards [eventually_pos_affine h'] with s hs
  nlinarith

theorem qtop_ev (h c : ZMod 5 → ℝ) (p : ZMod 5)
    (H : ∀ i, i ≠ p → LL (h i) (c i) (h (i - 1)) (c (i - 1)) ∨ LL (h i) (c i) (h (i + 1)) (c (i + 1))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), QTop 5 fun i => h i + s * c i := by
  have : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i : ZMod 5, i ≠ p →
      (h i + s * c i < h (i - 1) + s * c (i - 1) ∨ h i + s * c i < h (i + 1) + s * c (i + 1)) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i = p
    · exact Filter.Eventually.of_forall fun s h' => absurd hi h'
    · rcases H i hi with h1 | h1
      · filter_upwards [lex_ev h1] with s hs _ using Or.inl hs
      · filter_upwards [lex_ev h1] with s hs _ using Or.inr hs
  filter_upwards [this] with s hs
  exact ⟨p, hs⟩

theorem sgn_pos {σ a b : ℝ} (hσσ : σ * σ = 1) (ha : 0 < σ * a) (hab : 0 < a * b) : 0 < σ * b := by
  have e : (σ * b) * (σ * a) = a * b := by linear_combination (a * b) * hσσ
  by_contra hn
  push_neg at hn
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hn ha.le]

theorem sgn_neg {σ a b : ℝ} (hσσ : σ * σ = 1) (ha : 0 < σ * a) (hab : a * b < 0) : σ * b < 0 := by
  have e : (σ * b) * (σ * a) = a * b := by linear_combination (a * b) * hσσ
  by_contra hn
  push_neg at hn
  nlinarith [mul_nonneg hn ha.le]

def ClassV2tail (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ((Xr = L ∧ zr = zf ∧ Yg < Yr ∧ 0 < (zg - zf) * (zx - zf)) ∨
   (Xg = L ∧ zg = zf ∧ Yr < Yg ∧ (zr - zf) * (zx - zf) < 0) ∨
   (Yg = Yr ∧ Xg = L ∧ zg = zf ∧ L < Xr ∧ (zr - zf) * (zx - zf) < 0))

end Type08Sp
end Minimality
