module

public import Minimality.Type16SAT.Cls16W
public import Minimality.Type16NF

@[expose] public section

/-!
# Type 16: the class vectors with `[1234] >= 0` and `[0134]` or `[2346]` not negative do not occur

In the normal form of type 16 (`x 3 = o`, `x 0 = o + E₁`, `x 5 = o + E₂`, `x 6 = o + E₃`, `x 2 = (a, b, 0)`,
`x 1 = (0, g, d)`, `x 4 = (p, q, r)`, with `a b g d p q r > 0`) the chirality bracket is `C = D = det (E₁, E₂, E₃)` and
the other four brackets are `D` times

* `[0126] = b (d - 1) - g (a - 1)`,
* `[0134] = g r - d q`,
* `[1234] = a (d q - g r) - b d p`,
* `[2346] = b p - a q`.

Since `[1234] = -a [0134] - b d p` and `a d q >= b d p + a g r` when `[1234] >= 0`, if `C * [1234] >= 0` then
`C * [0134] < 0` and `C * [2346] < 0`.  The six strict sign vectors `++++ +++- +-++ -+++ -++- --++` are among the vectors this excludes
(they all have `C * [1234] > 0` with `C * [0134] > 0` or `C * [2346] > 0`), and so are all vectors with `C * [1234] >= 0`
and a zero or positive `C * [0134]` or `C * [2346]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality

namespace Minimality.H16.SAT

theorem cls16_brackets_nf {x : Fin 7 → ℝ³} (N : NF16 x) :
    C16 x * br16 x 0 1 2 6 = (N.b * (N.d - 1) - N.g * (N.a - 1)) * det3 N.E₁ N.E₂ N.E₃ ^ 2 ∧
    C16 x * br16 x 0 1 3 4 = (N.g * N.r - N.d * N.q) * det3 N.E₁ N.E₂ N.E₃ ^ 2 ∧
    C16 x * br16 x 1 2 3 4 = (N.a * (N.d * N.q - N.g * N.r) - N.b * N.d * N.p) * det3 N.E₁ N.E₂ N.E₃ ^ 2 ∧
    C16 x * br16 x 2 3 4 6 = (N.b * N.p - N.a * N.q) * det3 N.E₁ N.E₂ N.E₃ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [C16, br16, N.x0, N.x1, N.x2, N.x3, N.x4, N.x5, N.x6, nfP_sub, det3_nfV, det3c]
    ring

/-- **The sign relations among the class brackets.**  If `C * [1234] >= 0` then `C * [0134] < 0` and `C * [2346] < 0`. -/
theorem cls16_s3_nonneg {x : Fin 7 → ℝ³} (T : Type16 x) (h : 0 ≤ C16 x * br16 x 1 2 3 4) :
    C16 x * br16 x 0 1 3 4 < 0 ∧ C16 x * br16 x 2 3 4 6 < 0 := by
  have N := T.toNF
  obtain ⟨-, e2, e3, e4⟩ := cls16_brackets_nf N
  have hD2 : 0 < det3 N.E₁ N.E₂ N.E₃ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 N.hD))
  have ha := N.ha
  have hb := N.hb
  have hg := N.hg
  have hd := N.hd
  have hp := N.hp
  have hq := N.hq
  have hr := N.hr
  rw [e3] at h
  have h' : 0 ≤ N.a * (N.d * N.q - N.g * N.r) - N.b * N.d * N.p := nonneg_of_mul_nonneg_left h hD2
  rw [e2, e4]
  have hbd : 0 < N.b * N.d * N.p := by positivity
  have hag : 0 < N.a * N.g * N.r := by positivity
  constructor
  · apply mul_neg_of_neg_of_pos _ hD2
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg ha.le hc]
  · apply mul_neg_of_neg_of_pos _ hD2
    -- a d q >= b d p + a g r > b d p, so a q > b p
    have h1 : N.d * (N.b * N.p - N.a * N.q) < 0 := by nlinarith
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hd.le hc]

/-- The excluded class vectors: `C * [1234] >= 0` with `C * [0134] >= 0` or `C * [2346] >= 0` (in particular the six strict
vectors `++++ +++- +-++ -+++ -++- --++`). -/
def Cls16Dead (x : Fin 7 → ℝ³) : Prop :=
  0 ≤ C16 x * br16 x 1 2 3 4 ∧ (0 ≤ C16 x * br16 x 0 1 3 4 ∨ 0 ≤ C16 x * br16 x 2 3 4 6)

/-- **No type 16 configuration has a class vector in `Cls16Dead`.** -/
theorem not_cls16Dead {x : Fin 7 → ℝ³} (T : Type16 x) (h : Cls16Dead x) : False := by
  obtain ⟨h3, h24⟩ := h
  obtain ⟨n2, n4⟩ := cls16_s3_nonneg T h3
  rcases h24 with h | h <;> linarith

/-- A sign vector with `C * [1234]` zero or positive and `C * [0134]` or `C * [2346]` zero or positive is in `Cls16Dead`. -/
theorem cls16Dead_of_vec {e1 e2 e3 e4 : ℝ} {x : Fin 7 → ℝ³} (hv : Vec16 e1 e2 e3 e4 x)
    (h3 : e3 = 0 ∨ e3 = 1) (h24 : e2 = 0 ∨ e2 = 1 ∨ e4 = 0 ∨ e4 = 1) : Cls16Dead x := by
  have key : ∀ (e b : ℝ), (e = 0 ∨ e = 1) → SgnP e b → 0 ≤ b := by
    intro e b he h
    rcases he with rfl | rfl <;> simp [SgnP] at h
    · exact h.ge
    · exact h.le
  obtain ⟨-, s2, s3, s4⟩ := hv
  refine ⟨key _ _ h3 s3, ?_⟩
  rcases h24 with h | h | h | h
  · exact Or.inl (key _ _ (Or.inl h) s2)
  · exact Or.inl (key _ _ (Or.inr h) s2)
  · exact Or.inr (key _ _ (Or.inl h) s4)
  · exact Or.inr (key _ _ (Or.inr h) s4)

end Minimality.H16.SAT
