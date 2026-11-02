module

public import Minimality.Type21Sl2C

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-- The facing pattern `pat` (true = up) gives the cycle `c` as an up/down silhouette: every edge
`c i → c (i+1)` lies in an up facet `a` and a down facet `b` and every other vertex is off one. -/
def h21b_CycOK {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (pat : Fin 8 → Bool) : Prop :=
  ∀ i, ∃ a b : Fin 8, pat a = true ∧ pat b = false ∧ c i ∈ h21S a ∧ c i ∈ h21S b ∧
    c (i + 1) ∈ h21S a ∧ c (i + 1) ∈ h21S b ∧
    ∀ m : Fin 7, m ≠ c i → m ≠ c (i + 1) → m ∉ h21S a ∨ m ∉ h21S b

instance {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (pat : Fin 8 → Bool) :
    Decidable (h21b_CycOK c pat) := by unfold h21b_CycOK; infer_instance

/-- The lex facings of all eight facets at `(u, v)` follow the pattern. -/
def h21b_FacOK (F : Fac8 x) (pat : Fin 8 → Bool) (u v : ℝ³) : Prop :=
  ∀ t, (pat t = true → h21b_LP ⟪F.N t, u⟫ ⟪F.N t, v⟫) ∧
    (pat t = false → h21b_LP (-⟪F.N t, u⟫) (-⟪F.N t, v⟫))

theorem h21b_silL {k : ℕ} [NeZero k] (F : Fac8 x) {c : ZMod k → Fin 7} {pat : Fin 8 → Bool}
    {u v : ℝ³} (hcyc : h21b_CycOK c pat) (hfac : h21b_FacOK F pat u v) :
    Nonempty (h21b_SilDataL k x c u v) := by
  choose ea eb hea heb h0a h0b h1a h1b hs using hcyc
  exact ⟨{
    A := fun i => F.N (ea i)
    B := fun i => F.N (eb i)
    fA := fun i => F.f (ea i)
    fB := fun i => F.f (eb i)
    hA := fun i => F.hN (ea i)
    hB := fun i => F.hN (eb i)
    zA0 := fun i => F.zero _ _ (h0a i)
    zA1 := fun i => F.zero _ _ (h1a i)
    zB0 := fun i => F.zero _ _ (h0b i)
    zB1 := fun i => F.zero _ _ (h1b i)
    nA := fun i m => F.le _ m
    nB := fun i m => F.le _ m
    strict := fun i m a b => by
      rcases hs i m a b with h | h
      · exact Or.inl (F.neg _ _ h)
      · exact Or.inr (F.neg _ _ h)
    up := fun i => (hfac (ea i)).1 (hea i)
    dn := fun i => (hfac (eb i)).2 (heb i) }⟩

/-- A tilt with the prescribed facings of the two edge-on facets `X`, `Y` that separates the cycle
points. -/
theorem h21b_exists_v {k : ℕ} [NeZero k] (F : Fac8 x) (hx : Function.Injective x)
    {c : ZMod k → Fin 7} (hc : Function.Injective c) {pat : Fin 8 → Bool} {X Y : Fin 8}
    {v1 v2 u : ℝ³}
    (h1 : ⟪F.N X, v1⟫ < 0) (h1' : ⟪F.N Y, v1⟫ = 0) (h2 : ⟪F.N X, v2⟫ = 0) (h2' : ⟪F.N Y, v2⟫ < 0)
    (hX : ⟪F.N X, u⟫ = 0) (hY : ⟪F.N Y, u⟫ = 0)
    (hstr : ∀ t, t ≠ X → t ≠ Y → (pat t = true → 0 < ⟪F.N t, u⟫) ∧ (pat t = false → ⟪F.N t, u⟫ < 0)) :
    ∃ v, h21b_FacOK F pat u v ∧ ∀ i j : ZMod k, i ≠ j → ⟪x (c i), v⟫ ≠ ⟪x (c j), v⟫ := by
  have hXY : X ≠ Y := by
    intro e; subst e
    have := h2'; rw [h2] at this; exact lt_irrefl _ this
  set sX : ℝ := if pat X = true then 1 else -1 with hsX
  set sY : ℝ := if pat Y = true then 1 else -1 with hsY
  have sX2 : sX * sX = 1 := by rw [hsX]; split_ifs <;> norm_num
  have sY2 : sY * sY = 1 := by rw [hsY]; split_ifs <;> norm_num
  let O : Set ℝ³ := {v | 0 < sX * ⟪F.N X, v⟫ ∧ 0 < sY * ⟪F.N Y, v⟫}
  have c1 : Continuous fun v : ℝ³ => sX * ⟪F.N X, v⟫ := by fun_prop
  have c2 : Continuous fun v : ℝ³ => sY * ⟪F.N Y, v⟫ := by fun_prop
  have hO : IsOpen O := (isOpen_lt continuous_const c1).inter (isOpen_lt continuous_const c2)
  have hne : O.Nonempty := by
    refine ⟨(-sX) • v1 + (-sY) • v2, ?_, ?_⟩
    · simp only [inner_add_right, inner_smul_right, h2, h1]
      nlinarith
    · simp only [inner_add_right, inner_smul_right, h1', h2']
      nlinarith
  let ι := {p : ZMod k × ZMod k // p.1 ≠ p.2}
  obtain ⟨v, hvO, hv⟩ := exists_avoid_kernels (E := ℝ³) (ι := ι)
    (fun p => (innerSL ℝ (x (c p.1.1) - x (c p.1.2))).toLinearMap)
    (by
      intro p h
      have hne : x (c p.1.1) - x (c p.1.2) ≠ 0 := sub_ne_zero.2 fun e => p.2 (hc (hx e))
      have := LinearMap.congr_fun h (x (c p.1.1) - x (c p.1.2))
      exact hne (inner_self_eq_zero.1 this)) hO hne
  refine ⟨v, ?_, fun i j hij e => hv ⟨(i, j), hij⟩ ?_⟩
  · have hpos : ∀ t, t = X → (pat X = true → 0 < ⟪F.N X, v⟫) ∧ (pat X = false → ⟪F.N X, v⟫ < 0) := by
      intro t ht; subst ht
      obtain ⟨a, -⟩ := hvO
      constructor
      · intro h; rw [hsX, if_pos h] at a; linarith
      · intro h; rw [hsX, if_neg (by simp [h])] at a; linarith
    have hposY : (pat Y = true → 0 < ⟪F.N Y, v⟫) ∧ (pat Y = false → ⟪F.N Y, v⟫ < 0) := by
      obtain ⟨-, b⟩ := hvO
      constructor
      · intro h; rw [hsY, if_pos h] at b; linarith
      · intro h; rw [hsY, if_neg (by simp [h])] at b; linarith
    intro t
    by_cases htX : t = X
    · subst htX
      obtain ⟨p1, p2⟩ := hpos _ rfl
      refine ⟨fun h => Or.inr ⟨hX, p1 h⟩, fun h => Or.inr ⟨by rw [hX]; simp, by linarith [p2 h]⟩⟩
    by_cases htY : t = Y
    · subst htY
      refine ⟨fun h => Or.inr ⟨hY, hposY.1 h⟩, fun h => Or.inr ⟨by rw [hY]; simp, by linarith [hposY.2 h]⟩⟩
    obtain ⟨s1, s2⟩ := hstr t htX htY
    exact ⟨fun h => Or.inl (s1 h), fun h => Or.inl (by linarith [s2 h])⟩
  · simp [inner_sub_left, e]

end H21
end Minimality
