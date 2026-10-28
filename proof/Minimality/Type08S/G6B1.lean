module

public import Minimality.Type08TouchN2
public import Minimality.Type08TouchT4
public import Minimality.Type08
public import Minimality.Type08Codim
public import Minimality.Type08R0
public import Minimality.Type08Rd
public import Minimality.Type08Flat

@[expose] public section

set_option autoImplicit true

/-!
# G6' bridge, part 1: Gale brackets in normal-form coordinates (Fact 0.2 on H1, Lean form)
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem coef_zero {w u v : ℝ³} (hd : det3 w u v ≠ 0) {x y z : ℝ}
    (h : x • w + y • u + z • v = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  by_contra hn
  exact hd (det3_eq_zero_of_lin h hn)

/-- The four coordinate relations of an affine dependency, in the normal form of §41.0
(`c' = d + α w + β1 u`, `b' = d + α w + γ4 v`, `a' = d + β6 u + v`, `w,u,v = a-d,b-d,c-d`). -/
theorem dep_rel {a a' b b' c c' d : ℝ³} {l : ℝ³ → ℝ} (hl : IsDep a a' b b' c c' l)
    {α β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α • (a - d) + β1 • (b - d)) (hb' : b' = d + α • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (c - d)) :
    l a = -α * l c' - α * l b' ∧ l b = -β6 * l a' - β1 * l c' ∧ l c = - l a' - γ4 * l b' ∧
    -β6 * l a' + (1 - α - γ4) * l b' + (1 - α - β1) * l c' = 0 := by
  have h0 : (l a + α * l c' + α * l b') • (a - d) + (l b + β6 * l a' + β1 * l c') • (b - d) +
      (l c + l a' + γ4 * l b') • (c - d) = 0 := by
    have hv := hl.vsum
    have hs := hl.sum
    have e : l a • (a - d) + l a' • (a' - d) + l b • (b - d) + l b' • (b' - d) + l c • (c - d) +
        l c' • (c' - d) = 0 := by
      have : l a • (a - d) + l a' • (a' - d) + l b • (b - d) + l b' • (b' - d) + l c • (c - d) +
        l c' • (c' - d) = (l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c') -
          (l a + l a' + l b + l b' + l c + l c') • d := by
        simp only [smul_sub, add_smul]; abel
      rw [this, hv, hs]; simp
    have ha'd : a' - d = β6 • (b - d) + (c - d) := by rw [ha']; abel
    have hb'd : b' - d = α • (a - d) + γ4 • (c - d) := by rw [hb']; abel
    have hc'd : c' - d = α • (a - d) + β1 • (b - d) := by rw [hc']; abel
    rw [ha'd, hb'd, hc'd] at e
    rw [← e]
    module
  obtain ⟨h1, h2, h3⟩ := coef_zero hdet h0
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have := hl.sum
  nlinarith [this, h1, h2, h3]

theorem gale_coords {a a' b b' c c' d : ℝ³} (G : GaleData a a' b b' c c')
    {α β1 γ4 β6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α • (a - d) + β1 • (b - d)) (hb' : b' = d + α • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (c - d)) (hβ6 : β6 ≠ 0) :
    ∃ μ : ℝ, galeD G.l G.m a a' = μ * α * (γ4 - β1) ∧ galeD G.l G.m b b' = μ * β6 * (α - 1) := by
  obtain ⟨la, lb, lc, ls⟩ := dep_rel G.hl hdet hc' hb' ha'
  obtain ⟨ma, mb, mc, ms⟩ := dep_rel G.hm hdet hc' hb' ha'
  set Dbc := G.l b' * G.m c' - G.m b' * G.l c' with hDbc
  set Dca := G.l c' * G.m a' - G.m c' * G.l a' with hDca
  set Dab := G.l a' * G.m b' - G.m a' * G.l b' with hDab
  have e1 : Dca * (-β6) = Dbc * (1 - α - γ4) := by
    rw [hDca, hDbc]
    linear_combination (G.l c') * ms - (G.m c') * ls
  have e2 : Dab * (-β6) = Dbc * (1 - α - β1) := by
    rw [hDab, hDbc]
    linear_combination (-(G.l b')) * ms + (G.m b') * ls
  have hn : -β6 ≠ 0 := neg_ne_zero.mpr hβ6
  obtain ⟨μ, hμ⟩ : ∃ μ, μ * (-β6) = Dbc := ⟨Dbc / (-β6), div_mul_cancel₀ _ hn⟩
  have hca : Dca = μ * (1 - α - γ4) := mul_right_cancel₀ hn (by linear_combination e1 - (1 - α - γ4) * hμ)
  have hab : Dab = μ * (1 - α - β1) := mul_right_cancel₀ hn (by linear_combination e2 - (1 - α - β1) * hμ)
  refine ⟨μ, ?_, ?_⟩
  · unfold galeD
    rw [la, ma]
    linear_combination (-α) * hca + α * hab
  · unfold galeD
    rw [lb, mb]
    linear_combination (-β1) * hμ - β6 * hab

end Type08Sp
end Minimality
