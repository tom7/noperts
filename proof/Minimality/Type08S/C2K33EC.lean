module

public import Minimality.Type08S.C2K33EB

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Type08Sp
open C2

set_option maxHeartbeats 4000000 in
theorem k32e_core_x4 (α β b g pp s qq qr rr : ℝ) (hα : 1 < α) (hβ : 1 < β)
    (hrel : α * s * (qq + rr - 2 * qr) = -(β - 1) * (qq * rr - qr ^ 2))
    (hW : 0 < qq + rr - 2 * qr)
    (hX4 : k32e_G pp s qq qr rr (α - 1) β 0 α 0 (β - 1) = 0) :
    (α + β - 1) * k32e_G pp s qq qr rr 1 (-b) (-g) ((1 - α) * s - β * qr) 0 (-((1 - α) * pp - β * s))
      = -(k32e_G pp s qq qr rr (1 - α) (-β) 0 (1 - α) 0 (-β)) *
        k32e_G pp s qq qr rr α (β - b) (-g) α 0 (β - 1) := by
  have hα0 : α ≠ 0 := by linarith
  have hα1 : α - 1 ≠ 0 := by linarith
  have hWne : qq + rr - 2 * qr ≠ 0 := hW.ne'
  have hsE : s = -(β - 1) * (qq * rr - qr ^ 2) / (α * (qq + rr - 2 * qr)) := by
    rw [eq_div_iff (by positivity)]; linear_combination hrel
  simp only [k32e_G] at hX4 ⊢
  have hppE : pp = -((α - 1) * (β - 1) * s + α * β * s + β * (β - 1) * qr)
      / (α * (α - 1)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hX4
  rw [hppE, hsE]
  field_simp
  ring

set_option maxHeartbeats 4000000 in
theorem k32e_core_x3 (α β b g pp s qq qr rr : ℝ) (hα : 1 < α) (hβ : 1 < β)
    (hrel : α * s * (qq + rr - 2 * qr) = -(β - 1) * (qq * rr - qr ^ 2))
    (hW : 0 < qq + rr - 2 * qr)
    (hX3 : k32e_G pp s qq qr rr (1 - α) (-β) 0 (1 - α) 0 (-β) = 0) :
    (α + β - 1) * k32e_G pp s qq qr rr 0 (-b) (1 - g) ((1 - α) * s - β * qr) 0 (-((1 - α) * pp - β * s))
      = -(k32e_G pp s qq qr rr (α - 1) β 0 α 0 (β - 1)) *
        k32e_G pp s qq qr rr 0 (-b) (1 - g) (1 - α) 0 (-β) := by
  have hα0 : α ≠ 0 := by linarith
  have hα1 : α - 1 ≠ 0 := by linarith
  have hWne : qq + rr - 2 * qr ≠ 0 := hW.ne'
  have hsE : s = -(β - 1) * (qq * rr - qr ^ 2) / (α * (qq + rr - 2 * qr)) := by
    rw [eq_div_iff (by positivity)]; linear_combination hrel
  simp only [k32e_G] at hX3 ⊢
  have h1a : 1 - α ≠ 0 := by intro h; apply hα1; linarith
  have hα2 : (1 - α) ^ 2 ≠ 0 := by positivity
  have hppE : pp = (2 * β * (1 - α) * s - β ^ 2 * qr) / (1 - α) ^ 2 := by
    rw [eq_div_iff hα2]
    linear_combination hX3
  rw [hppE, hsE]
  field_simp
  ring

end Type08Sp
end Minimality
