module

public import Minimality.CaseC18Tests
public import Minimality.RobustCert
public import Minimality.RimCert
public import Minimality.RimHDN
public import Minimality.Type08Cases

@[expose] public section

/-!
# Type 18, acute case (c): the vertex crossing `V` as a closing at a vertex view
(`FEWER-FACES-PROOFS.md` §27, continued (3) §0, §27, continued (4) 27.51)

`Frame7.rupert_vertex`: Theorem 18.1 in its tie form at a vertex view given in frame
coordinates (`isRupert_of_vertexView_robust`): a rim cycle `c` with strictly positive screen tests,
the remaining points either strictly inside or middles over a side, robustly unimodal depths and
no horizontal double normal at the view.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- The strict screen test (sign `σ`). -/
def PS (σ : ℝ) (u a b : C3) : Prop := 0 < σ * Dc a b u

theorem robust_add_const {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) (a : ℝ) :
    IsRobustUnimodal (fun i => z i + a) where
  noPeaks B a' b c d hab hbc hcd hdk h := hz.noPeaks B a' b c d hab hbc hcd hdk (by
    simp only [add_lt_add_iff_right] at h; exact h)
  noTriple i j l hij hjl hil e1 e2 := hz.noTriple i j l hij hjl hil
    (add_right_cancel e1) (add_right_cancel e2)
  noLevelRun B a' b c d hab hbc hcd hdk e := by
    have := hz.noLevelRun B a' b c d hab hbc hcd hdk (add_right_cancel e)
    simp only [add_lt_add_iff_right]; exact this

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

lemma fvC_lin (a u : C3) (s δ : ℝ) :
    F.fvC ⟨s * a.x + δ * u.x, s * a.y + δ * u.y, s * a.z + δ * u.z⟩ =
      s • F.fvC a + δ • F.fvC u := by
  simp only [fvC]; module

end Frame7

namespace Shape18
variable (S : Shape18)

/-- The view of `V`, scaled by `1 - s+`: `(t+ (1 - s+), 0, h+ (1 - s+) - k+)` (frame coordinates). -/
def uV : C3 := ⟨-S.sp * S.tp + S.tp, 0, -S.hp * S.sp + S.hp - S.kp⟩

/-- `φ(m1-)` along the view of `V`, in the normalization of `uV`. -/
noncomputable def Vp : ℝ := (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm

/-- The upper middle `v` of `F1` lies over the open chord `(m1+, m1-)`. -/
lemma mid_v (hV : 0 < S.Vp) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ 0 = S.tp + s * (S.tm - S.tp) + δ * S.uV.x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * S.uV.z := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have hkp := S.kp_pos
  have hsp1 := S.sp_lt
  have hux : 0 < -S.sp * S.tp + S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hden : 0 < S.Vp + S.tp * S.kp := by positivity
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = S.tp * S.kp / (S.Vp + S.tp * S.kp) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos (mul_pos htp hkp) hden
  have hs1 : s < 1 := by rw [hsdef, div_lt_one hden]; nlinarith
  have hPx : 0 < S.tp + s * (S.tm - S.tp) := by
    rcases le_or_gt S.tp S.tm with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h hs0.le]
    · nlinarith [mul_pos hs0 (sub_pos.2 h)]
  have hs : s * (S.Vp + S.tp * S.kp) = S.tp * S.kp := by rw [hsdef]; field_simp
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = -(S.tp + s * (S.tm - S.tp)) / (-S.sp * S.tp + S.tp) := ⟨_, rfl⟩
  have hδ : δ * (-S.sp * S.tp + S.tp) = -(S.tp + s * (S.tm - S.tp)) := by
    rw [hδdef]; exact div_mul_cancel₀ _ hux.ne'
  refine ⟨s, δ, hs0, hs1, ?_, ?_, ?_⟩
  · rw [hδdef]; exact div_ne_zero (by linarith) hux.ne'
  · simp only [uV]; linarith
  · apply mul_left_cancel₀ hux.ne'
    simp only [uV, Vp] at hs hδ ⊢
    linear_combination (-(-S.hp * S.sp + S.hp - S.kp)) * hδ + hs

end Shape18

theorem quadTie_of_nws {z0 z1 z2 z3 : ℝ} (hA : z0 < z1 ∨ z0 < z3 ∨ z2 < z1 ∨ z2 < z3)
    (hB : z1 < z0 ∨ z3 < z0 ∨ z1 < z2 ∨ z3 < z2) : QuadTie z0 z1 z2 z3 := by
  unfold QuadTie
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  all_goals
    rintro ⟨e1, e2, e3⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith

theorem robust_quad_of_nws {z0 z1 z2 z3 : ℝ} (hA : z0 < z1 ∨ z0 < z3 ∨ z2 < z1 ∨ z2 < z3)
    (hB : z1 < z0 ∨ z3 < z0 ∨ z1 < z2 ∨ z3 < z2) : IsRobustUnimodal (quad z0 z1 z2 z3) := by
  refine isRobustUnimodal_quad (quadTie_of_nws hA hB) ?_ ?_
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    rcases hA with k | k | k | k <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    rcases hB with k | k | k | k <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]

namespace Shape18
variable (S : Shape18)

/-- The sign of the border `D2` between the rims of `V` (`D2 = tp tm (1-sp)(1-sm) (A1 - μ+ - μ-)`,
cleared of denominators). -/
noncomputable def D2p : ℝ :=
  (1 - S.sm) * (1 - S.sp) * (S.hm * S.tp + S.hp * S.tm) - S.km * S.tp * (1 - S.sp) -
    S.kp * S.tm * (1 - S.sm)

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

lemma ptC_0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [toFrame7, pt]
lemma ptC_1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [toFrame7, pt]
lemma ptC_2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [toFrame7, pt]
lemma ptC_3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [toFrame7, pt]
lemma ptC_4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [toFrame7, pt]
lemma ptC_5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [toFrame7, pt]
lemma ptC_6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [toFrame7, pt]

/-- The depth of the point `j` along the view of `V`. -/
noncomputable def dV (j : Fin 7) : ℝ := F.toFrame7.GG (F.toFrame7.ptC j) F.S.uV

lemma dV_0 : F.dV 0 = F.a11 * (F.S.tp * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (F.S.hp * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, ptC_0, GG_eq, Shape18.uV]; ring
lemma dV_6 : F.dV 6 = F.a11 * (F.S.tm * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (-F.S.hm * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, ptC_6, GG_eq, Shape18.uV]; ring

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- The depth of the point `j` along the view of `T_A` (`m1+ - xa`). -/
noncomputable def dA (j : Fin 7) : ℝ := F.toFrame7.GG (F.toFrame7.ptC j) ⟨F.S.tp - 1, 0, F.S.hp⟩

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

end Frame18

end Minimality.CaseC18

end
