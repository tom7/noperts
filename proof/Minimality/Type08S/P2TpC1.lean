module

public import Minimality.Type08S.P2TpC1T
public import Minimality.Type08S.P2TpEv

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X, cell C1 (Q_ac's top in `{d, c}`): the coordinate core
Rim `(d, a, b', c, a', b)`, tilt `t = (t1, t2)` in the cell `{n1·t > 0, n2·t > 0, n4·t < 0}`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 1600000 in
theorem tpX_C1 (hF : Fr e1 e2 e3) (o : ℝ³) {σ t1 t2 ν v1 ha w1 w3 C0 α4 γ4 β1 β6 γ6 : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hν : 0 < ν) (hha : 0 < ha) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hconv : 1 < β6 + γ6)
    (hv : σ * v1 < 0) (hp : 0 < σ * (ha * t1 - w1 * t2)) (ht2 : 0 < t2) (ht1 : t1 ≠ 0)
    (h2 : 0 < σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * t2))
    (hM : max w3 (α4 * w3 + γ4 * C0) < max 0 C0)
    (V : Finset ℝ³)
    (hV : ∀ y ∈ V, y = pt e1 e2 e3 o (-v1) 0 0 ∨ y = pt e1 e2 e3 o (-v1 + w1) ha w3 ∨
      y = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∨
      y = pt e1 e2 e3 o 0 0 C0 ∨ y = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) ∨
      y = pt e1 e2 e3 o (-v1) 0 ν ∨ y = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν))
    (m0 : pt e1 e2 e3 o (-v1) 0 0 ∈ V) (m1 : pt e1 e2 e3 o (-v1 + w1) ha w3 ∈ V)
    (m2 : pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∈ V)
    (m3 : pt e1 e2 e3 o 0 0 C0 ∈ V)
    (m4 : pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) ∈ V)
    (m5 : pt e1 e2 e3 o (-v1) 0 ν ∈ V) : IsRupert V := by
  have hv1 : v1 ≠ 0 := by rintro rfl; simp at hv
  refine rupert_of_coordRim hF o V (k := 6) (by norm_num) (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6) ?_
    σ hσ t1 t2 (tpC1_cyc hν hha hα4 hγ4 hE hβ6 hγ6 hγ61 hconv hv hp ht2 h2) ?_ ?_
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [m0, m1, m2, m3, m4, m5]
  · intro y hy
    rcases hV y hy with h | h | h | h | h | h | h
    · exact ⟨(-v1, 0, 0), h, Or.inl ⟨0, rfl⟩⟩
    · exact ⟨(-v1 + w1, ha, w3), h, Or.inl ⟨1, rfl⟩⟩
    · exact ⟨(-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0), h, Or.inl ⟨2, rfl⟩⟩
    · exact ⟨(0, 0, C0), h, Or.inl ⟨3, rfl⟩⟩
    · exact ⟨(-v1 * (1 - γ6), 0, γ6 * C0 + β6 * ν), h, Or.inl ⟨4, rfl⟩⟩
    · exact ⟨(-v1, 0, ν), h, Or.inl ⟨5, rfl⟩⟩
    · exact ⟨(-v1 + w1, ha, w3 + β1 * ν), h,
        Or.inr (tpC1_rest hν hha hα4 hγ4 hE hβ1 hγ6 hγ61 hv hp h2)⟩
  · -- depths
    have key : ∀ s : ℝ, (fun i => dep t1 t2 s (c1rim ν v1 ha w1 w3 C0 α4 γ4 β6 γ6 i)) =
        fun i => six 0 (w3 + s * (t1 * w1 + t2 * ha))
          (α4 * (w3 + s * (t1 * w1 + t2 * ha)) + γ4 * (C0 + s * (t1 * v1)))
          (C0 + s * (t1 * v1)) (γ6 * (C0 + s * (t1 * v1)) + β6 * ν) ν i + dep t1 t2 s (-v1, 0, 0) := by
      intro s
      funext i
      rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [c1rim, dep, six_0, six_1, six_2, six_3, six_4, six_5] <;> ring
    have hMs : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        max (w3 + s * (t1 * w1 + t2 * ha))
          (α4 * (w3 + s * (t1 * w1 + t2 * ha)) + γ4 * (C0 + s * (t1 * v1))) <
        max 0 (C0 + s * (t1 * v1)) :=
      ev_lt_cont (by fun_prop) (by fun_prop) (by simpa using hM)
    have hn1 := ev_ne_affine (A := γ6 * C0 + β6 * ν - ν) (B := γ6 * (t1 * v1))
      (Or.inr (mul_ne_zero hγ6.ne' (mul_ne_zero ht1 hv1)))
    have hn2 := ev_ne_affine (A := γ6 * C0 + β6 * ν - C0) (B := (γ6 - 1) * (t1 * v1))
      (Or.inr (mul_ne_zero (sub_ne_zero.2 hγ61.ne) (mul_ne_zero ht1 hv1)))
    filter_upwards [hMs, hn1, hn2] with s a1 a2 a3
    rw [key s]
    refine QTop_shift _ (tpU1 hν hα4 hγ4 hE hβ6 hγ6 hγ61 hconv a1 ?_ ?_)
    · intro h; apply a2; linarith
    · intro h; apply a3; linarith

end Type08Sp
end Minimality
