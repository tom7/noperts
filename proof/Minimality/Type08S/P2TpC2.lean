module

public import Minimality.Type08S.P2TpC2T
public import Minimality.Type08S.P2TpEv

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# T'X, cell C2 (Q_ac's top in `{a, b'}`): the coordinate core
Rim `(d, a, c', b', c)`, tilt `t = (t1, t2)` in the cell `{n1·t > 0, n2·t < 0, n4·t > 0}`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 1600000 in
theorem tpX_C2 (hF : Fr e1 e2 e3) (o : ℝ³) {σ t1 t2 ν v1 ha w1 w3 C0 α4 γ4 β1 β6 γ6 : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hν : 0 < ν) (hha : 0 < ha) (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hE : 1 < α4 + γ4) (hβ1 : 0 < β1)
    (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hv : σ * v1 < 0) (hp : 0 < σ * (ha * t1 - w1 * t2)) (ht2 : t2 < 0)
    (h2 : σ * ((α4 - 1) * ha * t1 - (γ4 * v1 + (α4 - 1) * w1) * t2) < 0)
    (hM : max 0 C0 < max w3 (α4 * w3 + γ4 * C0))
    (hne : (1 - α4) * w3 - γ4 * C0 + β1 * ν ≠ 0 ∨
      (1 - α4) * (t1 * w1 + t2 * ha) - γ4 * (t1 * v1) ≠ 0)
    (V : Finset ℝ³)
    (hV : ∀ y ∈ V, y = pt e1 e2 e3 o (-v1) 0 0 ∨ y = pt e1 e2 e3 o (-v1 + w1) ha w3 ∨
      y = pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) ∨
      y = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∨
      y = pt e1 e2 e3 o 0 0 C0 ∨ y = pt e1 e2 e3 o (-v1 * (1 - γ6)) 0 (γ6 * C0 + β6 * ν) ∨
      y = pt e1 e2 e3 o (-v1) 0 ν)
    (m0 : pt e1 e2 e3 o (-v1) 0 0 ∈ V) (m1 : pt e1 e2 e3 o (-v1 + w1) ha w3 ∈ V)
    (m2 : pt e1 e2 e3 o (-v1 + w1) ha (w3 + β1 * ν) ∈ V)
    (m3 : pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0) ∈ V)
    (m4 : pt e1 e2 e3 o 0 0 C0 ∈ V) : IsRupert V := by
  refine rupert_of_coordRim hF o V (k := 5) (by norm_num) (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν) ?_
    σ hσ t1 t2 (tpC2_cyc hν hha hα4 hγ4 hE hβ1 hv hp ht2 h2) ?_ ?_
  · intro i
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl
    exacts [m0, m1, m2, m3, m4]
  · intro y hy
    rcases hV y hy with h | h | h | h | h | h | h
    · exact ⟨(-v1, 0, 0), h, Or.inl ⟨0, rfl⟩⟩
    · exact ⟨(-v1 + w1, ha, w3), h, Or.inl ⟨1, rfl⟩⟩
    · exact ⟨(-v1 + w1, ha, w3 + β1 * ν), h, Or.inl ⟨2, rfl⟩⟩
    · exact ⟨(-v1 * (1 - γ4) + α4 * w1, α4 * ha, α4 * w3 + γ4 * C0), h, Or.inl ⟨3, rfl⟩⟩
    · exact ⟨(0, 0, C0), h, Or.inl ⟨4, rfl⟩⟩
    · exact ⟨(-v1 * (1 - γ6), 0, γ6 * C0 + β6 * ν), h,
        Or.inr fun i => (tpC2_rest hν hha hα4 hγ4 hE hβ1 hβ6 hγ6 hγ61 hv hp ht2 h2 i).1⟩
    · exact ⟨(-v1, 0, ν), h,
        Or.inr fun i => (tpC2_rest hν hha hα4 hγ4 hE hβ1 hβ6 hγ6 hγ61 hv hp ht2 h2 i).2⟩
  · have key : ∀ s : ℝ, (fun i => dep t1 t2 s (c2rim v1 ha w1 w3 C0 α4 γ4 β1 ν i)) =
        fun i => quint 0 (w3 + s * (t1 * w1 + t2 * ha))
          (w3 + s * (t1 * w1 + t2 * ha) + β1 * ν)
          (α4 * (w3 + s * (t1 * w1 + t2 * ha)) + γ4 * (C0 + s * (t1 * v1)))
          (C0 + s * (t1 * v1)) i + dep t1 t2 s (-v1, 0, 0) := by
      intro s
      funext i
      rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
        simp only [c2rim, dep, quint_0, quint_1, quint_2, quint_3, quint_4] <;> ring
    have hMs : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        max 0 (C0 + s * (t1 * v1)) <
        max (w3 + s * (t1 * w1 + t2 * ha))
          (α4 * (w3 + s * (t1 * w1 + t2 * ha)) + γ4 * (C0 + s * (t1 * v1))) :=
      ev_lt_cont (by fun_prop) (by fun_prop) (by simpa using hM)
    have hn1 := ev_ne_affine (A := (1 - α4) * w3 - γ4 * C0 + β1 * ν)
      (B := (1 - α4) * (t1 * w1 + t2 * ha) - γ4 * (t1 * v1)) hne
    filter_upwards [hMs, hn1] with s a1 a2
    rw [key s]
    refine QTop_shift _ (tpU2 hν hα4 hγ4 hE hβ1 a1 ?_)
    intro h; apply a2; linarith

end Type08Sp
end Minimality
