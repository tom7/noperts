module

public import Minimality.Type08S.P2RKBridge
public import Minimality.Type08S.P2RKCell_ppp
public import Minimality.Type08S.P2RKCell_mmm
public import Minimality.Type08S.P2RKCell_pmp
public import Minimality.Type08S.P2RKCell_pmm
public import Minimality.Type08S.P2RKCell_mpp
public import Minimality.Type08S.P2RKCell_mpm

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K, export: the six cell sign patterns in the T frame (`G6J4.h3_setup`).
Frame data as produced by `h3_setup` (coordinates `pt e1 e2 e3 o X Y z`, `b - d = ν • e3`), orientation `σ = ±1`
with `σ v1 < 0`, tilt vector `v = pc e1 e2 e3 t1 t2 t3` (`t3` is irrelevant for the `TiltSign` tests).
With `L1 = σ (w1 t2 - ha t1)` (side `[q, c̄']`), `L4 = - σ v1 t2` (side `[q', q]`),
`L3 = - σ v1 (γ4-1) t2 - α4 L1` (side `[b̄', q']`) the map.md sign is `s_i = - sign L_i`.
The conclusion `TiltTests V (orient σ x) (b - d) v` is the `hcyc`/`hrest` part of `LexCell` for the cycle
`orient σ x` (`x` itself if `σ = 1`, reversed if `σ = -1`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 3200000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace K

theorem K_ppp {a a' b b' c c' d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 σ t1 t2 t3 : ℝ}
    (hF : Fr e1 e2 e3) (hσ : σ = 1 ∨ σ = -1) (hν : 0 < ν) (hv : σ * v1 < 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3) (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν)) (hu : b - d = ν • e3)
    (hp1 : 0 < -(σ * (w1 * t2 - ha * t1)))
    (hp3 : 0 < -(-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))))
    (hp4 : 0 < -(-(σ * v1) * t2)) :
    TiltTests (V8 a a' b b' c c' d) (orient σ (cyc5 d a c' b' c)) (b - d) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ v1 = -(σ * r) := ⟨-(σ * v1), by linarith, by linear_combination (-v1) * hσ2⟩
  obtain ⟨W, rfl⟩ : ∃ W, w1 = σ * W := ⟨σ * w1, by linear_combination (-w1) * hσ2⟩
  have core := cell_ppp (r := r) (W := W) (T1 := σ * t1) (t2 := t2) (w3 := w3) (C0 := C0) (ν := ν) (ha := ha)
    (α1 := α1) (α4 := α4) (γ4 := γ4) (β1 := β1) (β6 := β6) hr hν hha hα hα4 hγ4 hβ1 hβ6 hE
    (by rcases hσ with rfl | rfl <;> linarith [hp1]) (by rcases hσ with rfl | rfl <;> linarith [hp3])
    (by rcases hσ with rfl | rfl <;> linarith [hp4])
  have e_0 : d = pr e1 e2 e3 o (unm σ (kd r)) := by rw [hd]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_1 : a = pr e1 e2 e3 o (unm σ (ka r W ha w3)) := by rw [ha_]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_2 : a' = pr e1 e2 e3 o (unm σ (ka' ν β6 C0)) := by rw [ha']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_3 : b = pr e1 e2 e3 o (unm σ (kb r ν)) := by rw [hb]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_4 : b' = pr e1 e2 e3 o (unm σ (kb' r W ha w3 C0 α4 γ4)) := by rw [hb']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_5 : c = pr e1 e2 e3 o (unm σ (kc C0)) := by rw [hc]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_6 : c' = pr e1 e2 e3 o (unm σ (kc' r W ha w3 ν α1 β1)) := by rw [hc']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  rw [hu]
  subst e_0 e_1 e_2 e_3 e_4 e_5 e_6
  refine wrapK hF o hσ hν t1 t2 t3 (cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) _ (fun i => ?_) _ core.1 ?_
  · rcases z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro y hy hyx
    simp only [V8, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 rfl).elim
    · exact (hyx 1 rfl).elim
    · exact ⟨(ka' ν β6 C0), rfl, core.2.1⟩
    · exact ⟨(kb r ν), rfl, core.2.2⟩
    · exact (hyx 3 rfl).elim
    · exact (hyx 4 rfl).elim
    · exact (hyx 2 rfl).elim

theorem K_mmm {a a' b b' c c' d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 σ t1 t2 t3 : ℝ}
    (hF : Fr e1 e2 e3) (hσ : σ = 1 ∨ σ = -1) (hν : 0 < ν) (hv : σ * v1 < 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3) (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν)) (hu : b - d = ν • e3)
    (hp1 : 0 < (σ * (w1 * t2 - ha * t1)))
    (hp3 : 0 < (-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))))
    (hp4 : 0 < (-(σ * v1) * t2)) :
    TiltTests (V8 a a' b b' c c' d) (orient σ (cyc4 b c' b' a')) (b - d) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ v1 = -(σ * r) := ⟨-(σ * v1), by linarith, by linear_combination (-v1) * hσ2⟩
  obtain ⟨W, rfl⟩ : ∃ W, w1 = σ * W := ⟨σ * w1, by linear_combination (-w1) * hσ2⟩
  have core := cell_mmm (r := r) (W := W) (T1 := σ * t1) (t2 := t2) (w3 := w3) (C0 := C0) (ν := ν) (ha := ha)
    (α1 := α1) (α4 := α4) (γ4 := γ4) (β1 := β1) (β6 := β6) hr hν hha hα hα4 hγ4 hβ1 hβ6 hE
    (by rcases hσ with rfl | rfl <;> linarith [hp1]) (by rcases hσ with rfl | rfl <;> linarith [hp3])
    (by rcases hσ with rfl | rfl <;> linarith [hp4])
  have e_0 : d = pr e1 e2 e3 o (unm σ (kd r)) := by rw [hd]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_1 : a = pr e1 e2 e3 o (unm σ (ka r W ha w3)) := by rw [ha_]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_2 : a' = pr e1 e2 e3 o (unm σ (ka' ν β6 C0)) := by rw [ha']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_3 : b = pr e1 e2 e3 o (unm σ (kb r ν)) := by rw [hb]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_4 : b' = pr e1 e2 e3 o (unm σ (kb' r W ha w3 C0 α4 γ4)) := by rw [hb']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_5 : c = pr e1 e2 e3 o (unm σ (kc C0)) := by rw [hc]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_6 : c' = pr e1 e2 e3 o (unm σ (kc' r W ha w3 ν α1 β1)) := by rw [hc']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  rw [hu]
  subst e_0 e_1 e_2 e_3 e_4 e_5 e_6
  refine wrapK hF o hσ hν t1 t2 t3 (cyc4 (kb r ν) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (ka' ν β6 C0)) _ (fun i => ?_) _ core.1 ?_
  · rcases z4c i with rfl | rfl | rfl | rfl <;> rfl
  · intro y hy hyx
    simp only [V8, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(kd r), rfl, core.2.1⟩
    · exact ⟨(ka r W ha w3), rfl, core.2.2.1⟩
    · exact (hyx 3 rfl).elim
    · exact (hyx 0 rfl).elim
    · exact (hyx 2 rfl).elim
    · exact ⟨(kc C0), rfl, core.2.2.2⟩
    · exact (hyx 1 rfl).elim

theorem K_pmp {a a' b b' c c' d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 σ t1 t2 t3 : ℝ}
    (hF : Fr e1 e2 e3) (hσ : σ = 1 ∨ σ = -1) (hν : 0 < ν) (hv : σ * v1 < 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3) (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν)) (hu : b - d = ν • e3)
    (hp1 : 0 < -(σ * (w1 * t2 - ha * t1)))
    (hp3 : 0 < (-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))))
    (hp4 : 0 < -(-(σ * v1) * t2)) :
    TiltTests (V8 a a' b b' c c' d) (orient σ (cyc6 d a c' b' a' c)) (b - d) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ v1 = -(σ * r) := ⟨-(σ * v1), by linarith, by linear_combination (-v1) * hσ2⟩
  obtain ⟨W, rfl⟩ : ∃ W, w1 = σ * W := ⟨σ * w1, by linear_combination (-w1) * hσ2⟩
  have core := cell_pmp (r := r) (W := W) (T1 := σ * t1) (t2 := t2) (w3 := w3) (C0 := C0) (ν := ν) (ha := ha)
    (α1 := α1) (α4 := α4) (γ4 := γ4) (β1 := β1) (β6 := β6) hr hν hha hα hα4 hγ4 hβ1 hβ6 hE
    (by rcases hσ with rfl | rfl <;> linarith [hp1]) (by rcases hσ with rfl | rfl <;> linarith [hp3])
    (by rcases hσ with rfl | rfl <;> linarith [hp4])
  have e_0 : d = pr e1 e2 e3 o (unm σ (kd r)) := by rw [hd]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_1 : a = pr e1 e2 e3 o (unm σ (ka r W ha w3)) := by rw [ha_]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_2 : a' = pr e1 e2 e3 o (unm σ (ka' ν β6 C0)) := by rw [ha']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_3 : b = pr e1 e2 e3 o (unm σ (kb r ν)) := by rw [hb]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_4 : b' = pr e1 e2 e3 o (unm σ (kb' r W ha w3 C0 α4 γ4)) := by rw [hb']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_5 : c = pr e1 e2 e3 o (unm σ (kc C0)) := by rw [hc]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_6 : c' = pr e1 e2 e3 o (unm σ (kc' r W ha w3 ν α1 β1)) := by rw [hc']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  rw [hu]
  subst e_0 e_1 e_2 e_3 e_4 e_5 e_6
  refine wrapK hF o hσ hν t1 t2 t3 (cyc6 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (ka' ν β6 C0) (kc C0)) _ (fun i => ?_) _ core.1 ?_
  · rcases z6c i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro y hy hyx
    simp only [V8, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 rfl).elim
    · exact (hyx 1 rfl).elim
    · exact (hyx 4 rfl).elim
    · exact ⟨(kb r ν), rfl, core.2⟩
    · exact (hyx 3 rfl).elim
    · exact (hyx 5 rfl).elim
    · exact (hyx 2 rfl).elim

theorem K_pmm {a a' b b' c c' d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 σ t1 t2 t3 : ℝ}
    (hF : Fr e1 e2 e3) (hσ : σ = 1 ∨ σ = -1) (hν : 0 < ν) (hv : σ * v1 < 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3) (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν)) (hu : b - d = ν • e3)
    (hp1 : 0 < -(σ * (w1 * t2 - ha * t1)))
    (hp3 : 0 < (-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))))
    (hp4 : 0 < (-(σ * v1) * t2)) :
    TiltTests (V8 a a' b b' c c' d) (orient σ (cyc6 a' b d a c' b')) (b - d) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ v1 = -(σ * r) := ⟨-(σ * v1), by linarith, by linear_combination (-v1) * hσ2⟩
  obtain ⟨W, rfl⟩ : ∃ W, w1 = σ * W := ⟨σ * w1, by linear_combination (-w1) * hσ2⟩
  have core := cell_pmm (r := r) (W := W) (T1 := σ * t1) (t2 := t2) (w3 := w3) (C0 := C0) (ν := ν) (ha := ha)
    (α1 := α1) (α4 := α4) (γ4 := γ4) (β1 := β1) (β6 := β6) hr hν hha hα hα4 hγ4 hβ1 hβ6 hE
    (by rcases hσ with rfl | rfl <;> linarith [hp1]) (by rcases hσ with rfl | rfl <;> linarith [hp3])
    (by rcases hσ with rfl | rfl <;> linarith [hp4])
  have e_0 : d = pr e1 e2 e3 o (unm σ (kd r)) := by rw [hd]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_1 : a = pr e1 e2 e3 o (unm σ (ka r W ha w3)) := by rw [ha_]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_2 : a' = pr e1 e2 e3 o (unm σ (ka' ν β6 C0)) := by rw [ha']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_3 : b = pr e1 e2 e3 o (unm σ (kb r ν)) := by rw [hb]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_4 : b' = pr e1 e2 e3 o (unm σ (kb' r W ha w3 C0 α4 γ4)) := by rw [hb']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_5 : c = pr e1 e2 e3 o (unm σ (kc C0)) := by rw [hc]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_6 : c' = pr e1 e2 e3 o (unm σ (kc' r W ha w3 ν α1 β1)) := by rw [hc']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  rw [hu]
  subst e_0 e_1 e_2 e_3 e_4 e_5 e_6
  refine wrapK hF o hσ hν t1 t2 t3 (cyc6 (ka' ν β6 C0) (kb r ν) (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4)) _ (fun i => ?_) _ core.1 ?_
  · rcases z6c i with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro y hy hyx
    simp only [V8, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 2 rfl).elim
    · exact (hyx 3 rfl).elim
    · exact (hyx 0 rfl).elim
    · exact (hyx 1 rfl).elim
    · exact (hyx 5 rfl).elim
    · exact ⟨(kc C0), rfl, core.2⟩
    · exact (hyx 4 rfl).elim

theorem K_mpp {a a' b b' c c' d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 σ t1 t2 t3 : ℝ}
    (hF : Fr e1 e2 e3) (hσ : σ = 1 ∨ σ = -1) (hν : 0 < ν) (hv : σ * v1 < 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3) (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν)) (hu : b - d = ν • e3)
    (hp1 : 0 < (σ * (w1 * t2 - ha * t1)))
    (hp3 : 0 < -(-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))))
    (hp4 : 0 < -(-(σ * v1) * t2)) :
    TiltTests (V8 a a' b b' c c' d) (orient σ (cyc5 b c' b' c d)) (b - d) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ v1 = -(σ * r) := ⟨-(σ * v1), by linarith, by linear_combination (-v1) * hσ2⟩
  obtain ⟨W, rfl⟩ : ∃ W, w1 = σ * W := ⟨σ * w1, by linear_combination (-w1) * hσ2⟩
  have core := cell_mpp (r := r) (W := W) (T1 := σ * t1) (t2 := t2) (w3 := w3) (C0 := C0) (ν := ν) (ha := ha)
    (α1 := α1) (α4 := α4) (γ4 := γ4) (β1 := β1) (β6 := β6) hr hν hha hα hα4 hγ4 hβ1 hβ6 hE
    (by rcases hσ with rfl | rfl <;> linarith [hp1]) (by rcases hσ with rfl | rfl <;> linarith [hp3])
    (by rcases hσ with rfl | rfl <;> linarith [hp4])
  have e_0 : d = pr e1 e2 e3 o (unm σ (kd r)) := by rw [hd]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_1 : a = pr e1 e2 e3 o (unm σ (ka r W ha w3)) := by rw [ha_]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_2 : a' = pr e1 e2 e3 o (unm σ (ka' ν β6 C0)) := by rw [ha']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_3 : b = pr e1 e2 e3 o (unm σ (kb r ν)) := by rw [hb]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_4 : b' = pr e1 e2 e3 o (unm σ (kb' r W ha w3 C0 α4 γ4)) := by rw [hb']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_5 : c = pr e1 e2 e3 o (unm σ (kc C0)) := by rw [hc]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_6 : c' = pr e1 e2 e3 o (unm σ (kc' r W ha w3 ν α1 β1)) := by rw [hc']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  rw [hu]
  subst e_0 e_1 e_2 e_3 e_4 e_5 e_6
  refine wrapK hF o hσ hν t1 t2 t3 (cyc5 (kb r ν) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0) (kd r)) _ (fun i => ?_) _ core.1 ?_
  · rcases z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro y hy hyx
    simp only [V8, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 4 rfl).elim
    · exact ⟨(ka r W ha w3), rfl, core.2.1⟩
    · exact ⟨(ka' ν β6 C0), rfl, core.2.2⟩
    · exact (hyx 0 rfl).elim
    · exact (hyx 2 rfl).elim
    · exact (hyx 3 rfl).elim
    · exact (hyx 1 rfl).elim

theorem K_mpm {a a' b b' c c' d e1 e2 e3 o : ℝ³} {ν v1 C0 w1 ha w3 α1 α4 β1 γ4 β6 σ t1 t2 t3 : ℝ}
    (hF : Fr e1 e2 e3) (hσ : σ = 1 ∨ σ = -1) (hν : 0 < ν) (hv : σ * v1 < 0) (hha : 0 < ha) (hα : 1 < α1)
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hd : d = pt e1 e2 e3 o (-v1) 0 0) (hb : b = pt e1 e2 e3 o (-v1) 0 ν) (hc : c = pt e1 e2 e3 o 0 0 C0)
    (ha_ : a = pt e1 e2 e3 o (-v1 + w1) ha w3) (ha' : a' = pt e1 e2 e3 o 0 0 (β6 * ν + C0))
    (hb' : b' = pt e1 e2 e3 o (-v1 * (1 - γ4) + α4 * w1) (α4 * ha) (α4 * w3 + γ4 * C0))
    (hc' : c' = pt e1 e2 e3 o (-v1 + α1 * w1) (α1 * ha) (α1 * w3 + β1 * ν)) (hu : b - d = ν • e3)
    (hp1 : 0 < (σ * (w1 * t2 - ha * t1)))
    (hp3 : 0 < -(-(σ * v1) * (γ4 - 1) * t2 - α4 * (σ * (w1 * t2 - ha * t1))))
    (hp4 : 0 < (-(σ * v1) * t2)) :
    TiltTests (V8 a a' b b' c c' d) (orient σ (cyc5 b c' b' c a')) (b - d) (pc e1 e2 e3 t1 t2 t3) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ v1 = -(σ * r) := ⟨-(σ * v1), by linarith, by linear_combination (-v1) * hσ2⟩
  obtain ⟨W, rfl⟩ : ∃ W, w1 = σ * W := ⟨σ * w1, by linear_combination (-w1) * hσ2⟩
  have core := cell_mpm (r := r) (W := W) (T1 := σ * t1) (t2 := t2) (w3 := w3) (C0 := C0) (ν := ν) (ha := ha)
    (α1 := α1) (α4 := α4) (γ4 := γ4) (β1 := β1) (β6 := β6) hr hν hha hα hα4 hγ4 hβ1 hβ6 hE
    (by rcases hσ with rfl | rfl <;> linarith [hp1]) (by rcases hσ with rfl | rfl <;> linarith [hp3])
    (by rcases hσ with rfl | rfl <;> linarith [hp4])
  have e_0 : d = pr e1 e2 e3 o (unm σ (kd r)) := by rw [hd]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_1 : a = pr e1 e2 e3 o (unm σ (ka r W ha w3)) := by rw [ha_]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_2 : a' = pr e1 e2 e3 o (unm σ (ka' ν β6 C0)) := by rw [ha']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_3 : b = pr e1 e2 e3 o (unm σ (kb r ν)) := by rw [hb]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_4 : b' = pr e1 e2 e3 o (unm σ (kb' r W ha w3 C0 α4 γ4)) := by rw [hb']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_5 : c = pr e1 e2 e3 o (unm σ (kc C0)) := by rw [hc]; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  have e_6 : c' = pr e1 e2 e3 o (unm σ (kc' r W ha w3 ν α1 β1)) := by rw [hc']; simp only [pr, unm, kd, kb, kc, ka, ka', kb', kc']; ring_nf
  rw [hu]
  subst e_0 e_1 e_2 e_3 e_4 e_5 e_6
  refine wrapK hF o hσ hν t1 t2 t3 (cyc5 (kb r ν) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0) (ka' ν β6 C0)) _ (fun i => ?_) _ core.1 ?_
  · rcases z5c i with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro y hy hyx
    simp only [V8, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(kd r), rfl, core.2.1⟩
    · exact ⟨(ka r W ha w3), rfl, core.2.2⟩
    · exact (hyx 4 rfl).elim
    · exact (hyx 0 rfl).elim
    · exact (hyx 2 rfl).elim
    · exact (hyx 3 rfl).elim
    · exact (hyx 1 rfl).elim

end K
end Type08Sp
end Minimality
