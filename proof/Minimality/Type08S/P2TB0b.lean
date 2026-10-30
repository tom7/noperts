module

public import Minimality.Type08S.P2TDefs
public import Minimality.Type08S.P2TL1
public import Minimality.Type08S.P2TB0a

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem notSep_of_rob4 {z0 z1 z2 z3 : ℝ} (R : Rob4 z0 z1 z2 z3) : ¬ Sep z0 z2 z1 z3 := by
  obtain ⟨pk1, pk2, t012, t013, t023, t123, l0, l1, l2, l3⟩ := R
  intro h
  simp only [Sep, max_le_iff, le_min_iff] at h
  rcases h with ⟨⟨a1, a2⟩, a3, a4⟩ | ⟨⟨a1, a2⟩, a3, a4⟩ <;>
  rcases a1.lt_or_eq with a1 | a1 <;> rcases a2.lt_or_eq with a2 | a2 <;>
  rcases a3.lt_or_eq with a3 | a3 <;> rcases a4.lt_or_eq with a4 | a4 <;>
  first
  | exact pk1 ⟨by linarith, by linarith, by linarith, by linarith⟩
  | exact pk2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  | exact t012 ⟨by linarith, by linarith⟩
  | exact t013 ⟨by linarith, by linarith⟩
  | exact t023 ⟨by linarith, by linarith⟩
  | exact t123 ⟨by linarith, by linarith⟩
  | exact (l0 (by linarith)).1 ⟨by linarith, by linarith⟩
  | exact (l0 (by linarith)).2 ⟨by linarith, by linarith⟩
  | exact (l1 (by linarith)).1 ⟨by linarith, by linarith⟩
  | exact (l1 (by linarith)).2 ⟨by linarith, by linarith⟩
  | exact (l2 (by linarith)).1 ⟨by linarith, by linarith⟩
  | exact (l2 (by linarith)).2 ⟨by linarith, by linarith⟩
  | exact (l3 (by linarith)).1 ⟨by linarith, by linarith⟩
  | exact (l3 (by linarith)).2 ⟨by linarith, by linarith⟩

theorem notSep_of_rob {z0 z1 z2 z3 : ℝ} (h : IsRobustUnimodal (quad z0 z1 z2 z3)) : ¬ Sep z0 z2 z1 z3 :=
  notSep_of_rob4 (rob4_of h)

theorem neg_mul_le_iff {k : ℝ} (hk : k < 0) (s t : ℝ) : k * s ≤ k * t ↔ t ≤ s := by
  constructor <;> intro h <;> nlinarith

theorem sep_mul_neg {k : ℝ} (hk : k < 0) (x y u v : ℝ) :
    Sep (k * x) (k * y) (k * u) (k * v) ↔ Sep x y u v := by
  simp only [Sep, max_le_iff, le_min_iff, neg_mul_le_iff hk]
  tauto

end Type08Sp
end Minimality
