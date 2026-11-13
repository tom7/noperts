module

public import Minimality.Type08S.GT_Wrap7

@[expose] public section

set_option autoImplicit true

/-!
# GT wrapper, part 8: T4 weakly beyond, `r2 != b2`, `zv > 0`
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
variable {a a' b b' c c' d : ℝ³}

theorem T4Cfg0.toCfg {E U zv zw A b1 b2 r1 r2 xa za ua a3 : ℝ} {FH FQac FT1 FT2 FT3 FT4 : Fc}
    (h : T4Cfg0 E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4) (hz : 0 < zv) :
    T4Cfg E U zv zw A b1 b2 r1 r2 xa za ua a3 FH FQac FT1 FT2 FT3 FT4 := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54⟩ := h
  exact ⟨f0, f1, hz, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54⟩

end Type08Sp
end Minimality
