module

public import Minimality.Type16SAT.Ent2

@[expose] public section

/-!
# L3, part 7: the normal table, three valued

Port of L/B21Ent8: for facets `a, b` sharing the edge `p q`, `det3 Na Nb Nc` is a positive multiple of
`det3 Na Nb d * <Nc, d>` (`d = x p - x q`).  The first factor has a constant sign (`kap_sound`), the second is a facing.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical

open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- The Gram identity for two normals orthogonal to `d`, against two vectors `u, v`. -/
theorem binet (a b d u v : ℝ³) (ha : ⟪a, d⟫ = 0) (hb : ⟪b, d⟫ = 0) :
    det3 a b d * det3 u v d = ⟪d, d⟫ * (⟪a, u⟫ * ⟪b, v⟫ - ⟪a, v⟫ * ⟪b, u⟫) := by
  have e : det3 a b d * det3 u v d =
      ⟪a, u⟫ * ⟪b, v⟫ * ⟪d, d⟫ + ⟪a, v⟫ * ⟪b, d⟫ * ⟪d, u⟫ + ⟪a, d⟫ * ⟪b, u⟫ * ⟪d, v⟫ -
      ⟪a, d⟫ * ⟪b, v⟫ * ⟪d, u⟫ - ⟪a, u⟫ * ⟪b, d⟫ * ⟪d, v⟫ - ⟪a, v⟫ * ⟪b, u⟫ * ⟪d, d⟫ := by
    simp only [det3_expand, inn3]; ring
  rw [e, ha, hb]; ring

/-- **The sign of `det3 Na Nb d` along a shared edge** `p q` of facets `a, b`, from the orientation of
a triple of `a`, with `r'` of `b` off `a` and `s'` of `a` off `b`. -/
theorem kap_sound {g : Geo} (hF : FacOK g) (hO : OriOK g) (a b p q r' s' : Nat)
    (hpa : inF a p = true) (hqa : inF a q = true) (hpb : inF b p = true) (hqb : inF b q = true)
    (hrb : inF b r' = true) (hra : inF a r' = false) (hsa : inF a s' = true) (hsb : inF b s' = false)
    (hr7 : r' < 7) (hs7 : s' < 7) (ho : oriv a p q s' ≠ 0) (hd : g.x p - g.x q ≠ 0) :
    0 < (-(oriv a p q s') : ℝ) * det3 (g.N a) (g.N b) (g.x p - g.x q) := by
  have ha : ⟪g.N a, g.x p - g.x q⟫ = 0 := hF.zero a p q hpa hqa
  have hb : ⟪g.N b, g.x p - g.x q⟫ = 0 := hF.zero b p q hpb hqb
  have B := binet (g.N a) (g.N b) (g.x p - g.x q) (g.x r' - g.x p) (g.x s' - g.x p) ha hb
  have i1 : ⟪g.N a, g.x s' - g.x p⟫ = 0 := hF.zero a s' p hsa hpa
  have i2 : ⟪g.N b, g.x r' - g.x p⟫ = 0 := hF.zero b r' p hrb hpb
  have p1 : 0 < ⟪g.N a, g.x p - g.x r'⟫ := hF.pos a p r' hr7 hpa hra
  have p2 : 0 < ⟪g.N b, g.x p - g.x s'⟫ := hF.pos b p s' hs7 hpb hsb
  have e1 : ⟪g.N a, g.x r' - g.x p⟫ = - ⟪g.N a, g.x p - g.x r'⟫ := by rw [← inner_neg_right, neg_sub]
  have e2 : ⟪g.N b, g.x s' - g.x p⟫ = - ⟪g.N b, g.x p - g.x s'⟫ := by rw [← inner_neg_right, neg_sub]
  have dd : 0 < ⟪g.x p - g.x q, g.x p - g.x q⟫ := real_inner_self_pos.mpr hd
  rw [i1, i2, e1, e2] at B
  have P : 0 < (-⟪g.N a, g.x p - g.x r'⟫) * (-⟪g.N b, g.x p - g.x s'⟫) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hDW : 0 < det3 (g.N a) (g.N b) (g.x p - g.x q) *
      det3 (g.x r' - g.x p) (g.x s' - g.x p) (g.x p - g.x q) := by
    rw [B]; nlinarith
  have Wd : det3 (g.x r' - g.x p) (g.x s' - g.x p) (g.x p - g.x q) = Bq g p q s' r' := by
    simp only [Bq, det3_expand, PiLp.sub_apply]; ring
  rw [Wd] at hDW
  have hb4 : 0 < -(oriv a p q s' : ℝ) * Bq g p q s' r' := by
    have o := oriv_sound hO a p q s' ho
    exact brk_fwd hF a p q s' r' hpa hqa hsa hr7 hra (oriv a p q s' : ℝ) o
  have hε : (0 : ℝ) < (oriv a p q s' : ℝ) * (oriv a p q s' : ℝ) :=
    mul_self_pos.2 (by exact_mod_cast ho)
  have hXY : 0 < (-(oriv a p q s' : ℝ) * det3 (g.N a) (g.N b) (g.x p - g.x q)) *
      (-(oriv a p q s' : ℝ) * Bq g p q s' r') := by
    have : (-(oriv a p q s' : ℝ) * det3 (g.N a) (g.N b) (g.x p - g.x q)) *
      (-(oriv a p q s' : ℝ) * Bq g p q s' r') = ((oriv a p q s' : ℝ) * (oriv a p q s' : ℝ)) *
        (det3 (g.N a) (g.N b) (g.x p - g.x q) * Bq g p q s' r') := by ring
    rw [this]; exact mul_pos hε hDW
  exact (pos_iff_pos_of_mul_pos hXY).mpr hb4

/-- Two distinct points separated by a facet differ. -/
theorem dne {g : Geo} (hF : FacOK g) (p q f : Nat) (hq : q < 7) (hp : inF f p = true) (hqf : inF f q = false) :
    g.x p - g.x q ≠ 0 := by
  intro h
  have := hF.pos f p q hq hp hqf
  rw [h] at this; simp at this

/-- The entry of a normal key along a shared edge: the constant times the facing of `c`. -/
def nlS (a p q s' c : Nat) : S3 := mul3 (cS (-(oriv a p q s'))) (fup3 c p q)

/-- **The product of a constant and a facing along a shared edge**, three valued. -/
theorem nl_core3 {g : Geo} (hF : FacOK g) (hO : OriOK g) (a b c p q r' s' : Nat)
    (hpa : inF a p = true) (hqa : inF a q = true) (hpb : inF b p = true) (hqb : inF b q = true)
    (hrb : inF b r' = true) (hra : inF a r' = false) (hsa : inF a s' = true) (hsb : inF b s' = false)
    (hr7 : r' < 7) (hs7 : s' < 7) (hp7 : p < 7) (hq7 : q < 7)
    (ho : oriv a p q s' ≠ 0) (hd : g.x p - g.x q ≠ 0) :
    Sg3 (rho g) (nlS a p q s' c) (det3 (g.N a) (g.N b) (g.N c)) := by
  have K := kap_sound hF hO a b p q r' s' hpa hqa hpb hqb hrb hra hsa hsb hr7 hs7 ho hd
  have dd : 0 < ⟪g.x p - g.x q, g.x p - g.x q⟫ := real_inner_self_pos.mpr hd
  have ha : ⟪g.x p - g.x q, g.N a⟫ = 0 := by rw [real_inner_comm]; exact hF.zero a p q hpa hqa
  have hb : ⟪g.x p - g.x q, g.N b⟫ = 0 := by rw [real_inner_comm]; exact hF.zero b p q hpb hqb
  have id := det_perp (g.N a) (g.N b) (g.N c) (g.x p - g.x q) ha hb
  have e : det3 (g.N a) (g.N b) (g.N c) =
      (1 / ⟪g.x p - g.x q, g.x p - g.x q⟫) *
        (det3 (g.N a) (g.N b) (g.x p - g.x q) * ⟪g.N c, g.x p - g.x q⟫) := by
    rw [real_inner_comm (g.x p - g.x q) (g.N c)]; field_simp; linarith [id]
  have SA := Sg3_of_mulpos (rho_proper g) (n := -(oriv a p q s')) (by push_cast; exact K)
  have P := Sg3.mul3 (rho_proper g) (rho_gateOK g) SA (fup3_sound hF c p q hp7 hq7)
  rw [e]
  exact Sg3.scale (by positivity) P

/-- The check of a normal-table key: facets `a, b` share the edge `p q`, `r'` is a vertex of `b`
off `a`, `s'` of `a` off `b`, and the entry is the constant times the facing of `c`. -/
def nlChk (a b c p q r' s' : Nat) (ent : S3) : Bool :=
  inF a p && inF a q && inF b p && inF b q && inF b r' && !inF a r' && inF a s' && !inF b s' &&
  decide (r' < 7) && decide (s' < 7) && decide (p < 7) && decide (q < 7) &&
  decide (oriv a p q s' ≠ 0) && (List.range 8).any (fun f => inF f p && !inF f q) &&
  decide (ent = nlS a p q s' c)

/-- **A checked normal-table key is true** (for the rotation `a b c` of the key). -/
theorem nl_chk3 {g : Geo} (hF : FacOK g) (hO : OriOK g) (a b c p q r' s' : Nat) (ent : S3)
    (h : nlChk a b c p q r' s' ent = true) :
    Sg3 (rho g) ent (det3 (g.N a) (g.N b) (g.N c)) := by
  simp only [nlChk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.any_eq_true,
    List.mem_range, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpa, hqa⟩, hpb⟩, hqb⟩, hrb⟩, hra⟩, hsa⟩, hsb⟩, hr7⟩, hs7⟩, hp7⟩, hq7⟩,
    ho⟩, ⟨f, hf8, hfpq⟩⟩, hent⟩ := h
  rw [hent]
  exact nl_core3 hF hO a b c p q r' s' hpa hqa hpb hqb hrb hra hsa hsb hr7 hs7 hp7 hq7 ho
    (dne hF p q f hq7 hfpq.1 hfpq.2)

/-- Rotation 0 of a key. -/
theorem nl_key0 {g : Geo} (hF : FacOK g) (hO : OriOK g) (r s t p q r' s' : Nat) (ent : S3)
    (h : nlChk s t r p q r' s' ent = true) : Sg3 (rho g) ent (det3 (g.N r) (g.N s) (g.N t)) := by
  have := nl_chk3 hF hO s t r p q r' s' ent h
  rw [det3_cyc]; exact this

/-- Rotation 1 of a key. -/
theorem nl_key1 {g : Geo} (hF : FacOK g) (hO : OriOK g) (r s t p q r' s' : Nat) (ent : S3)
    (h : nlChk t r s p q r' s' ent = true) : Sg3 (rho g) ent (det3 (g.N r) (g.N s) (g.N t)) := by
  have := nl_chk3 hF hO t r s p q r' s' ent h
  rw [det3_cyc, det3_cyc]; exact this

/-- Rotation 2 of a key. -/
theorem nl_key2 {g : Geo} (hF : FacOK g) (hO : OriOK g) (r s t p q r' s' : Nat) (ent : S3)
    (h : nlChk r s t p q r' s' ent = true) : Sg3 (rho g) ent (det3 (g.N r) (g.N s) (g.N t)) :=
  nl_chk3 hF hO r s t p q r' s' ent h

/-- A normal-table key that is an atom (no two of the three facets share an edge). -/
theorem nl_atom3 {g : Geo} (r s t : Nat) :
    Sg3 (rho g) (atomS (V.nv r s t)) (det3 (g.N r) (g.N s) (g.N t)) :=
  Sg3_atomG g (v := V.nv r s t) (by simp [rho])

end Minimality.H16.SAT
