module

public import Minimality.Type24SAT.Atoms24

@[expose] public section

set_option autoImplicit false

/-!
# Type 24, layer 1 spot check at the realized shape R14 (generated)

Shape: mpmmm_r14_rz.real (exact rationals, P0 = 0, P5 = al P3 + be P4).  Model: mpmmm_r14.model (class mpmmm).
Checked in the kernel over ℚ and moved to ℝ by `Sem24.litHolds_ofQ`: convexity (35), planarity of 0345,
all 305 model signs (`agreeR14`), a sample of 12 single real statements, and a mutant (one N sign flipped) that fails.
-/

namespace Minimality.T24.SAT

/-- The seven points of R14. -/
def ptsR14 : List (V3 ℚ) := [
  ⟨(0 : ℚ), (0 : ℚ), (0 : ℚ)⟩,
  ⟨((-213890823973 : ℚ) / 274877906944), ((522462014407 : ℚ) / 1099511627776), ((51769851761 : ℚ) / 274877906944)⟩,
  ⟨((-28378207987 : ℚ) / 34359738368), ((725187906235 : ℚ) / 549755813888), ((3388625475 : ℚ) / 137438953472)⟩,
  ⟨((-322403529117 : ℚ) / 549755813888), ((54132109947 : ℚ) / 68719476736), ((1749204125023 : ℚ) / 1099511627776)⟩,
  ⟨((-82155302837 : ℚ) / 137438953472), ((63208870691 : ℚ) / 137438953472), ((228905378727 : ℚ) / 137438953472)⟩,
  ⟨((15333330501815429128359 : ℚ) / 604462909807314587353088), ((120572193029591713225887 : ℚ) / 151115727451828646838272), ((-212009895134821342580281 : ℚ) / 1208925819614629174706176)⟩,
  ⟨((-282315970583 : ℚ) / 274877906944), ((268890480245 : ℚ) / 1099511627776), ((1065688738539 : ℚ) / 549755813888)⟩]

/-- Point `i` of R14. -/
def QR14 (i : Nat) : V3 ℚ := ptsR14.getD i ⟨0, 0, 0⟩

/-- The model mpmmm_r14.model by encoder variable: `(v, sign)`. -/
def modelR14 : List (Nat × Int) := [
(2, -1), (3, -1), (4, 1), (5, -1), (6, 1), (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1), (16, -1), (17, 1), (18, 1), (19, 1), (20, 1), (21, 1), (22, 1), (23, 1), (24, 1), (25, -1), (26, -1), (27, -1), (28, -1), (29, 1), (30, 1), (31, -1), (32, -1), (33, 1), (34, 1), (35, -1), (36, -1), (37, -1), (38, 1), (39, 1), (40, -1), (41, 1), (42, 1), (43, 1), (44, 1), (45, 1), (46, 1), (47, 1), (48, 1), (49, 1), (50, 1), (51, 1), (52, 1), (53, -1), (54, -1), (55, -1), (56, 1), (57, -1), (58, -1), (59, -1), (60, 1), (61, 1), (62, 1), (63, -1), (64, -1), (65, 1), (66, 1), (67, 1), (68, 1), (69, 1), (70, 1), (71, 1), (72, 1), (73, 1), (74, -1), (75, -1), (76, -1), (77, 1), (78, 1), (79, 1), (80, 1), (81, -1), (82, 1), (83, -1), (84, 1), (85, 1), (86, -1), (87, 1), (88, -1), (89, 1), (90, 1), (91, 1), (92, 1), (93, 1), (94, 1), (95, 1), (96, -1), (97, -1), (98, -1), (99, -1), (100, 1), (101, -1), (102, -1), (103, -1), (104, 1), (105, -1), (106, 1), (107, -1), (108, -1), (109, 1), (110, -1), (111, -1), (112, -1), (113, -1), (114, 1), (115, 1), (116, -1), (117, -1), (118, -1), (119, -1), (120, 1), (121, -1), (122, 1), (123, 1), (124, 1), (125, 1), (126, 1), (127, 1), (128, -1), (129, -1), (130, -1), (131, 1), (132, 1), (133, 1), (134, 1), (135, -1), (136, 1), (137, -1), (138, -1), (139, -1), (140, -1), (141, 1), (142, 1), (143, 1), (144, -1), (146, -1), (147, -1), (148, -1), (149, 1), (150, 1), (151, 1), (152, 1), (153, 1), (154, 1), (155, 1), (156, 1), (157, -1), (158, -1), (160, -1), (161, -1), (162, 1), (163, 1), (164, 1), (166, -1), (167, 1), (168, -1), (169, -1), (170, -1), (171, -1), (172, -1), (173, -1), (174, 1), (176, -1), (177, -1), (178, 1), (179, 1), (180, -1), (181, 1), (182, 1), (183, 1), (184, -1), (185, 1), (186, 1), (187, -1), (188, -1), (190, 1), (191, -1), (192, 1), (193, 1), (194, 1), (196, -1), (197, 1), (198, 1), (199, 1), (200, -1), (201, -1), (202, -1), (203, 1), (204, -1), (205, 1), (206, 1), (207, -1), (208, -1), (209, 1), (210, 1), (211, -1), (212, 1), (213, 1), (214, 1), (215, 1), (216, -1), (217, -1), (218, -1), (219, 1), (220, 1), (221, -1), (222, 1), (223, -1), (224, -1), (225, 1), (226, 1), (227, 1), (228, -1), (229, 1), (230, 1), (231, 1), (232, 1), (233, 1), (234, -1), (235, 1), (236, 1), (237, 1), (238, -1), (239, -1), (240, -1), (241, 1), (242, -1), (243, -1), (244, 1), (245, 1), (246, -1), (247, 1), (248, 1), (249, 1), (250, -1), (251, -1), (252, -1), (253, -1), (254, 1), (255, 1), (256, 1), (257, 1), (258, -1), (259, -1), (260, -1), (261, 1), (262, 1), (263, 1), (264, -1), (265, -1), (266, -1), (267, -1), (268, -1), (269, 1), (270, 1), (271, 1), (272, -1), (273, 1), (274, -1), (275, -1), (276, -1), (277, -1), (278, 1), (279, -1), (280, -1), (281, -1), (282, -1), (283, -1), (284, 1), (285, -1), (286, -1), (287, -1), (288, -1), (289, 1), (290, 1), (291, 1), (292, 1), (293, 1), (294, -1), (295, 1), (296, -1), (297, 1), (298, -1), (299, -1), (300, -1), (301, -1), (302, 1), (303, 1), (304, -1), (305, 1), (306, 1), (307, -1), (308, 1), (309, 1), (310, -1), (311, -1), (312, -1)]

/-- Every atom of the table has the model's sign at the shape (exact, over ℚ). -/
def agreeWith (Q : Nat → V3 ℚ) (m : List (Nat × Int)) : Bool :=
  atoms24.all fun a => match m.lookup a.v with
    | some s => decide (0 < (s : ℚ) * val3 Q a.lit)
    | none => false

theorem convexR14 : Convex24 (ofQ QR14) := convex24_ofQ _ (by decide +kernel)

theorem quadDR14 : QuadD (ofQ QR14) := by
  have h : val (ofQ QR14) (.br 0 3 4 5) = 0 := by
    rw [val_ofQ]; exact_mod_cast (show val3 QR14 (.br 0 3 4 5) = 0 by decide +kernel)
  exact h

theorem agreeR14 : agreeWith QR14 modelR14 = true := by decide +kernel

/-- Mutant: the model with the sign of NADH flipped is rejected (the check is not vacuous). -/
theorem mutantR14 : agreeWith QR14 (modelR14.map fun p => if p.1 = 300 then (p.1, -p.2) else p) = false := by
  decide +kernel

/-- `[1234]` has sign -1 at R14. -/
theorem sR14_br1234 : LitHolds (ofQ QR14) (.br 1 2 3 4) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `[1356]` has sign -1 at R14. -/
theorem sR14_br1356 : LitHolds (ofQ QR14) (.br 1 3 5 6) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `L013;24` has sign +1 at R14. -/
theorem sR14_L013_24 : LitHolds (ofQ QR14) (.lv 0 1 3 2 4) (1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `L256;04` has sign +1 at R14. -/
theorem sR14_L256_04 : LitHolds (ofQ QR14) (.lv 2 5 6 0 4) (1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `M01.23.45.` has sign -1 at R14. -/
theorem sR14_M01_23_45 : LitHolds (ofQ QR14) (.mv 0 1 2 3 4 5) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `M04.15.26.` has sign +1 at R14. -/
theorem sR14_M04_15_26 : LitHolds (ofQ QR14) (.mv 0 4 1 5 2 6) (1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `A:34` has sign -1 at R14. -/
theorem sR14_A_34 : LitHolds (ofQ QR14) (.fc 0 3 4) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `F:03` has sign -1 at R14. -/
theorem sR14_F_03 : LitHolds (ofQ QR14) (.fc 5 0 3) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `NADH` has sign -1 at R14. -/
theorem sR14_NADH : LitHolds (ofQ QR14) (.nv 0 3 7) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `NBDH` has sign +1 at R14. -/
theorem sR14_NBDH : LitHolds (ofQ QR14) (.nv 1 3 7) (1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `KD0435` has sign -1 at R14. -/
theorem sR14_KD0435 : LitHolds (ofQ QR14) (.kv 3 0 4 3 5) (-1) := litHolds_ofQ _ _ _ (by decide +kernel)

/-- `KD0534` has sign +1 at R14. -/
theorem sR14_KD0534 : LitHolds (ofQ QR14) (.kv 3 0 5 3 4) (1) := litHolds_ofQ _ _ _ (by decide +kernel)

end Minimality.T24.SAT

#print axioms Minimality.T24.SAT.agreeR14
#print axioms Minimality.T24.SAT.convexR14
