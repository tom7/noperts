default : annular229_test.exe tubetree229_test.exe nopert229_test.exe tube229_test.exe lib229_test.exe chart229_test.exe export_tubetree_pack.exe difficult229.exe lean229.exe pack229.exe test_all_pending.exe normalize-chart.exe compare-charts.exe split-chart.exe split-chart_test.exe

all: default test229.exe codebdd229.exe telescope229.exe convert_tubecert229.exe incrementaltube229.exe tubecert229.exe tube-visualize.exe analyzedifficult.exe replace_tu_with_difficult.exe extract_tu_intervals.exe generate_seeds229.exe apply_shallow_cert.exe verify_leaf.exe tiltperts.exe

UNAME := $(shell uname -o)
ifeq ($(findstring Linux,$(UNAME)),Linux)
CC=clang
LIBCXX := $(shell echo '\#include <vector>' | clang++ -stdlib=libc++ -x c++ - -c -o /dev/null 2>/dev/null && echo -stdlib=libc++)
CXX=clang++ $(LIBCXX)
PDB_FLAG=
else
PDB_FLAG=-Wl,--pdb=lean229.pdb
endif

CL_LFLAGS=-lOpenCL

# This is optional; if you want to use plain C++ code, just
# comment it out. But GMP is much faster.
GMP_LFLAGS=-lgmp
GMP_CFLAGS=-DBIG_USE_GMP

# On Mac, this is how I get them
ifeq ($(findstring Darwin,$(UNAME)),Darwin)
GMP_LFLAGS=`pkg-config --libs gmp`
GMP_CFLAGS=`pkg-config --cflags gmp` -DBIG_USE_GMP
endif

CC_LIB=../cc-lib
RUPERTS=../ruperts
CODEC=$(shell if [ -d ../codec ]; then echo ../codec; else echo ../../codec; fi)
SQLITE=$(shell if [ -d ../sqlite ]; then echo ../sqlite; else echo ../../sqlite; fi)

# Detect mimalloc if available, otherwise leave off
MALLOC_LFLAGS := $(shell echo 'int main(){}' | clang -x c - -lmimalloc -o /dev/null 2>/dev/null && echo -lmimalloc)

# for profiling (Very Sleepy)
# OPT=-O -g -gcodeview
OPT=-O3 -flto=thin -g
# ASAN=-g -fsanitize=address -fsanitize=undefined
# OPT=-O

# REMARKS=-Rpass=loop-vectorize -Rpass-missed=loop-vectorize -Rpass-analysis=loop-vectorize

CXXFLAGS=$(REMARKS) $(ASAN) $(OPT) $(GMP_CFLAGS) -march=native -mtune=native -Wall -Wno-psabi -Wno-unused-function -Wno-sign-compare -I. -I$(RUPERTS) -I$(CC_LIB) -I$(CODEC) -I$(SQLITE) --std=c++23
LFLAGS=$(ASAN) $(GMP_LFLAGS) -flto -lz $(MALLOC_LFLAGS)

CC_LIB_OBJECTS=$(CC_LIB)/util.o $(CC_LIB)/arcfour.o $(CC_LIB)/factorization.o $(CC_LIB)/base/stringprintf.o $(CC_LIB)/base/logging.o $(CC_LIB)/stb_image.o $(CC_LIB)/stb_image_write.o $(CC_LIB)/stb_truetype.o $(CC_LIB)/color-util.o $(CC_LIB)/image.o $(CC_LIB)/ansi.o  $(CC_LIB)/atomic-util.o $(CC_LIB)/status-bar.o $(CC_LIB)/zip.o $(CC_LIB)/miniz.o $(CC_LIB)/ansi-image.o $(CC_LIB)/image-resize.o $(CC_LIB)/opt/opt.o $(CC_LIB)/opt/large-optimizer.o $(CC_LIB)/bounds.o $(CC_LIB)/interval-cover.o $(CC_LIB)/interval-cover-util.o $(CC_LIB)/bignum/big.o $(CC_LIB)/bignum/bigz.o $(CC_LIB)/bignum/bign.o $(CC_LIB)/bignum/bigq.o $(CC_LIB)/bignum/big-numbers.o $(CC_LIB)/bignum/polynomial.o $(CC_LIB)/bignum/big-interval.o $(CC_LIB)/textsvg.o $(CC_LIB)/hexdump.o $(CC_LIB)/integer-voronoi.o $(CC_LIB)/crypt/sha256.o $(CC_LIB)/process-util.o $(CC_LIB)/numbers.o $(CC_LIB)/nice.o $(CC_LIB)/png.o $(CC_LIB)/geom/mesh.o $(CC_LIB)/geom/polygons.o $(CC_LIB)/geom/hull-3d.o $(CC_LIB)/geom/polyhedra.o $(CC_LIB)/geom/symmetry-groups.o $(CC_LIB)/geom/hull-2d.o $(CC_LIB)/z3/z3.o $(CC_LIB)/dirty.o

# This is only for generating animations of polyhedra; it should be pretty
# easy to excise the code if you're having trouble with it.
CODEC_OBJECTS=$(CODEC)/mov.o $(CODEC)/mov-recorder.o

# Only needed for GPU solvers.
CL_OBJECTS=$(CC_LIB)/opencl/clutil.o

SQLITE_OBJECTS=$(SQLITE)/database.o $(SQLITE)/sqlite3.o

RUPERTS_OBJECTS=$(RUPERTS)/ruperts-util.o $(RUPERTS)/big-csg.o $(RUPERTS)/rendering.o $(RUPERTS)/solutions.o $(RUPERTS)/shrinklutions.o $(RUPERTS)/hull.o $(RUPERTS)/big-polyhedra.o $(RUPERTS)/textured-mesh.o $(RUPERTS)/smallest-sphere.o $(RUPERTS)/dyson.o $(RUPERTS)/z3decs.o $(RUPERTS)/patches.o $(RUPERTS)/intervals.o $(RUPERTS)/hypercube.o

OBJECTS=$(CC_LIB_OBJECTS) $(CODEC_OBJECTS) $(SQLITE_OBJECTS) $(RUPERTS_OBJECTS)

# library objects shared in Nopert 229 search. No OpenCL.
OBJECTS_229=nopert229.o tube229.o tubetree229.o annular229.o chart229.o

$(CC_LIB)/%.o : $(CC_LIB)/%.cc
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

$(RUPERTS)/%.o : $(RUPERTS)/%.cc
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

$(CODEC)/%.o : $(CODEC)/%.cc
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

%.o : %.cc *.h makefile
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

# Test targets
test_greedy_50k.exe : test_greedy_50k.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_audit_83.exe : test_audit_83.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_emit_ax83.exe : test_emit_ax83.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_audit_node.exe : test_audit_node.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_sweep_bary.exe : test_sweep_bary.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_subdiv_deep14.exe : test_subdiv_deep14.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_worst_all50k.exe : test_worst_all50k.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_12_parameters.exe : test_12_parameters.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_print_vm.exe : test_print_vm.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_print_mix_u0.exe : test_print_mix_u0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cage_zero_defect.exe : test_cage_zero_defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_all_tag3_core.exe : test_all_tag3_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_sweep_ax0_mix.exe : test_sweep_ax0_mix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_close_annular.exe : test_close_annular.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_search_zero_annular.exe : test_search_zero_annular.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_greedy_flock.exe : test_greedy_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_check_6flock.exe : test_check_6flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_check_5flock.exe : test_check_5flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_print_u0.exe : test_print_u0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_find_ax0.exe : test_find_ax0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_full_cap_flock.exe : test_full_cap_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_bary_pure.exe : test_bary_pure.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_inspect_pure_vert.exe : test_inspect_pure_vert.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_pure_vert.exe : test_pure_vert.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_zero_defect.exe : test_zero_defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_c_cone_sweep.exe : test_c_cone_sweep.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_search_annular.exe : test_search_annular.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_inspect_9011.exe : test_inspect_9011.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_max_dot.exe : test_max_dot.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_4ring.exe : test_4ring.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_ax810_quad.exe : test_ax810_quad.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_canyon_pt.exe : test_canyon_pt.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_n128_canyon.exe : test_n128_canyon.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_n64_rings.exe : test_n64_rings.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_n64_sectors.exe : test_n64_sectors.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_canyon_sweep.exe : test_canyon_sweep.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_100pct_flock.exe : oneoffs/find_100pct_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_5flock_lean.exe : test_5flock_lean.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_inspect_canyon.exe : test_inspect_canyon.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_affine_quadtree.exe : test_affine_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_axis8362.exe : test_axis8362.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_4_flock_margin.exe : oneoffs/test_4_flock_margin.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_split_canyon_2ring.exe : oneoffs/test_split_canyon_2ring.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_dual_flock.exe : test_dual_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_spherical_flock.exe : oneoffs/test_spherical_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_polygons_03121303200.exe : oneoffs/test_flock_polygons_03121303200.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_pyramid_flock.exe : test_pyramid_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_next_gen_children.exe : test_next_gen_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

parallel_subdiv_canyon.exe : parallel_subdiv_canyon.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_recursive_subdivision.exe : test_recursive_subdivision.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diagnose_failing_child.exe : diagnose_failing_child.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_comp_cage_h.exe : test_comp_cage_h.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_best_core_axis.exe : find_best_core_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

audit_one_decomposed.exe : audit_one_decomposed.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_44_children.exe : test_44_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

parallel_solve_15.exe : parallel_solve_15.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_subdivide_15.exe : test_subdivide_15.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cage_enclosure.exe : test_cage_enclosure.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

annular229_test.exe : annular229_test.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tubetree229_test.exe : tubetree229_test.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

nopert229_test.exe : nopert229_test.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tube229_test.exe : tube229_test.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

lib229_test.exe : lib229_test.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

chart229_test.exe : chart229_test.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test229.exe : test229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

lean229.exe : lean229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

difficult229.exe : difficult229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

pack229.exe : pack229.o lib229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

export_tubetree_pack.exe : export_tubetree_pack.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_quadtree_centers.exe : test_quadtree_centers.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

export_single_tag3.exe : export_single_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_all_pending.exe : test_all_pending.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_coarse.exe : test_coarse.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

resolve_tree0.exe : resolve_tree0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_k1.exe : test_k1.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_hineq.exe : test_hineq.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_k1_search.exe : test_k1_search.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_03121300_children.exe : test_03121300_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_031213002_children.exe : test_031213002_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

audit_all_trees.exe : audit_all_trees.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

resolve_031213002.exe : resolve_031213002.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_direct_subdiv.exe : test_direct_subdiv.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0312130332_children.exe : test_0312130332_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

check_orig_0312130332.exe : check_orig_0312130332.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_direct_full.exe : test_direct_full.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_canyon_children_cert.exe : oneoffs/test_canyon_children_cert.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cage_0312130332.exe : test_cage_0312130332.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

compute_lean_bary.exe : compute_lean_bary.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tag1_bary.exe : test_tag1_bary.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_conical.exe : test_conical.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tune_c_cone.exe : tune_c_cone.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0312130332_subdiv.exe : test_0312130332_subdiv.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_west_synthesize.exe : test_west_synthesize.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_03121300_k1_exact.exe : test_03121300_k1_exact.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

synthesize_all_tag2.exe : synthesize_all_tag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tag2_exact.exe : test_tag2_exact.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_dec_leaves_clean.exe : test_dec_leaves_clean.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_perturbed_core.exe : test_perturbed_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_contact2.exe : test_contact2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_all_15_decomposed.exe : test_all_15_decomposed.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_core_0312130021.exe : find_core_0312130021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_flock_geom.exe : inspect_flock_geom.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cube_inter.exe : test_cube_inter.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_grid_coverage.exe : test_grid_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_subdivide_stubborn.exe : test_subdivide_stubborn.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_coverage.exe : test_flock_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_5flock_eval.exe : test_5flock_eval.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_find_6th_axis.exe : test_find_6th_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_all_11_children.exe : test_all_11_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_tree0_leaves.exe : inspect_tree0_leaves.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tag0_canyon.exe : test_tag0_canyon.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_children_full_tag2.exe : test_children_full_tag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tag_distribution.exe : test_tag_distribution.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_search_tag2.exe : test_search_tag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_subdiv_cage.exe : test_subdiv_cage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_4_offseam.exe : test_4_offseam.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_44_children.exe : test_44_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_fix_hdecomp.exe : test_fix_hdecomp.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tune_tag2.exe : test_tune_tag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_all_15_tune.exe : test_all_15_tune.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_subdiv_00.exe : test_subdiv_00.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

check_tree0_5nodes.exe : check_tree0_5nodes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

apply_full_subdivision.exe : apply_full_subdivision.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

codebdd229.exe : codebdd229.o nopert229.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

telescope229.exe : telescope229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

convert_tubecert229.exe : convert_tubecert229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

incrementaltube229.exe : incrementaltube229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tubecert229.exe : tubecert229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tube-visualize.exe : tube-visualize.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

analyzedifficult.exe : analyzedifficult.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

replace_tu_with_difficult.exe : replace_tu_with_difficult.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

extract_tu_intervals.exe : extract_tu_intervals.o
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

generate_seeds229.exe : generate_seeds229.o lib229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

apply_shallow_cert.exe : apply_shallow_cert.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

verify_leaf.exe : verify_leaf.o nopert229.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

normalize-chart.exe : normalize-chart.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

compare-charts.exe : compare-charts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

split-chart.exe : split-chart.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

split-chart_test.exe : split-chart_test.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tiltperts.exe : tiltperts.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS) $(PDB_FLAG)
validate_0312130332.exe : validate_0312130332.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_children_full_tag2.exe : test_children_full_tag2.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_aligned_core_axis.exe : find_aligned_core_axis.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth12.exe : test_depth12.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

sweep_mix_edges.exe : sweep_mix_edges.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

check_zero_defect.exe : check_zero_defect.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

search_depth12_individual.exe : search_depth12_individual.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_annular_defect.exe : inspect_annular_defect.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tag1_depth12.exe : test_tag1_depth12.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_original_nopertdata_cert.exe : test_original_nopertdata_cert.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

sweep_annular_axis.exe : sweep_annular_axis.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_collinear_annular_axis.exe : test_collinear_annular_axis.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_barycentric_collinear.exe : test_barycentric_collinear.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tag2_depth11.exe : test_tag2_depth11.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

audit_all_rows.exe : audit_all_rows.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

search_correct_norm.exe : search_correct_norm.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
audit_6_seam_nodes.exe : audit_6_seam_nodes.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

clean :
	rm -f *.o *.exe

ifeq ($(OPT),)
  $(warning Warning: OPT is completely disabled!)
endif

test_pool_size.exe : test_pool_size.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_extra_flock.exe : find_extra_flock.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

synthesize_quadtree_cover.exe : synthesize_quadtree_cover.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_point_cover.exe : test_point_cover.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_find_cage.exe : test_find_cage.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all_12_leaves.exe : test_all_12_leaves.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_node_0312130021.exe : test_node_0312130021.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_6_seam_nodes.exe : test_6_seam_nodes.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_lean_cage.exe : find_lean_cage.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_audit_0312130021.exe : test_audit_0312130021.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_greedy.exe : test_flock_greedy.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_child_defect.exe : test_child_defect.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

check_all_12_cages.exe : check_all_12_cages.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_leaf_tag3.o : test_leaf_tag3.cc
	@$(CXX) $(CXXFLAGS) -c $< -o $@

test_leaf_tag3.exe : test_leaf_tag3.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_leaf_params.o : inspect_leaf_params.cc
	@$(CXX) $(CXXFLAGS) -c $< -o $@

inspect_leaf_params.exe : inspect_leaf_params.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_subdiv_deep14.exe : test_subdiv_deep14.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_exact_zero_flock.exe : find_exact_zero_flock.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

diag_03121303021.exe : diag_03121303021.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

sweep_cone_03121303021.exe : sweep_cone_03121303021.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

verify_lean_cage.exe : verify_lean_cage.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_exact_cages_22_23.exe : find_exact_cages_22_23.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fine_quadtree.exe : test_fine_quadtree.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

check_exact_zero_pool.exe : check_exact_zero_pool.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

verify_4_exact_cages.exe : verify_4_exact_cages.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_exact_lean_quadtree.exe : test_exact_lean_quadtree.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_sweet_spot.exe : find_sweet_spot.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_original_fine_data.exe : test_original_fine_data.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_fine_flock.exe : find_fine_flock.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_mix.exe : test_mix.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_win.exe : test_win.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_contact2.exe : test_contact2.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_inspect.exe : test_inspect.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

audit_12_leaves.exe : audit_12_leaves.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fine_export.exe : test_fine_export.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_parent_flock.exe : test_parent_flock.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_mix_scan.exe : test_mix_scan.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

opt_contact2.exe : opt_contact2.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_coarse_mix.exe : test_coarse_mix.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_coarse_dots.exe : test_coarse_dots.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_coarse_axes.exe : test_coarse_axes.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_coverage.exe : test_flock_coverage.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_zero_defect_flock.exe : find_zero_defect_flock.o annular229.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_standard_leaf.exe : test_standard_leaf.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_adaptive_flock.exe : test_adaptive_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_zero_defect_a0.exe : test_zero_defect_a0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_subdiv_all.exe : test_subdiv_all.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_optimize_mix.exe : test_optimize_mix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_fast_subdiv.exe : test_fast_subdiv.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


find_leaf_cage.exe : find_leaf_cage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_search.exe : test_cage_search.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_audit_cages.exe : test_audit_cages.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_scan_params.exe : test_scan_params.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


find_cage_tripod.exe : find_cage_tripod.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_centers.exe : test_centers.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_all_12_annular.exe : test_all_12_annular.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


find_min_d0.exe : find_min_d0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_variant1.exe : test_variant1.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_all_12_tag3.exe : test_all_12_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_pool_as_a0.exe : test_pool_as_a0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_verify_zero_defect.exe : test_verify_zero_defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_find_cage_0021.exe : test_find_cage_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_u0_020.exe : print_u0_020.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_supp_0021.exe : print_supp_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_vs_m2.exe : test_cage_vs_m2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_coords.exe : test_cage_coords.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_sweep.exe : test_cage_sweep.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_geom.exe : print_geom.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


calc_d0_200.exe : calc_d0_200.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_violator.exe : print_violator.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_c2_mix800.exe : test_c2_mix800.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_direct_on_11.exe : test_direct_on_11.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_flock_0021_cone15.exe : test_flock_0021_cone15.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_zd0.exe : test_cage_zd0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_miss_0021.exe : inspect_miss_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_inner_cover_0021.exe : test_inner_cover_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


find_pool_core.exe : find_pool_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_core_v15.exe : test_core_v15.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


sweep_m01.exe : sweep_m01.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_c2_variations.exe : test_c2_variations.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_m500.exe : test_cage_m500.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_miss_pts.exe : print_miss_pts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_div_B.exe : test_div_B.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


fast_div_B.exe : fast_div_B.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


run_flock_0021.exe : run_flock_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_pool_u0.exe : test_pool_u0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_miss_dot.exe : test_miss_dot.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_ax0_flock.exe : test_ax0_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cap_pool_cover.exe : test_cap_pool_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_uncov.exe : print_uncov.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


find_cage_exact.exe : find_cage_exact.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_uncov28.exe : print_uncov28.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


make_tag3_0021.exe : make_tag3_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_lean_point.exe : test_lean_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_ax0_audit.exe : test_ax0_audit.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_ccone_window.exe : test_ccone_window.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_exact_flock_cover.exe : test_exact_flock_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_ccomp.exe : test_cage_ccomp.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_stored_cert_0021.exe : test_stored_cert_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_stored_bary_0021.exe : test_stored_bary_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_cage_axes_0021.exe : print_cage_axes_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_flock_0015.exe : test_flock_0015.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_single_point.exe : test_single_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_inner_mix.exe : print_inner_mix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_defect.exe : print_defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


sweep_mix.exe : sweep_mix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


sweep_supp.exe : sweep_supp.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_stored_params.exe : print_stored_params.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_lean_supp_calc.exe : test_lean_supp_calc.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


find_zero_defect_a0.exe : find_zero_defect_a0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_miss_d.exe : test_miss_d.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_ccone_sweep_flock.exe : test_ccone_sweep_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


search_cage_with_B.exe : search_cage_with_B.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_verts.exe : print_verts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


audit_all_12_leaves.exe : audit_all_12_leaves.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


print_cert_03021.exe : print_cert_03021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_build_stored_tree.exe : test_build_stored_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_4_paths.exe : test_4_paths.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_pool_as_a0.exe : test_pool_as_a0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_lean_cage_search.exe : test_lean_cage_search.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_inner_core.exe : inspect_inner_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


compare_annular_vs_inner.exe : compare_annular_vs_inner.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_mix_sweep_defect.exe : test_mix_sweep_defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_mix1000_params.exe : test_mix1000_params.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_mix1000_tree.exe : test_mix1000_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


generate_tag3_0021.exe : generate_tag3_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_all_leaves_mix_opt.exe : test_all_leaves_mix_opt.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_contacts_0022.exe : inspect_contacts_0022.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_depth11_children.exe : test_depth11_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_depth11_cage.exe : test_depth11_cage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_depth11_synth.exe : test_depth11_synth.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_dense_pool.exe : test_dense_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_find_hull_axis.exe : test_find_hull_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_hull_axis_details.exe : inspect_hull_axis_details.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_for_hull_axis.exe : test_cage_for_hull_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_0022_03321.exe : test_cage_0022_03321.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_refine_0022.exe : test_refine_0022.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


emit_stored_tag3.exe : emit_stored_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


generate_all_12_tag3.exe : generate_all_12_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_stored_params.exe : inspect_stored_params.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_03021.exe : test_cage_03021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_flock_deltas.exe : inspect_flock_deltas.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_lean_match_0021.exe : test_lean_match_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_miss.exe : inspect_miss.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_tree.exe : diag_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_grid_flock.exe : test_grid_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_fast_grid_flock.exe : test_fast_grid_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_3_pts.exe : print_3_pts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_rect_refine.exe : test_rect_refine.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_check_12_all_predicates.exe : test_check_12_all_predicates.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_12_decomposed_info.exe : print_12_decomposed_info.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_cage.exe : diag_cage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_find_cages_all_12.exe : test_find_cages_all_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

sweep_stubborn_cages.exe : sweep_stubborn_cages.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stubborn_015.exe : test_stubborn_015.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stubborn_quadtree_015.exe : test_stubborn_quadtree_015.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

verify_flock_0defect.exe : verify_flock_0defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_pool_defects.exe : test_pool_defects.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_best_flock_axis.exe : find_best_flock_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_axis_valid.exe : test_flock_axis_valid.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

generate_all_12_exact_lean.exe : generate_all_12_exact_lean.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_tree_stubborn.exe : diag_tree_stubborn.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0020.exe : test_0020.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0020_tree.exe : test_0020_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_compare_dots.exe : test_compare_dots.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stubborn_4axes_tree.exe : test_stubborn_4axes_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_uncovered.exe : diag_uncovered.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_refine_stubborn.exe : test_refine_stubborn.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_refine_stubborn_v2.exe : test_refine_stubborn_v2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_mag.exe : test_mag.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_miss_dir.exe : test_miss_dir.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth24.exe : test_depth24.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_pool_dirs.exe : test_pool_dirs.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_8_std_trees.exe : test_8_std_trees.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stubborn_core_ax.exe : test_stubborn_core_ax.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_row5_4axes.exe : test_row5_4axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_row5_tree_exact.exe : test_row5_tree_exact.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_fail22.exe : diag_fail22.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_corner.exe : diag_corner.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_rmin.exe : test_rmin.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_row5_c0009.exe : test_row5_c0009.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_fail0009.exe : diag_fail0009.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_gap_axis.exe : test_gap_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_row5_5axes.exe : test_row5_5axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_where5.exe : test_where5.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth28.exe : test_depth28.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_c_cone_range.exe : test_c_cone_range.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_v_dir.exe : test_v_dir.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_subdivide_stubborn.exe : test_subdivide_stubborn.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_greedy_flock.exe : test_greedy_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_greedy_flock_fast.exe : test_greedy_flock_fast.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_find_last_point.exe : test_find_last_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock5_c0006.exe : test_flock5_c0006.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_where_fail_c0006.exe : test_where_fail_c0006.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_best_for_cell.exe : test_best_for_cell.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_children_tag1_or_single_tag3.exe : test_children_tag1_or_single_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_open_leaves.exe : test_open_leaves.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth15.exe : test_depth15.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

solve_full_certificate_03121303200.exe : oneoffs/solve_full_certificate_03121303200.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cell_corners.exe : test_cell_corners.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_greedy_dense.exe : test_greedy_dense.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_quad_4axes.exe : test_quad_4axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_print_d2.exe : test_print_d2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cell_4axes.exe : test_cell_4axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_full_synth.exe : test_full_synth.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_map_stubborn.exe : test_map_stubborn.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_quad_builder.exe : test_quad_builder.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth11_tag3.exe : test_depth11_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_polygon.exe : test_polygon.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_poly_axes.exe : test_poly_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_quad_triangles.exe : test_quad_triangles.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth14_stubborn.exe : test_depth14_stubborn.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_quad_correct.exe : test_quad_correct.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_triangulation_mesh.exe : test_triangulation_mesh.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_ax_norm.exe : test_ax_norm.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_triangulation_mesh2.exe : test_triangulation_mesh2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_vertex_covered.exe : test_vertex_covered.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_t2.exe : test_t2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_edge.exe : test_edge.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_grid_triangles.exe : test_grid_triangles.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_where_uncovered.exe : test_where_uncovered.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_bisect_one.exe : test_bisect_one.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_diag2.exe : test_diag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cell_axes.exe : test_cell_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_odd_grids.exe : test_odd_grids.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_adaptive_grid.exe : test_adaptive_grid.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cell31.exe : test_cell31.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cell_interior.exe : test_cell_interior.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_dense_cell.exe : test_dense_cell.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_child1_subdiv.exe : test_child1_subdiv.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_all_tag3.exe : test_all_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_pool_coverage.exe : test_pool_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_zero_defect_count.exe : test_zero_defect_count.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_single_pool_cover.exe : test_single_pool_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_c_core_small.exe : test_c_core_small.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_point_dot.exe : test_point_dot.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_point_dot2.exe : test_point_dot2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_adaptive_flock.exe : test_adaptive_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_axis_norm.exe : print_axis_norm.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_miss_corners.exe : print_miss_corners.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_d_val.exe : print_d_val.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_miss_cell.exe : print_miss_cell.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_adaptive_flock2.exe : test_adaptive_flock2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_outside_check.exe : test_outside_check.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_cell_best_axis.exe : print_cell_best_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_miss_dot.exe : test_miss_dot.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_miss_dot2.exe : test_miss_dot2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_corners_390.exe : print_corners_390.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_miss_dot3.exe : test_miss_dot3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_params_0021.exe : test_params_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_params2.exe : test_params2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_close_axis.exe : find_close_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_wms.exe : print_wms.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

sweep_mix.exe : sweep_mix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_miss_corners.exe : test_miss_corners.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_miss_dot4.exe : test_miss_dot4.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_bary_limit.exe : test_bary_limit.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

pool_dot_dist.exe : pool_dot_dist.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_bary_coords.exe : print_bary_coords.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

pool_u0_dots.exe : pool_u0_dots.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_0020_axis.exe : print_0020_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_tie_fix.exe : test_tie_fix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_bak_axis.exe : test_bak_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_basis_print.exe : test_basis_print.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0021_with_inner.exe : test_0021_with_inner.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stored_cert_0021.exe : test_stored_cert_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stored_12.exe : test_stored_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_err_12.exe : test_err_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

search_zero_defect_0021.exe : search_zero_defect_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_coverage_0021.exe : test_flock_coverage_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_miss_0021.exe : inspect_miss_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_coverage_0022.exe : test_coverage_0022.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_miss_margin.exe : inspect_miss_margin.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_00_on_21.exe : test_flock_00_on_21.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_0020_on_siblings.exe : test_flock_0020_on_siblings.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

sweep_ccone_pool.exe : sweep_ccone_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_flock_0006.exe : test_flock_0006.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

export_0021.exe : export_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

diag_buildtree.exe : diag_buildtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_5th_axis.exe : test_5th_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cegar_axes.exe : test_cegar_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

check_flock_norms.exe : check_flock_norms.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_real_center.exe : print_real_center.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0020_correct_center.exe : test_0020_correct_center.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_uncov.exe : print_uncov.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_ccore_sweep.exe : test_ccore_sweep.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_correct_dirs.exe : test_correct_dirs.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_the_point.exe : print_the_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_ccone_sweep.exe : test_ccone_sweep.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_0021_quadtree.exe : test_0021_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_tree_fail.exe : print_tree_fail.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_basis.exe : print_basis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth20.exe : test_depth20.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cegar_flock.exe : test_cegar_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

inspect_15_boxes.exe : inspect_15_boxes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_min_rmin.exe : print_min_rmin.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_cegar_38.exe : test_cegar_38.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_8_boxes.exe : print_8_boxes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_depth22.exe : test_depth22.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

find_box6_axis.exe : find_box6_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_ccone_012_tree.exe : test_ccone_012_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_trace.exe : print_trace.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_0020_info.exe : print_0020_info.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_0020_core.exe : print_0020_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_0020_contacts.exe : print_0020_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_0021_contacts.exe : print_0021_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_stored_0021.exe : print_stored_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_stored_0021_valid.exe : test_stored_0021_valid.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

print_12_tree0_data.exe : print_12_tree0_data.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_synth_row2.exe : test_synth_row2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_audit_0021.exe : test_audit_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_0022_del.exe : test_0022_del.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_0022_zero.exe : test_0022_zero.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


synth_perfect_tag3.exe : synth_perfect_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


sweep_mix_0021.exe : sweep_mix_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


test_cage_0021.exe : test_cage_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_all_12.exe : inspect_all_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"


inspect_miss_cov.exe : inspect_miss_cov.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

closest_to_u0.exe : closest_to_u0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_stored_0021.exe : inspect_stored_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_single_axis_0021.exe : test_single_axis_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all_12_stored.exe : test_all_12_stored.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cage_03021.exe : test_cage_03021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_audit_stored_core.exe : test_audit_stored_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_derive.exe : test_derive.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_perfect_zero_defect_core.exe : find_perfect_zero_defect_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_pure_vertex_axes.exe : test_pure_vertex_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_contact2_mix.exe : test_contact2_mix.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_closest_zero_defect_core.exe : test_closest_zero_defect_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_norms.exe : print_norms.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_supp_all_12.exe : test_supp_all_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

compare_0020_0021.exe : compare_0020_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_03021_core.exe : print_03021_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_03021_axis_on_0021.exe : test_03021_axis_on_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_03021_axis_coverage_on_0021.exe : test_03021_axis_coverage_on_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cage_middle4.exe : test_cage_middle4.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_stored_cage_coords.exe : test_stored_cage_coords.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_origin_in_tetrahedron.exe : test_origin_in_tetrahedron.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_4_pts.exe : print_4_pts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_1_pt.exe : print_1_pt.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

sweep_ccone_0021.exe : sweep_ccone_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_fail_cell.exe : inspect_fail_cell.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_corners.exe : inspect_corners.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_pt_1008.exe : test_pt_1008.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_6axis_quadtree.exe : test_6axis_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fail_depth20.exe : test_fail_depth20.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_corner3_axis.exe : find_corner3_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_quadtree_guided_flock.exe : test_quadtree_guided_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_pt_953.exe : test_pt_953.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_stored_contacts.exe : print_stored_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_ccone_015_pool.exe : test_ccone_015_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_015_quadtree.exe : test_015_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_axis9030_tree.exe : test_axis9030_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cage_and_synth_0021.exe : test_cage_and_synth_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_ccone_21.exe : test_ccone_21.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cage_search.exe : test_cage_search.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_dirs.exe : print_dirs.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_flock_dots.exe : print_flock_dots.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_comp_dots.exe : print_comp_dots.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock6_tree.exe : test_flock6_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_uncov_leaf.exe : print_uncov_leaf.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_cluster_axis.exe : find_cluster_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_ccone21_ccore0004_tree.exe : test_ccone21_ccore0004_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_deep_point.exe : print_deep_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_stubborn_cover.exe : find_stubborn_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_tree_tight.exe : test_tree_tight.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_center_b.exe : test_center_b.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_leaf22.exe : print_leaf22.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_leaf_cover.exe : find_leaf_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

fast_find_cover.exe : fast_find_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

greedy_leaf_cover.exe : greedy_leaf_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_pool_coverage.exe : print_pool_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_axis_norms.exe : print_axis_norms.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_leaf199.exe : inspect_leaf199.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_centroid.exe : print_centroid.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

count_valid_contacts.exe : count_valid_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cap_silhouette.exe : test_cap_silhouette.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

count_all_valid_contacts.exe : count_all_valid_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_edge_lengths.exe : print_edge_lengths.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_degrees.exe : print_degrees.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_pool_dirs.exe : inspect_pool_dirs.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_annular_axis.exe : print_annular_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_delta.exe : print_delta.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_dec_fields.exe : print_dec_fields.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cage_0021_fixed.exe : test_cage_0021_fixed.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_existing_comp.exe : print_existing_comp.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_top_axes_for_v.exe : print_top_axes_for_v.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_axis_norm.exe : print_axis_norm.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_snub_dist.exe : test_snub_dist.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_zero_defect_angles.exe : inspect_zero_defect_angles.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_negative_z.exe : inspect_negative_z.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_annular_zero.exe : test_annular_zero.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_tree0_node.exe : print_tree0_node.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_mix200_zero.exe : test_mix200_zero.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_subdivide_0021.exe : test_subdivide_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_child1.exe : inspect_child1.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_child1_defect.exe : inspect_child1_defect.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_child1_flock.exe : test_child1_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all_12_tag2.exe : test_all_12_tag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_greedy_flock_0021.exe : test_greedy_flock_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_last_sample.exe : print_last_sample.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_child1_coverage.exe : test_child1_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_child1_quadtree.exe : test_child1_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_child1_exact_tree.exe : test_child1_exact_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_subdivide_tree_0021.exe : test_subdivide_tree_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_unres_0021.exe : test_unres_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_leaf_angle.exe : test_leaf_angle.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_u0_norm.exe : print_u0_norm.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

diag_child1_tree.exe : diag_child1_tree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_depth_fails.exe : test_depth_fails.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cegar_child1.exe : test_cegar_child1.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cegar_depth22.exe : test_cegar_depth22.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_axis_for_point.exe : print_axis_for_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_delta0.exe : print_delta0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_depth30.exe : test_depth30.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_full_cegar.exe : test_full_cegar.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_top_axes.exe : print_top_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_leaf_0020.exe : test_leaf_0020.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_verify_0020.exe : test_verify_0020.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all_11_subdiv.exe : test_all_11_subdiv.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_corner_cegar.exe : test_corner_cegar.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_build_quadtree.exe : test_build_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_add_sisters.exe : test_add_sisters.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fail_count.exe : test_fail_count.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_10_fails.exe : print_10_fails.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_depth12_coverage.exe : test_depth12_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_16_children_0021.exe : test_16_children_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fast_16.exe : test_fast_16.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fast_depth13.exe : test_fast_depth13.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_leaf_121_flock.exe : test_leaf_121_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_quadtree_121.exe : test_quadtree_121.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_quadtree_121_deep.exe : test_quadtree_121_deep.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_corner_axis.exe : test_corner_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_full_synth_121.exe : test_full_synth_121.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_contact_count.exe : test_contact_count.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_top5_dots.exe : print_top5_dots.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_depth14_all.exe : test_depth14_all.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_leaf_d14.exe : test_leaf_d14.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all4_121.exe : test_all4_121.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

count_subdiv_11.exe : count_subdiv_11.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_leaf_depths.exe : print_leaf_depths.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_leaf_tag2.exe : test_leaf_tag2.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

export_test_tag3.exe : export_test_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_dec_fields.exe : print_dec_fields.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cegar_5e5.exe : test_cegar_5e5.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_exact_0021_params.exe : test_exact_0021_params.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_actual_decomposed_leaves.exe : print_actual_decomposed_leaves.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_0021_d10.exe : test_0021_d10.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_0021_d12.exe : test_0021_d12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all_0021_d14.exe : test_all_0021_d14.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_full_synth_1212.exe : test_full_synth_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

sweep_mix_1212.exe : sweep_mix_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cegar_1212.exe : test_cegar_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_annular_0021.exe : print_annular_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_fail_v.exe : print_fail_v.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_corner_fail.exe : print_corner_fail.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_exact_fail.exe : print_exact_fail.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_all_12_dec.exe : print_all_12_dec.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_synth_1212.exe : inspect_synth_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_comb_1212.exe : test_comb_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_synth_iter_1212.exe : test_synth_iter_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cegar_inside.exe : test_cegar_inside.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_pool_size.exe : test_pool_size.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_v_dir.exe : print_v_dir.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_axis_5202.exe : print_axis_5202.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_axes_1212.exe : print_axes_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_ctr_ann_1212.exe : print_ctr_ann_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_ctr_ann_1210.exe : print_ctr_ann_1210.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_z_signs.exe : print_z_signs.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_hemi_1212.exe : test_flock_hemi_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_norm_1212.exe : test_flock_norm_1212.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_117.exe : inspect_117.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_neg_pts.exe : inspect_neg_pts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_corner_coords.exe : print_corner_coords.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_subdiv_0021.exe : test_subdiv_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_full_synth.exe : test_full_synth.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_all_12.exe : inspect_all_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_tag2_all12.exe : test_tag2_all12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_all12_tag2_exact.exe : test_all12_tag2_exact.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cegar_0021.exe : test_cegar_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_pool_contacts.exe : inspect_pool_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_fail_cell.exe : test_fail_cell.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_cert_leaf.exe : test_cert_leaf.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_one_tag3.exe : test_one_tag3.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_axis_from_0020.exe : test_axis_from_0020.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_mix200_pool.exe : test_mix200_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_with_mix200.exe : test_flock_with_mix200.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_10_pts.exe : test_10_pts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_good_axes.exe : print_good_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_solve_0021.exe : test_solve_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_solve_leaf.exe : test_solve_leaf.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_build_tree_leaf.exe : test_build_tree_leaf.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_root_cover.exe : test_root_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_old_axis.exe : test_old_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_box_cover.exe : find_box_cover.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_cage_0021.exe : find_cage_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_cell.exe : inspect_cell.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_tree_0021.exe : test_tree_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

export_0021.exe : export_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_params_0021.exe : test_params_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_sc_0021.exe : test_sc_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_8_unscaled.exe : test_8_unscaled.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_0021_pool_1node.exe : test_0021_pool_1node.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

sweep_sc_0021.exe : sweep_sc_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_tree_all4.exe : test_tree_all4.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

debug_cage_0021.exe : debug_cage_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

solve_0021_quadtree.exe : solve_0021_quadtree.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_perfect_match.exe : find_perfect_match.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

adaptive_flock_0021.exe : adaptive_flock_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_axis_5614.exe : test_axis_5614.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_tag2_0021.exe : test_tag2_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

audit_stored_0021.exe : audit_stored_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

audit_all_12_stored.exe : audit_all_12_stored.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

audit_8_core.exe : audit_8_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_flock_cohort_a.exe : find_flock_cohort_a.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_uncovered_samples.exe : inspect_uncovered_samples.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_root_box_coverage.exe : inspect_root_box_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_quadtree_from_pool.exe : test_quadtree_from_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_q00_coverage.exe : inspect_q00_coverage.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_point_axes.exe : inspect_point_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_limit_point.exe : inspect_limit_point.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_refined_pool.exe : test_refined_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)











find_boundary_axis.exe : find_boundary_axis.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_raw_pool.exe : inspect_raw_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

search_cage_0021.exe : search_cage_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_aligned_axes.exe : find_aligned_axes.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

check_flock_distribution.exe : check_flock_distribution.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

targeted_cage_search.exe : targeted_cage_search.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

find_pure_a0.exe : find_pure_a0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_03200.exe : inspect_03200.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

inspect_stored_12.exe : inspect_stored_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

audit_stored_dec.exe : audit_stored_dec.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_pool_12.exe : test_pool_12.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)





	$(CXX) $(CXXFLAGS) $^ -o $@

test_1node_from_pool.exe : test_1node_from_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_collar_flock.exe : test_collar_flock.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

sweep_inner_core.exe : sweep_inner_core.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_mix_0021.exe : test_mix_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_exact_contacts.exe : print_exact_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

compare_0020_0021.exe : compare_0020_0021.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_adaptive_collar.exe : test_adaptive_collar.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

diag_corner.exe : diag_corner.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

diag_pool_dirs.exe : diag_pool_dirs.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_1node_pool.exe : test_1node_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_all_bases.exe : print_all_bases.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_subdiv.exe : test_flock_subdiv.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

check_param_bounds.exe : check_param_bounds.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

compare_inner_vs_pool.exe : compare_inner_vs_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

print_norm_comp.exe : print_norm_comp.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_flock_around_u0.exe : test_flock_around_u0.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

build_leaf_cert.exe : build_leaf_cert.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

diag_uncovered.exe : diag_uncovered.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_corner_pool.exe : test_corner_pool.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

sweep_contacts.exe : sweep_contacts.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

test_0021_children.exe : test_0021_children.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
