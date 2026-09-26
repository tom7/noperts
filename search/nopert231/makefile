default : annular229_test.exe tubetree229_test.exe nopert229_test.exe tube229_test.exe lib229_test.exe export_tubetree_pack.exe difficult229.exe lean229.exe pack229.exe test_all_pending.exe

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
OBJECTS_229=nopert229.o tube229.o tubetree229.o annular229.o

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

test_cage_search.exe : test_cage_search.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_worst_all50k.exe : test_worst_all50k.o $(OBJECTS_229) $(OBJECTS)
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

test_contact2_10_15.exe : test_contact2_10_15.o $(OBJECTS_229) $(OBJECTS)
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

test229.exe : test229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

lean229.exe : lean229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

difficult229.exe : difficult229.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

pack229.exe : pack229.o lib229.o nopert229.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

export_tubetree_pack.exe : export_tubetree_pack.o $(OBJECTS_229) $(OBJECTS)
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

generate_seeds229.exe : generate_seeds229.o lib229.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

apply_shallow_cert.exe : apply_shallow_cert.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

verify_leaf.exe : verify_leaf.o nopert229.o $(OBJECTS)
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

clean :
	rm -f *.o *.exe

ifeq ($(OPT),)
  $(warning Warning: OPT is completely disabled!)
endif
