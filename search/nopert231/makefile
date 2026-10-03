# Unit tests of the 5D library and the identity-tube code.
default : exact5d_test.exe geom5d_test.exe contacts5d_test.exe cert5d_test.exe tubeatlas5d_test.exe rows5d_test.exe solve5d_test.exe lp5d_test.exe tubetree231_test.exe nopert231_test.exe tube231_test.exe

# Every program (rebuild.sh runs the pipeline; see notes/R.md).
all: default qtube s5d codebdd231.exe tube-visualize.exe repair-margin.exe polyrigidity.exe proof-visualize.exe

# Identity tube (notes/Q.md, R.md):
#  codebdd231: exact rational model, codes and code triangles (codebdd231.json).
#  tubecode231: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine231: refines tube leaves to larger certified radii (monotone).
#  export_codetrees_pack: tube trees -> Lean packs (validate_code_pack).
#  tube-scoreboard: per-triangle status of the tube trees.
qtube: tubecode231.exe tuberefine231.exe export_codetrees_pack.exe tube-scoreboard.exe

# 5D search (notes/SEARCH5D.md):
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code (check with Noperthedron's
#    check_global_rows / constructNopert231).
#  scoreboard5d: per-job status from the journals and packs.
s5d: search5d.exe pack5d.exe scoreboard5d.exe

UNAME := $(shell uname -o)
ifeq ($(findstring Linux,$(UNAME)),Linux)
CC=clang
LIBCXX :=
CXX=clang++ $(LIBCXX)
PDB_FLAG=
else
PDB_FLAG=-Wl,--pdb=nopert231.pdb
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

# Library objects shared by the #231 tools. No OpenCL.
OBJECTS_231=nopert231.o tube231.o tubetree231.o rigidity-margin.o exact5d.o geom5d.o contacts5d.o bounds5d.o cert5d.o tubeatlas5d.o rows5d.o solve5d.o lp5d.o

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

# Generic pattern rules for executables
%.exe : %.o $(OBJECTS_231) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# First-order rigidity margin of the identity pose over all views, for
# repairing #214 (survey, sensitivity, and optimization modes; see
# nopert229/notes/R.md).
repair-margin.exe : repair-margin.o rigidity-margin.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Near-identity Rupert passage survey (first-order margin over all views,
# then a passage search at the worst) for any polyhedron.
polyrigidity.exe : polyrigidity.o rigidity-margin.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Oneoffs kept for reuse (each source has a Usage line); build with
# make oneoffs/<name>.exe.
#   5D search diagnostics (#231):
#     margin_terms5d   terms of the best certificate margin at given 5D nodes, and at the
#                      same box one view level coarser (diagnosed the split-rule wall)
#     point_margin5d   best margin at a pose as box and view shrink: positive (subdivision
#                      ends) or tending to zero (a possible Rupert passage)
#     solve_subtree5d  re-solve given 5D subtrees with a chosen split rule; compare rules
#   Passage and rigidity probes at single views (any candidate):
#     canyon_passage   search for a near-identity Rupert passage at a fixed outer view
#     canyon_truedepth first-order rigidity depth at a view (column generation)
#     canyon_depth     Tag 1 feasibility at single views near a code-triangle edge
#     multicage_probe  how much multi-axis cages would coarsen a code's tube tree
#   Python:
#     ideal231.py      idealized #231 (planar quads): formulae, and distances to the
#                      verified model, the double vertices and ruperts.sqlite
#   (#229's passage-witness scripts are on branch q, with #229's data.)
oneoffs/%.o : oneoffs/%.cc *.h makefile
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

oneoffs/%.exe : oneoffs/%.o $(OBJECTS_231) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_split : split-chart_test.exe
	./split-chart_test.exe

test_flatten : flatten-charts_test.exe
	./flatten-charts_test.exe

clean :
	rm -f *.o *.exe oneoffs/*.o oneoffs/*.exe
