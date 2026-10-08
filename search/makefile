# Unit tests.
default : exact5d_test.exe geom5d_test.exe contacts5d_test.exe cert5d_test.exe tubeatlas5d_test.exe rows5d_test.exe solve5d_test.exe lp5d_test.exe tubetree_test.exe model_test.exe tube_test.exe

# Every program of the pipeline (rebuild.sh runs it).
all: default qtube s5d codebdd.exe icoprune_check.exe halfturn_check.exe tieviz.exe tietube.exe dfwhere.exe capleaf_check.exe pool_check.exe capcert.exe viewmap.exe shadowanim.exe

# Identity tube:
#  codebdd: exact rational model, codes and code triangles (codebdd.json).
#  tubecode: restartable (journaled) Tag 1 tree synthesis per code.
#  tuberefine: refines tube leaves to larger certified radii (monotone).
#  export_codetrees_pack: tube trees -> Lean packs (validate_code_pack).
qtube: tubecode.exe tuberefine.exe export_codetrees_pack.exe

# 5D search:
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean packs, one per code (checked by Noperthedron's
#    constructPentagonalHexecontahedron).
#  scoreboard5d: per-job status from the journals and packs.
#  icoprune_check: floating-point check of the icosahedral prune leaves
#    (icoprune_check.exe --journals DIR).
#  halfturn_check: floating-point check of the half-turn prune (centrally
#    symmetric solids: the group, the reduction's invariance, sampled boxes).
s5d: search5d.exe pack5d.exe scoreboard5d.exe

# Rendering (not part of the proof):
#  viewmap: the first-order margin, search density or tube radius over all
#    views, as an equirectangular image and a UDIM-textured OBJ of the solid.
#  shadowanim: an animation of first-order rigidity (shadowanim.txt).

UNAME := $(shell uname -o)
ifeq ($(findstring Linux,$(UNAME)),Linux)
CC=clang
LIBCXX :=
CXX=clang++ $(LIBCXX)
PDB_FLAG=
else
PDB_FLAG=-Wl,--pdb=nopert.pdb
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

# Library objects shared by the tools. No OpenCL.
OBJECTS_CORE=model.o tube.o tubetree.o tieatlas5d.o exact5d.o geom5d.o contacts5d.o bounds5d.o cert5d.o tubeatlas5d.o rows5d.o solve5d.o lp5d.o

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

shadowanim.exe : shadowanim.o rigidity-margin.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

viewmap.exe : viewmap.o rigidity-margin.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Generic pattern rules for executables
%.exe : %.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

halfturn_check.exe : halfturn_check.o rigidity-margin.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# tieviz: 4K pictures/animations of the deltoidal hexecontahedron's ties (video; see tieviz.txt).
tieviz.exe : tieviz.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# tietube: exact tie tubes for the deltoidal hexecontahedron (dh_tie_data.py; notes/T.md).
tietube.exe : tietube.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# dfwhere: where a 5D job's deferred leaves are (diagnostic).
dfwhere.exe : dfwhere.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

tufix.exe : tufix.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# pool_check: the pools' weighted defect bounds (Pareto frontiers) equal the direct maximum.
pool_check.exe : pool_check.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

# capleaf_check: exact re-check of the 5D journals' cap leaves.
capleaf_check.exe : capleaf_check.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)

# capcert: cap certificates for the deltoidal hexecontahedron's special views (work in progress; notes/T.md).
capcert7.exe : capcert7.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

capcert.exe : capcert.o $(OBJECTS_CORE) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"
