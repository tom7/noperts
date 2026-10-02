default : exact5d_test.exe geom5d_test.exe contacts5d_test.exe cert5d_test.exe tubeatlas5d_test.exe rows5d_test.exe solve5d_test.exe lp5d_test.exe annular229_test.exe tubetree229_test.exe nopert231_test.exe tube229_test.exe lib229_test.exe chart229_test.exe difficult229.exe lean229.exe pack229.exe test_all_pending.exe normalize-chart.exe compare-charts.exe split-chart.exe split-chart_test.exe flatten-charts.exe flatten-charts_test.exe

all: default test229.exe codebdd229.exe convert_tubecert229.exe incrementaltube229.exe tubecert229.exe tube-visualize.exe analyzedifficult.exe replace_tu_with_difficult.exe extract_tu_intervals.exe generate_seeds229.exe apply_shallow_cert.exe

# Quad-planar identity tube pipeline (notes/Q.md):
#  tubecode229: restartable (journaled) Tag 1 tree synthesis per code cell.
#  export_codetrees_pack: packs trees/tree.X.json for Lean's validate_code_pack.
#  tube-scoreboard: per-triangle status of all 79 codes / 157 triangles.
#  oneoffs/probe48edge: samples Tag 1 margins on sub-triangles along an edge
#    or a fixed path (reproduces the code 48 corner analysis, Q.md 1.7B).
#  oneoffs/canyon_depth, canyon_truedepth: first-order rigidity depth at a
#    single view (sampled / column-generated contacts), Q.md 1.8.
#  oneoffs/canyon_passage: searches for a near-identity Rupert passage at a
#    view (Q.md 1.8); oneoffs/rupert_witness229.py turns one into Lean data.
qtube: tubecode229.exe export_codetrees_pack.exe tube-scoreboard.exe oneoffs/probe48edge.exe oneoffs/canyon_depth.exe oneoffs/canyon_truedepth.exe oneoffs/canyon_passage.exe

# 5D search (notes/SEARCH5D.md):
#  search5d: parallel journaled search per (code triangle, chart) job.
#  pack5d: journals -> Lean global packs (check with Noperthedron's
#    check_global_rows / constructNopert229).
#  scoreboard5d: per-job status from the journals.
s5d: search5d.exe pack5d.exe scoreboard5d.exe

UNAME := $(shell uname -o)
ifeq ($(findstring Linux,$(UNAME)),Linux)
CC=clang
LIBCXX :=
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
OBJECTS_229=nopert231.o tube229.o tubetree229.o annular229.o chart229.o exact5d.o geom5d.o contacts5d.o bounds5d.o cert5d.o tubeatlas5d.o rows5d.o solve5d.o lp5d.o

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
%.exe : %.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# First-order rigidity margin of the identity pose over all views, for
# repairing #214 (survey, sensitivity, and optimization modes; see
# nopert229/notes/R.md).
repair-margin.exe : repair-margin.o $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

# Programs using lib229 (the 5D search library) also need lib229.o and
# OpenCL.
LIB229_EXES=lib229_test.exe lean229.exe difficult229.exe pack229.exe test229.exe generate_seeds229.exe
$(LIB229_EXES) : %.exe : %.o lib229.o $(OBJECTS_229) $(OBJECTS) $(CL_OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS) $(CL_LFLAGS)
	@echo -n "!"

oneoffs/%.o : oneoffs/%.cc *.h makefile
	@$(CXX) $(CXXFLAGS) -c $< -o $@
	@echo -n "."

oneoffs/%.exe : oneoffs/%.o $(OBJECTS_229) $(OBJECTS)
	@$(CXX) $^ -o $@ $(LFLAGS)
	@echo -n "!"

test_split : split-chart_test.exe
	./split-chart_test.exe

test_flatten : flatten-charts_test.exe
	./flatten-charts_test.exe

clean :
	rm -f *.o *.exe oneoffs/*.o oneoffs/*.exe
