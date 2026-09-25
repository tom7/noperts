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
	@echo -n "!"

clean :
	rm -f *.o *.exe

ifeq ($(OPT),)
  $(warning Warning: OPT is completely disabled!)
endif
