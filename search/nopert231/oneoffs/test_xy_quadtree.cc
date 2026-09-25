#include <cstdio>
#include <vector>
#include <cmath>
#include <algorithm>
#include "../cc-lib/bignum/bigq.h"

// Check quadtree on [-L, L]^2 in (x, y) coordinates on tangent plane H = { p : <p, u0> = 1 }.
// Any point in H is p(x, y) = (x, y, (1 - x*u0x - y*u0y)/u0z).

struct V3 {
    double x, y, z;
    V3(double x=0, double y=0, double z=0) : x(x), y(y), z(z) {}
    double dot(const V3& o) const { return x*o.x + y*o.y + z*o.z; }
    double norm() const { return std::sqrt(dot(*this)); }
};

struct HullAxis {
    int id;
    V3 v;
};

int main() {
    // Load u0 and core axes from test_quadtree_tangent.cc logic
    FILE* fp = popen("./ruperts/test_quadtree_tangent.exe 2>&1", "r");
    // Just run a quick check of the exact math
    return 0;
}
