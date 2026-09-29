
#include "nopert229.h"
#include "vertices229_exact27.h"

#include <array>

#include "bignum/big-vec.h"
#include "bignum/big.h"

const std::array<std::array<BigRat, 3>, NUM_VERTICES> &GetVerticesQ() {
  static const auto *v = []() {
    auto *res = new std::array<std::array<BigRat, 3>, NUM_VERTICES>;
    for (int i = 0; i < NUM_VERTICES; i++) {
      BigVecQ3 vq = VertexQ229(i);
      (*res)[i] = {vq.x, vq.y, vq.z};
    }
    return res;
  }();
  return *v;
}

const BigVecQ3 &VertexQ(size_t v) {
  static const auto *table = []() {
    auto *res = new std::array<BigVecQ3, NUM_VERTICES>;
    for (int i = 0; i < NUM_VERTICES; i++) {
      (*res)[i] = VertexQ229(i);
    }
    return res;
  }();
  return (*table)[v];
}
