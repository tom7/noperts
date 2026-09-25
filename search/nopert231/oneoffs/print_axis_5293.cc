#include <iostream>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  double box_delta = 234013.0 / 1000000000.0;
  std::vector<std::pair<std::string, Tube229::AuditedAxis>> valid_axes;
  for (size_t i = 0; i < axes.size(); i++) {
    if (axes[i].delta.ToDouble() <= box_delta) {
      valid_axes.push_back({"base " + std::to_string(i), axes[i]});
    }
  }
  for (int m1 = 0; m1 <= 1000; m1 += 50) {
    for (int m2 = 0; m2 <= 1000; m2 += 50) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      std::string err;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({"coarse m1=" + std::to_string(m1) + " m2=" + std::to_string(m2), {cert, ctr, del}});
        }
      }
    }
  }
  for (int m1 : {700, 800, 850, 900, 950, 1000}) {
    for (int m2 = 200; m2 <= 400; m2 += 10) {
      ContactInfo contacts[3] = {
        {2, 1, 1, 4, 0, 1},
        {10, 15, 15, 19, m1, 15},
        {3, 2, 2, 1, m2, 2}
      };
      AxisCertificate cert;
      BigVecQ3 ctr;
      BigRat del;
      std::string err;
      if (Tube229::AuditAxis(tri, contacts, &cert, &ctr, &del, &err, BigRat(1, 1000))) {
        if (del.ToDouble() <= box_delta) {
          valid_axes.push_back({"fine m1=" + std::to_string(m1) + " m2=" + std::to_string(m2), {cert, ctr, del}});
        }
      }
    }
  }

  std::cout << "5293 info: " << valid_axes[5293].first << "\n";
  std::cout << "5162 info: " << valid_axes[5162].first << "\n";
  return 0;
}
