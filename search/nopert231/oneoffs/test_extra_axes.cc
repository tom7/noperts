#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  // 5 zero-defect axes from find_minimal_cover:
  // Let's get the 500 hull support axes and pick the top ones
  auto axes500 = Tube229::FindAllHullSupportAxes(tri, 500);
  std::vector<Tube229::CandidateTriple> extra_axes;
  for (const auto &ax : axes500) {
    Tube229::CandidateTriple ct;
    ct.contacts[0] = ax.cert.contacts[0];
    ct.contacts[1] = ax.cert.contacts[1];
    ct.contacts[2] = ax.cert.contacts[2];
    ct.normalized_a = {ax.center.x.ToDouble(), ax.center.y.ToDouble(), ax.center.z.ToDouble()};
    ct.B = ax.cert.B.ToDouble();
    extra_axes.push_back(ct);
  }

  std::cout << "Supplying " << extra_axes.size() << " zero-defect axes as extra_axes...\n";
  TubeCertificate cert;
  if (Tube229::SynthesizeCertificate(tri, 10, &cert, {}, extra_axes, /*fast_only=*/false)) {
    std::cout << "SUCCESS! SynthesizeCertificate found a valid 4-axis cage!\n";
    std::cout << "c = " << cert.c.ToDouble() << ", r = " << cert.r.ToDouble()
              << ", delta = " << cert.delta.ToDouble() << "\n";
  } else {
    std::cout << "Failed to find 4-axis cage even with all 500 zero-defect axes.\n";
  }

  return 0;
}
