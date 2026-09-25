#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static vec3 ToD(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);
  vec3 tri_f[3] = { ToD(tri.corners[0]), ToD(tri.corners[1]), ToD(tri.corners[2]) };
  vec3 centroid = (tri_f[0] + tri_f[1] + tri_f[2]) / 3.0;

  auto contacts = Tube229::GenerateSilhouetteContacts(centroid, {0, 200, 333, 500, 800, 1000});

  ContactInfo c0[3] = {
    {3, 2, 2, 1, 800, 2},
    {1, 4, 4, 8, 800, 4},
    contacts[47]
  };
  AxisCertificate ax0; BigVecQ3 ctr0; BigRat del0; std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(0));

  std::cout << "def ax0_zero : AxisCertificate := {\n";
  std::cout << "  edgeStart := ![" << (int)ax0.contacts[0].edge_start << ", "
                                  << (int)ax0.contacts[1].edge_start << ", "
                                  << (int)ax0.contacts[2].edge_start << "],\n";
  std::cout << "  edgeFinish := ![" << (int)ax0.contacts[0].edge_finish << ", "
                                   << (int)ax0.contacts[1].edge_finish << ", "
                                   << (int)ax0.contacts[2].edge_finish << "],\n";
  std::cout << "  edgeStart₂ := ![" << (int)ax0.contacts[0].edge_start2 << ", "
                                   << (int)ax0.contacts[1].edge_start2 << ", "
                                   << (int)ax0.contacts[2].edge_start2 << "],\n";
  std::cout << "  edgeFinish₂ := ![" << (int)ax0.contacts[0].edge_finish2 << ", "
                                    << (int)ax0.contacts[1].edge_finish2 << ", "
                                    << (int)ax0.contacts[2].edge_finish2 << "],\n";
  std::cout << "  mix := ![" << ax0.contacts[0].mix << ", "
                             << ax0.contacts[1].mix << ", "
                             << ax0.contacts[2].mix << "],\n";
  std::cout << "  index := ![" << (int)ax0.contacts[0].vertex << ", "
                               << (int)ax0.contacts[1].vertex << ", "
                               << (int)ax0.contacts[2].vertex << "],\n";
  std::cout << "  nonzeroWitness := ![" << (int)ax0.nonzero_witness[0] << ", "
                                        << (int)ax0.nonzero_witness[1] << ", "
                                        << (int)ax0.nonzero_witness[2] << "],\n";
  std::cout << "  B := " << ax0.B.Numerator().ToString() << " / " << ax0.B.Denominator().ToString() << "\n";
  std::cout << "}\n\n";

  return 0;
}
