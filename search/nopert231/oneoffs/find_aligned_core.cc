#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"
#include "bignum/big-overloads.h"


using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 center0;
  BigRat delta0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &center0, &delta0, &err, BigRat(5, 1000));

  std::cout << "ax0 center: (" << center0.x.ToDouble() << ", " << center0.y.ToDouble() << ", " << center0.z.ToDouble() << ")\n";

  // Let's test all possible triples among the 9 vertices of the hull:
  // Vertices of the 9-vertex hull are: 0, 1, 2, 3, 4, 8, 10, 15, 19
  // Let's test all support axes from FindAllHullSupportAxes:
  auto axes = Tube229::FindAllHullSupportAxes(tri, 500);
  std::cout << "Testing " << axes.size() << " hull support axes for positive dot product with ax0...\n";

  BigVecQ3 u0 = {center0.x / ax0.B, center0.y / ax0.B, center0.z / ax0.B};
  double u0_len = std::sqrt((u0.x*u0.x + u0.y*u0.y + u0.z*u0.z).ToDouble());

  int best_idx = -1;
  double best_cos = -2.0;

  for (size_t i = 0; i < axes.size(); i++) {
    BigVecQ3 uc = {axes[i].center.x / axes[i].cert.B, axes[i].center.y / axes[i].cert.B, axes[i].center.z / axes[i].cert.B};
    double uc_len = std::sqrt((uc.x*uc.x + uc.y*uc.y + uc.z*uc.z).ToDouble());
    double dot = (u0.x*uc.x + u0.y*uc.y + u0.z*uc.z).ToDouble();
    double cos_ang = dot / (u0_len * uc_len);
    if (cos_ang > best_cos) {
      best_cos = cos_ang;
      best_idx = i;
    }
  }

  std::cout << "Best hull support axis is #" << best_idx << " with cos(angle) = " << best_cos << "\n";
  const auto &best = axes[best_idx];
  std::cout << "Contacts: " << best.cert.contacts[0].vertex << ", "
            << best.cert.contacts[1].vertex << ", " << best.cert.contacts[2].vertex << "\n";
  std::cout << "Center: (" << best.center.x.ToDouble() << ", " << best.center.y.ToDouble() << ", " << best.center.z.ToDouble() << ")\n";

  return 0;
}
