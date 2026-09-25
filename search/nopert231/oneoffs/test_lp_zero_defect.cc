#include <iostream>
#include <vector>
#include <cmath>
#include "tube229.h"
#include "tubetree229.h"

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

  // Generate zero-defect candidate axes:
  std::vector<ContactInfo> cand_contacts;
  for (int mix : {0, 200, 400, 500, 600, 800, 1000}) {
    cand_contacts.push_back(MakeContact(3, 2, 2, 1, mix, 2));
    cand_contacts.push_back(MakeContact(1, 4, 4, 8, mix, 4));
    cand_contacts.push_back(MakeContact(4, 8, 8, 9, mix, 8));
    cand_contacts.push_back(MakeContact(8, 9, 9, 10, mix, 9));
    cand_contacts.push_back(MakeContact(9, 10, 10, 15, mix, 10));
    cand_contacts.push_back(MakeContact(10, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(14, 15, 15, 19, mix, 15));
    cand_contacts.push_back(MakeContact(13, 14, 14, 15, mix, 14));
    cand_contacts.push_back(MakeContact(2, 1, 1, 4, mix, 1));
    cand_contacts.push_back(MakeContact(15, 19, 19, 3, mix, 19));
  }

  int C = cand_contacts.size();
  std::vector<vec3> centers;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        std::string err;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          centers.push_back({center.x.ToDouble(), center.y.ToDouble(), center.z.ToDouble()});
        }
      }
    }
  }

  std::cout << "Audited " << centers.size() << " zero-defect axes.\n";

  // Check if origin is strictly separated from centers by trying random and grid directions:
  // If origin is outside, there exists a unit vector n such that n . c > 0 for all c in centers!
  // Min over c of (n . c) must be > 0.
  // We can search for such n by gradient descent on smooth approximation of min:
  // Or test sphere directions:
  double max_min_dot = -1e9;
  vec3 best_n = {0, 0, 0};

  for (int lat = -90; lat <= 90; lat += 2) {
    double phi = lat * M_PI / 180.0;
    for (int lon = 0; lon < 360; lon += 2) {
      double theta = lon * M_PI / 180.0;
      vec3 n = {std::cos(phi) * std::cos(theta), std::cos(phi) * std::sin(theta), std::sin(phi)};
      double min_dot = 1e9;
      for (const auto &c : centers) {
        double d = yocto::dot(n, c);
        if (d < min_dot) min_dot = d;
      }
      if (min_dot > max_min_dot) {
        max_min_dot = min_dot;
        best_n = n;
      }
    }
  }

  std::cout << "Max min_dot across sphere: " << max_min_dot << "\n";
  if (max_min_dot > 0) {
    std::cout << "SEPARATING PLANE FOUND! Origin is OUTSIDE by margin " << max_min_dot << "\n";
    std::cout << "Separating normal: (" << best_n.x << ", " << best_n.y << ", " << best_n.z << ")\n";
  } else {
    std::cout << "No separating direction found on grid! Max min_dot = " << max_min_dot << "\n";
  }

  return 0;
}
