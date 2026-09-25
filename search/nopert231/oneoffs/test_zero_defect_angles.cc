#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"
#include "yocto-math.h"

using namespace tubetree229;

static ContactInfo MakeContact(int start, int finish, int start2, int finish2, int mix, int v) {
  ContactInfo c;
  c.edge_start = start; c.edge_finish = finish;
  c.edge_start2 = start2; c.edge_finish2 = finish2;
  c.mix = mix; c.vertex = v;
  return c;
}

int main() {
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  std::string err;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  vec3 u0 = {ctr0.x.ToDouble() / ax0.B.ToDouble(), ctr0.y.ToDouble() / ax0.B.ToDouble(), ctr0.z.ToDouble() / ax0.B.ToDouble()};
  vec3 u0_hat = yocto::normalize(u0);

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
  std::vector<double> dots;

  for (int i = 0; i < C; i++) {
    for (int j = i + 1; j < C; j++) {
      for (int k = j + 1; k < C; k++) {
        ContactInfo triple[3] = {cand_contacts[i], cand_contacts[j], cand_contacts[k]};
        AxisCertificate ax;
        BigVecQ3 center;
        BigRat delta;
        if (Tube229::AuditAxis(tri, triple, &ax, &center, &delta, &err, BigRat(0))) {
          vec3 u = {center.x.ToDouble() / ax.B.ToDouble(), center.y.ToDouble() / ax.B.ToDouble(), center.z.ToDouble() / ax.B.ToDouble()};
          double dot = yocto::dot(yocto::normalize(u), u0_hat);
          dots.push_back(dot);
        }
      }
    }
  }

  std::sort(dots.begin(), dots.end());
  std::cout << "Found " << dots.size() << " zero-defect axes.\n";
  std::cout << "Min dot with u0: " << dots.front() << "\n";
  std::cout << "Max dot with u0: " << dots.back() << "\n";
  std::cout << "Percentiles:\n";
  for (int p : {0, 10, 25, 50, 75, 90, 95, 99, 100}) {
    int idx = std::min((int)dots.size() - 1, (int)(dots.size() * p / 100.0));
    std::cout << "  p" << p << ": dot = " << dots[idx] << " (angle = " << std::acos(std::clamp(dots[idx], -1.0, 1.0)) * 180.0 / M_PI << " deg)\n";
  }

  return 0;
}
