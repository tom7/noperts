#include <iostream>
#include <string>
#include <cmath>
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
  std::string target = "03121303200";
  TriangleQ tri = TriangleFromPath(target);

  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };

  std::string err;
  AxisCertificate ax0, ax1, ax2, ax3;
  BigVecQ3 ctr0, ctr1, ctr2, ctr3;
  BigRat del0, del1, del2, del3;

  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(0));
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(0));
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(0));

  BigRat box_c(1, 1000);
  BigRat c_cone(65, 1000);
  BigRat B0 = ax0.B;
  BigRat B_prime = B0 * c_cone / box_c;

  std::cout << "Original B0 = " << B0.ToString() << " (" << B0.ToDouble() << ")\n";
  std::cout << "Scaled B'   = " << B_prime.ToString() << " (" << B_prime.ToDouble() << ")\n";

  // Check annular dominance with B_prime and c_cone = box_c:
  BigRat r(1, 300);
  BigRat r_min(1, 400);
  BigRat D0("13151143718341826856311484754606017041620112299484449951370602771939059/220332032000000000000000000000000000000000000000000000000000000000000000000"); // or true D0
  BigRat delta = del0; // delta0 is around 0.00007

  std::cout << "delta = " << delta.ToString() << " (" << delta.ToDouble() << ")\n";

  BigRat lhs = BigRat(1, 2) * r * r * B_prime + D0;
  lhs = lhs * lhs;

  BigRat rhs = r_min * r_min * (BigRat(1) - BigRat(1, 4) * r * r) * (box_c - delta) * (box_c - delta) * B_prime * B_prime;

  std::cout << "LHS = " << lhs.ToDouble() << "\n";
  std::cout << "RHS = " << rhs.ToDouble() << "\n";
  std::cout << "Annular dominance holds: " << (lhs <= rhs ? "YES!" : "NO") << "\n";

  // Check barycentric valid:
  TubeCertificate cage;
  cage.c = box_c;
  cage.delta = delta;
  cage.r = r;
  cage.axes[0] = ax0;
  cage.axes[0].B = B_prime;
  cage.axes[1] = ax1;
  cage.axes[2] = ax2;
  cage.axes[3] = ax3;

  TubeCertificate verified;
  bool audit_ok = Tube229::AuditCertificateAdaptive(tri, cage, &verified, &err);
  std::cout << "AuditCertificateAdaptive with scaled B': " << (audit_ok ? "SUCCESS!" : "FAILED: " + err) << "\n";

  return 0;
}
