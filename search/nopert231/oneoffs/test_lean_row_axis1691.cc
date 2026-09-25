#include <iostream>
#include <fstream>
#include <iomanip>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

static ContactInfo MakeContact(int es, int ef, int es2, int ef2, int mix, int idx) {
  return ContactInfo{es, ef, es2, ef2, mix, idx};
}

void PrintAxisLean(const std::string &name, const AxisCertificate &ax) {
  std::cout << "def " << name << " : AxisCertificate := {\n";
  std::cout << "  contacts := fun\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "    | " << i << " => { edgeStart := " << ax.contacts[i].edgeStart
              << ", edgeFinish := " << ax.contacts[i].edgeFinish
              << ", edgeStart2 := " << ax.contacts[i].edgeStart2
              << ", edgeFinish2 := " << ax.contacts[i].edgeFinish2
              << ", mix := " << ax.contacts[i].mix
              << ", index := " << ax.contacts[i].index << " }\n";
  }
  std::cout << "  nonzeroWitness := fun\n";
  for (int i = 0; i < 3; i++) {
    std::cout << "    | " << i << " => " << ax.nonzeroWitness[i] << "\n";
  }
  std::cout << "  B := " << ax.B.Numerator().ToString() << " / " << ax.B.Denominator().ToString() << "\n";
  std::cout << "}\n\n";
}

int main() {
  std::string target = "03121300";
  TriangleQ tri = TriangleFromPath(target);
  std::string err;

  // Annular axis c0
  ContactInfo c0[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(1, 4, 4, 8, 800, 4),
    MakeContact(13, 14, 14, 15, 200, 14)
  };
  AxisCertificate ax0;
  BigVecQ3 ctr0;
  BigRat del0;
  Tube229::AuditAxis(tri, c0, &ax0, &ctr0, &del0, &err, BigRat(5, 1000));

  // Axis 1691
  ContactInfo core_contacts[3] = {
    MakeContact(15, 19, 19, 3, 900, 19),
    MakeContact(3, 2, 2, 1, 333, 2),
    MakeContact(4, 8, 8, 9, 1000, 8)
  };
  AxisCertificate core_axis;
  BigVecQ3 core_center;
  BigRat core_delta;
  Tube229::AuditAxis(tri, core_contacts, &core_axis, &core_center, &core_delta, &err, BigRat(0));

  ContactInfo c1[3] = {
    MakeContact(15, 19, 19, 3, 200, 19),
    MakeContact(2, 1, 1, 4, 200, 1),
    MakeContact(8, 9, 9, 10, 200, 9)
  };
  AxisCertificate ax1;
  BigVecQ3 ctr1;
  BigRat del1;
  Tube229::AuditAxis(tri, c1, &ax1, &ctr1, &del1, &err, BigRat(5, 1000));

  ContactInfo c2[3] = {
    MakeContact(2, 1, 1, 4, 0, 1),
    MakeContact(10, 15, 15, 19, 333, 15),
    MakeContact(10, 15, 15, 19, 0, 15)
  };
  AxisCertificate ax2;
  BigVecQ3 ctr2;
  BigRat del2;
  Tube229::AuditAxis(tri, c2, &ax2, &ctr2, &del2, &err, BigRat(5, 1000));

  ContactInfo c3[3] = {
    MakeContact(3, 2, 2, 1, 800, 2),
    MakeContact(4, 8, 8, 9, 800, 8),
    MakeContact(14, 15, 15, 19, 800, 15)
  };
  AxisCertificate ax3;
  BigVecQ3 ctr3;
  BigRat del3;
  Tube229::AuditAxis(tri, c3, &ax3, &ctr3, &del3, &err, BigRat(5, 1000));

  BigVecQ3 u_ann = {ctr0.x / ax0.B, ctr0.y / ax0.B, ctr0.z / ax0.B};
  BigVecQ3 u_core = {core_center.x / core_axis.B, core_center.y / core_axis.B, core_center.z / core_axis.B};

  BigRat u_ann_sq = u_ann.x * u_ann.x + u_ann.y * u_ann.y + u_ann.z * u_ann.z;
  BigRat dot_ann_core = u_ann.x * u_core.x + u_ann.y * u_core.y + u_ann.z * u_core.z;
  BigRat u_core_sq = u_core.x * u_core.x + u_core.y * u_core.y + u_core.z * u_core.z;
  double cos_theta = dot_ann_core.ToDouble() / std::sqrt(u_ann_sq.ToDouble() * u_core_sq.ToDouble());
  double theta_deg = std::acos(std::clamp(cos_theta, -1.0, 1.0)) * 180.0 / M_PI;
  std::cerr << "Angle between u0 and u_core: " << theta_deg << " deg\n";
  BigRat lam = dot_ann_core / u_ann_sq;
  BigVecQ3 w = {u_core.x - lam * u_ann.x, u_core.y - lam * u_ann.y, u_core.z - lam * u_ann.z};

  std::cout << "def testTriangle : AtlasProjectiveView.Triangle ℚ := fun\n";
  for (int i = 0; i < 3; i++) {
    BigRat coords[3] = {tri.corners[i].x, tri.corners[i].y, tri.corners[i].z};
    for (int j = 0; j < 3; j++) {
      std::cout << "  | " << i << ", " << j << " => "
                << coords[j].Numerator().ToString() << " / "
                << coords[j].Denominator().ToString() << "\n";
    }
  }
  std::cout << "\n";

  std::cout << "-- Lean 4 definitions for manual decomposed certificate test:\n";
  PrintAxisLean("ax0", ax0);
  PrintAxisLean("ax1", ax1);
  PrintAxisLean("ax2", ax2);
  PrintAxisLean("ax3", ax3);
  PrintAxisLean("coreAx", core_axis);

  std::cout << "def testLam : ℚ := " << lam.Numerator().ToString() << " / " << lam.Denominator().ToString() << "\n";
  std::cout << "def testW : Fin 3 → ℚ := !["
            << w.x.Numerator().ToString() << " / " << w.x.Denominator().ToString() << ", "
            << w.y.Numerator().ToString() << " / " << w.y.Denominator().ToString() << ", "
            << w.z.Numerator().ToString() << " / " << w.z.Denominator().ToString() << "]\n";
  std::cout << "def testDefect0 : Fin 3 → ℚ := !["
            << del0.Numerator().ToString() << " / " << del0.Denominator().ToString() << ", 0, 0]\n";
  std::cout << "def testD0 : ℚ := " << del0.Numerator().ToString() << " / " << del0.Denominator().ToString() << "\n";

  return 0;
}
