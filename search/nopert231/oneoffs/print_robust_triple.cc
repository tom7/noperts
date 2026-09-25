#include <iostream>
#include <vector>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto all_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int N = all_axes.size();

  std::vector<Tube229::AuditedAxis> robust_axes;
  std::string err;
  for (int i = 0; i < N; i++) {
    BigRat var_radius;
    AxisCertificate ax;
    BigVecQ3 cnt;
    if (!Tube229::AuditAxis(tri, all_axes[i].cert.contacts, &ax, &cnt, &var_radius, &err, BigRat(5, 1000))) continue;
    if (ax.B.ToDouble() < 0.05) continue;
    double var_ratio = var_radius.ToDouble() / ax.B.ToDouble();
    if (var_ratio <= 0.000234013) {
      robust_axes.push_back(all_axes[i]);
    }
  }

  int idxs[3] = {184, 2262, 2899};
  for (int k = 0; k < 3; k++) {
    auto a = robust_axes[idxs[k]];
    std::cout << "Cage Axis " << (k+1) << " (idx " << idxs[k] << "): B = " << a.cert.B.ToString() << "\n";
    for (int i = 0; i < 3; i++) {
      std::cout << "  c" << i << ": (" << a.cert.contacts[i].edge_start << "," << a.cert.contacts[i].edge_finish
                << ")-(" << a.cert.contacts[i].edge_start2 << "," << a.cert.contacts[i].edge_finish2
                << ") mix=" << a.cert.contacts[i].mix << " v=" << a.cert.contacts[i].vertex << "\n";
    }
  }
  return 0;
}
