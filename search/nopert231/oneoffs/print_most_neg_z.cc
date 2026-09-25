#include <iostream>
#include <vector>
#include <algorithm>
#include "tube229.h"
#include "tubetree229.h"

using namespace tubetree229;

int main() {
  std::string path = "03121303200";
  TriangleQ tri = TriangleFromPath(path);
  auto base_axes = Tube229::FindAllHullSupportAxes(tri, 5000);
  int N = base_axes.size();

  std::vector<std::pair<double, int>> z_axes;
  for (int i = 0; i < N; i++) {
    double z = base_axes[i].center.z.ToDouble() / base_axes[i].cert.B.ToDouble();
    z_axes.push_back({z, i});
  }

  std::sort(z_axes.begin(), z_axes.end());

  std::cout << "Top 20 most negative z axes:\n";
  for (int i = 0; i < 20; i++) {
    int idx = z_axes[i].second;
    double x = base_axes[idx].center.x.ToDouble() / base_axes[idx].cert.B.ToDouble();
    double y = base_axes[idx].center.y.ToDouble() / base_axes[idx].cert.B.ToDouble();
    double z = z_axes[i].first;
    std::cout << "Axis " << idx << ": (" << x << ", " << y << ", " << z << ")\n";
  }

  return 0;
}
