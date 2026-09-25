#include <iostream>
#include <vector>
#include <memory>
#include <string>
#include <filesystem>
#include "bignum/big-overloads.h"
#include "tubetree229.h"
#include "tube229.h"
#include "base/logging.h"

using namespace tubetree229;

static inline vec3 ToVec3(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

static bool FindCageCert(const std::string &path, TubeCertificate *out_cert) {
  TriangleQ tri = TriangleFromPath(path);
  auto axes = Tube229::FindAllHullSupportAxes(tri, 200);

  int N = axes.size();
  for (int i0 = 0; i0 < N; i0++) {
    vec3 c0 = ToVec3(axes[i0].center);
    for (int i1 = i0 + 1; i1 < N; i1++) {
      vec3 c1 = ToVec3(axes[i1].center);
      for (int i2 = i1 + 1; i2 < N; i2++) {
        vec3 c2 = ToVec3(axes[i2].center);
        for (int i3 = i2 + 1; i3 < N; i3++) {
          vec3 c3 = ToVec3(axes[i3].center);

          double V0 = yocto::dot(c1, yocto::cross(c2, c3));
          double V1 = -yocto::dot(c0, yocto::cross(c2, c3));
          double V2 = yocto::dot(c0, yocto::cross(c1, c3));
          double V3 = -yocto::dot(c0, yocto::cross(c1, c2));

          double total = V0 + V1 + V2 + V3;
          if (std::abs(total) < 1e-6) continue;

          double l0 = V0 / total;
          double l1 = V1 / total;
          double l2 = V2 / total;
          double l3 = V3 / total;

          if (l0 > 0.05 && l1 > 0.05 && l2 > 0.05 && l3 > 0.05) {
            TubeCertificate test_cert;
            test_cert.axes[0] = axes[i0].cert;
            test_cert.axes[1] = axes[i1].cert;
            test_cert.axes[2] = axes[i2].cert;
            test_cert.axes[3] = axes[i3].cert;

            std::string fail;
            if (Tube229::AuditCertificateAdaptive(tri, test_cert, out_cert, &fail)) {
              std::cout << "  Certified " << path << ": c=" << out_cert->c.ToDouble()
                        << ", r=" << out_cert->r.ToDouble() << "\n";
              return true;
            }
          }
        }
      }
    }
  }
  return false;
}

static TreeNode* FindNodeByPath(TreeNode *node, const std::string &path) {
  if (node->path == path) return node;
  for (auto &child : node->children) {
    if (child) {
      TreeNode *res = FindNodeByPath(child.get(), path);
      if (res) return res;
    }
  }
  return nullptr;
}

int main() {
  std::string base_dir = std::filesystem::exists("ruperts/.artifacts/nopert229") ? "ruperts/.artifacts/nopert229" : ".artifacts/nopert229";
  std::string tree_path = base_dir + "/tree_0.json";
  std::cout << "Loading tree from " << tree_path << "...\n";
  auto root = LoadTreeJson(tree_path, false, base_dir);
  CHECK(root != nullptr);

  std::vector<std::string> single_leaves = {
    "03121303021",
    "03121303022",
    "03121303023",
    "03121303200",
    "0312130332"
  };

  for (const auto &p : single_leaves) {
    TreeNode *node = FindNodeByPath(root.get(), p);
    if (!node) {
      std::cerr << "Node not found: " << p << "\n";
      return 1;
    }
    TubeCertificate cert;
    if (!FindCageCert(p, &cert)) {
      std::cerr << "Failed to find cage cert for " << p << "\n";
      return 1;
    }
    node->direct_cert = cert;
    node->decomposed_cert.reset();
  }

  // Handle 03121300 by subdividing into 4 children:
  std::string split_path = "03121300";
  TreeNode *split_node = FindNodeByPath(root.get(), split_path);
  if (!split_node) {
    std::cerr << "Split node not found: " << split_path << "\n";
    return 1;
  }

  split_node->children.clear();
  split_node->direct_cert.reset();
  split_node->decomposed_cert.reset();
  for (int c = 0; c < 4; c++) {
    std::string child_path = split_path + std::to_string(c);
    auto child = std::make_unique<TreeNode>();
    child->path = child_path;
    TubeCertificate cert;
    if (!FindCageCert(child_path, &cert)) {
      std::cerr << "Failed to find cage cert for child " << child_path << "\n";
      return 1;
    }
    child->direct_cert = cert;
    child->decomposed_cert.reset();
    split_node->children.push_back(std::move(child));
  }

  std::cout << "Computing effective bounds after applying canyon certificates...\n";
  EffectiveBounds eff = ComputeEffectiveBounds(*root);
  std::cout << "Root effective bounds: r_lower = " << eff.r_lower.ToString()
            << ", r_upper = " << eff.r_upper.ToString()
            << ", complete = " << (eff.complete ? "YES" : "NO") << "\n";

  if (eff.complete && eff.r_lower > BigRat(0)) {
    std::cout << "SUCCESS! Tree 0 is 100% certified with positive radius!\n";
    std::string out_path = base_dir + "/tree_0_complete.json";
    std::cout << "Saving complete tree to " << out_path << "...\n";
    SaveTreeJson(*root, out_path, false);
    std::cout << "Saved successfully!\n";
  } else {
    std::cerr << "Tree 0 is still incomplete!\n";
    return 1;
  }

  return 0;
}
