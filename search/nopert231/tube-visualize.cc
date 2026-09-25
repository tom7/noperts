// High-resolution spherical map and margin visualization for Nopert #229.
// Visualizes incremental tubetree data (tubetree229_v1) and empirical clearances
// across the upper wedge fundamental domain, the projective plane, and the full sphere.

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <fstream>
#include <numbers>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "base/logging.h"
#include "base/print.h"
#include "color-util.h"
#include "image.h"
#include "ruperts-util.h"
#include "timer.h"
#include "tubetree229.h"
#include "util.h"
#include "yocto-math.h"

template<typename... Args>
inline void Printf(const char *fmt, Args &&...args) {
  std::printf(fmt, std::forward<Args>(args)...);
}
inline void Printf(const char *str) {
  std::fputs(str, stdout);
}

static inline vec3 ToDouble(const BigVecQ3 &v) {
  return vec3{v.x.ToDouble(), v.y.ToDouble(), v.z.ToDouble()};
}

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;
using namespace tubetree229;

// 4K UHD 16:9 canvas dimensions.
static constexpr int WIDTH  = 3840;
static constexpr int HEIGHT = 2160;

// Margin color map limits (logarithmic scale).
// Minimum certified margin c = 0.00020 (cut margin).
// Maximum scale margin c = 0.01000 (wide margin).
static constexpr double C_MIN = 0.00020;
static constexpr double C_MAX = 0.01000;

// Fundamental domain angular bounds for C5 rotational symmetry.
static constexpr double PHI_MAX_DEG  = 72.0;
static constexpr double ELEV_MAX_DEG = 90.0;
static constexpr double PHI_MAX_RAD  = PHI_MAX_DEG * std::numbers::pi / 180.0;

// Empirically discovered pinch canyons for Nopert #229.
struct CanyonGuide {
  const char *name;
  double phi_deg;
  double elev_deg;
  double phi_rad;
  double elev_rad;
  vec3 v;
  double c;
};

static const CanyonGuide CANYON1 = {
  .name = "Canyon 1 (Az 2.22', Elev 9.63')",
  .phi_deg = 2.222956,
  .elev_deg = 9.634125,
  .phi_rad = 2.222956 * std::numbers::pi / 180.0,
  .elev_rad = 9.634125 * std::numbers::pi / 180.0,
  .v = vec3{
    std::cos(9.634125 * std::numbers::pi / 180.0) * std::cos(2.222956 * std::numbers::pi / 180.0),
    std::cos(9.634125 * std::numbers::pi / 180.0) * std::sin(2.222956 * std::numbers::pi / 180.0),
    std::sin(9.634125 * std::numbers::pi / 180.0)
  },
  .c = 0.0002509,
};

static const CanyonGuide CANYON2 = {
  .name = "Canyon 2 (Az 12.90', Elev 18.48')",
  .phi_deg = 12.898822,
  .elev_deg = 18.476442,
  .phi_rad = 12.898822 * std::numbers::pi / 180.0,
  .elev_rad = 18.476442 * std::numbers::pi / 180.0,
  .v = vec3{
    std::cos(18.476442 * std::numbers::pi / 180.0) * std::cos(12.898822 * std::numbers::pi / 180.0),
    std::cos(18.476442 * std::numbers::pi / 180.0) * std::sin(12.898822 * std::numbers::pi / 180.0),
    std::sin(18.476442 * std::numbers::pi / 180.0)
  },
  .c = 0.0002278,
};

// Continuous color gradient palette for clearance margins:
// tau = 0.00 (Critical pinch) -> Deep Crimson (#C8102E)
// tau = 0.20 (Narrow margin)  -> Bright Orange (#FF8C00)
// tau = 0.40 (Safe margin)    -> Vibrant Yellow (#FFD700)
// tau = 0.70 (Wide margin)    -> Bright Cyan (#00C0C0)
// tau = 1.00 (Maximum margin) -> Deep Cobalt Blue (#0047AB)
static constexpr ColorUtil::Gradient MARGIN_RAMP{
  GradRGB(0.00f, 0xC8102E),
  GradRGB(0.20f, 0xFF8C00),
  GradRGB(0.40f, 0xFFD700),
  GradRGB(0.70f, 0x00C0C0),
  GradRGB(1.00f, 0x0047AB),
};

// Incomplete cell styling:
// Stippled 2x2 pixel grid, with prominent outline color.
static constexpr uint32_t INCOMPLETE_OUTLINE_COLOR = 0xFF1493FF; // Deep neon pink / magenta

// Numbered Tree visual styles (4 bright primary colors).
struct TreeStyle {
  const char *name;
  uint32_t color;       // Vibrant primary color (ARGB/RGBA)
  uint32_t badge_bg;    // Badge background color
};

static const TreeStyle TREE_STYLES[4] = {
  {.name = "Tree 0", .color = 0x00F0FFFF, .badge_bg = 0x002233F0}, // Electric Cyan
  {.name = "Tree 1", .color = 0x39FF14FF, .badge_bg = 0x003311F0}, // Neon Lime Green
  {.name = "Tree 2", .color = 0xFFE600FF, .badge_bg = 0x333300F0}, // Bright Yellow / Gold
  {.name = "Tree 3", .color = 0xFF007FFF, .badge_bg = 0x330022F0}, // Vibrant Pink / Magenta
};

// Certified or incomplete leaf triangle representation.
struct LeafTriangle {
  std::string path;
  int root = 0;
  int depth = 0;
  vec3 p[3];       // Projective ray vertices
  vec3 unit_v[3];  // Normalized unit vectors on S^2
  double phi[3];   // Azimuth in degrees [0, 72]
  double elev[3];  // Elevation in degrees [0, 90]
  double z[3];     // Unit z-coordinate for Lambert [0, 1]
  double c = 0.0;  // Certified margin (c_lower)
  double c_upper = 0.0; // Upper bound margin
  bool is_incomplete = false;
  uint32_t color = 0;
};

// Empirical point sample.
struct EmpiricalSample {
  vec3 v;
  double phi_deg = 0.0;
  double elev_deg = 0.0;
  double c = 0.0;
  uint32_t color = 0;
};

static inline uint32_t ColorForMargin(double c) {
  if (c <= 0.0) return 0xC8102EFF;
  double log_min = std::log10(C_MIN);
  double log_max = std::log10(C_MAX);
  double tau = (std::log10(c) - log_min) / (log_max - log_min);
  tau = std::clamp(tau, 0.0, 1.0);
  return ColorUtil::LinearGradient32(MARGIN_RAMP, (float)tau);
}

// Sub-pixel safe solid triangle rasterizer.
static void DrawTriangle(ImageRGBA *img,
                         int x0, int y0,
                         int x1, int y1,
                         int x2, int y2,
                         uint32_t color) {
  int minx = std::min({x0, x1, x2});
  int maxx = std::max({x0, x1, x2});
  int miny = std::min({y0, y1, y2});
  int maxy = std::max({y0, y1, y2});

  if (minx > img->Width() - 1 || maxx < 0 ||
      miny > img->Height() - 1 || maxy < 0) {
    return;
  }

  if (minx == maxx && miny == maxy) {
    img->BlendPixel32(minx, miny, color);
    return;
  }

  const int a = x1 - x0;
  const int b = y1 - y0;
  const int c = x2 - x0;
  const int d = y2 - y0;
  const int det = a * d - b * c;

  if (det == 0) {
    img->BlendLine32(x0, y0, x1, y1, color);
    img->BlendLine32(x1, y1, x2, y2, color);
    img->BlendLine32(x2, y2, x0, y0, color);
    return;
  }

  img->BlendTriangle32(x0, y0, x1, y1, x2, y2, color);
}

// Stippled triangle rasterizer for incomplete cells illustrating upper bounds.
// Uses a 2x2 pixel grid pattern so alternating 2x2 pixel blocks are drawn with color,
// letting the dark background show through on the alternate blocks.
static void DrawStippledTriangle(ImageRGBA *img,
                                 int x0, int y0,
                                 int x1, int y1,
                                 int x2, int y2,
                                 uint32_t color) {
  int minx = std::min({x0, x1, x2});
  int maxx = std::max({x0, x1, x2});
  int miny = std::min({y0, y1, y2});
  int maxy = std::max({y0, y1, y2});

  if (minx > img->Width() - 1 || maxx < 0 ||
      miny > img->Height() - 1 || maxy < 0) {
    return;
  }

  if (minx == maxx && miny == maxy) {
    if (((minx / 2) ^ (miny / 2)) & 1) {
      img->BlendPixel32(minx, miny, color);
    }
    return;
  }

  const int a = x1 - x0;
  const int b = y1 - y0;
  const int c = x2 - x0;
  const int d = y2 - y0;
  const int det = a * d - b * c;

  if (det == 0) {
    img->BlendLine32(x0, y0, x1, y1, color);
    img->BlendLine32(x1, y1, x2, y2, color);
    img->BlendLine32(x2, y2, x0, y0, color);
    return;
  }

  float inv_det = 1.0f / det;

  minx = std::max(minx, 0);
  maxx = std::min(maxx, img->Width() - 1);
  miny = std::max(miny, 0);
  maxy = std::min(maxy, img->Height() - 1);

  for (int y = miny; y <= maxy; y++) {
    for (int x = minx; x <= maxx; x++) {
      if (!(((x / 2) ^ (y / 2)) & 1)) continue;

      int px = x - x0;
      int py = y - y0;
      float u = (px * d - py * c) * inv_det;
      if (u >= 0.0f) {
        float v = (py * a - px * b) * inv_det;
        if (v >= 0.0f && u + v <= 1.0f) {
          img->BlendPixel32(x, y, color);
        }
      }
    }
  }
}

// Draw a filled rectangular card with a thin border.
static void DrawCard(ImageRGBA *img, int x, int y, int w, int h,
                     uint32_t fill_color, uint32_t border_color) {
  img->BlendRect32(x, y, w, h, fill_color);
  img->BlendBox32(x, y, w, h, border_color, border_color);
}

// Crisp thick segment rasterizer.
static void DrawThickSegment(ImageRGBA *img, float x0, float y0, float x1, float y1,
                             uint32_t color, float thickness) {
  img->BlendThickLine32(x0, y0, x1, y1, thickness * 0.5f, color);
}

// Draw a crisp corner bracket at a triangle vertex.
// Draws thick bracket arms pointing along the two adjacent edges meeting at vertex (vx, vy),
// with a dark contrast halo underneath so it remains vivid against any background.
static void DrawBracket(ImageRGBA *img,
                        float vx, float vy,
                        float ax, float ay,
                        float bx, float by,
                        uint32_t color,
                        float arm_len = 44.0f) {
  float dx1 = ax - vx;
  float dy1 = ay - vy;
  float len1 = std::hypot(dx1, dy1);
  float dx2 = bx - vx;
  float dy2 = by - vy;
  float len2 = std::hypot(dx2, dy2);

  if (len1 < 1.0f || len2 < 1.0f) return;

  float p1x = vx + (dx1 / len1) * std::min(arm_len, len1 * 0.45f);
  float p1y = vy + (dy1 / len1) * std::min(arm_len, len1 * 0.45f);
  float p2x = vx + (dx2 / len2) * std::min(arm_len, len2 * 0.45f);
  float p2y = vy + (dy2 / len2) * std::min(arm_len, len2 * 0.45f);

  // Black halo for contrast (thickness 6.0)
  DrawThickSegment(img, vx, vy, p1x, p1y, 0x000000FF, 6.0f);
  DrawThickSegment(img, vx, vy, p2x, p2y, 0x000000FF, 6.0f);

  // Foreground colored bracket arm (thickness 3.0)
  DrawThickSegment(img, vx, vy, p1x, p1y, color, 3.0f);
  DrawThickSegment(img, vx, vy, p2x, p2y, color, 3.0f);
}

// Crisp outlined 2x text helper for 4K UHD display.
static void BlendTextOutline2x32(ImageRGBA *img, int x, int y,
                                 uint32_t outline_color,
                                 uint32_t fg_color,
                                 std::string_view s) {
  for (int dy = -2; dy <= 2; dy += 2) {
    for (int dx = -2; dx <= 2; dx += 2) {
      if (dx != 0 || dy != 0) {
        img->BlendText2x32(x + dx, y + dy, outline_color, s);
      }
    }
  }
  img->BlendText2x32(x, y, fg_color, s);
}

// Canonical root tree triangles for Trees 0, 1, 2, 3.
static std::array<TriangleQ, 4> GetRootTrees() {
  TriangleQ rw = GetRootWedge();
  TriangleQ ch[4];
  rw.Subdivide(ch);
  return {ch[0], ch[1], ch[2], ch[3]};
}

// Convert exact rational triangle geometry to spherical coordinates for visualization.
static void PopulateTriangleGeometry(const TriangleQ &triQ, LeafTriangle *leaf) {
  for (int v = 0; v < 3; v++) {
    leaf->p[v] = ToDouble(triQ.corners[v]);
    double len = std::hypot(leaf->p[v].x, leaf->p[v].y, leaf->p[v].z);
    if (len > 0.0) {
      leaf->unit_v[v] = leaf->p[v] / len;
    } else {
      leaf->unit_v[v] = vec3{1, 0, 0};
    }

    double phi_rad = std::atan2(leaf->unit_v[v].y, leaf->unit_v[v].x);
    if (phi_rad < 0.0) phi_rad += 2.0 * std::numbers::pi;
    leaf->phi[v] = phi_rad * 180.0 / std::numbers::pi;

    double clamped_z = std::clamp(leaf->unit_v[v].z, -1.0, 1.0);
    double elev_rad = std::asin(clamped_z);
    leaf->elev[v] = elev_rad * 180.0 / std::numbers::pi;
    leaf->z[v] = clamped_z;
  }
}

// Recursively collect leaf triangles from a TreeNode.
// Subdivides geometry top-down so each node is subdivided exactly once.
static void CollectLeaves(const TreeNode &node,
                          const TriangleQ &cur_tri,
                          std::vector<LeafTriangle> *leaves,
                          int *total_nodes,
                          int *certified_leaves,
                          int *incomplete_leaves) {
  (*total_nodes)++;

  if (node.is_leaf()) {
    LeafTriangle leaf;
    leaf.path = node.path;
    leaf.depth = node.depth();
    leaf.root = node.path.empty() ? 0 : (node.path[0] - '0');
    PopulateTriangleGeometry(cur_tri, &leaf);

    double c_lower = node.direct_bounds.direct_c_lower.ToDouble();
    double c_upper = node.direct_bounds.direct_c_upper.ToDouble();
    leaf.c = c_lower;
    leaf.c_upper = c_upper;

    if (c_lower > 0.0) {
      leaf.color = ColorForMargin(c_lower);
      leaf.is_incomplete = false;
      (*certified_leaves)++;
    } else {
      // Incomplete cell: illustrate upper bound
      leaf.color = (c_upper > 0.0) ? ColorForMargin(c_upper) : 0x553366FF;
      leaf.is_incomplete = true;
      (*incomplete_leaves)++;
    }
    leaves->push_back(leaf);
    return;
  }

  // Internal node: subdivide geometry once and recurse to children
  TriangleQ ch[4];
  cur_tri.Subdivide(ch);
  for (size_t i = 0; i < node.children.size() && i < 4; i++) {
    if (node.children[i]) {
      CollectLeaves(*node.children[i], ch[i], leaves,
                    total_nodes, certified_leaves, incomplete_leaves);
    }
  }
}

// Load a tubetree229_v1 JSON file using tubetree229 library.
static bool LoadTubeTree(const std::string &path,
                         std::vector<LeafTriangle> *leaves,
                         int *total_nodes_out,
                         int *certified_leaves_out,
                         int *incomplete_leaves_out) {
  Timer timer;
  std::string base_dir = std::filesystem::path(path).parent_path().string();
  auto root = LoadTreeJson(path, true, base_dir);
  if (!root) {
    Printf("Failed to load tubetree from %s\n", path.c_str());
    return false;
  }

  TriangleQ root_tri = TriangleFromPath(root->path);
  int total = 0, cert = 0, incomp = 0;
  CollectLeaves(*root, root_tri, leaves, &total, &cert, &incomp);

  if (total_nodes_out) *total_nodes_out += total;
  if (certified_leaves_out) *certified_leaves_out += cert;
  if (incomplete_leaves_out) *incomplete_leaves_out += incomp;

  Printf("  Loaded %s in %.2fs: %d nodes, %d certified leaves, %d incomplete leaves\n",
         path.c_str(), timer.Seconds(), total, cert, incomp);
  return true;
}

// Load optional empirical samples CSV file.
static std::vector<EmpiricalSample> LoadEmpiricalSamples(const std::string &path) {
  std::vector<EmpiricalSample> samples;
  std::ifstream f(path);
  if (!f.is_open()) return samples;

  std::string line;
  bool first_line = true;
  while (std::getline(f, line)) {
    if (line.empty() || line[0] == '#') continue;
    if (first_line && line.find("azimuth") != std::string::npos) {
      first_line = false;
      continue;
    }
    first_line = false;

    for (char &c : line) {
      if (c == ',') c = ' ';
    }
    std::stringstream ss(line);
    double vx, vy, vz, phi, elev, c_val;
    if (ss >> vx >> vy >> vz >> phi >> elev >> c_val) {
      EmpiricalSample samp;
      samp.v = vec3{vx, vy, vz};
      samp.phi_deg = phi;
      samp.elev_deg = elev;
      samp.c = c_val;
      samp.color = ColorForMargin(c_val);
      samples.push_back(samp);
    }
  }
  Printf("Loaded %zu empirical samples from %s\n", samples.size(), path.c_str());
  return samples;
}

// // Draw corner brackets and identification badges for Trees 0..3 using a generic projection functor.
template <typename ProjectFn>
static void RenderTreeIndicators(ImageRGBA *img,
                                 int child_filter,
                                 bool draw_centroid_badges,
                                 ProjectFn &&project_fn) {
  auto root_trees = GetRootTrees();

  for (int k = 0; k < 4; k++) {
    if (child_filter >= 0 && k != child_filter) continue;
    const auto &style = TREE_STYLES[k];
    const auto &triQ = root_trees[k];

    vec2 p0 = project_fn(0, ToDouble(triQ.corners[0]));
    vec2 p1 = project_fn(1, ToDouble(triQ.corners[1]));
    vec2 p2 = project_fn(2, ToDouble(triQ.corners[2]));

    // Corner brackets at each of the 3 vertices
    DrawBracket(img, (float)p0.x, (float)p0.y, (float)p1.x, (float)p1.y, (float)p2.x, (float)p2.y, style.color);
    DrawBracket(img, (float)p1.x, (float)p1.y, (float)p2.x, (float)p2.y, (float)p0.x, (float)p0.y, style.color);
    DrawBracket(img, (float)p2.x, (float)p2.y, (float)p0.x, (float)p0.y, (float)p1.x, (float)p1.y, style.color);

    if (draw_centroid_badges) {
      // Tree Centroid Badge
      float cx = (float)(p0.x + p1.x + p2.x) / 3.0f;
      float cy = (float)(p0.y + p1.y + p2.y) / 3.0f;
      DrawCard(img, (int)cx - 68, (int)cy - 18, 136, 36, style.badge_bg, style.color);
      BlendTextOutline2x32(img, (int)cx - 54, (int)cy - 9, 0x000000FF, style.color, style.name);
    }
  }
}

// Render vertical color bar legend scaled for 4K display.
static void RenderColorbar(ImageRGBA *img, int bar_x, int bar_y, int bar_w, int bar_h) {
  for (int y = 0; y < bar_h; y++) {
    double tau = 1.0 - (double)y / (double)(bar_h - 1);
    uint32_t color = ColorUtil::LinearGradient32(MARGIN_RAMP, (float)tau);
    for (int x = 0; x < bar_w; x++) {
      img->SetPixel32(bar_x + x, bar_y + y, color);
    }
  }
  img->BlendBox32(bar_x, bar_y, bar_w, bar_h, 0xFFFFFFFF, 0xFFFFFFFF);
  img->BlendBox32(bar_x - 1, bar_y - 1, bar_w + 2, bar_h + 2, 0xFFFFFFFF, 0xFFFFFFFF);

  static constexpr double TICKS[] = {
    0.00020, 0.0002278, 0.0002509, 0.00050, 0.00100, 0.00200, 0.00500, 0.01000
  };
  static constexpr const char *TICK_LABELS[] = {
    "0.00020 (cut)",
    "0.00023 (Canyon 2 pinch: c=0.0002278)",
    "0.00025 (Canyon 1 notch: c=0.0002509)",
    "0.00050",
    "0.00100",
    "0.00200",
    "0.00500",
    "0.01000 (wide margin)",
  };

  double log_min = std::log10(C_MIN);
  double log_max = std::log10(C_MAX);

  for (size_t i = 0; i < std::size(TICKS); i++) {
    double t = (std::log10(TICKS[i]) - log_min) / (log_max - log_min);
    t = std::clamp(t, 0.0, 1.0);
    int ty = bar_y + (int)std::round((1.0 - t) * (bar_h - 1));

    img->BlendLine32(bar_x + bar_w, ty, bar_x + bar_w + 14, ty, 0xFFFFFFFF);
    img->BlendLine32(bar_x + bar_w, ty + 1, bar_x + bar_w + 14, ty + 1, 0xFFFFFFFF);

    uint32_t fg = 0xEEEEEEFF;
    if (i == 1) fg = 0xFFD700FF; // Canyon 2
    if (i == 2) fg = 0xFF5588FF; // Canyon 1
    BlendTextOutline2x32(img, bar_x + bar_w + 20, ty - 8,
                         0x000000FF, fg, TICK_LABELS[i]);
  }

  BlendTextOutline2x32(img, bar_x - 10, bar_y - 32, 0x000000FF, 0xFFFFFFFF, "Margin c");
}

// Render self-documenting legend card for cell fill patterns and numbered tree brackets.
static void RenderLegendCard(ImageRGBA *img, int x, int y, int child_filter = -1) {
  const int w = 880;
  const int h = 450;
  DrawCard(img, x, y, w, h, 0x161922F4, 0x556677FF);

  BlendTextOutline2x32(img, x + 24, y + 20, 0x000000FF, 0xFFFFFFFF, "TUBE STRUCTURE & MARGIN MAP");

  // Section 1: Cell Fill Status
  BlendTextOutline2x32(img, x + 24, y + 64, 0x000000FF, 0xAAAAAAFF, "Cell Status & Fill Patterns:");

  // Solid Box: Certified
  img->BlendRect32(x + 40, y + 96, 32, 24, 0x00A0D0FF);
  img->BlendBox32(x + 40, y + 96, 32, 24, 0xFFFFFFFF, 0xFFFFFFFF);
  BlendTextOutline2x32(img, x + 88, y + 98, 0x000000FF, 0xEEEEEEFF, "Solid: Certified Cell (c_lower > 0)");

  // Stippled Box: Incomplete (completely filled checkerboard pattern)
  for (int py = y + 136; py < y + 136 + 24; py++) {
    for (int px = x + 40; px < x + 40 + 32; px++) {
      if (((px / 2) ^ (py / 2)) & 1) {
        img->BlendPixel32(px, py, 0xFFD700FF);
      }
    }
  }
  img->BlendBox32(x + 40, y + 136, 32, 24, INCOMPLETE_OUTLINE_COLOR, INCOMPLETE_OUTLINE_COLOR);
  img->BlendBox32(x + 39, y + 135, 34, 26, INCOMPLETE_OUTLINE_COLOR, INCOMPLETE_OUTLINE_COLOR);
  BlendTextOutline2x32(img, x + 88, y + 138, 0x000000FF, 0xFF88CCFF, "Stippled: Incomplete Cell (c_upper bound)");

  // Section 2: Numbered Tree Root Wedges & Mini-Map
  BlendTextOutline2x32(img, x + 24, y + 184, 0x000000FF, 0xAAAAAAFF, "Numbered Tree Root Wedges:");

  const char *desc[4] = {
    "Az 0..31', Elev 0..45'",
    "Az 31..72', Elev 0..52'",
    "Pole (Elev >= 45')",
    "Transition Center",
  };

  for (int k = 0; k < 4; k++) {
    int row_y = y + 218 + k * 48;
    const auto &st = TREE_STYLES[k];
    DrawCard(img, x + 36, row_y, 116, 32, st.badge_bg, st.color);
    BlendTextOutline2x32(img, x + 44, row_y + 7, 0x000000FF, st.color, st.name);
    BlendTextOutline2x32(img, x + 165, row_y + 7, 0x000000FF,
                         (child_filter >= 0 && child_filter != k) ? 0x666666FF : 0xCCCCCCFF,
                         desc[k]);
  }

  // Mini-map of the 4 root trees (Triforce subdivision) on the right side of the card
  BlendTextOutline2x32(img, x + 665, y + 184, 0x000000FF, 0xAAAAAAFF, "Subdivision");

  const vec2 P0{(double)(x + 635), (double)(y + 400)};
  const vec2 P1{(double)(x + 845), (double)(y + 400)};
  const vec2 P2{(double)(x + 740), (double)(y + 225)};

  const vec2 M01{(double)(x + 740), (double)(y + 400)};
  const vec2 M12{(double)(x + 792), (double)(y + 312)};
  const vec2 M20{(double)(x + 688), (double)(y + 312)};

  auto DrawMiniSubTri = [&](const vec2 &a, const vec2 &b, const vec2 &c,
                            const TreeStyle &st, const char *label, int tx, int ty) {
    DrawTriangle(img, (float)a.x, (float)a.y, (float)b.x, (float)b.y, (float)c.x, (float)c.y, st.badge_bg);
    DrawThickSegment(img, (float)a.x, (float)a.y, (float)b.x, (float)b.y, st.color, 2.0f);
    DrawThickSegment(img, (float)b.x, (float)b.y, (float)c.x, (float)c.y, st.color, 2.0f);
    DrawThickSegment(img, (float)c.x, (float)c.y, (float)a.x, (float)a.y, st.color, 2.0f);
    BlendTextOutline2x32(img, tx, ty, 0x000000FF, st.color, label);
  };

  // Tree 2: North Pole (top apex)
  DrawMiniSubTri(M20, M12, P2, TREE_STYLES[2], "2", x + 732, y + 274);
  // Tree 0: Az 0..31' (bottom-left)
  DrawMiniSubTri(P0, M01, M20, TREE_STYLES[0], "0", x + 679, y + 361);
  // Tree 1: Az 31..72' (bottom-right)
  DrawMiniSubTri(M01, P1, M12, TREE_STYLES[1], "1", x + 784, y + 361);
  // Tree 3: Center Transition Wedge
  DrawMiniSubTri(M12, M20, M01, TREE_STYLES[3], "3", x + 732, y + 332);

  // Mini-map labels around perimeter
  img->BlendText32(x + 724, y + 210, 0x8899AAFF, "Pole");
  img->BlendText32(x + 620, y + 406, 0x8899AAFF, "0'");
  img->BlendText32(x + 728, y + 406, 0x8899AAFF, "31'");
  img->BlendText32(x + 830, y + 406, 0x8899AAFF, "72'");
}

// ----------------------------------------------------------------------------
// VIEW 1: Equirectangular Projection of Upper Wedge (phi in [0, 72], alpha in [0, 90])
// ----------------------------------------------------------------------------
static void RenderWedgeEquirect(const std::vector<LeafTriangle> &leaves,
                                const std::vector<EmpiricalSample> &samples,
                                int child_filter,
                                uint8_t line_alpha,
                                const std::string &outfile) {
  ImageRGBA base_img(WIDTH, HEIGHT);
  base_img.Clear32(0x101218FF);

  // Header Title & Subtitle
  BlendTextOutline2x32(&base_img, 60, 30, 0x000000FF, 0xFFFFFFFF,
                       "Nopert #229: Certified Clearance Margin Map (Upper Wedge Fundamental Domain)");
  base_img.BlendText2x32(60, 68, 0x99AAB8FF,
                         "Equirectangular projection of unit sphere S^2: Azimuth phi in [0, 72 deg], Elevation alpha in [0, 90 deg]");
  base_img.BlendText2x32(60, 102, 0x00FFCCFF,
                         "4K UHD Visualization | Pinch canyons C1 & C2 marked with crosshairs and crop marks | Tubetree v1 format");

  const int map_w = 1488;
  const int map_h = 1860;
  const int map_y = 150;
  const int map_x = 780;

  auto MapToPixel = [&](double phi_deg, double elev_deg) -> std::pair<int, int> {
    double u = std::clamp(phi_deg / PHI_MAX_DEG, 0.0, 1.0);
    double v = std::clamp(elev_deg / ELEV_MAX_DEG, 0.0, 1.0);
    int px = map_x + (int)std::round(u * (map_w - 1));
    int py = map_y + (int)std::round((1.0 - v) * (map_h - 1));
    return {px, py};
  };

  base_img.BlendRect32(map_x, map_y, map_w, map_h, 0x161922FF);

  // Coordinate grid lines
  for (int phi = 0; phi <= 72; phi += 10) {
    auto [gx, _] = MapToPixel((double)phi, 0.0);
    base_img.BlendLine32(gx, map_y, gx, map_y + map_h - 1, 0xFFFFFF18);
    base_img.BlendLine32(gx, map_y + map_h, gx, map_y + map_h + 8, 0xAAAAAAFF);
    std::string s = std::format("{}'", phi);
    BlendTextOutline2x32(&base_img, gx - 16, map_y + map_h + 12, 0x000000FF, 0xCCCCCCFF, s);
  }
  auto [b_x, _] = MapToPixel(72.0, 0.0);
  base_img.BlendLine32(b_x, map_y, b_x, map_y + map_h - 1, 0xFF444480);
  base_img.BlendLine32(b_x + 1, map_y, b_x + 1, map_y + map_h - 1, 0xFF444480);
  BlendTextOutline2x32(&base_img, b_x - 32, map_y + map_h + 40, 0x000000FF, 0xFF8888FF, "72'(C5)");

  for (int elev = 0; elev <= 90; elev += 10) {
    auto [_, gy] = MapToPixel(0.0, (double)elev);
    base_img.BlendLine32(map_x, gy, map_x + map_w - 1, gy, 0xFFFFFF18);
    base_img.BlendLine32(map_x - 8, gy, map_x, gy, 0xAAAAAAFF);
    std::string s = std::format("{:>2}'", elev);
    BlendTextOutline2x32(&base_img, map_x - 60, gy - 8, 0x000000FF, 0xCCCCCCFF, s);
  }

  // Canyon 1 & 2 guide lines
  auto [c1_x, c1_y] = MapToPixel(CANYON1.phi_deg, CANYON1.elev_deg);
  uint32_t c1_color = 0xFF3366FF;
  base_img.BlendLine32(c1_x, map_y, c1_x, map_y + map_h - 1, c1_color);
  base_img.BlendLine32(c1_x + 1, map_y, c1_x + 1, map_y + map_h - 1, c1_color);
  base_img.BlendLine32(map_x, c1_y, map_x + map_w - 1, c1_y, c1_color);
  base_img.BlendLine32(map_x, c1_y + 1, map_x + map_w - 1, c1_y + 1, c1_color);

  auto [c2_x, c2_y] = MapToPixel(CANYON2.phi_deg, CANYON2.elev_deg);
  uint32_t c2_color = 0xFFD700FF;
  base_img.BlendLine32(c2_x, map_y, c2_x, map_y + map_h - 1, c2_color);
  base_img.BlendLine32(c2_x + 1, map_y, c2_x + 1, map_y + map_h - 1, c2_color);
  base_img.BlendLine32(map_x, c2_y, map_x + map_w - 1, c2_y, c2_color);
  base_img.BlendLine32(map_x, c2_y + 1, map_x + map_w - 1, c2_y + 1, c2_color);

  BlendTextOutline2x32(&base_img, c1_x - 50, map_y + map_h + 40, 0x000000FF, c1_color, "C1:2.22'");
  BlendTextOutline2x32(&base_img, map_x - 245, c1_y - 8, 0x000000FF, c1_color, "C1: 9.63'");
  BlendTextOutline2x32(&base_img, c2_x - 20, map_y + map_h + 70, 0x000000FF, c2_color, "C2:12.90'");
  BlendTextOutline2x32(&base_img, map_x - 260, c2_y - 8, 0x000000FF, c2_color, "C2: 18.48'");

  BlendTextOutline2x32(&base_img, map_x + map_w / 2 - 120, map_y + map_h + 105,
                       0x000000FF, 0xFFFFFFFF, "Azimuth phi (degrees)");
  BlendTextOutline2x32(&base_img, map_x - 120, map_y - 25,
                       0x000000FF, 0xFFFFFFFF, "Elevation alpha");

  // Rasterize leaf triangles
  ImageRGBA wireframe(WIDTH, HEIGHT);
  wireframe.Clear32(0x00000000);
  ImageRGBA incomplete_wireframe(WIDTH, HEIGHT);
  incomplete_wireframe.Clear32(0x00000000);

  for (const auto &leaf : leaves) {
    auto [x0, y0] = MapToPixel(leaf.phi[0], leaf.elev[0]);
    auto [x1, y1] = MapToPixel(leaf.phi[1], leaf.elev[1]);
    auto [x2, y2] = MapToPixel(leaf.phi[2], leaf.elev[2]);

    if (leaf.is_incomplete) {
      DrawStippledTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
      if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
        incomplete_wireframe.BlendLine32(x0, y0, x1, y1, INCOMPLETE_OUTLINE_COLOR);
        incomplete_wireframe.BlendLine32(x1, y1, x2, y2, INCOMPLETE_OUTLINE_COLOR);
        incomplete_wireframe.BlendLine32(x2, y2, x0, y0, INCOMPLETE_OUTLINE_COLOR);
      }
    } else {
      DrawTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
      if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
        wireframe.BlendLine32(x0, y0, x1, y1, 0x000000FF);
        wireframe.BlendLine32(x1, y1, x2, y2, 0x000000FF);
        wireframe.BlendLine32(x2, y2, x0, y0, 0x000000FF);
      }
    }
  }

  // Composite certified wireframe with user alpha
  for (uint32_t &p : wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | line_alpha;
    }
  }
  base_img.BlendImage(0, 0, wireframe);

  // Composite incomplete cell outline with prominent opacity
  for (uint32_t &p : incomplete_wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | 0xE6;
    }
  }
  base_img.BlendImage(0, 0, incomplete_wireframe);

  // Overlay empirical samples if any
  for (const auto &samp : samples) {
    auto [sx, sy] = MapToPixel(samp.phi_deg, samp.elev_deg);
    base_img.BlendFilledCircleAA32((float)sx, (float)sy, 5.0f, samp.color);
    base_img.BlendCircle32(sx, sy, 6, 0x000000FF);
  }

  // Render corner brackets for Trees 0..3
  RenderTreeIndicators(&base_img, child_filter, false, [&](int corner_idx, const vec3 &p) -> vec2 {
    if (p.x == 0.0 && p.y == 0.0 && p.z > 0.0) {
      auto [px, py] = MapToPixel(36.0, 90.0);
      return vec2{(double)px, (double)py};
    }
    double phi_deg = std::atan2(p.y, p.x) * 180.0 / std::numbers::pi;
    if (phi_deg < 0.0) phi_deg += 360.0;
    double len = std::hypot(p.x, p.y, p.z);
    double elev_deg = std::asin(std::clamp(p.z / len, -1.0, 1.0)) * 180.0 / std::numbers::pi;
    auto [px, py] = MapToPixel(phi_deg, elev_deg);
    return vec2{(double)px, (double)py};
  });

  // Re-draw outer frame to stay sharp
  base_img.BlendBox32(map_x, map_y, map_w, map_h, 0xFFFFFFFF, 0xFFFFFFFF);

  // Colorbar & Legend Card
  RenderColorbar(&base_img, map_x + map_w + 80, map_y, 44, map_h);
  RenderLegendCard(&base_img, 2880, 200, child_filter);

  base_img.Save(outfile);
  Printf("Saved %s (%dx%d)\n", outfile.c_str(), WIDTH, HEIGHT);
}

// ----------------------------------------------------------------------------
// VIEW 2: Lambert Cylindrical Equal-Area Projection (phi in [0, 72], z in [0, 1])
// ----------------------------------------------------------------------------
static void RenderWedgeLambert(const std::vector<LeafTriangle> &leaves,
                               const std::vector<EmpiricalSample> &samples,
                               int child_filter,
                               uint8_t line_alpha,
                               const std::string &outfile) {
  ImageRGBA base_img(WIDTH, HEIGHT);
  base_img.Clear32(0x101218FF);

  // Header Title & Brief Stats
  BlendTextOutline2x32(&base_img, 60, 30, 0x000000FF, 0xFFFFFFFF,
                       "Nopert #229: Certified Margin Map (Lambert Equal-Area)");
  base_img.BlendText2x32(60, 68, 0x99AAB8FF,
                         "Lambert cylindrical equal-area preserves solid angle on unit sphere S^2 (phi in [0, 72 deg], z in [0, 1])");
  base_img.BlendText2x32(60, 102, 0x00FFCCFF,
                         "Pixel area is proportional to solid angle | Canyon 2 pinch: c = 0.0002278 | Proven tube radius: r = 0.00040");

  const int map_h = 1800;
  const int map_w = (int)std::round(map_h * (PHI_MAX_RAD / 1.0)); // 2262 px
  const int map_y = 180;
  const int map_x = 340;

  auto MapToPixel = [&](double phi_deg, double z_val) -> std::pair<int, int> {
    double u = std::clamp(phi_deg / PHI_MAX_DEG, 0.0, 1.0);
    double v = std::clamp(z_val, 0.0, 1.0);
    int px = map_x + (int)std::round(u * (map_w - 1));
    int py = map_y + (int)std::round((1.0 - v) * (map_h - 1));
    return {px, py};
  };

  base_img.BlendRect32(map_x, map_y, map_w, map_h, 0x161922FF);

  // Coordinate grid lines
  for (int phi = 0; phi <= 72; phi += 10) {
    auto [gx, _] = MapToPixel((double)phi, 0.0);
    base_img.BlendLine32(gx, map_y, gx, map_y + map_h - 1, 0xFFFFFF18);
    base_img.BlendLine32(gx, map_y + map_h, gx, map_y + map_h + 8, 0xAAAAAAFF);
    std::string s = std::format("{}'", phi);
    BlendTextOutline2x32(&base_img, gx - 16, map_y + map_h + 12, 0x000000FF, 0xCCCCCCFF, s);
  }
  auto [b_x, _] = MapToPixel(72.0, 0.0);
  base_img.BlendLine32(b_x, map_y, b_x, map_y + map_h - 1, 0xFF444480);
  base_img.BlendLine32(b_x + 1, map_y, b_x + 1, map_y + map_h - 1, 0xFF444480);
  BlendTextOutline2x32(&base_img, b_x - 32, map_y + map_h + 40, 0x000000FF, 0xFF8888FF, "72'(C5)");

  for (int zi = 0; zi <= 10; zi++) {
    double z_val = zi / 10.0;
    auto [_, gy] = MapToPixel(0.0, z_val);
    base_img.BlendLine32(map_x, gy, map_x + map_w - 1, gy, 0xFFFFFF18);
    base_img.BlendLine32(map_x - 8, gy, map_x, gy, 0xAAAAAAFF);
    std::string s = std::format("{:.1f}", z_val);
    BlendTextOutline2x32(&base_img, map_x - 60, gy - 8, 0x000000FF, 0xCCCCCCFF, s);
  }

  // Canyon 1 & 2 guide lines
  auto [c1_x, c1_y] = MapToPixel(CANYON1.phi_deg, CANYON1.v.z);
  uint32_t c1_color = 0xFF3366FF;
  base_img.BlendLine32(c1_x, map_y, c1_x, map_y + map_h - 1, c1_color);
  base_img.BlendLine32(c1_x + 1, map_y, c1_x + 1, map_y + map_h - 1, c1_color);
  base_img.BlendLine32(map_x, c1_y, map_x + map_w - 1, c1_y, c1_color);
  base_img.BlendLine32(map_x, c1_y + 1, map_x + map_w - 1, c1_y + 1, c1_color);

  auto [c2_x, c2_y] = MapToPixel(CANYON2.phi_deg, CANYON2.v.z);
  uint32_t c2_color = 0xFFD700FF;
  base_img.BlendLine32(c2_x, map_y, c2_x, map_y + map_h - 1, c2_color);
  base_img.BlendLine32(c2_x + 1, map_y, c2_x + 1, map_y + map_h - 1, c2_color);
  base_img.BlendLine32(map_x, c2_y, map_x + map_w - 1, c2_y, c2_color);
  base_img.BlendLine32(map_x, c2_y + 1, map_x + map_w - 1, c2_y + 1, c2_color);

  BlendTextOutline2x32(&base_img, c1_x - 50, map_y + map_h + 40, 0x000000FF, c1_color, "C1:2.22'");
  BlendTextOutline2x32(&base_img, map_x - 245, c1_y - 8, 0x000000FF, c1_color, "C1: z=0.167");
  BlendTextOutline2x32(&base_img, c2_x - 20, map_y + map_h + 70, 0x000000FF, c2_color, "C2:12.90'");
  BlendTextOutline2x32(&base_img, map_x - 260, c2_y - 8, 0x000000FF, c2_color, "C2: z=0.317");

  BlendTextOutline2x32(&base_img, map_x + map_w / 2 - 120, map_y + map_h + 105,
                       0x000000FF, 0xFFFFFFFF, "Azimuth phi (degrees)");
  BlendTextOutline2x32(&base_img, map_x - 120, map_y - 25,
                       0x000000FF, 0xFFFFFFFF, "Cylindrical z");

  // Rasterize leaf triangles
  ImageRGBA wireframe(WIDTH, HEIGHT);
  wireframe.Clear32(0x00000000);
  ImageRGBA incomplete_wireframe(WIDTH, HEIGHT);
  incomplete_wireframe.Clear32(0x00000000);

  for (const auto &leaf : leaves) {
    auto [x0, y0] = MapToPixel(leaf.phi[0], leaf.z[0]);
    auto [x1, y1] = MapToPixel(leaf.phi[1], leaf.z[1]);
    auto [x2, y2] = MapToPixel(leaf.phi[2], leaf.z[2]);

    if (leaf.is_incomplete) {
      DrawStippledTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
      if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
        incomplete_wireframe.BlendLine32(x0, y0, x1, y1, INCOMPLETE_OUTLINE_COLOR);
        incomplete_wireframe.BlendLine32(x1, y1, x2, y2, INCOMPLETE_OUTLINE_COLOR);
        incomplete_wireframe.BlendLine32(x2, y2, x0, y0, INCOMPLETE_OUTLINE_COLOR);
      }
    } else {
      DrawTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
      if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
        wireframe.BlendLine32(x0, y0, x1, y1, 0x000000FF);
        wireframe.BlendLine32(x1, y1, x2, y2, 0x000000FF);
        wireframe.BlendLine32(x2, y2, x0, y0, 0x000000FF);
      }
    }
  }

  for (uint32_t &p : wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | line_alpha;
    }
  }
  base_img.BlendImage(0, 0, wireframe);

  for (uint32_t &p : incomplete_wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | 0xE6;
    }
  }
  base_img.BlendImage(0, 0, incomplete_wireframe);

  for (const auto &samp : samples) {
    auto [sx, sy] = MapToPixel(samp.phi_deg, samp.v.z);
    base_img.BlendFilledCircleAA32((float)sx, (float)sy, 5.0f, samp.color);
    base_img.BlendCircle32(sx, sy, 6, 0x000000FF);
  }

  // Render corner brackets for Trees 0..3
  RenderTreeIndicators(&base_img, child_filter, false, [&](int corner_idx, const vec3 &p) -> vec2 {
    if (p.x == 0.0 && p.y == 0.0 && p.z > 0.0) {
      auto [px, py] = MapToPixel(36.0, 1.0);
      return vec2{(double)px, (double)py};
    }
    double phi_deg = std::atan2(p.y, p.x) * 180.0 / std::numbers::pi;
    if (phi_deg < 0.0) phi_deg += 360.0;
    double len = std::hypot(p.x, p.y, p.z);
    double z_val = std::clamp(p.z / len, 0.0, 1.0);
    auto [px, py] = MapToPixel(phi_deg, z_val);
    return vec2{(double)px, (double)py};
  });

  base_img.BlendBox32(map_x, map_y, map_w, map_h, 0xFFFFFFFF, 0xFFFFFFFF);

  RenderColorbar(&base_img, map_x + map_w + 50, map_y, 44, map_h);
  RenderLegendCard(&base_img, 2940, 200, child_filter);

  base_img.Save(outfile);
  Printf("Saved %s (%dx%d)\n", outfile.c_str(), WIDTH, HEIGHT);
}

// ----------------------------------------------------------------------------
// VIEW 3: Full Sphere Equirectangular (Replicated C5 orbits and z-reflection)
// ----------------------------------------------------------------------------
static void RenderFullSphere(const std::vector<LeafTriangle> &leaves,
                             int child_filter,
                             uint8_t line_alpha,
                             const std::string &outfile) {
  ImageRGBA base_img(WIDTH, HEIGHT);
  base_img.Clear32(0x101218FF);

  BlendTextOutline2x32(&base_img, 60, 30, 0x000000FF, 0xFFFFFFFF,
                       "Nopert #229: Full View Sphere Clearance Map (360 x 180 deg)");
  base_img.BlendText2x32(60, 68, 0x99AAB8FF,
                         "Replicated across fivefold rotational symmetry (C5) and elevation reflection | Sector 0 framed with Tree 0..3 brackets");

  const int map_w = 3520;
  const int map_h = 1760;
  const int map_x = (WIDTH - map_w) / 2; // 160 px
  const int map_y = 120;

  auto MapFullPixel = [&](double phi_deg, double elev_deg) -> std::pair<int, int> {
    double u = std::clamp(phi_deg / 360.0, 0.0, 1.0);
    double v = std::clamp((elev_deg + 90.0) / 180.0, 0.0, 1.0);
    int px = map_x + (int)std::round(u * (map_w - 1));
    int py = map_y + (int)std::round((1.0 - v) * (map_h - 1));
    return {px, py};
  };

  base_img.BlendRect32(map_x, map_y, map_w, map_h, 0x161922FF);

  for (int phi = 0; phi <= 360; phi += 72) {
    auto [gx, _] = MapFullPixel((double)phi, 0.0);
    base_img.BlendLine32(gx, map_y, gx, map_y + map_h - 1, 0xFFFFFF28);
    base_img.BlendLine32(gx, map_y + map_h, gx, map_y + map_h + 8, 0xAAAAAAFF);
    std::string s = std::format("{}'", phi);
    BlendTextOutline2x32(&base_img, gx - 20, map_y + map_h + 12, 0x000000FF, 0xCCCCCCFF, s);
  }

  for (int elev = -90; elev <= 90; elev += 30) {
    auto [_, gy] = MapFullPixel(0.0, (double)elev);
    base_img.BlendLine32(map_x, gy, map_x + map_w - 1, gy, 0xFFFFFF20);
    base_img.BlendLine32(map_x - 8, gy, map_x, gy, 0xAAAAAAFF);
    std::string s = std::format("{:+d}'", elev);
    BlendTextOutline2x32(&base_img, map_x - 65, gy - 8, 0x000000FF, 0xCCCCCCFF, s);
  }

  auto [_, eq_y] = MapFullPixel(0.0, 0.0);
  base_img.BlendLine32(map_x, eq_y, map_x + map_w - 1, eq_y, 0xFFFFFF50);

  // Rasterize leaf triangles replicated across 5 sectors and 2 hemispheres
  ImageRGBA wireframe(WIDTH, HEIGHT);
  wireframe.Clear32(0x00000000);
  ImageRGBA incomplete_wireframe(WIDTH, HEIGHT);
  incomplete_wireframe.Clear32(0x00000000);

  for (int k = 0; k < 5; k++) {
    double sector_offset = k * 72.0;

    for (int hem = 0; hem < 2; hem++) {
      double elev_mult = (hem == 0) ? 1.0 : -1.0;

      for (const auto &leaf : leaves) {
        auto [x0, y0] = MapFullPixel(leaf.phi[0] + sector_offset, leaf.elev[0] * elev_mult);
        auto [x1, y1] = MapFullPixel(leaf.phi[1] + sector_offset, leaf.elev[1] * elev_mult);
        auto [x2, y2] = MapFullPixel(leaf.phi[2] + sector_offset, leaf.elev[2] * elev_mult);

        if (leaf.is_incomplete) {
          DrawStippledTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
          if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
            incomplete_wireframe.BlendLine32(x0, y0, x1, y1, INCOMPLETE_OUTLINE_COLOR);
            incomplete_wireframe.BlendLine32(x1, y1, x2, y2, INCOMPLETE_OUTLINE_COLOR);
            incomplete_wireframe.BlendLine32(x2, y2, x0, y0, INCOMPLETE_OUTLINE_COLOR);
          }
        } else {
          DrawTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
          if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
            wireframe.BlendLine32(x0, y0, x1, y1, 0x000000FF);
            wireframe.BlendLine32(x1, y1, x2, y2, 0x000000FF);
            wireframe.BlendLine32(x2, y2, x0, y0, 0x000000FF);
          }
        }
      }
    }
  }

  for (uint32_t &p : wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | line_alpha;
    }
  }
  base_img.BlendImage(0, 0, wireframe);

  for (uint32_t &p : incomplete_wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | 0xE6;
    }
  }
  base_img.BlendImage(0, 0, incomplete_wireframe);

  // Render corner brackets and badges on primary sector 0
  RenderTreeIndicators(&base_img, child_filter, true, [&](int corner_idx, const vec3 &p) -> vec2 {
    if (p.x == 0.0 && p.y == 0.0 && p.z > 0.0) {
      auto [px, py] = MapFullPixel(36.0, 90.0);
      return vec2{(double)px, (double)py};
    }
    double phi_deg = std::atan2(p.y, p.x) * 180.0 / std::numbers::pi;
    if (phi_deg < 0.0) phi_deg += 360.0;
    double len = std::hypot(p.x, p.y, p.z);
    double elev_deg = std::asin(std::clamp(p.z / len, -1.0, 1.0)) * 180.0 / std::numbers::pi;
    auto [px, py] = MapFullPixel(phi_deg, elev_deg);
    return vec2{(double)px, (double)py};
  });

  base_img.BlendBox32(map_x, map_y, map_w, map_h, 0xFFFFFFFF, 0xFFFFFFFF);

  // Bottom horizontal colorbar
  int cbar_x = 800;
  int cbar_y = 1970;
  int cbar_w = 2240;
  int cbar_h = 30;

  for (int x = 0; x < cbar_w; x++) {
    double tau = (double)x / (double)(cbar_w - 1);
    uint32_t color = ColorUtil::LinearGradient32(MARGIN_RAMP, (float)tau);
    for (int y = 0; y < cbar_h; y++) {
      base_img.SetPixel32(cbar_x + x, cbar_y + y, color);
    }
  }
  base_img.BlendBox32(cbar_x, cbar_y, cbar_w, cbar_h, 0xFFFFFFFF, 0xFFFFFFFF);

  double log_min = std::log10(C_MIN);
  double log_max = std::log10(C_MAX);

  BlendTextOutline2x32(&base_img, cbar_x - 300, cbar_y + 4, 0x000000FF, 0xFFFFFFFF, "Margin c:");
  BlendTextOutline2x32(&base_img, cbar_x - 140, cbar_y + 4, 0x000000FF, 0xFFFFFFFF, "0.00020");

  static constexpr double STD_TICKS[] = {0.00050, 0.00100, 0.00200, 0.00500, 0.01000};
  static constexpr const char *STD_LABS[] = {
    "0.00050",
    "0.00100",
    "0.00200",
    "0.00500",
    "0.01000 (wide)"
  };

  for (size_t i = 0; i < std::size(STD_TICKS); i++) {
    double tau = (std::log10(STD_TICKS[i]) - log_min) / (log_max - log_min);
    int tx = cbar_x + (int)std::round(tau * (cbar_w - 1));
    if (i % 2 == 0) {
      base_img.BlendLine32(tx, cbar_y + cbar_h, tx, cbar_y + cbar_h + 8, 0xFFFFFFFF);
      base_img.BlendLine32(tx + 1, cbar_y + cbar_h, tx + 1, cbar_y + cbar_h + 8, 0xFFFFFFFF);
      int offset_x = (i == std::size(STD_TICKS) - 1) ? 110 : 35;
      BlendTextOutline2x32(&base_img, tx - offset_x, cbar_y + cbar_h + 12, 0x000000FF, 0xEEEEEEFF, STD_LABS[i]);
    } else {
      base_img.BlendLine32(tx, cbar_y - 8, tx, cbar_y, 0xFFFFFFFF);
      base_img.BlendLine32(tx + 1, cbar_y - 8, tx + 1, cbar_y, 0xFFFFFFFF);
      BlendTextOutline2x32(&base_img, tx - 35, cbar_y - 28, 0x000000FF, 0xEEEEEEFF, STD_LABS[i]);
    }
  }

  base_img.Save(outfile);
  Printf("Saved %s (%dx%d)\n", outfile.c_str(), WIDTH, HEIGHT);
}

// Projective Triangle domain constants on the 4K canvas:
// C0 = (1, 0, 0) -> bottom-left
// C1 = (10/41, 31/41, 0) -> bottom-right
// C2 = (0, 0, 1) -> top-apex
static constexpr vec2 PROJ_P_C0{400.0, 1960.0};
static constexpr vec2 PROJ_P_C1{2720.0, 1960.0};
static constexpr vec2 PROJ_P_C2{1560.0, 200.0};

// Convert exact 3D ray point to 2D projective barycentric screen space.
static inline vec2 ProjectiveToBarycentric(const vec3 &p) {
  double c2 = p.z;
  double c1 = (41.0 / 31.0) * p.y;
  double c0 = p.x - (10.0 / 31.0) * p.y;
  double sum = c0 + c1 + c2;
  if (sum <= 0.0) sum = 1.0;
  double u0 = c0 / sum;
  double u1 = c1 / sum;
  double u2 = c2 / sum;

  double sx = u0 * PROJ_P_C0.x + u1 * PROJ_P_C1.x + u2 * PROJ_P_C2.x;
  double sy = u0 * PROJ_P_C0.y + u1 * PROJ_P_C1.y + u2 * PROJ_P_C2.y;
  return vec2{sx, sy};
}

// Cohen-Sutherland 2D line segment clipping against [xmin, xmax] x [ymin, ymax].
static bool ClipLineToBox(double &x0, double &y0, double &x1, double &y1,
                          double xmin, double xmax, double ymin, double ymax) {
  auto Code = [&](double x, double y) -> int {
    int code = 0;
    if (x < xmin) code |= 1;
    else if (x > xmax) code |= 2;
    if (y < ymin) code |= 4;
    else if (y > ymax) code |= 8;
    return code;
  };

  int c0 = Code(x0, y0);
  int c1 = Code(x1, y1);

  while (true) {
    if ((c0 | c1) == 0) return true;
    if (c0 & c1) return false;

    int c_out = c0 ? c0 : c1;
    double x = 0, y = 0;
    if (c_out & 8) {
      x = x0 + (x1 - x0) * (ymax - y0) / (y1 - y0);
      y = ymax;
    } else if (c_out & 4) {
      x = x0 + (x1 - x0) * (ymin - y0) / (y1 - y0);
      y = ymin;
    } else if (c_out & 2) {
      y = y0 + (y1 - y0) * (xmax - x0) / (x1 - x0);
      x = xmax;
    } else if (c_out & 1) {
      y = y0 + (y1 - y0) * (xmin - x0) / (x1 - x0);
      x = xmin;
    }

    if (c_out == c0) {
      x0 = x; y0 = y;
      c0 = Code(x0, y0);
    } else {
      x1 = x; y1 = y;
      c1 = Code(x1, y1);
    }
  }
}

// Sutherland-Hodgman polygon clipping against [xmin, xmax] x [ymin, ymax].
static std::vector<vec2> ClipPolygonToBox(const std::vector<vec2> &poly,
                                          double xmin, double xmax,
                                          double ymin, double ymax) {
  std::vector<vec2> output = poly;

  auto ClipAgainstEdge = [&](double nx, double ny, double d) {
    if (output.empty()) return;
    std::vector<vec2> input = output;
    output.clear();
    for (size_t i = 0; i < input.size(); i++) {
      vec2 curr = input[i];
      vec2 prev = input[(i + input.size() - 1) % input.size()];
      double d_curr = curr.x * nx + curr.y * ny - d;
      double d_prev = prev.x * nx + prev.y * ny - d;
      if (d_curr >= 0.0) {
        if (d_prev < 0.0) {
          double denom = d_curr - d_prev;
          double t = (std::abs(denom) > 1e-12) ? (-d_prev / denom) : 0.0;
          output.push_back(vec2{prev.x + t * (curr.x - prev.x),
                                prev.y + t * (curr.y - prev.y)});
        }
        output.push_back(curr);
      } else if (d_prev >= 0.0) {
        double denom = d_curr - d_prev;
        double t = (std::abs(denom) > 1e-12) ? (-d_prev / denom) : 0.0;
        output.push_back(vec2{prev.x + t * (curr.x - prev.x),
                              prev.y + t * (curr.y - prev.y)});
      }
    }
  };

  ClipAgainstEdge(1.0, 0.0, xmin);
  ClipAgainstEdge(-1.0, 0.0, -xmax);
  ClipAgainstEdge(0.0, 1.0, ymin);
  ClipAgainstEdge(0.0, -1.0, -ymax);

  return output;
}

// ----------------------------------------------------------------------------
// VIEW 4: Projective Plane Triangle View (Barycentric Subdivision)
// ----------------------------------------------------------------------------
static void RenderProjectivePlane(const std::vector<LeafTriangle> &leaves,
                                  int child_filter,
                                  uint8_t line_alpha,
                                  const std::string &outfile) {
  ImageRGBA base_img(WIDTH, HEIGHT);
  base_img.Clear32(0x101218FF);

  BlendTextOutline2x32(&base_img, 60, 30, 0x000000FF, 0xFFFFFFFF,
                       "Nopert #229: Projective Triangle Domain ('Nested Triforces')");
  base_img.BlendText2x32(60, 68, 0x99AAB8FF,
                         "Exact native geometry of recursive projective quadtree bisection on the plane x + y + z = 1");
  base_img.BlendText2x32(60, 102, 0x00FFCCFF,
                         "Straight lines from apex C2 are constant phi meridians; horizontal lines are constant z parallels");

  const vec2 &P_C0 = PROJ_P_C0;
  const vec2 &P_C1 = PROJ_P_C1;
  const vec2 &P_C2 = PROJ_P_C2;

  DrawTriangle(&base_img,
               (int)P_C0.x, (int)P_C0.y,
               (int)P_C1.x, (int)P_C1.y,
               (int)P_C2.x, (int)P_C2.y,
               0x161922FF);

  // Canyon 1 & 2 projective lines
  uint32_t c1_color = 0xFF3366FF;
  vec2 c1_base = ProjectiveToBarycentric(vec3{std::cos(CANYON1.phi_rad), std::sin(CANYON1.phi_rad), 0.0});
  base_img.BlendLine32((int)P_C2.x, (int)P_C2.y, (int)c1_base.x, (int)c1_base.y, c1_color);
  base_img.BlendLine32((int)P_C2.x + 1, (int)P_C2.y, (int)c1_base.x + 1, (int)c1_base.y, c1_color);

  double c1_proj_z = CANYON1.v.z / (CANYON1.v.x + CANYON1.v.y + CANYON1.v.z);
  vec2 c1_left = (1.0 - c1_proj_z) * P_C0 + c1_proj_z * P_C2;
  vec2 c1_right = (1.0 - c1_proj_z) * P_C1 + c1_proj_z * P_C2;
  base_img.BlendLine32((int)c1_left.x, (int)c1_left.y, (int)c1_right.x, (int)c1_right.y, c1_color);
  base_img.BlendLine32((int)c1_left.x, (int)c1_left.y + 1, (int)c1_right.x, (int)c1_right.y + 1, c1_color);

  uint32_t c2_color = 0xFFD700FF;
  vec2 c2_base = ProjectiveToBarycentric(vec3{std::cos(CANYON2.phi_rad), std::sin(CANYON2.phi_rad), 0.0});
  base_img.BlendLine32((int)P_C2.x, (int)P_C2.y, (int)c2_base.x, (int)c2_base.y, c2_color);
  base_img.BlendLine32((int)P_C2.x + 1, (int)P_C2.y, (int)c2_base.x + 1, (int)c2_base.y, c2_color);

  double c2_proj_z = CANYON2.v.z / (CANYON2.v.x + CANYON2.v.y + CANYON2.v.z);
  vec2 c2_left = (1.0 - c2_proj_z) * P_C0 + c2_proj_z * P_C2;
  vec2 c2_right = (1.0 - c2_proj_z) * P_C1 + c2_proj_z * P_C2;
  base_img.BlendLine32((int)c2_left.x, (int)c2_left.y, (int)c2_right.x, (int)c2_right.y, c2_color);
  base_img.BlendLine32((int)c2_left.x, (int)c2_left.y + 1, (int)c2_right.x, (int)c2_right.y + 1, c2_color);

  BlendTextOutline2x32(&base_img, (int)c1_base.x - 45, (int)c1_base.y + 22, 0x000000FF, c1_color, "C1:2.22'");
  BlendTextOutline2x32(&base_img, (int)c1_left.x - 225, (int)c1_left.y - 8, 0x000000FF, c1_color, "C1: z=0.167");
  BlendTextOutline2x32(&base_img, (int)c2_base.x - 20, (int)c2_base.y + 48, 0x000000FF, c2_color, "C2:12.90'");
  BlendTextOutline2x32(&base_img, (int)c2_left.x - 225, (int)c2_left.y - 8, 0x000000FF, c2_color, "C2: z=0.317");

  // Rasterize leaf triangles
  ImageRGBA wireframe(WIDTH, HEIGHT);
  wireframe.Clear32(0x00000000);
  ImageRGBA incomplete_wireframe(WIDTH, HEIGHT);
  incomplete_wireframe.Clear32(0x00000000);

  for (const auto &leaf : leaves) {
    vec2 p0 = ProjectiveToBarycentric(leaf.p[0]);
    vec2 p1 = ProjectiveToBarycentric(leaf.p[1]);
    vec2 p2 = ProjectiveToBarycentric(leaf.p[2]);

    int x0 = (int)std::round(p0.x);
    int y0 = (int)std::round(p0.y);
    int x1 = (int)std::round(p1.x);
    int y1 = (int)std::round(p1.y);
    int x2 = (int)std::round(p2.x);
    int y2 = (int)std::round(p2.y);

    if (leaf.is_incomplete) {
      DrawStippledTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
      if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
        incomplete_wireframe.BlendLine32(x0, y0, x1, y1, INCOMPLETE_OUTLINE_COLOR);
        incomplete_wireframe.BlendLine32(x1, y1, x2, y2, INCOMPLETE_OUTLINE_COLOR);
        incomplete_wireframe.BlendLine32(x2, y2, x0, y0, INCOMPLETE_OUTLINE_COLOR);
      }
    } else {
      DrawTriangle(&base_img, x0, y0, x1, y1, x2, y2, leaf.color);
      if (!(x0 == x1 && x1 == x2 && y0 == y1 && y1 == y2)) {
        wireframe.BlendLine32(x0, y0, x1, y1, 0x000000FF);
        wireframe.BlendLine32(x1, y1, x2, y2, 0x000000FF);
        wireframe.BlendLine32(x2, y2, x0, y0, 0x000000FF);
      }
    }
  }

  for (uint32_t &p : wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | line_alpha;
    }
  }
  base_img.BlendImage(0, 0, wireframe);

  for (uint32_t &p : incomplete_wireframe.data()) {
    if ((p & 0xFF) != 0) {
      p = (p & 0xFFFFFF00) | 0xE6;
    }
  }
  base_img.BlendImage(0, 0, incomplete_wireframe);

  // Outer boundary outline
  auto DrawThickBoundary = [&](int xa, int ya, int xb, int yb) {
    base_img.BlendLine32(xa, ya, xb, yb, 0xFFFFFFFF);
    base_img.BlendLine32(xa + 1, ya, xb + 1, yb, 0xFFFFFFFF);
    base_img.BlendLine32(xa, ya + 1, xb, yb + 1, 0xFFFFFFFF);
  };
  DrawThickBoundary((int)P_C0.x, (int)P_C0.y, (int)P_C1.x, (int)P_C1.y);
  DrawThickBoundary((int)P_C1.x, (int)P_C1.y, (int)P_C2.x, (int)P_C2.y);
  DrawThickBoundary((int)P_C2.x, (int)P_C2.y, (int)P_C0.x, (int)P_C0.y);

  // Corner labels
  BlendTextOutline2x32(&base_img, (int)P_C0.x - 340, (int)P_C0.y + 12,
                       0x000000FF, 0xFFFFFFFF, "C0 = (1, 0, 0)");
  BlendTextOutline2x32(&base_img, (int)P_C0.x - 260, (int)P_C0.y + 44,
                       0x000000FF, 0xAAAAAAFF, "[phi=0]");
  BlendTextOutline2x32(&base_img, (int)P_C1.x + 16, (int)P_C1.y + 12,
                       0x000000FF, 0xFFFFFFFF, "C1 = (10/41, 31/41, 0) [72.1 deg]");
  BlendTextOutline2x32(&base_img, (int)P_C2.x - 120, (int)P_C2.y - 32,
                       0x000000FF, 0xFFFFFFFF, "C2 = (0, 0, 1) [Pole]");

  // Render corner brackets for Trees 0..3 in projective barycentric space
  RenderTreeIndicators(&base_img, child_filter, false, [&](int corner_idx, const vec3 &p) -> vec2 {
    return ProjectiveToBarycentric(p);
  });

  RenderColorbar(&base_img, 2950, 200, 44, 1760);
  RenderLegendCard(&base_img, 80, 180, child_filter);

  base_img.Save(outfile);
  Printf("Saved %s (%dx%d)\n", outfile.c_str(), WIDTH, HEIGHT);
}

// ----------------------------------------------------------------------------
// VIEW 5: Zoomed Subdivision Detail View (16:9 Full Screen, Projective Domain)
// ----------------------------------------------------------------------------
struct ZoomBox {
  double x0 = 0.0;
  double x1 = 0.0;
  double y0 = 0.0;
  double y1 = 0.0;
  double zoom_mag = 1.0;
  std::string focal_desc1;
  std::string focal_desc2;
};

static ZoomBox FindZoomBox(int tree_idx, const std::vector<LeafTriangle> &all_leaves) {
  std::vector<const LeafTriangle *> tree_leaves;
  std::vector<const LeafTriangle *> incomp_leaves;
  int max_depth = 0;

  for (const auto &leaf : all_leaves) {
    if (leaf.root == tree_idx) {
      tree_leaves.push_back(&leaf);
      max_depth = std::max(max_depth, leaf.depth);
      if (leaf.is_incomplete) {
        incomp_leaves.push_back(&leaf);
      }
    }
  }

  ZoomBox box;
  constexpr double ASPECT = 16.0 / 9.0;

  auto FitTo16By9 = [&](double min_x, double max_x,
                        double min_y, double max_y,
                        double margin_frac) {
    double bw = std::max(max_x - min_x, 1e-4);
    double bh = std::max(max_y - min_y, 1e-4);
    double w_prime = bw * (1.0 + 2.0 * margin_frac);
    double h_prime = bh * (1.0 + 2.0 * margin_frac);
    double cx = (min_x + max_x) * 0.5;
    double cy = (min_y + max_y) * 0.5;
    double wf, hf;
    if (w_prime / h_prime < ASPECT) {
      wf = ASPECT * h_prime;
      hf = h_prime;
    } else {
      wf = w_prime;
      hf = w_prime / ASPECT;
    }
    box.x0 = cx - wf * 0.5;
    box.x1 = cx + wf * 0.5;
    box.y0 = cy - hf * 0.5;
    box.y1 = cy + hf * 0.5;
    box.zoom_mag = 3840.0 / wf;
  };

  if (!incomp_leaves.empty()) {
    // Incomplete tree: take bounding box of incomplete regions + 5% margin
    double min_x = 1e30, max_x = -1e30;
    double min_y = 1e30, max_y = -1e30;
    for (const auto *leaf : incomp_leaves) {
      for (int v = 0; v < 3; v++) {
        vec2 pt = ProjectiveToBarycentric(leaf->p[v]);
        min_x = std::min(min_x, pt.x);
        max_x = std::max(max_x, pt.x);
        min_y = std::min(min_y, pt.y);
        max_y = std::max(max_y, pt.y);
      }
    }
    FitTo16By9(min_x, max_x, min_y, max_y, 0.05);
    box.focal_desc1 = "Incomplete pinch canyon";
    box.focal_desc2 = std::format("{} cells, depth 7..{}", incomp_leaves.size(), max_depth);
    return box;
  }

  // Complete tree: choose an area that has a lot of subdivision.
  // Evaluate bounding box of deepest leaves vs dense subdivision subtrees.
  std::vector<const LeafTriangle *> deepest_leaves;
  for (const auto *leaf : tree_leaves) {
    if (leaf->depth == max_depth) {
      deepest_leaves.push_back(leaf);
    }
  }

  double d_min_x = 1e30, d_max_x = -1e30;
  double d_min_y = 1e30, d_max_y = -1e30;
  for (const auto *leaf : deepest_leaves) {
    for (int v = 0; v < 3; v++) {
      vec2 pt = ProjectiveToBarycentric(leaf->p[v]);
      d_min_x = std::min(d_min_x, pt.x);
      d_max_x = std::max(d_max_x, pt.x);
      d_min_y = std::min(d_min_y, pt.y);
      d_max_y = std::max(d_max_y, pt.y);
    }
  }

  double d_width = d_max_x - d_min_x;
  // If the deepest leaves form a compact cluster (<= 150 projective pixels),
  // zoom in directly on the deepest leaves with 5% margin!
  if (d_width <= 150.0 && !deepest_leaves.empty()) {
    FitTo16By9(d_min_x, d_max_x, d_min_y, d_max_y, 0.05);
    box.focal_desc1 = "Deepest subdivision";
    box.focal_desc2 = std::format("{} cells at max depth {}", deepest_leaves.size(), max_depth);
  } else {
    // If the deepest leaves are spread along an extended boundary (like Tree 1),
    // group leaves by depth-5 path prefix (5 digits) and find the prefix
    // with the highest number of deep leaves:
    std::unordered_map<std::string, std::vector<const LeafTriangle *>> prefix_map;
    for (const auto *leaf : tree_leaves) {
      if (leaf->path.size() >= 5) {
        prefix_map[leaf->path.substr(0, 5)].push_back(leaf);
      }
    }

    std::string best_prefix;
    size_t best_count = 0;
    for (const auto &[pref, plist] : prefix_map) {
      if (plist.size() > best_count) {
        best_count = plist.size();
        best_prefix = pref;
      }
    }

    if (!best_prefix.empty()) {
      const auto &plist = prefix_map[best_prefix];
      double p_min_x = 1e30, p_max_x = -1e30;
      double p_min_y = 1e30, p_max_y = -1e30;
      for (const auto *leaf : plist) {
        for (int v = 0; v < 3; v++) {
          vec2 pt = ProjectiveToBarycentric(leaf->p[v]);
          p_min_x = std::min(p_min_x, pt.x);
          p_max_x = std::max(p_max_x, pt.x);
          p_min_y = std::min(p_min_y, pt.y);
          p_max_y = std::max(p_max_y, pt.y);
        }
      }
      FitTo16By9(p_min_x, p_max_x, p_min_y, p_max_y, 0.05);
      box.focal_desc1 = std::format("Dense cluster (prefix {})", best_prefix);
      box.focal_desc2 = std::format("{} leaves, max depth {}", plist.size(), max_depth);
    } else {
      // Fallback
      FitTo16By9(d_min_x, d_max_x, d_min_y, d_max_y, 0.05);
      box.focal_desc1 = "Subdivision detail";
      box.focal_desc2 = std::format("Maximum depth {}", max_depth);
    }
  }

  // For complete trees: check if all triangles in view are large.
  // Zoom out around the focal center while all triangles in the zoomed view
  // are large (i.e. until at least some triangle in the zoomed image is small,
  // say <= 16 pixels tall or wide).
  double cx = (box.x0 + box.x1) * 0.5;
  double cy = (box.y0 + box.y1) * 0.5;
  double cur_w = box.x1 - box.x0;
  double cur_h = box.y1 - box.y0;

  struct LeafBBox {
    double min_x, max_x, min_y, max_y;
    double w, h;
  };
  std::vector<LeafBBox> bboxes;
  bboxes.reserve(tree_leaves.size());
  for (const auto *leaf : tree_leaves) {
    double lx0 = 1e30, lx1 = -1e30, ly0 = 1e30, ly1 = -1e30;
    for (int v = 0; v < 3; v++) {
      vec2 pt = ProjectiveToBarycentric(leaf->p[v]);
      lx0 = std::min(lx0, pt.x);
      lx1 = std::max(lx1, pt.x);
      ly0 = std::min(ly0, pt.y);
      ly1 = std::max(ly1, pt.y);
    }
    bboxes.push_back({lx0, lx1, ly0, ly1, lx1 - lx0, ly1 - ly0});
  }

  auto AnyTriangleSmallInView = [&](double w, double h) -> bool {
    double mag = 3840.0 / w;
    double vx0 = cx - w * 0.5;
    double vx1 = cx + w * 0.5;
    double vy0 = cy - h * 0.5;
    double vy1 = cy + h * 0.5;

    for (const auto &b : bboxes) {
      if (b.max_x < vx0 || b.min_x > vx1 || b.max_y < vy0 || b.min_y > vy1) {
        continue;
      }
      double tw = b.w * mag;
      double th = b.h * mag;
      // Small if <= 16 pixels tall or wide
      if (tw <= 16.0 || th <= 16.0) {
        return true;
      }
    }
    return false;
  };

  while (!AnyTriangleSmallInView(cur_w, cur_h) && cur_w < 2400.0) {
    cur_w *= 1.02;
    cur_h = cur_w / ASPECT;
  }

  box.x0 = cx - cur_w * 0.5;
  box.x1 = cx + cur_w * 0.5;
  box.y0 = cy - cur_h * 0.5;
  box.y1 = cy + cur_h * 0.5;
  box.zoom_mag = 3840.0 / cur_w;
  return box;
}

static void RenderZoomView(const std::vector<LeafTriangle> &all_leaves,
                           int tree_idx,
                           uint8_t line_alpha,
                           const std::string &outfile) {
  ImageRGBA base_img(WIDTH, HEIGHT);
  base_img.Clear32(0x101218FF);

  ZoomBox zoom_box = FindZoomBox(tree_idx, all_leaves);

  auto ProjToScreen = [&](const vec2 &p) -> vec2 {
    double sx = (p.x - zoom_box.x0) / (zoom_box.x1 - zoom_box.x0) * (double)WIDTH;
    double sy = (p.y - zoom_box.y0) / (zoom_box.y1 - zoom_box.y0) * (double)HEIGHT;
    return vec2{sx, sy};
  };

  ImageRGBA wireframe(WIDTH, HEIGHT);
  wireframe.Clear32(0x00000000);
  ImageRGBA incomplete_wireframe(WIDTH, HEIGHT);
  incomplete_wireframe.Clear32(0x00000000);

  int total_tree_leaves = 0;
  int leaves_in_view = 0;
  int cert_in_view = 0;
  int incomp_in_view = 0;

  // Render leaves belonging to this tree
  for (const auto &leaf : all_leaves) {
    if (leaf.root != tree_idx) continue;
    total_tree_leaves++;

    vec2 p0 = ProjectiveToBarycentric(leaf.p[0]);
    vec2 p1 = ProjectiveToBarycentric(leaf.p[1]);
    vec2 p2 = ProjectiveToBarycentric(leaf.p[2]);

    // Fast bounding box rejection in projective coordinates
    double b_min_x = std::min({p0.x, p1.x, p2.x});
    double b_max_x = std::max({p0.x, p1.x, p2.x});
    double b_min_y = std::min({p0.y, p1.y, p2.y});
    double b_max_y = std::max({p0.y, p1.y, p2.y});
    if (b_max_x < zoom_box.x0 || b_min_x > zoom_box.x1 ||
        b_max_y < zoom_box.y0 || b_min_y > zoom_box.y1) {
      continue;
    }

    vec2 s0 = ProjToScreen(p0);
    vec2 s1 = ProjToScreen(p1);
    vec2 s2 = ProjToScreen(p2);

    double scr_min_x = std::min({s0.x, s1.x, s2.x});
    double scr_max_x = std::max({s0.x, s1.x, s2.x});
    double scr_min_y = std::min({s0.y, s1.y, s2.y});
    double scr_max_y = std::max({s0.y, s1.y, s2.y});

    if (scr_max_x < 0.0 || scr_min_x >= (double)WIDTH ||
        scr_max_y < 0.0 || scr_min_y >= (double)HEIGHT) {
      continue;
    }

    leaves_in_view++;
    if (leaf.is_incomplete) incomp_in_view++;
    else cert_in_view++;

    // Draw triangle (with clipping if needed)
    if (scr_min_x >= 0.0 && scr_max_x < (double)WIDTH &&
        scr_min_y >= 0.0 && scr_max_y < (double)HEIGHT) {
      // Completely on screen
      if (leaf.is_incomplete) {
        DrawStippledTriangle(&base_img,
                             (int)std::round(s0.x), (int)std::round(s0.y),
                             (int)std::round(s1.x), (int)std::round(s1.y),
                             (int)std::round(s2.x), (int)std::round(s2.y),
                             leaf.color);
      } else {
        DrawTriangle(&base_img,
                     (int)std::round(s0.x), (int)std::round(s0.y),
                     (int)std::round(s1.x), (int)std::round(s1.y),
                     (int)std::round(s2.x), (int)std::round(s2.y),
                     leaf.color);
      }
    } else {
      // Straddles screen boundary: clip polygon
      std::vector<vec2> poly = {s0, s1, s2};
      poly = ClipPolygonToBox(poly, 0.0, (double)(WIDTH - 1), 0.0, (double)(HEIGHT - 1));
      if (poly.size() >= 3) {
        for (size_t i = 1; i + 1 < poly.size(); i++) {
          if (leaf.is_incomplete) {
            DrawStippledTriangle(&base_img,
                                 (int)std::round(poly[0].x), (int)std::round(poly[0].y),
                                 (int)std::round(poly[i].x), (int)std::round(poly[i].y),
                                 (int)std::round(poly[i + 1].x), (int)std::round(poly[i + 1].y),
                                 leaf.color);
          } else {
            DrawTriangle(&base_img,
                         (int)std::round(poly[0].x), (int)std::round(poly[0].y),
                         (int)std::round(poly[i].x), (int)std::round(poly[i].y),
                         (int)std::round(poly[i + 1].x), (int)std::round(poly[i + 1].y),
                         leaf.color);
          }
        }
      }
    }

    // Wireframe edges: clip each edge to screen boundary
    vec2 edge_v[3][2] = {{s0, s1}, {s1, s2}, {s2, s0}};
    for (int e = 0; e < 3; e++) {
      double lx0 = edge_v[e][0].x, ly0 = edge_v[e][0].y;
      double lx1 = edge_v[e][1].x, ly1 = edge_v[e][1].y;
      if (ClipLineToBox(lx0, ly0, lx1, ly1, 0.0, (double)(WIDTH - 1), 0.0, (double)(HEIGHT - 1))) {
        if (leaf.is_incomplete) {
          incomplete_wireframe.BlendLine32((int)std::round(lx0), (int)std::round(ly0),
                                          (int)std::round(lx1), (int)std::round(ly1),
                                          INCOMPLETE_OUTLINE_COLOR);
        } else {
          wireframe.BlendLine32((int)std::round(lx0), (int)std::round(ly0),
                                (int)std::round(lx1), (int)std::round(ly1),
                                0xFFFFFF00);
        }
      }
    }
  }

  // Blend wireframes
  for (uint32_t &p : wireframe.data()) {
    if ((p & 0xFF) != 0) p = (p & 0xFFFFFF00) | line_alpha;
  }
  base_img.BlendImage(0, 0, wireframe);

  for (uint32_t &p : incomplete_wireframe.data()) {
    if ((p & 0xFF) != 0) p = (p & 0xFFFFFF00) | 0xE6;
  }
  base_img.BlendImage(0, 0, incomplete_wireframe);

  // Canyon 1 & 2 guide lines
  auto DrawCanyonLine = [&](const vec2 &start, const vec2 &end, uint32_t color,
                            std::string_view label) {
    double x0 = start.x, y0 = start.y, x1 = end.x, y1 = end.y;
    if (ClipLineToBox(x0, y0, x1, y1, 0.0, (double)(WIDTH - 1), 0.0, (double)(HEIGHT - 1))) {
      DrawThickSegment(&base_img, (float)x0, (float)y0, (float)x1, (float)y1, color, 3.5f);
      int lx = (int)std::clamp((x0 + x1) * 0.5 + 15.0, 40.0, (double)(WIDTH - 300));
      int ly = (int)std::clamp((y0 + y1) * 0.5 - 20.0, 40.0, (double)(HEIGHT - 40));
      BlendTextOutline2x32(&base_img, lx, ly, 0x000000FF, color, label);
    }
  };

  vec2 c1_base = ProjectiveToBarycentric(vec3{std::cos(CANYON1.phi_rad), std::sin(CANYON1.phi_rad), 0.0});
  DrawCanyonLine(ProjToScreen(PROJ_P_C2), ProjToScreen(c1_base), 0xFF3366FF, "Canyon 1 (Az 2.22')");

  double c1_proj_z = CANYON1.v.z / (CANYON1.v.x + CANYON1.v.y + CANYON1.v.z);
  vec2 c1_left = (1.0 - c1_proj_z) * PROJ_P_C0 + c1_proj_z * PROJ_P_C2;
  vec2 c1_right = (1.0 - c1_proj_z) * PROJ_P_C1 + c1_proj_z * PROJ_P_C2;
  DrawCanyonLine(ProjToScreen(c1_left), ProjToScreen(c1_right), 0xFF3366FF, "Canyon 1 (Elev 9.63')");

  vec2 c2_base = ProjectiveToBarycentric(vec3{std::cos(CANYON2.phi_rad), std::sin(CANYON2.phi_rad), 0.0});
  DrawCanyonLine(ProjToScreen(PROJ_P_C2), ProjToScreen(c2_base), 0xFFD700FF, "Canyon 2 (Az 12.90')");

  double c2_proj_z = CANYON2.v.z / (CANYON2.v.x + CANYON2.v.y + CANYON2.v.z);
  vec2 c2_left = (1.0 - c2_proj_z) * PROJ_P_C0 + c2_proj_z * PROJ_P_C2;
  vec2 c2_right = (1.0 - c2_proj_z) * PROJ_P_C1 + c2_proj_z * PROJ_P_C2;
  DrawCanyonLine(ProjToScreen(c2_left), ProjToScreen(c2_right), 0xFFD700FF, "Canyon 2 (Elev 18.48')");

  // Root Tree boundary edges
  std::array<TriangleQ, 4> root_trees = GetRootTrees();
  const TriangleQ &cur_root = root_trees[tree_idx];
  vec2 rt_pts[3];
  for (int v = 0; v < 3; v++) {
    rt_pts[v] = ProjToScreen(ProjectiveToBarycentric(ToDouble(cur_root.corners[v])));
  }
  for (int e = 0; e < 3; e++) {
    int next_e = (e + 1) % 3;
    double x0 = rt_pts[e].x, y0 = rt_pts[e].y;
    double x1 = rt_pts[next_e].x, y1 = rt_pts[next_e].y;
    if (ClipLineToBox(x0, y0, x1, y1, 0.0, (double)(WIDTH - 1), 0.0, (double)(HEIGHT - 1))) {
      DrawThickSegment(&base_img, (float)x0, (float)y0, (float)x1, (float)y1,
                       TREE_STYLES[tree_idx].color, 2.0f);
    }
  }

  // Draw corner brackets if any vertex of tree_idx is on-screen
  for (int v = 0; v < 3; v++) {
    if (rt_pts[v].x >= 0 && rt_pts[v].x < WIDTH &&
        rt_pts[v].y >= 0 && rt_pts[v].y < HEIGHT) {
      int prev_v = (v + 2) % 3;
      int next_v = (v + 1) % 3;
      DrawBracket(&base_img, (float)rt_pts[v].x, (float)rt_pts[v].y,
                  (float)rt_pts[prev_v].x, (float)rt_pts[prev_v].y,
                  (float)rt_pts[next_v].x, (float)rt_pts[next_v].y,
                  TREE_STYLES[tree_idx].color, 60.0f);
    }
  }

  // HUD Card & Mini-Map
  const int card_w = 1120;
  const int card_h = 300;
  int card_x = 60;
  // If focal area is in top half of screen, place card at bottom-left; otherwise top-left
  int card_y = (zoom_box.y0 < 600.0) ? (HEIGHT - card_h - 60) : 60;

  DrawCard(&base_img, card_x, card_y, card_w, card_h, 0x141822F0, TREE_STYLES[tree_idx].color);

  // Tree Badge
  DrawCard(&base_img, card_x + 24, card_y + 18, 120, 32,
           TREE_STYLES[tree_idx].badge_bg, TREE_STYLES[tree_idx].color);
  BlendTextOutline2x32(&base_img, card_x + 32, card_y + 25, 0x000000FF,
                       TREE_STYLES[tree_idx].color, TREE_STYLES[tree_idx].name);

  // Title
  BlendTextOutline2x32(&base_img, card_x + 160, card_y + 24, 0x000000FF,
                       0xFFFFFFFF, "SUBDIVISION DETAIL ZOOM (16:9)");

  // Line 2: Magnification & projection
  std::string line2 = std::format("Magnification: {:.1f}x  |  Projective Triangle Domain",
                                  zoom_box.zoom_mag);
  BlendTextOutline2x32(&base_img, card_x + 24, card_y + 60, 0x000000FF, 0x00FFCCFF, line2);

  // Line 3 & 4: Focal area
  std::string line3 = std::format("Focal: {}", zoom_box.focal_desc1);
  BlendTextOutline2x32(&base_img, card_x + 24, card_y + 94, 0x000000FF, 0xCCCCCCFF, line3);
  if (!zoom_box.focal_desc2.empty()) {
    std::string line4 = std::format("       {}", zoom_box.focal_desc2);
    BlendTextOutline2x32(&base_img, card_x + 24, card_y + 128, 0x000000FF, 0xAAAAAAFF, line4);
  }

  // Line 5 & 6: Cells in view
  std::string line5 = std::format("In View: {} leaves ({:.1f}% of tree)",
                                  leaves_in_view,
                                  total_tree_leaves > 0 ? (leaves_in_view * 100.0 / total_tree_leaves) : 0.0);
  BlendTextOutline2x32(&base_img, card_x + 24, card_y + 162, 0x000000FF, 0xEEEEEEFF, line5);

  if (incomp_in_view > 0) {
    std::string line6 = std::format("         {} certified, {} incomplete", cert_in_view, incomp_in_view);
    BlendTextOutline2x32(&base_img, card_x + 24, card_y + 196, 0x000000FF, 0xFF88CCFF, line6);
  } else {
    std::string line6 = std::format("         {} certified (100% complete)", cert_in_view);
    BlendTextOutline2x32(&base_img, card_x + 24, card_y + 196, 0x000000FF, 0x88FF88FF, line6);
  }

  // Mini colorbar
  int bar_x = card_x + 24;
  int bar_y = card_y + 236;
  int bar_w = 340;
  int bar_h = 16;
  for (int bx = 0; bx < bar_w; bx++) {
    float tau = (float)bx / (float)(bar_w - 1);
    uint32_t c = ColorUtil::LinearGradient32(MARGIN_RAMP, tau);
    for (int by = 0; by < bar_h; by++) {
      base_img.BlendPixel32(bar_x + bx, bar_y + by, c);
    }
  }
  base_img.BlendBox32(bar_x, bar_y, bar_w, bar_h, 0xFFFFFFFF, 0xFFFFFFFF);
  BlendTextOutline2x32(&base_img, bar_x, bar_y + 20, 0x000000FF, 0xAAAAAAFF, "1e-4");
  BlendTextOutline2x32(&base_img, bar_x + bar_w / 2 - 20, bar_y + 20, 0x000000FF, 0xAAAAAAFF, "1e-2");
  BlendTextOutline2x32(&base_img, bar_x + bar_w - 40, bar_y + 20, 0x000000FF, 0xAAAAAAFF, "1e-1");

  // Incomplete swatch if incomplete cells exist in view
  if (incomp_in_view > 0) {
    int sw_x = card_x + 390;
    int sw_y = bar_y;
    for (int py = sw_y; py < sw_y + 16; py++) {
      for (int px = sw_x; px < sw_x + 24; px++) {
        if (((px / 2) ^ (py / 2)) & 1) {
          base_img.BlendPixel32(px, py, 0xFFD700FF);
        }
      }
    }
    base_img.BlendBox32(sw_x, sw_y, 24, 16, INCOMPLETE_OUTLINE_COLOR, INCOMPLETE_OUTLINE_COLOR);
    base_img.BlendBox32(sw_x - 1, sw_y - 1, 26, 18, INCOMPLETE_OUTLINE_COLOR, INCOMPLETE_OUTLINE_COLOR);
    BlendTextOutline2x32(&base_img, sw_x + 32, sw_y, 0x000000FF, 0xFF88CCFF,
                         "Stippled: Incomp bound");
  }

  // Mini-Map on right of card
  BlendTextOutline2x32(&base_img, card_x + 885, card_y + 24, 0x000000FF, 0xAAAAAAFF, "Full Domain");
  const vec2 P0{(double)(card_x + 840), (double)(card_y + 265)};
  const vec2 P1{(double)(card_x + 1080), (double)(card_y + 265)};
  const vec2 P2{(double)(card_x + 960), (double)(card_y + 65)};
  const vec2 M01{(double)(card_x + 960), (double)(card_y + 265)};
  const vec2 M12{(double)(card_x + 1020), (double)(card_y + 165)};
  const vec2 M20{(double)(card_x + 900), (double)(card_y + 165)};

  auto DrawMiniSubTri = [&](const vec2 &a, const vec2 &b, const vec2 &c,
                            const TreeStyle &st, const char *label, int tx, int ty) {
    DrawTriangle(&base_img, (float)a.x, (float)a.y, (float)b.x, (float)b.y, (float)c.x, (float)c.y, st.badge_bg);
    DrawThickSegment(&base_img, (float)a.x, (float)a.y, (float)b.x, (float)b.y, st.color, 1.5f);
    DrawThickSegment(&base_img, (float)b.x, (float)b.y, (float)c.x, (float)c.y, st.color, 1.5f);
    DrawThickSegment(&base_img, (float)c.x, (float)c.y, (float)a.x, (float)a.y, st.color, 1.5f);
    BlendTextOutline2x32(&base_img, tx, ty, 0x000000FF, st.color, label);
  };

  DrawMiniSubTri(M20, M12, P2, TREE_STYLES[2], "2", card_x + 952, card_y + 125);
  DrawMiniSubTri(P0, M01, M20, TREE_STYLES[0], "0", card_x + 892, card_y + 220);
  DrawMiniSubTri(M01, P1, M12, TREE_STYLES[1], "1", card_x + 1012, card_y + 220);
  DrawMiniSubTri(M12, M20, M01, TREE_STYLES[3], "3", card_x + 952, card_y + 190);

  // Draw current zoom window on mini-map
  auto MapToMini = [&](double px, double py) -> vec2 {
    double u_x = (px - PROJ_P_C0.x) / (PROJ_P_C1.x - PROJ_P_C0.x);
    double u_y = (py - PROJ_P_C2.y) / (PROJ_P_C0.y - PROJ_P_C2.y);
    return vec2{card_x + 840.0 + u_x * 240.0, card_y + 65.0 + u_y * 200.0};
  };

  vec2 m0 = MapToMini(zoom_box.x0, zoom_box.y0);
  vec2 m1 = MapToMini(zoom_box.x1, zoom_box.y1);
  int bx0 = std::clamp((int)m0.x, card_x + 830, card_x + 1090);
  int bx1 = std::clamp((int)m1.x, card_x + 830, card_x + 1090);
  int by0 = std::clamp((int)m0.y, card_y + 55, card_y + 275);
  int by1 = std::clamp((int)m1.y, card_y + 55, card_y + 275);
  int bw = std::max(bx1 - bx0, 6);
  int bh = std::max(by1 - by0, 4);

  base_img.BlendRect32(bx0 - 1, by0 - 1, bw + 2, bh + 2, 0xFF3300C0);
  base_img.BlendBox32(bx0 - 2, by0 - 2, bw + 4, bh + 4, 0xFFFFFFFF, 0xFFFFFFFF);
  base_img.BlendBox32(bx0 - 3, by0 - 3, bw + 6, bh + 6, 0x000000FF, 0x000000FF);

  base_img.Save(outfile);
  Printf("Saved %s (%dx%d, %.1fx zoom)\n", outfile.c_str(), WIDTH, HEIGHT, zoom_box.zoom_mag);
}

// ----------------------------------------------------------------------------
// Main CLI Entrypoint
// ----------------------------------------------------------------------------
int main(int argc, char **argv) {
  std::string artifacts_dir;
  std::string tree_file;
  std::string samples_file;
  std::string output_prefix = "tube_";
  int child_filter = -1; // -1 = load all available children (0..3)
  uint8_t line_alpha = 56; // 56/255 ≈ 22% opacity for wireframe overlay

  // Search candidate artifact directories
  const std::vector<std::string> CANDIDATES = {
    "/home/tom/tom7misc/ruperts/.artifacts/nopert229",
    "../tom7misc/ruperts/.artifacts/nopert229",
    "/home/tom/nopert-project/Noperthedron/.artifacts/nopert229",
    "../Noperthedron/.artifacts/nopert229",
    "Noperthedron/.artifacts/nopert229",
    ".artifacts/nopert229",
  };

  for (const auto &cand : CANDIDATES) {
    if (std::filesystem::exists(cand)) {
      artifacts_dir = cand;
      break;
    }
  }

  // Parse CLI args
  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--artifacts_dir" && i + 1 < argc) {
      artifacts_dir = argv[++i];
    } else if (arg == "--tree" && i + 1 < argc) {
      tree_file = argv[++i];
    } else if (arg == "--samples" && i + 1 < argc) {
      samples_file = argv[++i];
    } else if (arg == "--output_prefix" && i + 1 < argc) {
      output_prefix = argv[++i];
    } else if (arg == "--child" && i + 1 < argc) {
      child_filter = std::atoi(argv[++i]);
    } else if (arg == "--line_alpha" && i + 1 < argc) {
      line_alpha = (uint8_t)std::clamp(std::atoi(argv[++i]), 0, 255);
    } else if (arg == "--help" || arg == "-h") {
      Printf("Usage: %s [options]\n", argv[0]);
      Printf("  --artifacts_dir <path> : Path to directory with tree_0.json .. tree_3.json\n");
      Printf("  --tree <file.json>     : Load a single tree JSON file directly\n");
      Printf("  --child <0..3>         : Load specific child index (-1 for all, default -1)\n");
      Printf("  --samples <file.csv>   : Optional empirical samples CSV\n");
      Printf("  --output_prefix <pre>  : Output file prefix (default 'tube_')\n");
      Printf("  --line_alpha <0..255>  : Wireframe layer opacity (default 56 = ~22%%)\n");
      return 0;
    }
  }

  Printf("=== Nopert #229 Identity Tube & View Sphere Margin Visualization ===\n");
  if (!tree_file.empty()) {
    Printf("Direct Tree File:    %s\n", tree_file.c_str());
  } else {
    Printf("Artifacts Directory: %s\n", artifacts_dir.c_str());
  }
  Printf("Canvas Dimensions:   %d x %d (16:9)\n", WIDTH, HEIGHT);
  Printf("Wireframe Alpha:     %d/255\n", line_alpha);

  std::vector<LeafTriangle> leaves;
  int total_nodes = 0;
  int certified_leaves = 0;
  int incomplete_leaves = 0;

  if (!tree_file.empty()) {
    if (!LoadTubeTree(tree_file, &leaves, &total_nodes, &certified_leaves, &incomplete_leaves)) {
      Printf("Error: Failed to load tree file: %s\n", tree_file.c_str());
      return 1;
    }
  } else {
    if (artifacts_dir.empty()) {
      Printf("Error: No artifacts directory found. Please specify with --artifacts_dir <path>\n");
      return 1;
    }

    for (int child = 0; child < 4; child++) {
      if (child_filter >= 0 && child != child_filter) continue;
      std::string filename = std::format("tree_{}.json", child);
      std::string fullpath = (std::filesystem::path(artifacts_dir) / filename).string();

      if (std::filesystem::exists(fullpath)) {
        LoadTubeTree(fullpath, &leaves, &total_nodes, &certified_leaves, &incomplete_leaves);
      } else {
        Printf("  Tree %d (%s) not found (pending computation)\n", child, fullpath.c_str());
      }
    }
  }

  if (leaves.empty()) {
    Printf("Error: No leaf triangles loaded from %s!\n",
           tree_file.empty() ? artifacts_dir.c_str() : tree_file.c_str());
    return 1;
  }

  Printf("Loaded %zu total leaves (%d certified, %d incomplete) across %d tree nodes.\n",
         leaves.size(), certified_leaves, incomplete_leaves, total_nodes);

  std::vector<EmpiricalSample> samples;
  if (!samples_file.empty()) {
    samples = LoadEmpiricalSamples(samples_file);
  }

  // Generate all 4 visualizations:
  std::string file_wedge_eq = output_prefix + "wedge_equirect.png";
  std::string file_wedge_lam = output_prefix + "wedge_lambert.png";
  std::string file_full = output_prefix + "full_sphere.png";
  std::string file_proj = output_prefix + "projective_plane.png";

  Printf("\nRendering View 1: Upper Wedge Equirectangular -> %s...\n", file_wedge_eq.c_str());
  RenderWedgeEquirect(leaves, samples, child_filter, line_alpha, file_wedge_eq);

  Printf("\nRendering View 2: Upper Wedge Lambert Equal-Area -> %s...\n", file_wedge_lam.c_str());
  RenderWedgeLambert(leaves, samples, child_filter, line_alpha, file_wedge_lam);

  Printf("\nRendering View 3: Full Sphere (C5 Replicated) -> %s...\n", file_full.c_str());
  RenderFullSphere(leaves, child_filter, line_alpha, file_full);

  Printf("\nRendering View 4: Projective Plane Barycentric Triangle -> %s...\n", file_proj.c_str());
  RenderProjectivePlane(leaves, child_filter, line_alpha, file_proj);

  // Generate View 5: Zoomed Views (16:9 full-screen, projective projection) for each tree:
  // For incomplete trees: bounding box of incomplete regions + 5% margin.
  // For complete trees: area of heavy subdivision.
  // Files: tube_zoom0.png, tube_zoom1.png, tube_zoom2.png, tube_zoom3.png.
  for (int k = 0; k < 4; k++) {
    if (child_filter >= 0 && child_filter != k) continue;
    bool has_tree = false;
    for (const auto &leaf : leaves) {
      if (leaf.root == k) {
        has_tree = true;
        break;
      }
    }
    if (!has_tree) continue;

    std::string file_zoom = output_prefix + "zoom" + std::to_string(k) + ".png";
    Printf("\nRendering View 5.%d: Zoomed Detail for Tree %d -> %s...\n", k, k, file_zoom.c_str());
    RenderZoomView(leaves, k, line_alpha, file_zoom);
  }

  Printf("\nAll visualizations generated successfully!\n");
  return 0;
}
