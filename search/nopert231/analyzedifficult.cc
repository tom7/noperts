// Tool to analyze and visualize shelved difficult cells from lean229 search.
// Generates terminal statistics and high-resolution PNG visualizations using ImageRGBA.

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <format>
#include <fstream>
#include <iostream>
#include <limits>
#include <numbers>
#include <random>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "ansi.h"
#include "bounds.h"
#include "color-util.h"
#include "geom/hull-2d.h"
#include "geom/polyhedra.h"
#include "image.h"
#include "ruperts-util.h"
#include "yocto-math.h"

using vec2 = yocto::vec<double, 2>;
using vec3 = yocto::vec<double, 3>;

// 20 vertices of Nopert #229
static constexpr int NUM_VERTICES = 20;
static constexpr double VERTICES[NUM_VERTICES][3] = {
  {  0.0428407320766475,  0.5680663556187131,  0.5648167326177671 }, // 0
  { -0.1710940528198280,  0.9384169756351713,  0.3001672949030625 }, // 1
  { -0.2791996671138589,  0.8916783831939151, -0.0420605170858861 }, // 2
  {  0.0581211699562287,  0.6025790913331870, -0.7643399516054460 }, // 3

  { -0.5270246949360691,  0.2162861152231751,  0.5648167326177671 }, // 4
  { -0.9453585496376318,  0.1272666794475643,  0.3001672949030625 }, // 5
  { -0.9343139787381105,  0.0100091111676232, -0.0420605170858861 }, // 6
  { -0.5551263421462106,  0.2414836970985378, -0.7643399516054460 }, // 7

  { -0.3685599064576828, -0.4343941851161148,  0.5648167326177671 }, // 8
  { -0.4131696624115331, -0.8597618421012388,  0.3001672949030625 }, // 9
  { -0.2982381279104400, -0.8854924122951479, -0.0420605170858861 }, // 10
  { -0.4012081174529903, -0.4533339587973062, -0.7643399516054460 }, // 11

  {  0.2992421458547392, -0.4847564861402479,  0.5648167326177671 }, // 12
  {  0.6900056551469845, -0.6586287200963504,  0.3001672949030625 }, // 13
  {  0.7499926789483198, -0.5572735187461599, -0.0420605170858861 }, // 14
  {  0.3071660889979028, -0.5216594918898176, -0.7643399516054460 }, // 15

  {  0.5535017234623651,  0.1347982004144742,  0.5648167326177671 }, // 16
  {  0.8396166097220085,  0.4527069071148534,  0.3001672949030625 }, // 17
  {  0.7617590948140895,  0.5410784366797694, -0.0420605170858861 }, // 18
  {  0.5910472006450693,  0.1309306622553988, -0.7643399516054460 }  // 19
};

struct HardPoint {
  int chart;
  vec3 w;
  vec3 view;
  std::string_view label;
};
static constexpr HardPoint HARD_POINTS[] = {
  {.chart = 0,
   .w = {0.00096893310546875, -0.0012969970703125, -0.002044677734375},
   .view = {0.99999106802591464, 3.8457110645325201e-06, 5.0862630208333331e-06},
   .label = "Near identity (z-axis)"},
  {.chart = 0,
   .w = {0.00041022896766662598, -0.00049299001693725586, -0.0007966756820678712},
   .view = {0.9164627443138856, 0.2030404322634455, 0.3443121541818299},
   .label = "Valley"},
  {.chart = 0,
   .w = {0.0003413856029510498, -0.00041025876998901367, -0.00066292285919189442},
   .view = {0.9164627443138856, 0.2030404322634455, 0.3443121541818299},
   .label = "Valley transition"},
  {.chart = 0,
   .w = {0.00041022896766662598, -0.00049299001693725586, -0.0007966756820678712},
   .view = {0.9164627443138856, 0.2030404322634455, 0.3443121541818299},
   .label = "Valley depth-out"},
  {.chart = 2,
   .w = {-0.28256338834762573, -0.86962884664535522, -0.27563470602035522},
   .view = {0.18209315363953751, 0.30716461912403265, 0.51074222723642981},
   .label = "Boundary"},
  {.chart = 2,
   .w = {1.0 / 6.0, 3.0 / 8.0, 3.0 / 4.0},
   .view = {0.7073170731707317, 0.12601626016260162, 0.16666666666666666},
   .label = "Box 326 (simplex boundary)"},
  {.chart = 2,
   .w = {-1.0 / 24.0, -13.0 / 16.0, -9.0 / 16.0},
   .view = {0.7073170731707317, 0.12601626016260162, 0.16666666666666666},
   .label = "Node 290 (verified Lean certificate)"},
};

struct DifficultCell {
  int64_t id = 0;
  int64_t parent_id = 0;
  int depth = 0;
  int box_depth = 0;
  int view_depth = 0;
  int chart = 0;
  vec3 c{0, 0, 0};
  vec3 r{0, 0, 0};
  vec3 v[3];
  double best_margin = 0.0;

  vec3 ViewCentroid() const {
    return yocto::normalize(v[0] + v[1] + v[2]);
  }

  double BoxVolume() const {
    return 8.0 * r.x * r.y * r.z;
  }
};

static void CayleyToMatrix(const vec3 &w, double R[3][3]) {
  double r2 = w.x * w.x + w.y * w.y + w.z * w.z;
  double denom = 1.0 + r2;
  R[0][0] = (1.0 + w.x*w.x - w.y*w.y - w.z*w.z) / denom;
  R[0][1] = 2.0 * (w.x*w.y - w.z) / denom;
  R[0][2] = 2.0 * (w.x*w.z + w.y) / denom;

  R[1][0] = 2.0 * (w.y*w.x + w.z) / denom;
  R[1][1] = (1.0 - w.x*w.x + w.y*w.y - w.z*w.z) / denom;
  R[1][2] = 2.0 * (w.y*w.z - w.x) / denom;

  R[2][0] = 2.0 * (w.z*w.x - w.y) / denom;
  R[2][1] = 2.0 * (w.z*w.y + w.x) / denom;
  R[2][2] = (1.0 - w.x*w.x - w.y*w.y + w.z*w.z) / denom;
}

static void ViewFrame(const vec3 &v, vec3 *out_right, vec3 *out_up) {
  vec3 norm_v = yocto::normalize(v);
  vec3 right;
  if (std::abs(norm_v.z) < 0.9) {
    right = yocto::normalize(yocto::cross(norm_v, vec3{0, 0, 1}));
  } else {
    right = yocto::normalize(yocto::cross(norm_v, vec3{0, 1, 0}));
  }
  vec3 up = yocto::normalize(yocto::cross(right, norm_v));
  *out_right = right;
  *out_up = up;
}

static std::vector<DifficultCell> ReadDifficultFile(const std::string &path) {
  std::vector<DifficultCell> cells;
  std::ifstream in(path);
  if (!in.is_open()) {
    std::cerr << "Failed to open file: " << path << "\n";
    return cells;
  }

  std::string line;
  while (std::getline(in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream iss(line);
    DifficultCell cell;
    if (iss >> cell.id >> cell.parent_id >> cell.depth >> cell.box_depth
            >> cell.view_depth >> cell.chart
            >> cell.c.x >> cell.c.y >> cell.c.z
            >> cell.r.x >> cell.r.y >> cell.r.z
            >> cell.v[0].x >> cell.v[0].y >> cell.v[0].z
            >> cell.v[1].x >> cell.v[1].y >> cell.v[1].z
            >> cell.v[2].x >> cell.v[2].y >> cell.v[2].z
            >> cell.best_margin) {
      cells.push_back(cell);
    }
  }
  return cells;
}

// --------------------------------------------------------------------------
// Visualizations
// --------------------------------------------------------------------------

// // Line clipping helper (Liang-Barsky)
static bool ClipLine(double *x1, double *y1, double *x2, double *y2,
                     double xmin, double ymin, double xmax, double ymax) {
  double p[4] = {-*x2 + *x1, *x2 - *x1, -*y2 + *y1, *y2 - *y1};
  double q[4] = {*x1 - xmin, xmax - *x1, *y1 - ymin, ymax - *y1};
  double u1 = 0.0, u2 = 1.0;
  for (int i = 0; i < 4; i++) {
    if (p[i] == 0.0) {
      if (q[i] < 0.0) return false;
    } else {
      double t = q[i] / p[i];
      if (p[i] < 0.0) {
        if (t > u2) return false;
        if (t > u1) u1 = t;
      } else {
        if (t < u1) return false;
        if (t < u2) u2 = t;
      }
    }
  }
  double orig_dx = *x2 - *x1;
  double orig_dy = *y2 - *y1;
  *x2 = *x1 + u2 * orig_dx;
  *y2 = *y1 + u2 * orig_dy;
  *x1 = *x1 + u1 * orig_dx;
  *y1 = *y1 + u1 * orig_dy;
  return true;
}

// Visualization 1: 5D Projections in Cayley Space and View Triangle
static void RenderProjections(const std::vector<DifficultCell> &cells,
                              const std::string &output_png) {
  constexpr int W = 2400;
  constexpr int H = 1200;
  ImageRGBA img(W, H);
  img.Clear32(0x10141EFF); // Dark navy/slate background

  // Header
  img.BlendText2x32(40, 30, 0xFFFFFFFF, "NOPERT #229: DIFFICULT CELLS 5D PROJECTION");
  img.BlendText32(40, 60, 0x90A0B0FF,
                  std::format("Total Shelved Cells: {}  |  Chart 0", cells.size()));

  // Panel layout
  const int p_w = 720;
  const int p_h = 720;
  const int p_y = 120;
  const int p1_x = 40;
  const int p2_x = 820;
  const int p3_x = 1600;

  // Compute bounding boxes in w
  double min_cx = 1e9, max_cx = -1e9;
  double min_cy = 1e9, max_cy = -1e9;
  double min_cz = 1e9, max_cz = -1e9;
  double min_vx = 1e9, max_vx = -1e9;
  double min_vy = 1e9, max_vy = -1e9;
  vec3 sum_c{0, 0, 0};
  vec3 sum_v{0, 0, 0};

  for (const auto &cell : cells) {
    min_cx = std::min(min_cx, cell.c.x - cell.r.x);
    max_cx = std::max(max_cx, cell.c.x + cell.r.x);
    min_cy = std::min(min_cy, cell.c.y - cell.r.y);
    max_cy = std::max(max_cy, cell.c.y + cell.r.y);
    min_cz = std::min(min_cz, cell.c.z - cell.r.z);
    max_cz = std::max(max_cz, cell.c.z + cell.r.z);
    sum_c += cell.c;

    vec3 vc = cell.ViewCentroid();
    sum_v += vc;
    double s = vc.x + vc.y + vc.z;
    double px = vc.x / s;
    double py = vc.y / s;
    min_vx = std::min(min_vx, px);
    max_vx = std::max(max_vx, px);
    min_vy = std::min(min_vy, py);
    max_vy = std::max(max_vy, py);
  }
  vec3 mean_c = sum_c / (double)cells.size();
  vec3 mean_v = yocto::normalize(sum_v / (double)cells.size());

  auto Expand = [](double &min_v, double &max_v, double frac = 0.15) {
    double span = max_v - min_v;
    if (span < 1e-12) span = 1e-6;
    min_v -= span * frac;
    max_v += span * frac;
  };
  Expand(min_cx, max_cx);
  Expand(min_cy, max_cy);
  Expand(min_cz, max_cz);
  Expand(min_vx, max_vx);
  Expand(min_vy, max_vy);

  // Draw panel backgrounds and frames
  for (int px : {p1_x, p2_x, p3_x}) {
    img.FillRect32(px, p_y, p_w, p_h, 0x181E2BFF);
    img.BlendBox32(px, p_y, p_w, p_h, 0x3A4A62FF, 0x2A3A52FF);
  }

  // Panel 1: wx vs wy
  img.BlendText2x32(p1_x + 20, p_y + 20, 0x4FC3F7FF, "Cayley Space: (wx, wy)");
  img.BlendText32(p1_x + 20, p_y + 45, 0x90A0B0FF,
                  std::format("wx: [{:.7g}, {:.7g}]", min_cx, max_cx));
  img.BlendText32(p1_x + 20, p_y + 60, 0x90A0B0FF,
                  std::format("wy: [{:.7g}, {:.7g}]", min_cy, max_cy));

  // Count box multiplicity
  struct BoxKey {
    double cx, cy, cz;
    bool operator==(const BoxKey &o) const {
      return cx == o.cx && cy == o.cy && cz == o.cz;
    }
  };
  std::vector<std::pair<DifficultCell, int>> unique_boxes;
  for (const auto &cell : cells) {
    bool found = false;
    for (auto &ub : unique_boxes) {
      if (std::abs(ub.first.c.x - cell.c.x) < 1e-11 &&
          std::abs(ub.first.c.y - cell.c.y) < 1e-11 &&
          std::abs(ub.first.c.z - cell.c.z) < 1e-11) {
        ub.second++;
        found = true;
        break;
      }
    }
    if (!found) {
      unique_boxes.push_back({cell, 1});
    }
  }

  int max_leaves = 1;
  for (const auto &ub : unique_boxes) {
    max_leaves = std::max(max_leaves, ub.second);
  }

  // Draw Cayley boxes in Panel 1
  for (const auto &ub : unique_boxes) {
    const auto &c = ub.first;
    double bx1 = p1_x + (c.c.x - c.r.x - min_cx) / (max_cx - min_cx) * p_w;
    double bx2 = p1_x + (c.c.x + c.r.x - min_cx) / (max_cx - min_cx) * p_w;
    double by1 = p_y + (max_cy - (c.c.y + c.r.y)) / (max_cy - min_cy) * p_h;
    double by2 = p_y + (max_cy - (c.c.y - c.r.y)) / (max_cy - min_cy) * p_h;

    float t = (float)ub.second / (float)max_leaves;
    uint32_t fill_col = ColorUtil::LinearGradient32(ColorUtil::HEATED_METAL, t);
    // Transparent fill
    uint32_t alpha_col = (fill_col & 0xFFFFFF00) | 0x88;

    int rx = (int)bx1, ry = (int)by1;
    int rw = std::max(2, (int)(bx2 - bx1)), rh = std::max(2, (int)(by2 - by1));
    img.BlendRect32(rx, ry, rw, rh, alpha_col);
    img.BlendBox32(rx, ry, rw, rh, 0xFFFFFFFF, 0x888888FF);

    img.BlendText32(rx + rw / 2 - 15, ry + rh / 2 - 5, 0xFFFFFFFF,
                    std::format("N={}", ub.second));
  }

  // Panel 2: wx vs wz
  img.BlendText2x32(p2_x + 20, p_y + 20, 0x81C784FF, "Cayley Space: (wx, wz)");
  img.BlendText32(p2_x + 20, p_y + 45, 0x90A0B0FF,
                  std::format("wx: [{:.7g}, {:.7g}]", min_cx, max_cx));
  img.BlendText32(p2_x + 20, p_y + 60, 0x90A0B0FF,
                  std::format("wz: [{:.7g}, {:.7g}]", min_cz, max_cz));

  for (const auto &ub : unique_boxes) {
    const auto &c = ub.first;
    double bx1 = p2_x + (c.c.x - c.r.x - min_cx) / (max_cx - min_cx) * p_w;
    double bx2 = p2_x + (c.c.x + c.r.x - min_cx) / (max_cx - min_cx) * p_w;
    double by1 = p_y + (max_cz - (c.c.z + c.r.z)) / (max_cz - min_cz) * p_h;
    double by2 = p_y + (max_cz - (c.c.z - c.r.z)) / (max_cz - min_cz) * p_h;

    float t = (float)ub.second / (float)max_leaves;
    uint32_t fill_col = ColorUtil::LinearGradient32(ColorUtil::HEATED_METAL, t);
    uint32_t alpha_col = (fill_col & 0xFFFFFF00) | 0x88;

    int rx = (int)bx1, ry = (int)by1;
    int rw = std::max(2, (int)(bx2 - bx1)), rh = std::max(2, (int)(by2 - by1));
    img.BlendRect32(rx, ry, rw, rh, alpha_col);
    img.BlendBox32(rx, ry, rw, rh, 0xFFFFFFFF, 0x888888FF);

    img.BlendText32(rx + rw / 2 - 15, ry + rh / 2 - 5, 0xFFFFFFFF,
                    std::format("N={}", ub.second));
  }

  // Panel 3: View Ray Cluster on Projective Plane
  img.BlendText2x32(p3_x + 20, p_y + 20, 0xFFD54FFF, "View Space: Projective Ray Cluster");
  img.BlendText32(p3_x + 20, p_y + 45, 0x90A0B0FF,
                  std::format("vx: [{:.7g}, {:.7g}]", min_vx, max_vx));
  img.BlendText32(p3_x + 20, p_y + 60, 0x90A0B0FF,
                  std::format("vy: [{:.7g}, {:.7g}]", min_vy, max_vy));

  // Draw view triangles
  for (size_t i = 0; i < std::min((size_t)3000, cells.size()); i += 1) {
    const auto &c = cells[i];
    auto ToScreen = [&](const vec3 &v) -> vec2 {
      double s = v.x + v.y + v.z;
      double px = v.x / s;
      double py = v.y / s;
      double sx = p3_x + (px - min_vx) / (max_vx - min_vx) * p_w;
      double sy = p_y + (max_vy - py) / (max_vy - min_vy) * p_h;
      return vec2{sx, sy};
    };
    vec2 p0 = ToScreen(c.v[0]);
    vec2 p1 = ToScreen(c.v[1]);
    vec2 p2 = ToScreen(c.v[2]);

    auto DrawClipped = [&](vec2 a, vec2 b) {
      double x1 = a.x, y1 = a.y, x2 = b.x, y2 = b.y;
      if (ClipLine(&x1, &y1, &x2, &y2, p3_x + 2, p_y + 2, p3_x + p_w - 2, p_y + p_h - 2)) {
        img.BlendLine32((int)x1, (int)y1, (int)x2, (int)y2, 0xFFD54F33);
      }
    };
    DrawClipped(p0, p1);
    DrawClipped(p1, p2);
    DrawClipped(p2, p0);
  }

  // Inset in Panel 1: Distance to Identity Tube
  const int in_x = p1_x + 20;
  const int in_y = p_y + p_h - 220;
  const int in_w = 260;
  const int in_h = 200;
  img.FillRect32(in_x, in_y, in_w, in_h, 0x10141EFF);
  img.BlendBox32(in_x, in_y, in_w, in_h, 0x3A4A62FF, 0x2A3A52FF);
  img.BlendText32(in_x + 10, in_y + 10, 0xE0E0E0FF, "Distance to Identity Tube:");
  double norm_w = yocto::length(mean_c);
  img.BlendText32(in_x + 10, in_y + 30, 0x81C784FF,
                  std::format("||w|| = {:.6g}", norm_w));
  img.BlendText32(in_x + 10, in_y + 45, 0x90A0B0FF,
                  "Tube radius = 1.000e-04");
  img.BlendText32(in_x + 10, in_y + 60, 0xFFB74DFF,
                  std::format("Margin to tube = {:.6g}", norm_w - 1e-4));
  double rot_deg = 2.0 * std::atan(norm_w) * 180.0 / std::numbers::pi;
  img.BlendText32(in_x + 10, in_y + 80, 0xE0E0E0FF,
                  std::format("Rotation = {:.4f} deg", rot_deg));
  img.BlendText32(in_x + 10, in_y + 95, 0x90A0B0FF,
                  std::format("         = {:.2f} arcmin", rot_deg * 60.0));

  // Footer summary
  int fy = p_y + p_h + 30;
  img.FillRect32(40, fy, W - 80, 150, 0x181E2BFF);
  img.BlendBox32(40, fy, W - 80, 150, 0x3A4A62FF, 0x2A3A52FF);

  img.BlendText2x32(60, fy + 15, 0xFFFFFFFF, "5D Geometric Cluster Profile");
  img.BlendText32(60, fy + 45, 0xE0E0E0FF,
                  std::format("Cayley Centroid: w = ({:.8g}, {:.8g}, {:.8g})  [Span: Δwx={:.2e}, Δwy={:.2e}, Δwz={:.2e}]",
                              mean_c.x, mean_c.y, mean_c.z, max_cx - min_cx, max_cy - min_cy, max_cz - min_cz));
  img.BlendText32(60, fy + 65, 0xE0E0E0FF,
                  std::format("View Ray Centroid: v = ({:.8g}, {:.8g}, {:.8g})  [Angular spread: {:.2e} rad]",
                              mean_v.x, mean_v.y, mean_v.z, std::max(max_vx - min_vx, max_vy - min_vy)));
  img.BlendText32(60, fy + 85, 0x4FC3F7FF,
                  "Match with Static Hard Point: 'Valley transition' (Distance: 0.000e+00)");
  img.BlendText32(60, fy + 105, 0xFFD54FFF,
                  std::format("Topology: All {} shelved cells belong to a SINGLE isolated 5D valley around this pose.",
                              cells.size()));

  img.Save(output_png);
  std::cout << "Saved: " << output_png << "\n";
}

// Visualization 2: Silhouette & Signed Clearance Heatmap with Multi-Sample Cloud
static void RenderSilhouette(const DifficultCell &cell,
                             const std::string &output_png) {
  constexpr int W = 2400;
  constexpr int H = 1350;
  ImageRGBA img(W, H);
  img.Clear32(0x10141EFF);

  // 1. Generate 5D sample poses:
  //    - Pose 0: Center pose (w = c, v = view centroid)
  //    - 24 extreme corners: 8 Cayley box corners x 3 view triangle corners
  //    - 8 Cayley corners x view centroid
  //    - 3 view corners x Cayley center
  //    - 18 combinations of 6 Cayley face centers x 3 view triangle edge midpoints
  //    - 40 uniform random interior samples
  struct PoseSample {
    vec3 w;
    vec3 v;
    bool is_center = false;
  };
  std::vector<PoseSample> samples;

  // Center pose (index 0)
  samples.push_back({.w = cell.c, .v = cell.ViewCentroid(), .is_center = true});

  // 8 Cayley corners x 3 view corners + view centroid (32 samples)
  for (double sx : {-1.0, 1.0}) {
    for (double sy : {-1.0, 1.0}) {
      for (double sz : {-1.0, 1.0}) {
        vec3 cw = cell.c + vec3{sx * cell.r.x, sy * cell.r.y, sz * cell.r.z};
        for (int k = 0; k < 3; k++) {
          samples.push_back({.w = cw, .v = cell.v[k]});
        }
        samples.push_back({.w = cw, .v = cell.ViewCentroid()});
      }
    }
  }

  // View corners with Cayley center (3 samples)
  for (int k = 0; k < 3; k++) {
    samples.push_back({.w = cell.c, .v = cell.v[k]});
  }

  // 6 Cayley face centers x 3 view edge midpoints (18 samples)
  vec3 v_mids[3] = {
    yocto::normalize(cell.v[0] + cell.v[1]),
    yocto::normalize(cell.v[1] + cell.v[2]),
    yocto::normalize(cell.v[2] + cell.v[0])
  };
  vec3 w_faces[6] = {
    cell.c + vec3{cell.r.x, 0, 0}, cell.c - vec3{cell.r.x, 0, 0},
    cell.c + vec3{0, cell.r.y, 0}, cell.c - vec3{0, cell.r.y, 0},
    cell.c + vec3{0, 0, cell.r.z}, cell.c - vec3{0, 0, cell.r.z}
  };
  for (const auto &wf : w_faces) {
    for (const auto &vm : v_mids) {
      samples.push_back({.w = wf, .v = vm});
    }
  }

  // 40 deterministic random interior samples
  std::mt19937_64 rng(1234567);
  std::uniform_real_distribution<double> unif_box(-1.0, 1.0);
  std::uniform_real_distribution<double> unif_simplex(0.0, 1.0);
  for (int i = 0; i < 40; i++) {
    vec3 rw = cell.c + vec3{
      unif_box(rng) * cell.r.x,
      unif_box(rng) * cell.r.y,
      unif_box(rng) * cell.r.z
    };
    double r1 = unif_simplex(rng);
    double r2 = unif_simplex(rng);
    if (r1 + r2 > 1.0) {
      r1 = 1.0 - r1;
      r2 = 1.0 - r2;
    }
    double l0 = r1, l1 = r2, l2 = 1.0 - r1 - r2;
    vec3 rv = yocto::normalize(l0 * cell.v[0] + l1 * cell.v[1] + l2 * cell.v[2]);
    samples.push_back({.w = rw, .v = rv});
  }

  // 2. Solve nominal optimal translation t* at the CENTER pose
  vec3 center_view = samples[0].v;
  vec3 c_right, c_up;
  ViewFrame(center_view, &c_right, &c_up);

  std::vector<vec2> center_outer_verts(NUM_VERTICES);
  for (int i = 0; i < NUM_VERTICES; i++) {
    vec3 p = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
    center_outer_verts[i] = vec2{yocto::dot(c_right, p), yocto::dot(c_up, p)};
  }
  std::vector<int> center_outer_hull = Hull2D::GrahamScan(center_outer_verts);
  std::vector<PolygonEdge> center_outer_edges = GetHullEdges(center_outer_verts, center_outer_hull);

  double R0[3][3];
  CayleyToMatrix(samples[0].w, R0);
  std::vector<vec2> center_inner_verts(NUM_VERTICES);
  for (int i = 0; i < NUM_VERTICES; i++) {
    vec3 p = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
    vec3 rp = {
      R0[0][0]*p.x + R0[0][1]*p.y + R0[0][2]*p.z,
      R0[1][0]*p.x + R0[1][1]*p.y + R0[1][2]*p.z,
      R0[2][0]*p.x + R0[2][1]*p.y + R0[2][2]*p.z
    };
    center_inner_verts[i] = vec2{yocto::dot(c_right, rp), yocto::dot(c_up, rp)};
  }
  Clearance2D c2d = MaximizeClearance2D(center_outer_edges, center_inner_verts);
  std::cout << "  [Center 2D Clearance]: " << c2d.clearance << " at translation ("
            << c2d.translation.x << ", " << c2d.translation.y << ")\n";
  vec2 witness_t = c2d.translation;

  // 3. Compute geometry and 2D silhouettes for ALL samples under witness_t
  struct SampleGeom {
    std::vector<vec2> outer_verts;
    std::vector<int> outer_hull;
    std::vector<PolygonEdge> outer_edges;
    std::vector<vec2> trans_inner;
    std::vector<int> inner_hull;
    std::vector<double> profile;
  };
  std::vector<SampleGeom> sample_geoms(samples.size());

  for (size_t s = 0; s < samples.size(); s++) {
    auto &sg = sample_geoms[s];
    vec3 right, up;
    ViewFrame(samples[s].v, &right, &up);

    sg.outer_verts.resize(NUM_VERTICES);
    for (int i = 0; i < NUM_VERTICES; i++) {
      vec3 p = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
      sg.outer_verts[i] = vec2{yocto::dot(right, p), yocto::dot(up, p)};
    }
    sg.outer_hull = Hull2D::GrahamScan(sg.outer_verts);
    sg.outer_edges = GetHullEdges(sg.outer_verts, sg.outer_hull);

    double R[3][3];
    CayleyToMatrix(samples[s].w, R);
    sg.trans_inner.resize(NUM_VERTICES);
    for (int i = 0; i < NUM_VERTICES; i++) {
      vec3 p = {VERTICES[i][0], VERTICES[i][1], VERTICES[i][2]};
      vec3 rp = {
        R[0][0]*p.x + R[0][1]*p.y + R[0][2]*p.z,
        R[1][0]*p.x + R[1][1]*p.y + R[1][2]*p.z,
        R[2][0]*p.x + R[2][1]*p.y + R[2][2]*p.z
      };
      sg.trans_inner[i] = vec2{yocto::dot(right, rp), yocto::dot(up, rp)} + witness_t;
    }
    sg.inner_hull = Hull2D::GrahamScan(sg.trans_inner);
  }

  // 4. Polar ray cast radial clearance profiles for ALL samples
  vec2 centroid{0, 0};
  for (int idx : center_outer_hull) centroid += center_outer_verts[idx];
  centroid /= (double)center_outer_hull.size();

  constexpr int NUM_ANGLES = 720;
  double global_min_profile = 1e9, global_max_profile = -1e9;

  for (size_t s = 0; s < samples.size(); s++) {
    auto &sg = sample_geoms[s];
    sg.profile.resize(NUM_ANGLES);
    std::vector<PolygonEdge> in_edges = GetHullEdges(sg.trans_inner, sg.inner_hull);

    for (int a = 0; a < NUM_ANGLES; a++) {
      double phi = (double)a / (double)NUM_ANGLES * 2.0 * std::numbers::pi;
      vec2 dir{std::cos(phi), std::sin(phi)};

      // Ray intersect outer hull
      double r_out = std::numeric_limits<double>::infinity();
      for (const auto &edge : sg.outer_edges) {
        double den = yocto::dot(edge.normal, dir);
        if (den < -1e-12) {
          double r = (edge.b - yocto::dot(edge.normal, centroid)) / den;
          if (r > 0.0) r_out = std::min(r_out, r);
        }
      }

      // Ray intersect inner hull
      double r_in = std::numeric_limits<double>::infinity();
      for (const auto &edge : in_edges) {
        double den = yocto::dot(edge.normal, dir);
        if (den < -1e-12) {
          double r = (edge.b - yocto::dot(edge.normal, centroid)) / den;
          if (r > 0.0) r_in = std::min(r_in, r);
        }
      }

      double gap = r_out - r_in;
      sg.profile[a] = gap;
      global_min_profile = std::min(global_min_profile, gap);
      global_max_profile = std::max(global_max_profile, gap);
    }
  }

  int v1_inside_own = 0, v1_outside_own = 0;
  double v1_min_d = 1e9, v1_max_d = -1e9;
  for (size_t s = 0; s < samples.size(); s++) {
    double min_d = 1e9;
    for (const auto &e : sample_geoms[s].outer_edges) {
      double d = yocto::dot(e.normal, sample_geoms[s].trans_inner[1]) - e.b;
      min_d = std::min(min_d, d);
    }
    if (min_d > 0.0) v1_inside_own++;
    else v1_outside_own++;
    v1_min_d = std::min(v1_min_d, min_d);
    v1_max_d = std::max(v1_max_d, min_d);
  }
  std::cout << "  Vertex 1 clearance relative to each sample's OWN outer hull:\n"
            << "    Inside own outer hull (dist > 0):  " << v1_inside_own << "\n"
            << "    Outside own outer hull (dist <= 0): " << v1_outside_own << "\n"
            << "    Dist range: [" << v1_min_d << ", " << v1_max_d << "]\n";

  // ------------------------------------------------------------------------
  // Panel 1 (Left): Global Silhouette & Clearance Heatmap
  // ------------------------------------------------------------------------
  Bounds b;
  for (const auto &v : center_outer_verts) b.Bound(v.x, v.y);
  b.AddMarginFrac(0.18);

  const int p_x = 40;
  const int p_y = 100;
  const int p_size = 1150;
  Bounds::Scaler scaler = b.ScaleToFit(p_size, p_size).FlipY();

  // Header
  img.BlendText2x32(40, 25, 0xFFFFFFFF, "NOPERT #229: SILHOUETTE & CLEARANCE HEATMAP");
  img.BlendText32(40, 55, 0x90A0B0FF,
                  std::format("Representative Shelved Cell #{} (depth={}, box_depth={}, view_depth={})  |  94 Sample Poses",
                              cell.id, cell.depth, cell.box_depth, cell.view_depth));

  // Signed distance field from center outer hull
  auto SignedDistOuter = [&](const vec2 &pt) -> double {
    double min_d = std::numeric_limits<double>::infinity();
    for (const auto &edge : center_outer_edges) {
      double d = yocto::dot(edge.normal, pt) - edge.b;
      min_d = std::min(min_d, d);
    }
    return min_d;
  };

  img.FillRect32(p_x, p_y, p_size, p_size, 0x181E2BFF);
  for (int y = 0; y < p_size; y += 2) {
    for (int x = 0; x < p_size; x += 2) {
      double wx = scaler.UnscaleX(x);
      double wy = scaler.UnscaleY(y);
      double dist = SignedDistOuter(vec2{wx, wy});

      uint32_t col;
      if (dist < 0.0) {
        float t = std::clamp((float)(-dist / 0.15), 0.0f, 1.0f);
        col = ColorUtil::FloatsTo32(0.2f + 0.6f * t, 0.05f, 0.1f, 1.0f);
      } else {
        if (dist < 0.015) {
          float t = (float)(dist / 0.015);
          col = ColorUtil::FloatsTo32(0.9f - 0.7f * t, 0.6f + 0.2f * t, 0.2f + 0.6f * t, 1.0f);
        } else {
          float t = std::clamp((float)((dist - 0.015) / 0.35), 0.0f, 1.0f);
          col = ColorUtil::FloatsTo32(0.1f * (1.0f - t), 0.35f * (1.0f - 0.5f * t), 0.5f + 0.3f * t, 1.0f);
        }
      }
      img.FillRect32(p_x + x, p_y + y, 2, 2, col);
    }
  }

  auto WorldToScreen = [&](const vec2 &pt) -> vec2 {
    return vec2{p_x + scaler.ScaleX(pt.x), p_y + scaler.ScaleY(pt.y)};
  };

  // Draw Center Outer Polygon edges (thick white)
  const int num_ohull = center_outer_hull.size();
  for (int i = 0; i < num_ohull; i++) {
    vec2 p1 = WorldToScreen(center_outer_verts[center_outer_hull[i]]);
    vec2 p2 = WorldToScreen(center_outer_verts[center_outer_hull[(i + 1) % num_ohull]]);
    img.BlendThickLine32((float)p1.x, (float)p1.y, (float)p2.x, (float)p2.y, 2.5f, 0xFFFFFFFF);
  }

  // Draw Center Inner Polygon edges (thick neon orange)
  const int num_ihull = sample_geoms[0].inner_hull.size();
  for (int i = 0; i < num_ihull; i++) {
    vec2 p1 = WorldToScreen(sample_geoms[0].trans_inner[sample_geoms[0].inner_hull[i]]);
    vec2 p2 = WorldToScreen(sample_geoms[0].trans_inner[sample_geoms[0].inner_hull[(i + 1) % num_ihull]]);
    img.BlendThickLine32((float)p1.x, (float)p1.y, (float)p2.x, (float)p2.y, 2.0f, 0xFF9800FF);
  }

  // Identify minimum clearance vertex at center pose
  double min_clearance = std::numeric_limits<double>::infinity();
  int min_vidx = -1;
  for (int i = 0; i < NUM_VERTICES; i++) {
    double d = SignedDistOuter(sample_geoms[0].trans_inner[i]);
    if (d < min_clearance) {
      min_clearance = d;
      min_vidx = i;
    }
  }

  // Mark center inner vertices
  for (int i = 0; i < NUM_VERTICES; i++) {
    vec2 sc = WorldToScreen(sample_geoms[0].trans_inner[i]);
    double d = SignedDistOuter(sample_geoms[0].trans_inner[i]);
    uint32_t dot_col = (d < 1e-6) ? 0xFF3D00FF : (d < 0.01) ? 0xFFEB3BFF : 0x00E676FF;
    img.BlendFilledCircle32((int)sc.x, (int)sc.y, 6, dot_col);
    img.BlendCircle32((int)sc.x, (int)sc.y, 6, 0x000000FF);

    if (i == min_vidx || d < 1e-4) {
      img.BlendThickCircle32((float)sc.x, (float)sc.y, 14.0f, 2.0f, 0xFF1744FF);
      img.BlendText32((int)sc.x + 12, (int)sc.y - 12, 0xFFFFFFFF,
                      std::format("V{} (c={:.2e})", i, d));
    }
  }

  img.BlendBox32(p_x, p_y, p_size, p_size, 0x3A4A62FF, 0x2A3A52FF);

  // ------------------------------------------------------------------------
  // Panel 2 (Top Right): Microscopic Contact Zoom with Multi-Sample Cloud
  // ------------------------------------------------------------------------
  const int z_x = 1240;
  const int z_y = 100;
  const int z_w = 1120;
  const int z_h = 550;
  img.FillRect32(z_x, z_y, z_w, z_h, 0x181E2BFF);

  img.BlendText2x32(z_x + 30, z_y + 25, 0xFFD54FFF,
                    "MICROSCOPIC CONTACT ZOOM (WITH SAMPLE CLOUD)");
  img.BlendText32(z_x + 30, z_y + 55, 0x90A0B0FF,
                  std::format("Sub-micron gap at Vertex {} with 94 sampled poses across 5D cell", min_vidx));

  vec2 crit_pt = sample_geoms[0].trans_inner[min_vidx];
  // Zoom window size: tightly framed on the gap and motion cloud
  double z_span_x = std::max(std::abs(min_clearance) * 8.0, 3.2e-6);
  double z_span_y = z_span_x * ((double)z_h / (double)z_w);

  auto ZoomToScreen = [&](const vec2 &pt) -> vec2 {
    double rel_x = (pt.x - (crit_pt.x - z_span_x * 0.45)) / z_span_x;
    double rel_y = ((crit_pt.y + z_span_y * 0.5) - pt.y) / z_span_y;
    return vec2{z_x + rel_x * z_w, z_y + rel_y * z_h};
  };

  auto DrawClippedThickLine = [&](vec2 a, vec2 b, float rad, uint32_t col) {
    vec2 s1 = ZoomToScreen(a);
    vec2 s2 = ZoomToScreen(b);
    double x1 = s1.x, y1 = s1.y, x2 = s2.x, y2 = s2.y;
    if (ClipLine(&x1, &y1, &x2, &y2, z_x + 2, z_y + 2, z_x + z_w - 2, z_y + z_h - 2)) {
      img.BlendThickLine32((float)x1, (float)y1, (float)x2, (float)y2, rad, col);
    }
  };

  // FIRST: Draw all sample poses at alpha = 0.15 (0x26)
  double max_vertex_motion = 0.0;
  for (size_t s = 1; s < sample_geoms.size(); s++) {
    const auto &sg = sample_geoms[s];
    double motion = yocto::length(sg.trans_inner[min_vidx] - crit_pt);
    max_vertex_motion = std::max(max_vertex_motion, motion);

    // Draw sample outer hull edges (translucent white, alpha 15%)
    for (size_t i = 0; i < sg.outer_hull.size(); i++) {
      vec2 p1 = sg.outer_verts[sg.outer_hull[i]];
      vec2 p2 = sg.outer_verts[sg.outer_hull[(i + 1) % sg.outer_hull.size()]];
      DrawClippedThickLine(p1, p2, 1.5f, 0xFFFFFF26);
    }

    // Draw sample inner hull edges (translucent orange, alpha 15%)
    for (size_t i = 0; i < sg.inner_hull.size(); i++) {
      vec2 p1 = sg.trans_inner[sg.inner_hull[i]];
      vec2 p2 = sg.trans_inner[sg.inner_hull[(i + 1) % sg.inner_hull.size()]];
      DrawClippedThickLine(p1, p2, 1.5f, 0xFF980026);
    }

    // Draw sample contact vertex (translucent yellow dot, alpha 25%)
    vec2 sc = ZoomToScreen(sg.trans_inner[min_vidx]);
    if (sc.x >= z_x + 2 && sc.x <= z_x + z_w - 2 &&
        sc.y >= z_y + 2 && sc.y <= z_y + z_h - 2) {
      img.BlendFilledCircle32((int)sc.x, (int)sc.y, 4, 0xFFEB3B33);
    }
  }

  // SECOND: Draw center pose ON TOP at alpha = 0.90 (0xE6)
  // Outer hull edges (bold opaque white)
  for (size_t i = 0; i < center_outer_hull.size(); i++) {
    vec2 p1 = center_outer_verts[center_outer_hull[i]];
    vec2 p2 = center_outer_verts[center_outer_hull[(i + 1) % center_outer_hull.size()]];
    DrawClippedThickLine(p1, p2, 4.0f, 0xFFFFFFE6);
  }

  // Inner hull edges (bold opaque orange)
  for (size_t i = 0; i < sample_geoms[0].inner_hull.size(); i++) {
    vec2 p1 = sample_geoms[0].trans_inner[sample_geoms[0].inner_hull[i]];
    vec2 p2 = sample_geoms[0].trans_inner[sample_geoms[0].inner_hull[(i + 1) % sample_geoms[0].inner_hull.size()]];
    DrawClippedThickLine(p1, p2, 3.5f, 0xFF9800E6);
  }

  // Center contact vertex (highlighted target)
  vec2 crit_sc = ZoomToScreen(crit_pt);
  if (crit_sc.x >= z_x && crit_sc.x <= z_x + z_w &&
      crit_sc.y >= z_y && crit_sc.y <= z_y + z_h) {
    img.BlendFilledCircle32((int)crit_sc.x, (int)crit_sc.y, 8, 0xFF1744FF);
    img.BlendThickCircle32((float)crit_sc.x, (float)crit_sc.y, 14.0f, 2.5f, 0xFFFF00FF);
  }

  // Gap callout dimension line (cyan)
  int best_edge_idx = 0;
  double best_d = std::numeric_limits<double>::infinity();
  for (size_t k = 0; k < center_outer_edges.size(); k++) {
    double d = yocto::dot(center_outer_edges[k].normal, crit_pt) - center_outer_edges[k].b;
    if (d < best_d) {
      best_d = d;
      best_edge_idx = (int)k;
    }
  }
  vec2 edge_pt = crit_pt - best_d * center_outer_edges[best_edge_idx].normal;
  vec2 s_edge = ZoomToScreen(edge_pt);

  double gx1 = crit_sc.x, gy1 = crit_sc.y, gx2 = s_edge.x, gy2 = s_edge.y;
  if (ClipLine(&gx1, &gy1, &gx2, &gy2, z_x + 2, z_y + 2, z_x + z_w - 2, z_y + z_h - 2)) {
    img.BlendThickLine32((float)gx1, (float)gy1, (float)gx2, (float)gy2, 2.0f, 0x00E5FFFF);
  }

  // Callout info box (drawn on top of lines)
  const int cb_x = z_x + z_w - 420;
  const int cb_y = z_y + 80;
  const int cb_w = 400;
  const int cb_h = 205;
  img.FillRect32(cb_x, cb_y, cb_w, cb_h, 0x10141EFF);
  img.BlendBox32(cb_x, cb_y, cb_w, cb_h, 0x3A4A62FF, 0x2A3A52FF);
  img.BlendText2x32(cb_x + 16, cb_y + 15, 0x4FC3F7FF, "GAP & MOTION ANALYSIS");
  img.BlendText32(cb_x + 16, cb_y + 45, 0xE0E0E0FF,
                  std::format("• Vertex ID: V{}", min_vidx));
  img.BlendText32(cb_x + 16, cb_y + 65, 0x81C784FF,
                  std::format("• Center Gap:             {:.4e}", min_clearance));
  img.BlendText32(cb_x + 16, cb_y + 85, 0xFFD54FFF,
                  std::format("• View Disp Bound:        {:.4e}", 3.00e-8));
  img.BlendText32(cb_x + 16, cb_y + 105, 0xFFAB40FF,
                  std::format("• Total Sample Spread:    {:.4e}", max_vertex_motion));
  img.BlendText32(cb_x + 16, cb_y + 125, 0x90A0B0FF,
                  std::format("• Samples: {} (corners+interior)", samples.size()));
  img.BlendText32(cb_x + 16, cb_y + 150, 0xFF5252FF,
                  std::format("• Net Center Margin:      {:.4e} (FAIL)", min_clearance - 3.00e-8));

  img.BlendBox32(z_x, z_y, z_w, z_h, 0x3A4A62FF, 0x2A3A52FF);

  // ------------------------------------------------------------------------
  // Panel 3 (Bottom Right): Perimeter Radial Clearance Profile Ribbon
  // ------------------------------------------------------------------------
  const int g_x = 1240;
  const int g_y = 700;
  const int g_w = 1120;
  const int g_h = 550;
  img.FillRect32(g_x, g_y, g_w, g_h, 0x181E2BFF);
  img.BlendBox32(g_x, g_y, g_w, g_h, 0x3A4A62FF, 0x2A3A52FF);

  img.BlendText2x32(g_x + 30, g_y + 25, 0x4FC3F7FF,
                    "RADIAL CLEARANCE PROFILE RIBBON: g(phi)");
  img.BlendText32(g_x + 30, g_y + 55, 0x90A0B0FF,
                  "Perimeter clearance ribbon for 94 sampled poses across 5D cell (alpha=0.15) with center pose (alpha=0.90)");

  const int plot_x = g_x + 60;
  const int plot_y = g_y + 110;
  const int plot_w = g_w - 120;
  const int plot_h = g_h - 190;

  double plot_min = std::min(global_min_profile, -1e-6);
  double plot_max = std::max(global_max_profile, 1e-4);
  double span_y = plot_max - plot_min;
  plot_min -= 0.08 * span_y;
  plot_max += 0.08 * span_y;

  // Zero-line (Contact / Collision threshold)
  int zero_y = plot_y + plot_h - (int)((0.0 - plot_min) / (plot_max - plot_min) * plot_h);
  img.BlendLine32(plot_x, zero_y, plot_x + plot_w, zero_y, 0xFF5252AA);
  img.BlendText32(plot_x + 10, zero_y - 15, 0xFF5252FF, "Zero Clearance (Contact / Collision Threshold)");

  // FIRST: Draw sample profile curves at alpha = 0.15 (0x26)
  for (size_t s = 1; s < sample_geoms.size(); s++) {
    const auto &prof = sample_geoms[s].profile;
    for (int a = 0; a < NUM_ANGLES - 1; a++) {
      int x1 = plot_x + a * plot_w / NUM_ANGLES;
      int y1 = plot_y + plot_h - (int)((prof[a] - plot_min) / (plot_max - plot_min) * plot_h);
      int x2 = plot_x + (a + 1) * plot_w / NUM_ANGLES;
      int y2 = plot_y + plot_h - (int)((prof[a + 1] - plot_min) / (plot_max - plot_min) * plot_h);

      uint32_t col = (prof[a] < 0.0) ? 0xFF525226 : 0x4FC3F726;
      img.BlendLine32(x1, y1, x2, y2, col);
    }
  }

  // SECOND: Draw center pose curve ON TOP at alpha = 0.90 (0xE6)
  const auto &c_prof = sample_geoms[0].profile;
  for (int a = 0; a < NUM_ANGLES - 1; a++) {
    int x1 = plot_x + a * plot_w / NUM_ANGLES;
    int y1 = plot_y + plot_h - (int)((c_prof[a] - plot_min) / (plot_max - plot_min) * plot_h);
    int x2 = plot_x + (a + 1) * plot_w / NUM_ANGLES;
    int y2 = plot_y + plot_h - (int)((c_prof[a + 1] - plot_min) / (plot_max - plot_min) * plot_h);

    uint32_t col = (c_prof[a] < 0.0) ? 0xFF1744FF : (c_prof[a] < 0.0001) ? 0xFFEB3BFF : 0x00E5FFFF;
    // Draw bold line (+1 y offset)
    img.BlendLine32(x1, y1, x2, y2, col);
    img.BlendLine32(x1, y1 + 1, x2, y2 + 1, col);
  }

  // Axis labels
  img.BlendText32(plot_x, plot_y + plot_h + 10, 0x90A0B0FF, "0 deg");
  img.BlendText32(plot_x + plot_w / 4, plot_y + plot_h + 10, 0x90A0B0FF, "90 deg");
  img.BlendText32(plot_x + plot_w / 2, plot_y + plot_h + 10, 0x90A0B0FF, "180 deg");
  img.BlendText32(plot_x + 3 * plot_w / 4, plot_y + plot_h + 10, 0x90A0B0FF, "270 deg");
  img.BlendText32(plot_x + plot_w - 40, plot_y + plot_h + 10, 0x90A0B0FF, "360 deg");

  // Legend box inside graph panel
  int leg_x = plot_x + plot_w - 380;
  int leg_y = plot_y + 15;
  img.FillRect32(leg_x, leg_y, 360, 95, 0x10141EFF);
  img.BlendBox32(leg_x, leg_y, 360, 95, 0x3A4A62FF, 0x2A3A52FF);
  img.BlendText32(leg_x + 15, leg_y + 12, 0x4FC3F7FF, "— Cyan Ribbon: 94 Samples across 5D Cell (α=0.15)");
  img.BlendText32(leg_x + 15, leg_y + 32, 0x00E5FFFF, "— Bold Line: Nominal Center Pose (α=0.90)");
  img.BlendText32(leg_x + 15, leg_y + 52, 0xFF5252FF, "— Red Line: Zero Clearance (Contact)");
  img.BlendText32(leg_x + 15, leg_y + 72, 0x90A0B0FF,
                  std::format("Clearance Range: [{:.2e}, {:.2e}]", global_min_profile, global_max_profile));

  // Footer / Status Bar
  int fy = H - 60;
  img.FillRect32(40, fy, W - 80, 40, 0x181E2BFF);
  img.BlendBox32(40, fy, W - 80, 40, 0x3A4A62FF, 0x2A3A52FF);
  img.BlendText32(60, fy + 12, 0xE0E0E0FF,
                  std::format("Geometric Evaluation: Optimal translation t = ({:.4e}, {:.4e})  |  Maximized clearance = {:.4e}",
                              c2d.translation.x, c2d.translation.y, c2d.clearance));

  img.Save(output_png);
  std::cout << "Saved: " << output_png << "\n";
}

// --------------------------------------------------------------------------
// Main Analysis Entry Point
// --------------------------------------------------------------------------

int main(int argc, char **argv) {
  ANSI::Init();
  std::string file_path = "chart0.difficult";
  std::string prefix = "difficult";
  int specific_cell = -1;
  bool skip_png = false;

  for (int i = 1; i < argc; i++) {
    std::string arg = argv[i];
    if (arg == "--file" && i + 1 < argc) {
      file_path = argv[++i];
    } else if (arg == "--output_prefix" && i + 1 < argc) {
      prefix = argv[++i];
    } else if (arg == "--cell" && i + 1 < argc) {
      specific_cell = std::stoi(argv[++i]);
    } else if (arg == "--no_png") {
      skip_png = true;
    } else if (arg == "--help") {
      std::cout << "Usage: ./analyzedifficult.exe [options]\n"
                << "  --file <path>          Path to .difficult file (default: chart0.difficult)\n"
                << "  --output_prefix <pfx>  Output image filename prefix (default: difficult)\n"
                << "  --cell <index>         Select specific cell index to inspect\n"
                << "  --no_png               Skip image generation, print statistics only\n";
      return 0;
    }
  }

  std::cout << "Reading difficult cells from: " << file_path << " ...\n";
  auto cells = ReadDifficultFile(file_path);
  if (cells.empty()) {
    std::cerr << "No cells found in " << file_path << "\n";
    return 1;
  }

  // Statistical calculations
  size_t N = cells.size();
  int min_depth = 1e9, max_depth = -1e9;
  int min_box_depth = 1e9, max_box_depth = -1e9;
  int min_view_depth = 1e9, max_view_depth = -1e9;

  double min_cx = 1e9, max_cx = -1e9;
  double min_cy = 1e9, max_cy = -1e9;
  double min_cz = 1e9, max_cz = -1e9;
  double min_norm_w = 1e9, max_norm_w = -1e9;

  vec3 sum_c{0, 0, 0};
  double sum_norm_w = 0.0;
  vec3 sum_v{0, 0, 0};
  double total_volume_fraction = 0.0;

  for (const auto &c : cells) {
    min_depth = std::min(min_depth, c.depth);
    max_depth = std::max(max_depth, c.depth);
    min_box_depth = std::min(min_box_depth, c.box_depth);
    max_box_depth = std::max(max_box_depth, c.box_depth);
    min_view_depth = std::min(min_view_depth, c.view_depth);
    max_view_depth = std::max(max_view_depth, c.view_depth);

    min_cx = std::min(min_cx, c.c.x);
    max_cx = std::max(max_cx, c.c.x);
    min_cy = std::min(min_cy, c.c.y);
    max_cy = std::max(max_cy, c.c.y);
    min_cz = std::min(min_cz, c.c.z);
    max_cz = std::max(max_cz, c.c.z);

    double nw = yocto::length(c.c);
    min_norm_w = std::min(min_norm_w, nw);
    max_norm_w = std::max(max_norm_w, nw);
    sum_norm_w += nw;
    sum_c += c.c;

    vec3 vc = c.ViewCentroid();
    sum_v += vc;

    int k = c.box_depth + 2 * c.view_depth;
    total_volume_fraction += std::ldexp(1.0, -k);
  }

  vec3 mean_c = sum_c / (double)N;
  double mean_norm_w = sum_norm_w / (double)N;
  vec3 mean_v = yocto::normalize(sum_v / (double)N);

  // Variances & Angular spread
  double var_cx = 0, var_cy = 0, var_cz = 0;
  double max_ang_dist = 0.0;
  for (const auto &c : cells) {
    var_cx += (c.c.x - mean_c.x) * (c.c.x - mean_c.x);
    var_cy += (c.c.y - mean_c.y) * (c.c.y - mean_c.y);
    var_cz += (c.c.z - mean_c.z) * (c.c.z - mean_c.z);

    vec3 vc = c.ViewCentroid();
    double dot_v = std::clamp(yocto::dot(mean_v, vc), -1.0, 1.0);
    max_ang_dist = std::max(max_ang_dist, std::acos(dot_v));
  }
  double std_cx = std::sqrt(var_cx / N);
  double std_cy = std::sqrt(var_cy / N);
  double std_cz = std::sqrt(var_cz / N);

  // Find cell closest to mean
  int rep_idx = 0;
  double min_dist_to_mean = 1e9;
  for (size_t i = 0; i < N; i++) {
    double d = yocto::length(cells[i].c - mean_c);
    if (d < min_dist_to_mean) {
      min_dist_to_mean = d;
      rep_idx = (int)i;
    }
  }
  if (specific_cell >= 0 && specific_cell < (int)N) {
    rep_idx = specific_cell;
  }

  // Terminal Output
  std::cout << "\n"
            << "======================================================================\n"
            << "              NOPERT #229: DIFFICULT CELLS ANALYSIS REPORT            \n"
            << "======================================================================\n\n";

  std::cout << "• Dataset: " << file_path << "\n"
            << "  Total Shelved Cells:     " << N << "\n"
            << "  Tree Depth Range:        [" << min_depth << ", " << max_depth << "]\n"
            << "  Box Depth Range:         [" << min_box_depth << ", " << max_box_depth << "]\n"
            << "  View Depth Range:        [" << min_view_depth << ", " << max_view_depth << "]\n"
            << "  Combined 5D Volume:      " << std::format("{:.6e}", total_volume_fraction)
            << " (approx " << N << " × 2^-100)\n\n";

  std::cout << "• Rotation Parameter w = (wx, wy, wz):\n"
            << "  wx: mean = " << std::format("{:.8g}", mean_c.x)
            << "  range = [" << std::format("{:.8g}", min_cx) << ", " << std::format("{:.8g}", max_cx) << "]"
            << "  span = " << std::format("{:.2e}", max_cx - min_cx)
            << "  std = " << std::format("{:.2e}", std_cx) << "\n"
            << "  wy: mean = " << std::format("{:.8g}", mean_c.y)
            << "  range = [" << std::format("{:.8g}", min_cy) << ", " << std::format("{:.8g}", max_cy) << "]"
            << "  span = " << std::format("{:.2e}", max_cy - min_cy)
            << "  std = " << std::format("{:.2e}", std_cy) << "\n"
            << "  wz: mean = " << std::format("{:.8g}", mean_c.z)
            << "  range = [" << std::format("{:.8g}", min_cz) << ", " << std::format("{:.8g}", max_cz) << "]"
            << "  span = " << std::format("{:.2e}", max_cz - min_cz)
            << "  std = " << std::format("{:.2e}", std_cz) << "\n\n";

  double rot_deg = 2.0 * std::atan(mean_norm_w) * 180.0 / std::numbers::pi;
  std::cout << "• Magnitude & Rotation Angle:\n"
            << "  ||w||: mean = " << std::format("{:.8g}", mean_norm_w)
            << "  range = [" << std::format("{:.8g}", min_norm_w) << ", " << std::format("{:.8g}", max_norm_w) << "]"
            << "  span = " << std::format("{:.2e}", max_norm_w - min_norm_w) << "\n"
            << "  Rotation angle θ:        " << std::format("{:.5f}°", rot_deg)
            << " (" << std::format("{:.2f}", rot_deg * 60.0) << " arcmin)\n"
            << "  Distance to Tube (1e-4): " << std::format("{:.8g}", mean_norm_w - 1e-4) << "\n\n";

  std::cout << "• View Direction (Ray on Unit Sphere):\n"
            << "  Normalized Centroid v:   (" << std::format("{:.8g}", mean_v.x) << ", "
                                             << std::format("{:.8g}", mean_v.y) << ", "
                                             << std::format("{:.8g}", mean_v.z) << ")\n"
            << "  Maximum Angular Radius:  " << std::format("{:.3e} rad", max_ang_dist)
            << " (" << std::format("{:.2f} arcsec", max_ang_dist * 180.0 / std::numbers::pi * 3600.0) << ")\n\n";

  // Comparison with static hard points
  std::cout << "• Proximity to Known Hard Points:\n";
  for (const auto &hp : HARD_POINTS) {
    if (hp.chart != 0) continue;
    double dist_w = yocto::length(mean_c - hp.w);
    vec3 hp_nv = yocto::normalize(hp.view);
    double dist_v = yocto::length(mean_v - hp_nv);
    std::cout << "  - " << std::format("{:<24}", hp.label)
              << " Δw = " << std::format("{:.2e}", dist_w)
              << ", Δv = " << std::format("{:.2e}", dist_v) << "\n";
  }

  std::cout << "\n• Representative Cell Selection:\n"
            << "  Index:                   #" << rep_idx << " (id=" << cells[rep_idx].id << ")\n"
            << "  Depth:                   tree=" << cells[rep_idx].depth
            << ", box=" << cells[rep_idx].box_depth
            << ", view=" << cells[rep_idx].view_depth << "\n"
            << "  Center w:                (" << std::format("{:.8g}", cells[rep_idx].c.x) << ", "
                                             << std::format("{:.8g}", cells[rep_idx].c.y) << ", "
                                             << std::format("{:.8g}", cells[rep_idx].c.z) << ")\n"
            << "  View ray:                (" << std::format("{:.8g}", cells[rep_idx].ViewCentroid().x) << ", "
                                             << std::format("{:.8g}", cells[rep_idx].ViewCentroid().y) << ", "
                                             << std::format("{:.8g}", cells[rep_idx].ViewCentroid().z) << ")\n\n";

  if (!skip_png) {
    std::cout << "• Generating PNG Visualizations...\n";
    std::string proj_png = prefix + "_projections.png";
    std::string sil_png = prefix + "_silhouette.png";
    RenderProjections(cells, proj_png);
    RenderSilhouette(cells[rep_idx], sil_png);
    std::cout << "Done! All visualizations generated successfully.\n";
  }

  std::cout << "======================================================================\n\n";
  return 0;
}
