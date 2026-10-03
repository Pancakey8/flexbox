#pragma once

#include <stddef.h>
#include <stdint.h>

enum fb_align : uint8_t {
  FB_ALIGN_START,
  FB_ALIGN_END,
  FB_ALIGN_CENTER,
  FB_ALIGN_STRETCH,
};

enum fb_justify : uint8_t {
  FB_JUSTIFY_START,
  FB_JUSTIFY_END,
  FB_JUSTIFY_CENTER,
  FB_JUSTIFY_SPACED,
};

enum fb_layout_node_kind : uint8_t {
  FB_LAYOUT_OBJ,
  FB_LAYOUT_ROW,
  FB_LAYOUT_COL,
};

struct fb_layout_node {
  union {
    struct {
      char *name;
      float w, h;
    } obj;

    uint32_t child;
  };

  uint32_t sib;

  uint8_t growth;
  enum fb_align align;
  enum fb_justify just;
  enum fb_layout_node_kind kind;
};

struct fb_layout {
  struct fb_layout_node *nodes;
  uint32_t len, cap;
};

bool fb_layout_init(struct fb_layout *layout, uint32_t reserv);
void fb_layout_delete(struct fb_layout *layout);
uint32_t fb_layout_add(struct fb_layout *layout, struct fb_layout_node node);
void fb_layout_reset(struct fb_layout *layout);

struct fb_bounds {
  float w, h;
};

struct fb_bounds fb_layout_bounds(struct fb_layout const *layout,
                                  uint32_t root);

struct fb_builder_ctx {
  struct fb_layout *target;
  uint32_t first;
  uint32_t last;
  bool done;
  struct fb_builder_ctx *parent;
};

void fb_ctx_finish(struct fb_builder_ctx *ctx, enum fb_layout_node_kind kind,
                   uint8_t growth, enum fb_align align,
                   enum fb_justify justify);

#define FB_AT(layout_, root_)                                                  \
  for (struct fb_builder_ctx fb_ctx_ = {(layout_), -1, -1, false, nullptr};    \
       !fb_ctx_.done; fb_ctx_.done = true, root_ = fb_ctx_.first)

#define FB_OBJ(nm_, w_, h_, g_, a_)                                            \
  do {                                                                         \
    struct fb_layout_node fb_node_ = {                                         \
        .obj = {.w = (w_), .h = (h_), .name = (nm_)},                          \
        .sib = -1,                                                             \
        .growth = (g_),                                                        \
        .align = (a_),                                                         \
        .kind = FB_LAYOUT_OBJ};                                                \
    auto fb_node_id_ = fb_layout_add(fb_ctx_.target, fb_node_);                \
    if (fb_ctx_.last != -1) {                                                  \
      fb_ctx_.target->nodes[fb_ctx_.last].sib = fb_node_id_;                   \
    }                                                                          \
    if (fb_ctx_.first == -1)                                                   \
      fb_ctx_.first = fb_node_id_;                                             \
    fb_ctx_.last = fb_node_id_;                                                \
  } while (0)

#define FB_ROW(g_, a_, j_)                                                     \
  for (struct fb_builder_ctx *fb_orig_ = &fb_ctx_,                             \
                             fb_ctx_ = {fb_orig_->target, -1, -1, false,       \
                                        fb_orig_};                             \
       !fb_ctx_.done;                                                          \
       fb_ctx_finish(&fb_ctx_, FB_LAYOUT_ROW, (g_), (a_), (j_)))
#define FB_COL(g_, a_, j_)                                                     \
  for (struct fb_builder_ctx *fb_orig_ = &fb_ctx_,                             \
                             fb_ctx_ = {fb_orig_->target, -1, -1, false,       \
                                        fb_orig_};                             \
       !fb_ctx_.done;                                                          \
       fb_ctx_finish(&fb_ctx_, FB_LAYOUT_COL, (g_), (a_), (j_)))
