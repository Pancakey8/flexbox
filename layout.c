#include "layout.h"
#include <assert.h>
#include <float.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef NDEBUG
#define fb_assert(x, ...)                                                      \
  do {                                                                         \
    if (!(x)) {                                                                \
      __VA_ARGS__                                                              \
    }                                                                          \
  } while (0)
#else
#define fb_assert(x, ...) assert((x))
#endif

bool fb_layout_init(struct fb_layout *layout, uint32_t reserv) {
  fb_assert(layout, { return false; });

  layout->len = 0;
  layout->nodes = calloc(reserv, sizeof(struct fb_layout_node));
  fb_assert(layout->nodes, {
    layout->cap = 0;
    return false;
  });
  layout->cap = reserv;

  return true;
}

void fb_layout_delete(struct fb_layout *layout) {
  fb_assert(layout, { return; });
  free(layout->nodes);
  *layout = (struct fb_layout){};
}

uint32_t fb_layout_add(struct fb_layout *layout, struct fb_layout_node node) {
  fb_assert(layout, { return -1; });
  fb_assert(layout->len <= layout->cap, { return -1; });
  fb_assert(layout->len != UINT32_MAX, { return -1; });

  if (layout->len == layout->cap) {
    uint32_t new_cap = 8;
    if (layout->cap > 0) {
      new_cap = layout->cap <= UINT32_MAX / 2 ? layout->cap * 2 : UINT32_MAX;
    }
    fb_assert((size_t)new_cap <= SIZE_MAX / sizeof(struct fb_layout_node),
              { return -1; });
    struct fb_layout_node *new_nodes =
        realloc(layout->nodes, (size_t)new_cap * sizeof(struct fb_layout_node));
    fb_assert(new_nodes, { return -1; });
    layout->nodes = new_nodes;
    layout->cap = new_cap;
  }

  layout->nodes[layout->len] = node;
  return layout->len++;
}

void fb_layout_reset(struct fb_layout *layout) { layout->len = 0; }

#define lget(l, i) ((i) != (uint32_t)-1 ? &(l)->nodes[(i)] : nullptr)

struct fb_bounds fb_layout_bounds(struct fb_layout const *layout,
                                  uint32_t root) {
  fb_assert(layout, { return (struct fb_bounds){-1, -1}; });
  struct fb_layout_node const *node = lget(layout, root);
  fb_assert(node, { return (struct fb_bounds){-1, -1}; });

  switch (node->kind) {
  case FB_LAYOUT_OBJ:
    return (struct fb_bounds){node->obj.w, node->obj.h};

  case FB_LAYOUT_ROW: {
    float w = 0;
    float h = 0;
    uint32_t child = node->child;
    while (lget(layout, child)) {
      struct fb_bounds bb = fb_layout_bounds(layout, child);
      w += bb.w;
      if (bb.h > h)
        h = bb.h;
      child = lget(layout, child)->sib;
    }
    return (struct fb_bounds){w, h};
  } break;

  case FB_LAYOUT_COL: {
    float w = 0;
    float h = 0;
    uint32_t child = node->child;
    while (lget(layout, child)) {
      struct fb_bounds bb = fb_layout_bounds(layout, child);
      if (bb.w > w)
        w = bb.w;
      h += bb.h;
      child = lget(layout, child)->sib;
    }
    return (struct fb_bounds){w, h};
  } break;
  }

  fb_assert(false, { return (struct fb_bounds){-1, -1}; });
}

#undef lget

void fb_ctx_finish(struct fb_builder_ctx *ctx, enum fb_layout_node_kind kind,
                   uint8_t growth, enum fb_align align,
                   enum fb_justify justify) {
  ctx->done = true;
  struct fb_layout_node node = {.child = ctx->first,
                                .sib = -1,
                                .growth = growth,
                                .align = align,
                                .just = justify,
                                .kind = kind};
  uint32_t id = fb_layout_add(ctx->target, node);
  if (ctx->parent) {
    if (ctx->parent->last != -1) {
      ctx->target->nodes[ctx->parent->last].sib = id;
    }
    if (ctx->parent->first == -1) {
      ctx->parent->first = id;
    }
    ctx->parent->last = id;
  } else {
    ctx->last = ctx->first = id;
  }
}
