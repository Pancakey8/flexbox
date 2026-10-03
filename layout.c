#include "layout.h"
#include <assert.h>
#include <float.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

bool fb_pms_push(struct fb_placements *pms, struct fb_placement pm) {
  fb_assert(pms, { return false; });
  fb_assert(pms->len <= pms->cap, { return false; });
  fb_assert(pms->len != UINT32_MAX, { return false; });

  if (pms->len == pms->cap) {
    uint32_t new_cap = 8;
    if (pms->cap > 0) {
      new_cap = pms->cap <= UINT32_MAX / 2 ? pms->cap * 2 : UINT32_MAX;
    }
    fb_assert((size_t)new_cap <= SIZE_MAX / sizeof(struct fb_placement),
              { return false; });
    struct fb_placement *new_data =
        realloc(pms->data, new_cap * sizeof(struct fb_placement));
    fb_assert(new_data, { return false; });
    pms->data = new_data;
    pms->cap = new_cap;
  }

  pms->data[pms->len++] = pm;
  return true;
}

void fb_pms_delete(struct fb_placements *pms) {
  fb_assert(pms, { return; });
  free(pms->data);
  *pms = (struct fb_placements){};
}

/* bool fb_pms_append(struct fb_placements *pms, */
/*                    struct fb_placements const *other) { */
/*   fb_assert(pms, { return false; }); */
/*   fb_assert(other, { return false; }); */
/*   fb_assert(pms->len <= pms->cap, { return false; }); */
/*   fb_assert(UINT32_MAX - pms->len >= other->len, { return false; }); */

/*   if (other->len == 0) */
/*     return true; */

/*   if (pms->cap - pms->len < other->len) { */
/*     uint32_t new_cap = pms->cap <= UINT32_MAX / 2 ? pms->cap * 2 :
 * UINT32_MAX; */
/*     if (new_cap < pms->len + other->len) */
/*       new_cap = pms->len + other->len; */
/*     fb_assert((size_t)new_cap <= SIZE_MAX / sizeof(struct fb_placement), */
/*               { return false; }); */
/*     struct fb_placement *new_data = */
/*         realloc(pms->data, new_cap * sizeof(struct fb_placement)); */
/*     fb_assert(new_data, { return false; }); */
/*     pms->data = new_data; */
/*     pms->cap = new_cap; */
/*   } */

/*   memcpy(pms->data + pms->len, other->data, */
/*          other->len * sizeof(struct fb_placement)); */
/*   pms->len += other->len; */

/*   return true; */
/* } */

struct fb_place_context {
  uint32_t i, n;
  float x, y;
  float w, w_gap;
  float h, h_gap;
  uint8_t tg;
};

struct fb_placement fb_compute_row1(struct fb_layout const *layout,
                                    uint32_t root, enum fb_justify just,
                                    struct fb_place_context *ctx) {
  fb_assert(layout, { return (struct fb_placement){"", -1, -1, -1, -1}; });
  struct fb_layout_node *node = lget(layout, root);
  fb_assert(node, { return (struct fb_placement){"", -1, -1, -1, -1}; });

  struct fb_bounds bb = fb_layout_bounds(layout, root);

  float w_new = bb.w;
  if (ctx->tg > 0) {
    w_new = bb.w + ctx->w_gap * node->growth / ctx->tg;
  }

  float y_new = ctx->y;
  switch (node->align) {
  case FB_ALIGN_START:
    y_new = ctx->y;
    break;
  case FB_ALIGN_END:
    y_new = ctx->y + (ctx->h - bb.h);
    break;
  case FB_ALIGN_CENTER:
    y_new = ctx->y + (ctx->h - bb.h) / 2;
    break;
  case FB_ALIGN_STRETCH:
    y_new = ctx->y;
    break;
  }

  float h_new = bb.h;
  if (node->align == FB_ALIGN_STRETCH) {
    h_new = ctx->h;
  }

  float x_new = ctx->x;
  if (ctx->tg == 0) {
    switch (just) {
    case FB_JUSTIFY_START:
      x_new = ctx->x;
      break;
    case FB_JUSTIFY_END:
      x_new = ctx->x + ctx->w_gap;
      break;
    case FB_JUSTIFY_CENTER:
      x_new = ctx->x + ctx->w_gap / 2;
      break;
    case FB_JUSTIFY_SPACED:
      x_new = ctx->x + (ctx->i + 1) * ctx->w_gap / (ctx->n + 1);
      break;
    }
  }

  ctx->i++;
  ctx->x += w_new;
  return (struct fb_placement){"", x_new, y_new, w_new, h_new};
}

struct fb_placement fb_compute_col1(struct fb_layout const *layout,
                                    uint32_t root, enum fb_justify just,
                                    struct fb_place_context *ctx) {
  fb_assert(layout, { return (struct fb_placement){"", -1, -1, -1, -1}; });
  struct fb_layout_node *node = lget(layout, root);
  fb_assert(node, { return (struct fb_placement){"", -1, -1, -1, -1}; });

  struct fb_bounds bb = fb_layout_bounds(layout, root);

  float h_new = bb.h;
  if (ctx->tg > 0) {
    h_new = bb.h + ctx->h_gap * node->growth / ctx->tg;
  }

  float x_new = ctx->x;
  switch (node->align) {
  case FB_ALIGN_START:
    x_new = ctx->x;
    break;
  case FB_ALIGN_END:
    x_new = ctx->x + (ctx->w - bb.w);
    break;
  case FB_ALIGN_CENTER:
    x_new = ctx->x + (ctx->w - bb.w) / 2;
    break;
  case FB_ALIGN_STRETCH:
    x_new = ctx->x;
    break;
  }

  float w_new = bb.w;
  if (node->align == FB_ALIGN_STRETCH) {
    w_new = ctx->w;
  }

  float y_new = ctx->y;
  if (ctx->tg == 0) {
    switch (just) {
    case FB_JUSTIFY_START:
      y_new = ctx->y;
      break;
    case FB_JUSTIFY_END:
      y_new = ctx->y + ctx->h_gap;
      break;
    case FB_JUSTIFY_CENTER:
      y_new = ctx->y + ctx->h_gap / 2;
      break;
    case FB_JUSTIFY_SPACED:
      y_new = ctx->y + (ctx->i + 1) * ctx->h_gap / (ctx->n + 1);
      break;
    }
  }

  ctx->i++;
  ctx->y += h_new;
  return (struct fb_placement){"", x_new, y_new, w_new, h_new};
}

bool fb_place_rec(struct fb_placements *pms, struct fb_layout const *layout,
                  uint32_t root, float x, float y, float w, float h) {
  fb_assert(layout, { return false; });
  struct fb_layout_node *node = lget(layout, root);
  fb_assert(node, { return false; });

  switch (node->kind) {
  case FB_LAYOUT_OBJ:
    fb_pms_push(pms, (struct fb_placement){node->obj.name, x, y, w, h});
    return true;
  case FB_LAYOUT_ROW:
    [[fallthrough]];
  case FB_LAYOUT_COL: {
    struct fb_bounds bb = fb_layout_bounds(layout, root);
    float w_gap = w > bb.w ? (w - bb.w) : 0;
    float h_gap = h > bb.h ? (h - bb.h) : 0;
    uint8_t tg = 0;
    uint32_t len = 0;
    struct fb_layout_node *child = lget(layout, node->child);
    while (child) {
      tg += child->growth;
      len++;
      child = lget(layout, child->sib);
    }
    struct fb_place_context ctx = {
        .i = 0,
        .n = len,
        .x = x,
        .y = y,
        .w = w,
        .w_gap = w_gap,
        .h = h,
        .h_gap = h_gap,
        .tg = tg,
    };
    uint32_t cid = node->child;
    while (lget(layout, cid)) {
      struct fb_placement p;
      if (node->kind == FB_LAYOUT_ROW) {
        p = fb_compute_row1(layout, cid, node->just, &ctx);
      } else {
        p = fb_compute_col1(layout, cid, node->just, &ctx);
      }
      fb_place_rec(pms, layout, cid, p.x, p.y, p.w, p.h);
      cid = lget(layout, cid)->sib;
    }
    return true;
  } break;
  }

  fb_assert(false, { return false; });
}

struct fb_placements fb_place(struct fb_layout const *layout, uint32_t root,
                              float x, float y, float w, float h) {
  fb_assert(layout, { return (struct fb_placements){}; });
  struct fb_layout_node *node = lget(layout, root);
  fb_assert(node, { return (struct fb_placements){}; });

  struct fb_placements pms = {};

  switch (node->kind) {
  case FB_LAYOUT_OBJ: {
    struct fb_bounds bb = fb_layout_bounds(layout, root);
    float w_gap = w > bb.w ? (w - bb.w) : 0;
    float h_gap = h > bb.h ? (h - bb.h) : 0;
    uint8_t tg = node->growth;
    uint32_t len = 1;
    struct fb_place_context ctx = {
        .i = 0,
        .n = len,
        .x = x,
        .y = y,
        .w = w,
        .w_gap = w_gap,
        .h = h,
        .h_gap = h_gap,
        .tg = tg,
    };
    struct fb_placement p = fb_compute_row1(layout, root, node->just, &ctx);
    fb_pms_push(&pms,
                (struct fb_placement){node->obj.name, p.x, p.y, p.w, p.h});
    return pms;
  } break;
  case FB_LAYOUT_ROW:
  case FB_LAYOUT_COL:
    fb_place_rec(&pms, layout, root, x, y, w, h);
    return pms;
    break;
  }

  fb_assert(false, { return (struct fb_placements){}; });
}

#undef lget

void fb_ctx_finish(struct fb_builder_ctx *ctx, enum fb_layout_node_kind kind,
                   uint8_t growth, enum fb_align align,
                   enum fb_justify justify) {
  fb_assert(ctx, { return; });
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

size_t fb_pms_format(struct fb_placements const *pms, char **out) {
  fb_assert(pms, { return -1; });
  fb_assert(out, { return -1; });
  size_t len = 0;
  *out = malloc(1);
  fb_assert(*out, { goto fail; });
  (*out)[0] = '\0';

  for (uint32_t i = 0; i < pms->len; ++i) {
    struct fb_placement *p = &pms->data[i];

    int n =
        snprintf(NULL, 0, "|%s,%f,%f,%f,%f", p->name, p->x, p->y, p->w, p->h);
    fb_assert(n >= 0, { goto fail; });
    fb_assert(SIZE_MAX - len >= (size_t)n + 1, { goto fail; });

    size_t new_len = len + n;
    char *new_data = realloc(*out, new_len + 1);
    fb_assert(new_data, { goto fail; });
    *out = new_data;

    snprintf(*out + len, n + 1, "|%s,%f,%f,%f,%f", p->name, p->x, p->y, p->w,
             p->h);
    len = new_len;
  }

  return len;

fail:
  free(*out);
  *out = NULL;
  return -1;
}
