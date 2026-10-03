#include "layout.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char **str_pool = nullptr;
size_t str_pool_len = 0, str_pool_cap = 0;

enum fb_align parse_align(char a) {
  switch (a) {
  case 's':
    return FB_ALIGN_START;
  case 'e':
    return FB_ALIGN_END;
  case 'c':
    return FB_ALIGN_CENTER;
  case 't':
    return FB_ALIGN_STRETCH;
  default:
    return FB_ALIGN_START;
  }
}

enum fb_justify parse_justify(char a) {
  switch (a) {
  case 's':
    return FB_JUSTIFY_START;
  case 'e':
    return FB_JUSTIFY_END;
  case 'c':
    return FB_JUSTIFY_CENTER;
  case 'p':
    return FB_JUSTIFY_SPACED;
  default:
    return FB_JUSTIFY_START;
  }
}

uint32_t parse_layout(struct fb_layout *layout, char **input) {
  char kind;
  int read = 0;
  if (sscanf(*input, " %c%n", &kind, &read) != 1)
    return -1;
  *input += read;

  if (kind == 'O') {
    char name[64];
    unsigned int w, h;
    unsigned int g;
    char a;
    int read = 0;
    if (sscanf(*input, " %63s %u %u %u %c%n", name, &w, &h, &g, &a, &read) != 5)
      return -1;
    *input += read;
    char *sname = strdup(name);
    if (str_pool_len == str_pool_cap) {
      str_pool_cap = str_pool_cap <= SIZE_MAX / 2 ? str_pool_cap * 2 : SIZE_MAX;
      if (str_pool_cap > SIZE_MAX / sizeof(char *))
        str_pool_cap = SIZE_MAX / sizeof(char *);
      str_pool = realloc(str_pool, str_pool_cap * sizeof(char *));
      if (!str_pool)
        assert(false);
    }
    str_pool[str_pool_len++] = sname;
    return fb_layout_add(
        layout, (struct fb_layout_node){.obj = {.w = w, .h = h, .name = sname},
                                        .sib = -1,
                                        .growth = g,
                                        .align = parse_align(a),
                                        .kind = FB_LAYOUT_OBJ});
  } else if (kind == 'R' || kind == 'C') {
    unsigned int g, count;
    char a, j;
    int read = 0;
    if (sscanf(*input, " %u %c %c %u%n", &g, &a, &j, &count, &read) != 4)
      return -1;
    *input += read;

    uint32_t first = -1, last = -1;
    for (uint32_t i = 0; i < count; ++i) {
      uint32_t child = parse_layout(layout, input);
      if (first == -1)
        first = child;
      if (last != -1)
        layout->nodes[last].sib = child;
      last = child;
    }

    return fb_layout_add(
        layout, (struct fb_layout_node){
                    .child = first,
                    .sib = -1,
                    .growth = g,
                    .align = parse_align(a),
                    .just = parse_justify(j),
                    .kind = (kind == 'R') ? FB_LAYOUT_ROW : FB_LAYOUT_COL,
                });
  }

  return -1;
}

int main(int argc, char **argv) {
  int ret = 0;

  str_pool = calloc(32, sizeof(char *));
  if (!str_pool)
    return 1;
  str_pool_cap = 32;

  char *input = argc >= 2 ? argv[1] : "";

  char *arg_x = argc >= 3 ? argv[2] : "0";
  int x = atoi(arg_x);

  char *arg_y = argc >= 4 ? argv[3] : "0";
  int y = atoi(arg_y);

  char *arg_w = argc >= 5 ? argv[4] : "0";
  int w = atoi(arg_w);

  char *arg_h = argc >= 6 ? argv[5] : "0";
  int h = atoi(arg_h);

  struct fb_layout layout = {};
  fb_layout_init(&layout, 32);

  uint32_t root = parse_layout(&layout, &input);
  if (root == -1) {
    fprintf(stderr, "Failed to parse layout\n");
    ret = 1;
    goto end;
  }

  struct fb_bounds bb = fb_layout_bounds(&layout, root);
  if (w < bb.w) w = bb.w;
  if (h < bb.h) h = bb.h;

  struct fb_placements pms = fb_place(&layout, root, x, y, w, h);

  char *fmt;
  size_t fmt_len = fb_pms_format(&pms, &fmt);

  puts(fmt);

end:
  for (size_t i = 0; i < str_pool_len; ++i)
    free(str_pool[i]);
  free(str_pool);
  free(fmt);
  fb_pms_delete(&pms);
  fb_layout_delete(&layout);
  return ret;
}
