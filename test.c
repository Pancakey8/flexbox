#include "layout.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  struct fb_layout layout = {};
  fb_layout_init(&layout, 2);

  uint32_t root;
  FB_AT(&layout, root) {
    FB_ROW(0, FB_ALIGN_START, FB_JUSTIFY_SPACED) {
      FB_OBJ("A", 100, 100, 0, FB_ALIGN_START);
      FB_OBJ("B", 100, 100, 0, FB_ALIGN_CENTER);
      FB_OBJ("C", 100, 100, 0, FB_ALIGN_END);
      FB_OBJ("D", 100, 100, 0, FB_ALIGN_STRETCH);
    }
  }

  struct fb_placements pms = fb_place(&layout, root, 0, 0, 1000, 200);

  char *fmt;
  size_t fmt_len = fb_pms_format(&pms, &fmt);
  puts(fmt);

  free(fmt);
  fb_pms_delete(&pms);
  fb_layout_delete(&layout);
}
