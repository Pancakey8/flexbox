#include "layout.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
  struct fb_layout layout = {};
  fb_layout_init(&layout, 2);

  uint32_t root;
  FB_AT(&layout, root) {
    FB_ROW(0, FB_ALIGN_START, FB_JUSTIFY_START) {
      FB_COL(0, FB_ALIGN_START, FB_JUSTIFY_START) {
        FB_OBJ("A", 300, 200, 0, FB_ALIGN_START);
        FB_OBJ("B", 200, 600, 0, FB_ALIGN_START);
      }
      FB_OBJ("C", 100, 400, 0, FB_ALIGN_START);
    }
  }

  struct fb_bounds bb2 = fb_layout_bounds(&layout, root);
  printf("%f, %f\n", bb2.w, bb2.h);
  fb_layout_delete(&layout);
}
