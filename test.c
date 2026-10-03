#include "layout.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <raylib.h>

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

  InitWindow(1000, 300, "Test");

  SetWindowState(FLAG_WINDOW_RESIZABLE);
  struct fb_bounds bb = fb_layout_bounds(&layout, root);
  SetWindowMinSize(bb.w, bb.h);
  SetTargetFPS(60);

  struct fb_placements pms = fb_place(&layout, root, 0, 0, 1000, 300);

  while (!WindowShouldClose()) {
    if (IsWindowResized()) {
      int w = GetScreenWidth();
      int h = GetScreenHeight();
      fb_pms_delete(&pms);
      pms = fb_place(&layout, root, 0, 0, w, h);
    }

    BeginDrawing();

    ClearBackground(RAYWHITE);

    for (uint32_t i = 0; i < pms.len; ++i) {
      struct fb_placement *p = &pms.data[i];
      DrawRectangle(p->x, p->y, p->w, p->h, RED);
      DrawText(p->name, p->x + p->w / 2, p->y + p->h / 2, 16, WHITE);
    }

    EndDrawing();
  }

  fb_pms_delete(&pms);
  fb_layout_delete(&layout);
}
