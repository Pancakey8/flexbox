import Layout.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- This file is highly sloppy LLM code, it's not meant to be studied.
-- The key theorems are `place_inside` and `place_no_overlap`.

-- `place_inside` proves that for any placement with an allotted
-- width/height greater than the bounding box (which is the minimal
-- space needed), the placement doesn't overflow.

-- `place_no_overlap` proves that any two placed objects are disjoint in
-- space, that there are no overlapping placements.

def overlap (a b : PlacedObject) : Prop :=
  a.x < b.x + b.w ∧
  b.x < a.x + a.w ∧
  a.y < b.y + b.h ∧
  b.y < a.y + a.h

def inside (x y w h : Rat) (p : PlacedObject) : Prop :=
  x ≤ p.x ∧
  y ≤ p.y ∧
  p.x + p.w ≤ x + w ∧
  p.y + p.h ≤ y + h

lemma inside_mono {x1 y1 w1 h1 x2 y2 w2 h2 : Rat} {p : PlacedObject}
    (hp : inside x1 y1 w1 h1 p)
    (hx : x2 ≤ x1) (hy : y2 ≤ y1)
    (hw : x1 + w1 ≤ x2 + w2) (hh : y1 + h1 ≤ y2 + h2) :
    inside x2 y2 w2 h2 p := by
  rcases hp with ⟨hx1, hy1, hw1, hh1⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma le_max_getD_0 (xs : List Rat) (x : Rat) (hx : x ∈ xs) : x ≤ xs.max?.getD 0 := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [Option.elim]
      split <;> simp_all
    · apply le_trans (ih hx) ?_
      simp [Option.elim]
      split <;> simp_all

lemma max_getD_0_nonneg (xs : List Rat) (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.max?.getD 0 := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    simp [Option.elim]
    split <;> simp_all

mutual
  theorem bb_w_nonneg (l : Layout) : 0 ≤ (boundingBox l).w := by
    cases l with
    | obj _ _ _ h_wh =>
      simp [boundingBox]
      exact h_wh.1
    | row ls =>
      simp [boundingBox]
      exact list_sum_w_nonneg ls
    | col ls =>
      simp [boundingBox]
      exact max_getD_0_nonneg _ (list_forall_w_nonneg ls)

  theorem bb_h_nonneg (l : Layout) : 0 ≤ (boundingBox l).h := by
    cases l with
    | obj _ _ _ h_wh =>
      simp [boundingBox]
      exact h_wh.2
    | row ls =>
      simp [boundingBox]
      exact max_getD_0_nonneg _ (list_forall_h_nonneg ls)
    | col ls =>
      simp [boundingBox]
      exact list_sum_h_nonneg ls

  theorem list_sum_w_nonneg (ls : List Layout) : 0 ≤ (ls.map (fun l => (boundingBox l).w)).sum :=
    match ls with
    | [] => le_refl 0
    | l::ls => by
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (bb_w_nonneg l) (list_sum_w_nonneg ls)

  theorem list_sum_h_nonneg (ls : List Layout) : 0 ≤ (ls.map (fun l => (boundingBox l).h)).sum :=
    match ls with
    | [] => le_refl 0
    | l::ls => by
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (bb_h_nonneg l) (list_sum_h_nonneg ls)

  theorem list_forall_w_nonneg (ls : List Layout) : ∀ x ∈ ls.map (fun l => (boundingBox l).w), 0 ≤ x :=
    match ls with
    | [] => fun x hx => by contradiction
    | l::ls => fun x hx => by
      simp only [List.map_cons, List.mem_cons] at hx
      cases hx with
      | inl h => rw [h]; exact bb_w_nonneg l
      | inr h => exact list_forall_w_nonneg ls x h

  theorem list_forall_h_nonneg (ls : List Layout) : ∀ x ∈ ls.map (fun l => (boundingBox l).h), 0 ≤ x :=
    match ls with
    | [] => fun x hx => by contradiction
    | l::ls => fun x hx => by
      simp only [List.map_cons, List.mem_cons] at hx
      cases hx with
      | inl h => rw [h]; exact bb_h_nonneg l
      | inr h => exact list_forall_h_nonneg ls x h
end

lemma growthOf_nonneg (l : Layout) : 0 ≤ growthOf l :=
  match l with
  | .obj _ _ _ _ _ h_g _ => h_g
  | .row _ _ h_g _ _ => h_g
  | .col _ _ h_g _ _ => h_g

def req_w (ls : List Layout) (w_gap tg : Rat) : Rat :=
  (ls.map (fun l => (boundingBox l).w)).sum + if tg > 0 then w_gap * (ls.map growthOf).sum / tg else w_gap

def req_h (ls : List Layout) (h_gap tg : Rat) : Rat :=
  (ls.map (fun l => (boundingBox l).h)).sum + if tg > 0 then h_gap * (ls.map growthOf).sum / tg else h_gap

lemma req_w_cons (l : Layout) (ls : List Layout) (w_gap tg : Rat) :
    let w' := if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w
    w' + req_w ls w_gap tg = req_w (l :: ls) w_gap tg := by
  dsimp [req_w]
  split
  · rename_i htg
    simp only [List.map_cons, List.sum_cons]
    have : w_gap * (growthOf l + (ls.map growthOf).sum) / tg = w_gap * growthOf l / tg + w_gap * (ls.map growthOf).sum / tg := by
      ring
    linarith
  · simp only [List.map_cons, List.sum_cons]
    linarith

lemma req_h_cons (l : Layout) (ls : List Layout) (h_gap tg : Rat) :
    let h' := if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h
    h' + req_h ls h_gap tg = req_h (l :: ls) h_gap tg := by
  dsimp [req_h]
  split
  · rename_i htg
    simp only [List.map_cons, List.sum_cons]
    have : h_gap * (growthOf l + (ls.map growthOf).sum) / tg = h_gap * growthOf l / tg + h_gap * (ls.map growthOf).sum / tg := by
      ring
    linarith
  · simp only [List.map_cons, List.sum_cons]
    linarith

lemma list_sum_growthOf_nonneg (ls : List Layout) : 0 ≤ (ls.map growthOf).sum := by
  induction ls with
  | nil => exact le_refl 0
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (growthOf_nonneg l) ih

mutual
  theorem place'_inside
      (l : Layout) (x y w h : Rat)
      (hw : (boundingBox l).w ≤ w)
      (hh : (boundingBox l).h ≤ h) :
      ∀ p ∈ place' l x y w h, inside x y w h p := by
    match l with
    | .obj name w' h' h_wh g h_g a =>
      simp [place', inside]
    | .row ls g h_g a j =>
      intro p hp
      simp only [place'] at hp
      let w_gap := max 0 (w - (boundingBox (.row ls)).w)
      let h_gap := max 0 (h - (boundingBox (.row ls)).h)
      let tg := (ls.map growthOf).sum
      have hw_gap : 0 ≤ w_gap := le_max_left 0 _
      have h_req : x + req_w ls w_gap tg ≤ x + w := by
        dsimp [req_w]
        split
        · rename_i htg
          have : w_gap = w - (boundingBox (.row ls)).w := max_eq_right $ by
            simp [boundingBox] at hw ⊢
            exact hw
          have h_sum : (ls.map fun l => (boundingBox l).w).sum = (boundingBox (.row ls)).w := by
            simp [boundingBox]
            rfl
          rw [h_sum, this]
          have h_mul : (w - (boundingBox (.row ls)).w) * (ls.map growthOf).sum / (ls.map growthOf).sum = w - (boundingBox (.row ls)).w := by
            exact mul_div_cancel_right₀ _ (ne_of_gt htg)
          linarith
        · have : w_gap = w - (boundingBox (.row ls)).w := max_eq_right $ by
            simp [boundingBox] at hw ⊢
            exact hw
          have h_sum : (ls.map fun l => (boundingBox l).w).sum = (boundingBox (.row ls)).w := by
            simp [boundingBox]
            rfl
          rw [h_sum, this]
          linarith
      have h_h : ∀ l' ∈ ls, (boundingBox l').h ≤ h := by
        intro l' hl'
        apply le_trans ?_ hh
        simp [boundingBox]
        apply le_max_getD_0
        exact List.mem_map_of_mem hl'
      exact placeRow_inside ls j 0 ls.length x y w w_gap h h_gap tg x w (le_refl x) hw_gap h_req h_h (by simp) p hp
    | .col ls g h_g a j =>
      intro p hp
      simp only [place'] at hp
      let w_gap := max 0 (w - (boundingBox (.col ls)).w)
      let h_gap := max 0 (h - (boundingBox (.col ls)).h)
      let tg := (ls.map growthOf).sum
      have hh_gap : 0 ≤ h_gap := le_max_left 0 _
      have h_req : y + req_h ls h_gap tg ≤ y + h := by
        dsimp [req_h]
        split
        · rename_i htg
          have : h_gap = h - (boundingBox (.col ls)).h := max_eq_right $ by
            simp [boundingBox] at hh ⊢
            exact hh
          have h_sum : (ls.map fun l => (boundingBox l).h).sum = (boundingBox (.col ls)).h := by
            simp [boundingBox]
            rfl
          rw [h_sum, this]
          have h_mul : (h - (boundingBox (.col ls)).h) * (ls.map growthOf).sum / (ls.map growthOf).sum = h - (boundingBox (.col ls)).h := by
            exact mul_div_cancel_right₀ _ (ne_of_gt htg)
          linarith
        · have : h_gap = h - (boundingBox (.col ls)).h := max_eq_right $ by
            simp [boundingBox] at hh ⊢
            exact hh
          have h_sum : (ls.map fun l => (boundingBox l).h).sum = (boundingBox (.col ls)).h := by
            simp [boundingBox]
            rfl
          rw [h_sum, this]
          linarith
      have h_w : ∀ l' ∈ ls, (boundingBox l').w ≤ w := by
        intro l' hl'
        apply le_trans ?_ hw
        simp [boundingBox]
        apply le_max_getD_0
        exact List.mem_map_of_mem hl'
      exact placeCol_inside ls j 0 ls.length x y w w_gap h h_gap tg y h (le_refl y) hh_gap h_req h_w (by simp) p hp

  theorem placeRow_inside
      (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat)
      (x0 w0 : Rat)
      (hx0 : x0 ≤ x)
      (hw_gap : 0 ≤ w_gap)
      (h_bound : x + req_w ls w_gap tg ≤ x0 + w0)
      (hh_all : ∀ l ∈ ls, (boundingBox l).h ≤ h)
      (hi : i + ls.length ≤ n) :
      ∀ p ∈ placeRow ls j i n x y w w_gap h h_gap tg, inside x0 y w0 h p := by
    cases ls with
    | nil => simp [placeRow]
    | cons l ls' =>
      intro p hp
      simp only [placeRow, List.mem_append] at hp
      rcases hp with h_l | h_ls'
      · have hw' : (boundingBox l).w ≤ if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
          split
          · rename_i htg
            have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
            linarith
          · exact le_refl _
        have hh' : (boundingBox l).h ≤ if alignOf l = .stretch then h else (boundingBox l).h := by
          split
          · exact hh_all l List.mem_cons_self
          · exact le_refl _
        have p_in := place'_inside l _ _ _ _ hw' hh' p h_l
        have hx_sub : x0 ≤ if tg > 0 then x else match j with
            | .start => x
            | .center => x + w_gap / 2
            | .end => x + w_gap
            | .spaced => x + (i + 1) * w_gap / (n + 1) := by
          split
          · exact hx0
          · cases j <;> (try linarith)
            · have : 0 ≤ (i + 1) * w_gap / (n + 1) := by
                apply div_nonneg
                · apply mul_nonneg <;> linarith
                · linarith
              linarith
        have hy_sub : y ≤ match alignOf l with
            | .start => y
            | .center => y + (h - (boundingBox l).h) / 2
            | .end => y + (h - (boundingBox l).h)
            | .stretch => y := by
          cases hl : alignOf l
          <;> simp_all
          obtain ⟨hh_all_1, hh_all_2⟩ := hh_all
          linarith
        have hw_sub : (if tg > 0 then x else match j with
            | .start => x
            | .center => x + w_gap / 2
            | .end => x + w_gap
            | .spaced => x + (i + 1) * w_gap / (n + 1)) +
            (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) ≤ x0 + w0 := by
          simp only [req_w, List.map_cons, List.sum_cons] at h_bound
          have h_sum_w := list_sum_w_nonneg ls'
          have h_g_sum := list_sum_growthOf_nonneg ls'
          split
          · rename_i htg
            have h_div : 0 ≤ w_gap * (ls'.map growthOf).sum / tg :=
              div_nonneg (mul_nonneg hw_gap h_g_sum) (le_of_lt htg)
            have h_ring : w_gap * (growthOf l + (ls'.map growthOf).sum) / tg =
                w_gap * growthOf l / tg + w_gap * (ls'.map growthOf).sum / tg := by ring
            simp_all
            linarith
          · cases j
            · simp_all; linarith
            · simp_all; linarith
            · simp_all; linarith
            · have h_ratio : (i + 1) * w_gap / (n + 1) ≤ w_gap := by
                have hn_pos : 0 < (n : Rat) + 1 := by linarith
                rw [div_le_iff₀ hn_pos]
                simp at hi
                have : ls'.length ≥ 0 := by simp
                rw [mul_comm w_gap (↑n + 1)]
                gcongr
                linarith
              simp_all; linarith
        have hh_sub : (match alignOf l with
            | .start => y
            | .center => y + (h - (boundingBox l).h) / 2
            | .end => y + (h - (boundingBox l).h)
            | .stretch => y) + (if alignOf l = .stretch then h else (boundingBox l).h) ≤ y + h := by
          cases hl : alignOf l
          <;> simp_all
          <;> linarith
        exact inside_mono p_in (by cases j <;> simp_all) hy_sub (by cases j <;> simp_all) hh_sub
      · have h_req_cons := req_w_cons l ls' w_gap tg
        have h_bound_next : (x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) + req_w ls' w_gap tg ≤ x0 + w0 := by
          linarith
        have hx0_next : x0 ≤ x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
          have : 0 ≤ if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
            split
            · rename_i htg
              have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
              have := bb_w_nonneg l
              linarith
            · exact bb_w_nonneg l
          linarith
        have hh_next : ∀ l' ∈ ls', (boundingBox l').h ≤ h := fun l' hl' => hh_all l' (List.mem_cons_of_mem _ hl')
        exact placeRow_inside ls' j (i + 1) n _ y w w_gap h h_gap tg x0 w0 hx0_next hw_gap h_bound_next hh_next (by simp at hi; omega) p h_ls'

  theorem placeCol_inside
      (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat)
      (y0 h0 : Rat)
      (hy0 : y0 ≤ y)
      (hh_gap : 0 ≤ h_gap)
      (h_bound : y + req_h ls h_gap tg ≤ y0 + h0)
      (hw_all : ∀ l ∈ ls, (boundingBox l).w ≤ w)
      (hi : i + ls.length ≤ n) :
      ∀ p ∈ placeCol ls j i n x y w w_gap h h_gap tg, inside x y0 w h0 p := by
    cases ls with
    | nil => simp [placeCol]
    | cons l ls' =>
      intro p hp
      simp only [placeCol, List.mem_append] at hp
      rcases hp with h_l | h_ls'
      · have hh' : (boundingBox l).h ≤ if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
          split
          · rename_i htg
            have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
            linarith
          · exact le_refl _
        have hw' : (boundingBox l).w ≤ if alignOf l = .stretch then w else (boundingBox l).w := by
          split
          · exact hw_all l List.mem_cons_self
          · exact le_refl _
        have p_in := place'_inside l _ _ _ _ hw' hh' p h_l
        have hx_sub : x ≤ match alignOf l with
            | .start => x
            | .center => x + (w - (boundingBox l).w) / 2
            | .end => x + (w - (boundingBox l).w)
            | .stretch => x := by
          cases hl : alignOf l
          <;> simp_all
          obtain ⟨hw_all_1, hw_all_2⟩ := hw_all
          linarith
        have hy_sub : y0 ≤ if tg > 0 then y else match j with
            | .start => y
            | .center => y + h_gap / 2
            | .end => y + h_gap
            | .spaced => y + (i + 1) * h_gap / (n + 1) := by
          split
          · exact hy0
          · cases j <;> (try linarith)
            · have : 0 ≤ (i + 1) * h_gap / (n + 1) := by
                apply div_nonneg
                · apply mul_nonneg <;> linarith
                · linarith
              linarith
        have hw_sub : (match alignOf l with
            | .start => x
            | .center => x + (w - (boundingBox l).w) / 2
            | .end => x + (w - (boundingBox l).w)
            | .stretch => x) + (if alignOf l = .stretch then w else (boundingBox l).w) ≤ x + w := by
          cases hl : alignOf l
          <;> simp_all
          <;> linarith
        have hh_sub : (if tg > 0 then y else match j with
            | .start => y
            | .center => y + h_gap / 2
            | .end => y + h_gap
            | .spaced => y + (i + 1) * h_gap / (n + 1)) +
            (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) ≤ y0 + h0 := by
          simp only [req_h, List.map_cons, List.sum_cons] at h_bound
          have h_sum_h := list_sum_h_nonneg ls'
          have h_g_sum := list_sum_growthOf_nonneg ls'
          split
          · rename_i htg
            have h_div : 0 ≤ h_gap * (ls'.map growthOf).sum / tg :=
              div_nonneg (mul_nonneg hh_gap h_g_sum) (le_of_lt htg)
            have h_ring : h_gap * (growthOf l + (ls'.map growthOf).sum) / tg =
                h_gap * growthOf l / tg + h_gap * (ls'.map growthOf).sum / tg := by ring
            simp_all
            linarith
          · cases j
            · simp_all; linarith
            · simp_all; linarith
            · simp_all; linarith
            · have h_ratio : (i + 1) * h_gap / (n + 1) ≤ h_gap := by
                have hn_pos : 0 < (n : Rat) + 1 := by linarith
                rw [div_le_iff₀ hn_pos]
                simp at hi
                have : ls'.length ≥ 0 := by simp
                rw [mul_comm h_gap (↑n + 1)]
                gcongr
                linarith
              simp_all; linarith
        exact inside_mono p_in hx_sub (by cases j <;> simp_all) hw_sub (by cases j <;> simp_all)
      · have h_req_cons := req_h_cons l ls' h_gap tg
        have h_bound_next : (y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) + req_h ls' h_gap tg ≤ y0 + h0 := by
          linarith
        have hy0_next : y0 ≤ y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
          have : 0 ≤ if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
            split
            · rename_i htg
              have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
              have := bb_h_nonneg l
              linarith
            · exact bb_h_nonneg l
          linarith
        have hw_next : ∀ l' ∈ ls', (boundingBox l').w ≤ w := fun l' hl' => hw_all l' (List.mem_cons_of_mem _ hl')
        exact placeCol_inside ls' j (i + 1) n x _ w w_gap h h_gap tg y0 h0 hy0_next hh_gap h_bound_next hw_next (by simp at hi; omega) p h_ls'
end

theorem place_inside
    (l : Layout) (x y w h : Rat)
    (hw : (boundingBox l).w ≤ w)
    (hh : (boundingBox l).h ≤ h) :
    ∀ p ∈ place l x y w h, inside x y w h p := by
  cases l with
  | obj name w' h' h_wh g h_g a =>
    simp only [place]
    apply place'_inside
    · simp [boundingBox] at hw ⊢; exact hw
    · simp [boundingBox] at hh ⊢; exact hh
  | row ls g h_g a j =>
    simp only [place]
    apply place'_inside <;> assumption
  | col ls g h_g a j =>
    simp only [place]
    apply place'_inside <;> assumption


def SeparatedX (ps1 ps2 : List PlacedObject) : Prop :=
  ∀ a ∈ ps1, ∀ b ∈ ps2, a.x + a.w ≤ b.x

def SeparatedY (ps1 ps2 : List PlacedObject) : Prop :=
  ∀ a ∈ ps1, ∀ b ∈ ps2, a.y + a.h ≤ b.y

lemma SeparatedX_no_overlap {ps1 ps2 : List PlacedObject} (h : SeparatedX ps1 ps2) :
    ∀ a ∈ ps1, ∀ b ∈ ps2, ¬ overlap a b := by
  intro a ha b hb ho
  dsimp [overlap] at ho
  have hsep := h a ha b hb
  linarith

lemma SeparatedY_no_overlap {ps1 ps2 : List PlacedObject} (h : SeparatedY ps1 ps2) :
    ∀ a ∈ ps1, ∀ b ∈ ps2, ¬ overlap a b := by
  intro a ha b hb ho
  dsimp [overlap] at ho
  have hsep := h a ha b hb
  linarith

lemma pairwise_append_no_overlap {ps1 ps2 : List PlacedObject}
    (h1 : ps1.Pairwise (fun a b => ¬ overlap a b))
    (h2 : ps2.Pairwise (fun a b => ¬ overlap a b))
    (h_sep : ∀ a ∈ ps1, ∀ b ∈ ps2, ¬ overlap a b) :
    (ps1 ++ ps2).Pairwise (fun a b => ¬ overlap a b) := by
  induction ps1 with
  | nil => exact h2
  | cons x xs ih =>
    rw [List.pairwise_cons] at h1
    rw [List.cons_append, List.pairwise_cons]
    refine ⟨?_, ih h1.2 (fun a ha b hb => h_sep a (List.mem_cons_of_mem x ha) b hb)⟩
    intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact h1.1 y hy
    · exact h_sep x List.mem_cons_self y hy

def insideX (x w : Rat) (p : PlacedObject) : Prop :=
  x ≤ p.x ∧ p.x + p.w ≤ x + w

def insideY (y h : Rat) (p : PlacedObject) : Prop :=
  y ≤ p.y ∧ p.y + p.h ≤ y + h

mutual
  theorem place'_insideX
      (l : Layout) (x y w h : Rat)
      (hw : (boundingBox l).w ≤ w) :
      ∀ p ∈ place' l x y w h, insideX x w p := by
    match l with
    | .obj name w' h' h_wh g h_g a =>
      intro p hp
      simp only [place', List.mem_singleton] at hp
      subst hp
      simp [boundingBox] at hw
      exact ⟨le_refl x, by linarith⟩
    | .row ls g h_g a j =>
      intro p hp
      simp only [place'] at hp
      let w_gap := max 0 (w - (boundingBox (.row ls)).w)
      let h_gap := max 0 (h - (boundingBox (.row ls)).h)
      let tg := (ls.map growthOf).sum
      have hw_gap : 0 ≤ w_gap := le_max_left 0 _
      have h_req : x + req_w ls w_gap tg ≤ x + w := by
        dsimp [req_w]
        split
        · rename_i htg
          have : w_gap = w - (boundingBox (.row ls)).w := max_eq_right (by simp [boundingBox] at hw ⊢; exact hw)
          have h_sum : (ls.map fun l => (boundingBox l).w).sum = (boundingBox (.row ls)).w := by simp [boundingBox]; rfl
          rw [h_sum, this]
          have h_mul : (w - (boundingBox (.row ls)).w) * (ls.map growthOf).sum / (ls.map growthOf).sum = w - (boundingBox (.row ls)).w :=
            mul_div_cancel_right₀ _ (ne_of_gt htg)
          linarith
        · have : w_gap = w - (boundingBox (.row ls)).w := max_eq_right (by simp [boundingBox] at hw ⊢; exact hw)
          have h_sum : (ls.map fun l => (boundingBox l).w).sum = (boundingBox (.row ls)).w := by simp [boundingBox]; rfl
          rw [h_sum, this]
          linarith
      exact placeRow_insideX ls j 0 ls.length x y w w_gap h h_gap tg x w (le_refl x) hw_gap h_req (by simp) p hp
    | .col ls g h_g a j =>
      intro p hp
      simp only [place'] at hp
      let w_gap := max 0 (w - (boundingBox (.col ls)).w)
      let h_gap := max 0 (h - (boundingBox (.col ls)).h)
      let tg := (ls.map growthOf).sum
      have h_w : ∀ l' ∈ ls, (boundingBox l').w ≤ w := by
        intro l' hl'
        apply le_trans ?_ hw
        simp [boundingBox]
        apply le_max_getD_0
        exact List.mem_map_of_mem hl'
      exact placeCol_insideX ls j 0 ls.length x y w w_gap h h_gap tg x w (le_refl x) (le_refl _) h_w p hp

  theorem placeRow_insideX
      (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat)
      (x0 w0 : Rat)
      (hx0 : x0 ≤ x)
      (hw_gap : 0 ≤ w_gap)
      (h_bound : x + req_w ls w_gap tg ≤ x0 + w0)
      (hi : i + ls.length ≤ n) :
      ∀ p ∈ placeRow ls j i n x y w w_gap h h_gap tg, insideX x0 w0 p := by
    cases ls with
    | nil => simp [placeRow]
    | cons l ls' =>
      intro p hp
      simp only [placeRow, List.mem_append] at hp
      rcases hp with h_l | h_ls'
      · have hw' : (boundingBox l).w ≤ if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
          split
          · rename_i htg
            have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
            linarith
          · exact le_refl _
        have p_in := place'_insideX l _ _ _ _ hw' p h_l
        have hx_sub : x0 ≤ if tg > 0 then x else match j with
            | .start => x
            | .center => x + w_gap / 2
            | .end => x + w_gap
            | .spaced => x + (i + 1) * w_gap / (n + 1) := by
          split
          · exact hx0
          · cases j <;> (try linarith)
            · have : 0 ≤ (i + 1) * w_gap / (n + 1) := div_nonneg (mul_nonneg (by linarith) hw_gap) (by linarith)
              linarith
        have hw_sub : (if tg > 0 then x else match j with
            | .start => x
            | .center => x + w_gap / 2
            | .end => x + w_gap
            | .spaced => x + (i + 1) * w_gap / (n + 1)) +
            (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) ≤ x0 + w0 := by
          simp only [req_w, List.map_cons, List.sum_cons] at h_bound
          have h_sum_w := list_sum_w_nonneg ls'
          have h_g_sum := list_sum_growthOf_nonneg ls'
          split
          · rename_i htg
            have h_div : 0 ≤ w_gap * (ls'.map growthOf).sum / tg :=
              div_nonneg (mul_nonneg hw_gap h_g_sum) (le_of_lt htg)
            have h_ring : w_gap * (growthOf l + (ls'.map growthOf).sum) / tg =
                w_gap * growthOf l / tg + w_gap * (ls'.map growthOf).sum / tg := by ring
            simp_all
            linarith
          · cases j
            · simp_all; linarith
            · simp_all; linarith
            · simp_all; linarith
            · have h_ratio : (i + 1) * w_gap / (n + 1) ≤ w_gap := by
                have hn_pos : 0 < (n : Rat) + 1 := by linarith
                rw [div_le_iff₀ hn_pos]
                rw [mul_comm w_gap (↑n + 1)]
                gcongr
                linarith
              simp_all; linarith
        obtain ⟨h1, h2⟩ := p_in
        exact ⟨le_trans hx_sub (by cases j <;> simpa using h1), le_trans h2 (by cases j <;> simpa using hw_sub)⟩
      · have h_req_cons := req_w_cons l ls' w_gap tg
        have h_bound_next : (x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) + req_w ls' w_gap tg ≤ x0 + w0 := by
          linarith
        have hx0_next : x0 ≤ x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
          have : 0 ≤ if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
            split
            · rename_i htg
              have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
              have := bb_w_nonneg l
              linarith
            · exact bb_w_nonneg l
          linarith
        exact placeRow_insideX ls' j (i + 1) n _ y w w_gap h h_gap tg x0 w0 hx0_next hw_gap h_bound_next (by simp at hi; omega) p h_ls'

  theorem placeCol_insideX
      (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat)
      (x0 w0 : Rat)
      (hx0 : x0 ≤ x)
      (hxw : x + w ≤ x0 + w0)
      (hw_all : ∀ l ∈ ls, (boundingBox l).w ≤ w) :
      ∀ p ∈ placeCol ls j i n x y w w_gap h h_gap tg, insideX x0 w0 p := by
    cases ls with
    | nil => simp [placeCol]
    | cons l ls' =>
      intro p hp
      simp only [placeCol, List.mem_append] at hp
      rcases hp with h_l | h_ls'
      · have hbw : (boundingBox l).w ≤ w := hw_all l List.mem_cons_self
        have hw' : (boundingBox l).w ≤ if alignOf l = .stretch then w else (boundingBox l).w := by
          split
          · exact hbw
          · exact le_refl _
        have p_in := place'_insideX l _ _ _ _ hw' p h_l
        have hx_sub : x0 ≤ match alignOf l with
            | .start => x
            | .center => x + (w - (boundingBox l).w) / 2
            | .end => x + (w - (boundingBox l).w)
            | .stretch => x := by
          first
            | (split <;> linarith)
            | (cases hl : alignOf l <;> simp <;> linarith)
        have hw_sub : (match alignOf l with
            | .start => x
            | .center => x + (w - (boundingBox l).w) / 2
            | .end => x + (w - (boundingBox l).w)
            | .stretch => x) + (if alignOf l = .stretch then w else (boundingBox l).w) ≤ x0 + w0 := by
          first
            | (cases hl : alignOf l <;> simp <;> linarith)
        obtain ⟨h1, h2⟩ := p_in
        exact ⟨le_trans hx_sub h1, le_trans h2 hw_sub⟩
      · have hw_next : ∀ l' ∈ ls', (boundingBox l').w ≤ w := fun l' hl' => hw_all l' (List.mem_cons_of_mem _ hl')
        exact placeCol_insideX ls' j (i + 1) n x _ w w_gap h h_gap tg x0 w0 hx0 hxw hw_next p h_ls'
end

mutual
  theorem place'_insideY
      (l : Layout) (x y w h : Rat)
      (hh : (boundingBox l).h ≤ h) :
      ∀ p ∈ place' l x y w h, insideY y h p := by
    match l with
    | .obj name w' h' h_wh g h_g a =>
      intro p hp
      simp only [place', List.mem_singleton] at hp
      subst hp
      simp [boundingBox] at hh
      exact ⟨le_refl y, by linarith⟩
    | .row ls g h_g a j =>
      intro p hp
      simp only [place'] at hp
      let w_gap := max 0 (w - (boundingBox (.row ls)).w)
      let h_gap := max 0 (h - (boundingBox (.row ls)).h)
      let tg := (ls.map growthOf).sum
      have h_h : ∀ l' ∈ ls, (boundingBox l').h ≤ h := by
        intro l' hl'
        apply le_trans ?_ hh
        simp [boundingBox]
        apply le_max_getD_0
        exact List.mem_map_of_mem hl'
      exact placeRow_insideY ls j 0 ls.length x y w w_gap h h_gap tg y h (le_refl y) (le_refl _) h_h p hp
    | .col ls g h_g a j =>
      intro p hp
      simp only [place'] at hp
      let w_gap := max 0 (w - (boundingBox (.col ls)).w)
      let h_gap := max 0 (h - (boundingBox (.col ls)).h)
      let tg := (ls.map growthOf).sum
      have hh_gap : 0 ≤ h_gap := le_max_left 0 _
      have h_req : y + req_h ls h_gap tg ≤ y + h := by
        dsimp [req_h]
        split
        · rename_i htg
          have : h_gap = h - (boundingBox (.col ls)).h := max_eq_right (by simp [boundingBox] at hh ⊢; exact hh)
          have h_sum : (ls.map fun l => (boundingBox l).h).sum = (boundingBox (.col ls)).h := by simp [boundingBox]; rfl
          rw [h_sum, this]
          have h_mul : (h - (boundingBox (.col ls)).h) * (ls.map growthOf).sum / (ls.map growthOf).sum = h - (boundingBox (.col ls)).h :=
            mul_div_cancel_right₀ _ (ne_of_gt htg)
          linarith
        · have : h_gap = h - (boundingBox (.col ls)).h := max_eq_right (by simp [boundingBox] at hh ⊢; exact hh)
          have h_sum : (ls.map fun l => (boundingBox l).h).sum = (boundingBox (.col ls)).h := by simp [boundingBox]; rfl
          rw [h_sum, this]
          linarith
      exact placeCol_insideY ls j 0 ls.length x y w w_gap h h_gap tg y h (le_refl y) hh_gap h_req (by simp) p hp

  theorem placeRow_insideY
      (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat)
      (y0 h0 : Rat)
      (hy0 : y0 ≤ y)
      (hyh : y + h ≤ y0 + h0)
      (hh_all : ∀ l ∈ ls, (boundingBox l).h ≤ h) :
      ∀ p ∈ placeRow ls j i n x y w w_gap h h_gap tg, insideY y0 h0 p := by
    cases ls with
    | nil => simp [placeRow]
    | cons l ls' =>
      intro p hp
      simp only [placeRow, List.mem_append] at hp
      rcases hp with h_l | h_ls'
      · have hbh : (boundingBox l).h ≤ h := hh_all l List.mem_cons_self
        have hh' : (boundingBox l).h ≤ if alignOf l = .stretch then h else (boundingBox l).h := by
          split
          · exact hbh
          · exact le_refl _
        have p_in := place'_insideY l _ _ _ _ hh' p h_l
        have hy_sub : y0 ≤ match alignOf l with
            | .start => y
            | .center => y + (h - (boundingBox l).h) / 2
            | .end => y + (h - (boundingBox l).h)
            | .stretch => y := by
          first
            | (split <;> linarith)
            | (cases hl : alignOf l <;> simp <;> linarith)
        have hh_sub : (match alignOf l with
            | .start => y
            | .center => y + (h - (boundingBox l).h) / 2
            | .end => y + (h - (boundingBox l).h)
            | .stretch => y) + (if alignOf l = .stretch then h else (boundingBox l).h) ≤ y0 + h0 := by
          first
            | (cases hl : alignOf l <;> simp <;> linarith)
        obtain ⟨h1, h2⟩ := p_in
        exact ⟨le_trans hy_sub h1, le_trans h2 hh_sub⟩
      · have hh_next : ∀ l' ∈ ls', (boundingBox l').h ≤ h := fun l' hl' => hh_all l' (List.mem_cons_of_mem _ hl')
        exact placeRow_insideY ls' j (i + 1) n _ y w w_gap h h_gap tg y0 h0 hy0 hyh hh_next p h_ls'

  theorem placeCol_insideY
      (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat)
      (y0 h0 : Rat)
      (hy0 : y0 ≤ y)
      (hh_gap : 0 ≤ h_gap)
      (h_bound : y + req_h ls h_gap tg ≤ y0 + h0)
      (hi : i + ls.length ≤ n) :
      ∀ p ∈ placeCol ls j i n x y w w_gap h h_gap tg, insideY y0 h0 p := by
    cases ls with
    | nil => simp [placeCol]
    | cons l ls' =>
      intro p hp
      simp only [placeCol, List.mem_append] at hp
      rcases hp with h_l | h_ls'
      · have hh' : (boundingBox l).h ≤ if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
          split
          · rename_i htg
            have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
            linarith
          · exact le_refl _
        have p_in := place'_insideY l _ _ _ _ hh' p h_l
        have hy_sub : y0 ≤ if tg > 0 then y else match j with
            | .start => y
            | .center => y + h_gap / 2
            | .end => y + h_gap
            | .spaced => y + (i + 1) * h_gap / (n + 1) := by
          split
          · exact hy0
          · cases j <;> (try linarith)
            · have : 0 ≤ (i + 1) * h_gap / (n + 1) := div_nonneg (mul_nonneg (by linarith) hh_gap) (by linarith)
              linarith
        have hh_sub : (if tg > 0 then y else match j with
            | .start => y
            | .center => y + h_gap / 2
            | .end => y + h_gap
            | .spaced => y + (i + 1) * h_gap / (n + 1)) +
            (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) ≤ y0 + h0 := by
          simp only [req_h, List.map_cons, List.sum_cons] at h_bound
          have h_sum_h := list_sum_h_nonneg ls'
          have h_g_sum := list_sum_growthOf_nonneg ls'
          split
          · rename_i htg
            have h_div : 0 ≤ h_gap * (ls'.map growthOf).sum / tg :=
              div_nonneg (mul_nonneg hh_gap h_g_sum) (le_of_lt htg)
            have h_ring : h_gap * (growthOf l + (ls'.map growthOf).sum) / tg =
                h_gap * growthOf l / tg + h_gap * (ls'.map growthOf).sum / tg := by ring
            simp_all
            linarith
          · cases j
            · simp_all; linarith
            · simp_all; linarith
            · simp_all; linarith
            · have h_ratio : (i + 1) * h_gap / (n + 1) ≤ h_gap := by
                have hn_pos : 0 < (n : Rat) + 1 := by linarith
                rw [div_le_iff₀ hn_pos]
                simp at hi
                have : ls'.length ≥ 0 := by simp
                rw [mul_comm h_gap (↑n + 1)]
                gcongr
                linarith
              simp_all; linarith
        obtain ⟨h1, h2⟩ := p_in
        exact ⟨le_trans hy_sub (by cases j <;> simpa using h1), le_trans h2 (by cases j <;> simpa using hh_sub)⟩
      · have h_req_cons := req_h_cons l ls' h_gap tg
        have h_bound_next : (y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) + req_h ls' h_gap tg ≤ y0 + h0 := by
          linarith
        have hy0_next : y0 ≤ y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
          have : 0 ≤ if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
            split
            · rename_i htg
              have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
              have := bb_h_nonneg l
              linarith
            · exact bb_h_nonneg l
          linarith
        exact placeCol_insideY ls' j (i + 1) n x _ w w_gap h h_gap tg y0 h0 hy0_next hh_gap h_bound_next (by simp at hi; omega) p h_ls'
end

def rowX' (j : Justify) (i n : Nat) (x w_gap tg : Rat) : Rat :=
  if tg > 0 then x else
  match j with
  | .start => x
  | .center => x + w_gap / 2
  | .end => x + w_gap
  | .spaced => x + (i + 1) * w_gap / (n + 1)

lemma rowX'_step (j : Justify) (i n : Nat) (x w_gap tg w' : Rat) (hw_gap : 0 ≤ w_gap) :
    rowX' j i n x w_gap tg + w' ≤ rowX' j (i + 1) n (x + w') w_gap tg := by
  dsimp [rowX']
  split
  · linarith
  · cases j
    · linarith
    · linarith
    · linarith
    · have hn : 0 < (n : Rat) + 1 := by linarith
      have h_nonneg : 0 ≤ w_gap / (n + 1) := div_nonneg hw_gap (le_of_lt hn)
      have h_ring : (i + 2 : Rat) * w_gap / (n + 1) = (i + 1 : Rat) * w_gap / (n + 1) + w_gap / (n + 1) := by ring
      have h_ring' : ((i : Rat) + 1 + 1) * w_gap / (n + 1) = (i + 1 : Rat) * w_gap / (n + 1) + w_gap / (n + 1) := by ring
      first
        | (simp; rw [show (i : Rat) + 1 + 1 = (i : Rat) + 2 by linarith]; rw [h_ring]; linarith)

theorem placeRow_min_rowX' (ls : List Layout) (j : Justify) (i n : Nat)
    (x y w w_gap h h_gap tg : Rat) (hw_gap : 0 ≤ w_gap) :
    ∀ p ∈ placeRow ls j i n x y w w_gap h h_gap tg, rowX' j i n x w_gap tg ≤ p.x := by
  induction ls generalizing i x with
  | nil => simp [placeRow]
  | cons l ls' ih =>
    intro p hp
    simp only [placeRow, List.mem_append] at hp
    rcases hp with h_l | h_ls'
    · have hw' : (boundingBox l).w ≤ if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
        split
        · rename_i htg
          have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
          linarith
        · exact le_refl _
      have p_in := place'_insideX l _ _ _ _ hw' p h_l
      change rowX' j i n x w_gap tg ≤ p.x
      obtain ⟨h1, _⟩ := p_in
      exact h1
    · have hW : 0 ≤ (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) := by
        split
        · rename_i htg
          have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
          have := bb_w_nonneg l
          linarith
        · exact bb_w_nonneg l
      have h_step := rowX'_step j i n x w_gap tg (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) hw_gap
      have ih_p := ih (i + 1) (x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) p h_ls'
      exact le_trans (le_trans (le_add_of_nonneg_right hW) h_step) ih_p

def colY' (j : Justify) (i n : Nat) (y h_gap tg : Rat) : Rat :=
  if tg > 0 then y else
  match j with
  | .start => y
  | .center => y + h_gap / 2
  | .end => y + h_gap
  | .spaced => y + (i + 1) * h_gap / (n + 1)

lemma colY'_step (j : Justify) (i n : Nat) (y h_gap tg h' : Rat) (hh_gap : 0 ≤ h_gap) :
    colY' j i n y h_gap tg + h' ≤ colY' j (i + 1) n (y + h') h_gap tg := by
  dsimp [colY']
  split
  · linarith
  · cases j
    · linarith
    · linarith
    · linarith
    · have hn : 0 < (n : Rat) + 1 := by linarith
      have h_nonneg : 0 ≤ h_gap / (n + 1) := div_nonneg hh_gap (le_of_lt hn)
      have h_ring : (i + 2 : Rat) * h_gap / (n + 1) = (i + 1 : Rat) * h_gap / (n + 1) + h_gap / (n + 1) := by ring
      simp
      rw [show (i : Rat) + 1 + 1 = (i : Rat) + 2 by linarith]
      rw [h_ring]
      linarith

theorem placeCol_min_colY' (ls : List Layout) (j : Justify) (i n : Nat)
    (x y w w_gap h h_gap tg : Rat) (hh_gap : 0 ≤ h_gap) :
    ∀ p ∈ placeCol ls j i n x y w w_gap h h_gap tg, colY' j i n y h_gap tg ≤ p.y := by
  induction ls generalizing i y with
  | nil => simp [placeCol]
  | cons l ls' ih =>
    intro p hp
    simp only [placeCol, List.mem_append] at hp
    rcases hp with h_l | h_ls'
    · have hh' : (boundingBox l).h ≤ if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
        split
        · rename_i htg
          have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
          linarith
        · exact le_refl _
      have p_in := place'_insideY l _ _ _ _ hh' p h_l
      change colY' j i n y h_gap tg ≤ p.y
      obtain ⟨h1, _⟩ := p_in
      exact h1
    · have hH : 0 ≤ (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) := by
        split
        · rename_i htg
          have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
          have := bb_h_nonneg l
          linarith
        · exact bb_h_nonneg l
      have h_step := colY'_step j i n y h_gap tg (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) hh_gap
      have ih_p := ih (i + 1) (y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) p h_ls'
      exact le_trans (le_trans (le_add_of_nonneg_right hH) h_step) ih_p

mutual
  theorem place'_no_overlap (l : Layout) (x y w h : Rat) :
      (place' l x y w h).Pairwise (fun a b => ¬ overlap a b) := by
    cases l with
    | obj name w' h' h_wh g h_g a =>
      simp [place']
    | row ls g h_g a j =>
      simp only [place']
      exact placeRow_no_overlap ls j 0 ls.length x y w (max 0 (w - (boundingBox (.row ls)).w)) h (max 0 (h - (boundingBox (.row ls)).h)) (ls.map growthOf).sum (le_max_left 0 _)
    | col ls g h_g a j =>
      simp only [place']
      exact placeCol_no_overlap ls j 0 ls.length x y w (max 0 (w - (boundingBox (.col ls)).w)) h (max 0 (h - (boundingBox (.col ls)).h)) (ls.map growthOf).sum (le_max_left 0 _)

  theorem placeRow_no_overlap (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat) (hw_gap : 0 ≤ w_gap) :
      (placeRow ls j i n x y w w_gap h h_gap tg).Pairwise (fun a b => ¬ overlap a b) := by
    cases ls with
    | nil => simp [placeRow]
    | cons l ls' =>
      simp only [placeRow]
      have hw' : (boundingBox l).w ≤ if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w := by
        split
        · rename_i htg
          have : 0 ≤ w_gap * growthOf l / tg := div_nonneg (mul_nonneg hw_gap (growthOf_nonneg l)) (le_of_lt htg)
          linarith
        · exact le_refl _
      have h1 := place'_no_overlap l
        (if tg > 0 then x else match j with | .start => x | .center => x + w_gap / 2 | .end => x + w_gap | .spaced => x + (i + 1) * w_gap / (n + 1))
        (match alignOf l with | .start => y | .center => y + (h - (boundingBox l).h) / 2 | .end => y + (h - (boundingBox l).h) | .stretch => y)
        (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w)
        (if alignOf l = .stretch then h else (boundingBox l).h)
      have h2 := placeRow_no_overlap ls' j (i + 1) n
        (x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w)
        y w w_gap h h_gap tg hw_gap
      have h_sep : ∀ a ∈ place' l
        (if tg > 0 then x else match j with | .start => x | .center => x + w_gap / 2 | .end => x + w_gap | .spaced => x + (i + 1) * w_gap / (n + 1))
        (match alignOf l with | .start => y | .center => y + (h - (boundingBox l).h) / 2 | .end => y + (h - (boundingBox l).h) | .stretch => y)
        (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w)
        (if alignOf l = .stretch then h else (boundingBox l).h),
        ∀ b ∈ placeRow ls' j (i + 1) n
        (x + if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w)
        y w w_gap h h_gap tg,
        ¬ overlap a b := by
        apply SeparatedX_no_overlap
        intro a ha b hb
        have ha_in := place'_insideX l _ _ _ _ hw' a ha
        have hb_min := placeRow_min_rowX' ls' j (i + 1) n _ y w w_gap h h_gap tg hw_gap b hb
        have h_step := rowX'_step j i n x w_gap tg (if tg > 0 then (boundingBox l).w + w_gap * growthOf l / tg else (boundingBox l).w) hw_gap
        obtain ⟨_, ha2⟩ := ha_in
        exact le_trans ha2 (le_trans h_step hb_min)
      exact pairwise_append_no_overlap h1 h2 h_sep

  theorem placeCol_no_overlap (ls : List Layout) (j : Justify) (i n : Nat)
      (x y w w_gap h h_gap tg : Rat) (hh_gap : 0 ≤ h_gap) :
      (placeCol ls j i n x y w w_gap h h_gap tg).Pairwise (fun a b => ¬ overlap a b) := by
    cases ls with
    | nil => simp [placeCol]
    | cons l ls' =>
      simp only [placeCol]
      have hh' : (boundingBox l).h ≤ if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h := by
        split
        · rename_i htg
          have : 0 ≤ h_gap * growthOf l / tg := div_nonneg (mul_nonneg hh_gap (growthOf_nonneg l)) (le_of_lt htg)
          linarith
        · exact le_refl _
      have h1 := place'_no_overlap l       (match alignOf l with | .start => x | .center => x + (w - (boundingBox l).w) / 2 | .end => x + (w - (boundingBox l).w) | .stretch => x)
        (if tg > 0 then y else match j with | .start => y | .center => y + h_gap / 2 | .end => y + h_gap | .spaced => y + (i + 1) * h_gap / (n + 1))
        (if alignOf l = .stretch then w else (boundingBox l).w)
        (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h)
      have h2 := placeCol_no_overlap ls' j (i + 1) n x
        (y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h)
        w w_gap h h_gap tg hh_gap
      have h_sep : ∀ a ∈ place' l
        (match alignOf l with | .start => x | .center => x + (w - (boundingBox l).w) / 2 | .end => x + (w - (boundingBox l).w) | .stretch => x)
        (if tg > 0 then y else match j with | .start => y | .center => y + h_gap / 2 | .end => y + h_gap | .spaced => y + (i + 1) * h_gap / (n + 1))
        (if alignOf l = .stretch then w else (boundingBox l).w)
        (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h),
        ∀ b ∈ placeCol ls' j (i + 1) n x
        (y + if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h)
        w w_gap h h_gap tg,
        ¬ overlap a b := by
        apply SeparatedY_no_overlap
        intro a ha b hb
        have ha_in := place'_insideY l _ _ _ _ hh' a ha
        have hb_min := placeCol_min_colY' ls' j (i + 1) n x _ w w_gap h h_gap tg hh_gap b hb
        have h_step := colY'_step j i n y h_gap tg (if tg > 0 then (boundingBox l).h + h_gap * growthOf l / tg else (boundingBox l).h) hh_gap
        obtain ⟨_, ha2⟩ := ha_in
        exact le_trans ha2 (le_trans h_step hb_min)
      exact pairwise_append_no_overlap h1 h2 h_sep
end

theorem place_no_overlap (l : Layout) (x y w h : Rat) :
    (place l x y w h).Pairwise (fun a b => ¬ overlap a b) := by
  cases l with
  | obj name w' h' h_wh g h_g a =>
    simp only [place]
    exact place'_no_overlap (.row [.obj name w' h' h_wh g h_g a]) x y w h
  | row ls g h_g a j =>
    simp only [place]
    exact place'_no_overlap (.row ls g h_g a j) x y w h
  | col ls g h_g a j =>
    simp only [place]
    exact place'_no_overlap (.col ls g h_g a j) x y w h
