import Aesop

inductive Align
| start
| «end»
| center
| stretch
deriving DecidableEq, Repr

inductive Justify
| start
| «end»
| center
| spaced
deriving DecidableEq, Repr

inductive Layout
| obj (name : String)
      (w h : Rat)
      (h_wh : w ≥ 0 ∧ h ≥ 0 := by aesop)
      (g : Rat := 0)
      (h_g : g ≥ 0 := by aesop)
      (a : Align := .start)
| row (children : List Layout)
      (g : Rat := 0) (h_g : g ≥ 0 := by aesop)
      (a : Align := .start)
      (j : Justify := .start)
| col (children : List Layout)
      (g : Rat := 0) (h_g : g ≥ 0 := by aesop)
      (a : Align := .start)
      (j : Justify := .start)
deriving Repr

structure BoundingBox where
  w : Rat
  h : Rat
deriving DecidableEq, Repr

def boundingBox : Layout → BoundingBox
| .obj _ w h .. => ⟨w, h⟩
| .row ls .. =>
  let bbs := ls.map boundingBox
  ⟨bbs.map (BoundingBox.w) |>.sum,
   bbs.map (BoundingBox.h) |>.max?.getD 0⟩
| .col ls .. =>
  let bbs := ls.map boundingBox
  ⟨bbs.map (BoundingBox.w) |>.max?.getD 0,
   bbs.map (BoundingBox.h) |>.sum⟩

def sampleMenu : Layout :=
  .row [
    .col [ .obj "A" 300 200, .obj "B" 200 600 ],
    .obj "C" 100 400
  ]

example : boundingBox sampleMenu = ⟨400, 800⟩ := by
  native_decide

structure PlacedObject where
  name : String
  (x y : Rat)
  (w h : Rat)
deriving DecidableEq, Repr

def growthOf (l : Layout) : Rat :=
  match l with
  | .obj (g := g) .. => g
  | .row (g := g) .. => g
  | .col (g := g) .. => g

def alignOf (l : Layout) : Align :=
  match l with
  | .obj (a := a) .. => a
  | .row (a := a) .. => a
  | .col (a := a) .. => a

mutual
  def place' (l : Layout) (x y w h : Rat) : List PlacedObject :=
    match l with
    | .obj name .. =>
      [⟨name, x, y, w, h⟩]
    | .row ls (j := j) .. =>
      let bb := boundingBox (.row ls)
      let w_gap := max 0 (w - bb.w)
      let h_gap := max 0 (h - bb.h)
      let tg := (ls.map growthOf).sum
      placeRow ls j 0 ls.length x y w w_gap h h_gap tg
    | .col ls (j := j) .. =>
      let bb := boundingBox (.col ls)
      let w_gap := max 0 (w - bb.w)
      let h_gap := max 0 (h - bb.h)
      let tg := (ls.map growthOf).sum
      placeCol ls j 0 ls.length x y w w_gap h h_gap tg

  def placeRow (ls : List Layout) (j : Justify) (i n : Nat) (x y w w_gap h h_gap tg : Rat) : List PlacedObject :=
    match ls with
    | [] => []
    | l :: ls =>
      let bb := boundingBox l
      let w' :=
        if tg > 0 then
          bb.w + w_gap * (growthOf l) / tg
        else
          bb.w
      let y' :=
        match alignOf l with
        | .start => y
        | .center => y + (h - bb.h) / 2
        | .end => y + (h - bb.h)
        | .stretch => y
      let h' :=
        if alignOf l = .stretch then h else bb.h
      let x' :=
        if tg > 0 then
          x
        else
          match j with
          | .start => x
          | .center => x + w_gap / 2
          | .end => x + w_gap
          | .spaced => x + (i + 1) * w_gap / (n + 1)
      place' l x' y' w' h' ++ placeRow ls j (i + 1) n (x + w') y w w_gap h h_gap tg

  def placeCol (ls : List Layout) (j : Justify) (i n : Nat) (x y w w_gap h h_gap tg : Rat) : List PlacedObject :=
    match ls with
    | [] => []
    | l :: ls =>
      let bb := boundingBox l
      let h' :=
        if tg > 0 then
          bb.h + h_gap * (growthOf l) / tg
        else
          bb.h
      let x' :=
        match alignOf l with
        | .start => x
        | .center => x + (w - bb.w) / 2
        | .end => x + (w - bb.w)
        | .stretch => x
      let w' :=
        if alignOf l = .stretch then w else bb.w
      let y' :=
        if tg > 0 then
          y
        else
          match j with
          | .start => y
          | .center => y + h_gap / 2
          | .end => y + h_gap
          | .spaced => y + (i + 1) * h_gap / (n + 1)
      place' l x' y' w' h' ++ placeCol ls j (i + 1) n x (y + h') w w_gap h h_gap tg
end

def place (l : Layout) (x y w h : Rat) : List PlacedObject :=
  match l with
  | .obj .. =>
    place' (.row [l]) x y w h
  | .col .. | .row .. =>
    place' l x y w h

-- 400x100 row
def sampleMenu2 : Layout :=
  .row (j := .center) [
    .obj (a := .start) "A" 100 100,
    .obj (a := .center) "B" 100 100,
    .obj (a := .end) "C" 100 100,
    .obj (a := .stretch) "D" 100 100,
  ]

