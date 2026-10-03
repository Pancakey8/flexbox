import Layout
import Batteries.Data.Float.Rat

def parseAlign : String → Align
| "s" => .start
| "e" => .end
| "c" => .center
| "t" => .stretch
| _ => .start

def parseJustify : String → Justify
| "s" => .start
| "e" => .end
| "c" => .center
| "p" => .spaced
| _ => .start

partial
def parseLayout (tokens : List String) : Option (Layout × List String) :=
  match tokens with
  | "O" :: name :: w :: h :: g :: a :: ts =>
    let w' := w.toNat?.getD 0
    let h' := h.toNat?.getD 0
    let g' := g.toNat?.getD 0
    let a' := parseAlign a
    .some (.obj name w' h' (by aesop) g' (by aesop) a', ts)
  | "R" :: g :: a :: j :: n :: ts => do
    let g' := g.toNat?.getD 0
    let a' := parseAlign a
    let j' := parseJustify j
    let n' := n.toNat?.getD 0
    let (cs, ts') ←
      (List.range n').foldlM (init := ([], ts)) λ (cs, ts) i => do
        let (c, ts') ← parseLayout ts
        some (cs ++ [c], ts')
    some (.row cs g' (by aesop) a' j', ts')
  | "C" :: g :: a :: j :: n :: ts => do
    let g' := g.toNat?.getD 0
    let a' := parseAlign a
    let j' := parseJustify j
    let n' := n.toNat?.getD 0
    let (cs, ts') ←
      (List.range n').foldlM (init := ([], ts)) λ (cs, ts) i => do
        let (c, ts') ← parseLayout ts
        some (cs ++ [c], ts')
    some (.col cs g' (by aesop) a' j', ts')
  | _ => none

def formatSvg (p : PlacedObject) : String :=
  s!"|{p.name},{p.x.toFloat},{p.y.toFloat},{p.w.toFloat},{p.h.toFloat}"

def main (args : List String) : IO Unit := do
  let input := args.getD 0 ""
  let x := (args.getD 1 "0").toNat?.getD 0
  let y := (args.getD 2 "0").toNat?.getD 0
  let w := (args.getD 3 "0").toNat?.getD 0
  let h := (args.getD 4 "0").toNat?.getD 0
  let tokens := input.splitOn " " |>.filter (· ≠ "")
  -- IO.println (repr tokens)
  match parseLayout tokens with
  | some (l, _) =>
    let w' := max (boundingBox l).w w
    let h' := max (boundingBox l).h h
    let result := place l x y w' h' |>.map formatSvg |> String.join
    IO.println result
  | none =>
    IO.eprintln "Failed to parse layout"
    IO.Process.exit 1
