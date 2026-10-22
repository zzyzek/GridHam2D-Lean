/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Challenge: the Itai–Papadimitriou–Szwarcfiter characterization

The statement `GridHam.ips_characterization` at the end of this file is Theorem 3.2 of A. Itai,
C. H. Papadimitriou and J. L. Szwarcfiter, *Hamilton paths in grid graphs*, SIAM J. Comput. 11
(1982), 676–686: for distinct vertices `s`
and `t` of the `width × height` rectangular grid graph, a Hamiltonian path from `s` to `t` exists
exactly when the problem is acceptable, that is, colour compatible and not forbidden (the
paper's F1, F2, F3).

Coordinates are 0-indexed: the vertices are `(x, y)` with `x < width` and `y < height`, and two
vertices are adjacent when they differ by `1` in exactly one coordinate. A Hamiltonian path is a
list of vertices (`ValidPath`) that visits every vertex once, starts at `s`, ends at `t`, and
steps between adjacent vertices. The paper's `R(m, n)` is `width = m`, `height = n`, with its
1-indexed `(x, y)` at `(x - 1, y - 1)` here. The paper states F3 up to isomorphism of the grid.
`ForbiddenCase3` writes the reflections out (either dimension may be the one equal to `3`, and
`t` may lie on either side of `s`).

The definitions are copied verbatim from the library module `GridHam.Defs`.
-/

namespace GridHam

/-! ### The grid and Hamiltonian paths -/

/-- A grid vertex, given as `(x, y)` coordinates. -/
abbrev Coord := ℕ × ℕ

/-- `v` lies within a `width × height` grid (`0 ≤ x < width`, `0 ≤ y < height`, with the lower
bound automatic since coordinates are natural numbers). -/
def InBounds (width height : ℕ) (v : Coord) : Prop :=
  v.1 < width ∧ v.2 < height

instance : DecidablePred (fun v => InBounds width height v) :=
  fun v => by unfold InBounds; infer_instance

/-- Two vertices are grid-adjacent: they differ by exactly 1 in exactly one coordinate. -/
def Adjacent (v w : Coord) : Prop :=
  (v.1 = w.1 ∧ (v.2 + 1 = w.2 ∨ w.2 + 1 = v.2)) ∨
  (v.2 = w.2 ∧ (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1))

instance : DecidableRel Adjacent := fun v w => by unfold Adjacent; infer_instance

/-- `Adjacent` as a `Bool`, for use inside the recursive chain check below. -/
def adjacentB (v w : Coord) : Bool := decide (Adjacent v w)

/-- Every consecutive pair in `p` is adjacent, checked by direct recursion on the list. -/
def chainAdjacent : List Coord → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => adjacentB a b && chainAdjacent (b :: rest)

/-- Every coordinate of a `width × height` grid, as a flat list. -/
def allCoords (width height : ℕ) : List Coord :=
  (List.range width).flatMap (fun x => (List.range height).map (fun y => (x, y)))

/-- `p` is a Hamiltonian path from `s` to `t` in the `width × height` grid graph:

* it has exactly `width * height` vertices (one for every grid vertex),
* it starts at `s` and ends at `t`,
* it has no repeated vertex,
* every vertex it contains is in bounds,
* every in-bounds vertex is contained in it (together with the previous two conditions, this
  makes `p` a permutation of the whole grid),
* every consecutive pair is grid-adjacent.
-/
def ValidPath (width height : ℕ) (s t : Coord) (p : List Coord) : Prop :=
  p.length = width * height ∧
  p.head? = some s ∧
  p.getLast? = some t ∧
  p.Nodup ∧
  (∀ v ∈ p, InBounds width height v) ∧
  (∀ v ∈ allCoords width height, v ∈ p) ∧
  chainAdjacent p = true

/-- A Hamiltonian path exists between `s` and `t` in the `width × height` grid graph. -/
def HasHamPath (width height : ℕ) (s t : Coord) : Prop :=
  ∃ p, ValidPath width height s t p

instance : DecidablePred (fun p => ValidPath width height s t p) :=
  fun p => by unfold ValidPath; infer_instance

/-! ### Colour compatibility -/

/-- The checkerboard color of a vertex: `0` or `1`. -/
def parity (v : Coord) : ℕ := (v.1 + v.2) % 2

/-- Colour compatibility (the paper, Section 3.1). If the grid has an odd number of vertices,
both endpoints have the colour of the corners (`0`). Otherwise the endpoints have different
colours. -/
def ColorCompatible (width height : ℕ) (s t : Coord) : Prop :=
  if (width * height) % 2 = 1 then
    parity s = 0 ∧ parity t = 0
  else
    parity s ≠ parity t

instance : DecidablePred (fun p : Coord × Coord => ColorCompatible width height p.1 p.2) :=
  fun p => by unfold ColorCompatible; infer_instance

/-! ### Forbidden cases -/

/-- `v` is one of the four corners of the `width × height` grid. -/
def IsCorner (width height : ℕ) (v : Coord) : Prop :=
  v = (0, 0) ∨ v = (width - 1, 0) ∨ v = (0, height - 1) ∨ v = (width - 1, height - 1)

instance : DecidablePred (fun v => IsCorner width height v) :=
  fun v => by unfold IsCorner; infer_instance

/-- The paper's F1, used when `width = 1` or `height = 1`: `{s, t}` is not the pair of the two
ends `(0, 0)` and `far` of the line, that is, `s` or `t` is not a corner. -/
def ForbiddenCase1 (width height : ℕ) (s t : Coord) : Prop :=
  let isW := width = 1
  let bound := if isW then height else width
  let far : Coord := if isW then (0, bound - 1) else (bound - 1, 0)
  ¬ ((s = (0, 0) ∧ t = far) ∨ (s = far ∧ t = (0, 0)))

instance : DecidablePred (fun p : Coord × Coord => ForbiddenCase1 width height p.1 p.2) :=
  fun p => by unfold ForbiddenCase1; infer_instance

/-- The paper's F2, used when `width = 2` or `height = 2`: `st` is an edge across the short
dimension (a rung) and is not on the outer face, that is, neither endpoint is a corner. -/
def ForbiddenCase2 (width height : ℕ) (s t : Coord) : Prop :=
  ¬ IsCorner width height s ∧ ¬ IsCorner width height t ∧
  ((width = 2 ∧ s.2 = t.2) ∨ (height = 2 ∧ s.1 = t.1))

/-- The paper's F3, used when `width = 3` or `height = 3`. The dimension other than `3`
(`oppDim`) is even, and `s` and `t` have different colours. `c0`, `c1` are the coordinates of
`s` and `t` along that dimension, and `oppCoord` is the coordinate of `s` across it (`1` is the
middle line). The distance from `s` to `t` along the long dimension is at least `2`, or at
least `1` when `s` is on the middle line. If `t` is past `s` (`¬ isGreater`), `s` has a colour
different from the corners at `0` (colour `0`). If `t` is before `s`, the grid is read from the
other end, whose corners have colour `1`. -/
def ForbiddenCase3 (width height : ℕ) (s t : Coord) : Prop :=
  let isW := width = 3
  let oppDim := if isW then height else width
  oppDim % 2 = 0 ∧
  parity s ≠ parity t ∧
  ( let c0 := if isW then s.2 else s.1
    let c1 := if isW then t.2 else t.1
    let oppCoord := if isW then s.1 else s.2
    let isGreater := c1 < c0
    let distance := if isGreater then c0 - c1 else c1 - c0
    let distSat := if oppCoord = 1 then distance > 0 else distance > 1
    distSat ∧
    ((isGreater ∧ parity s ≠ 1) ∨ ((¬ isGreater) ∧ parity s ≠ 0)) )

/-- The problem is forbidden (the paper, Section 3.1): the forbidden case for the smallest of
`width` and `height` when it is `1`, `2` or `3`, and never otherwise. -/
def IsForbidden (width height : ℕ) (s t : Coord) : Prop :=
  if width = 1 ∨ height = 1 then ForbiddenCase1 width height s t
  else if width = 2 ∨ height = 2 then ForbiddenCase2 width height s t
  else if width = 3 ∨ height = 3 then ForbiddenCase3 width height s t
  else False

/-- The problem is acceptable (the paper, Section 3.1): colour compatible and not forbidden. -/
def IsAcceptable (width height : ℕ) (s t : Coord) : Prop :=
  ColorCompatible width height s t ∧ ¬ IsForbidden width height s t

/-! Direct (non-`DecidablePred`) instances, so `decide` can evaluate `IsAcceptable w h s t` for
concrete arguments. -/

instance instDecColorCompatible (w h : ℕ) (s t : Coord) :
    Decidable (ColorCompatible w h s t) := by
  unfold ColorCompatible; infer_instance

instance instDecForbiddenCase1 (w h : ℕ) (s t : Coord) :
    Decidable (ForbiddenCase1 w h s t) := by
  unfold ForbiddenCase1; infer_instance

instance instDecForbiddenCase2 (w h : ℕ) (s t : Coord) :
    Decidable (ForbiddenCase2 w h s t) := by
  unfold ForbiddenCase2 IsCorner; infer_instance

instance instDecForbiddenCase3 (w h : ℕ) (s t : Coord) :
    Decidable (ForbiddenCase3 w h s t) := by
  unfold ForbiddenCase3; infer_instance

instance instDecIsForbidden (w h : ℕ) (s t : Coord) :
    Decidable (IsForbidden w h s t) := by
  unfold IsForbidden; infer_instance

instance instDecIsAcceptable (w h : ℕ) (s t : Coord) :
    Decidable (IsAcceptable w h s t) := by
  unfold IsAcceptable; infer_instance

/-! ### The statement -/

/-- **Itai–Papadimitriou–Szwarcfiter.** A Hamiltonian path exists between distinct vertices `s`
and `t` of the `width × height` grid graph if and only if the problem is acceptable (colour
compatible and not forbidden). -/
theorem ips_characterization (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t) :
    HasHamPath width height s t ↔ IsAcceptable width height s t := by
  sorry

end GridHam
