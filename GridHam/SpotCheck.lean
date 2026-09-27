import GridHam.Main

/-!
# Spot checks

Not part of the proof. Concrete instances you can edit and re-run, to check
that the definitions mean what you expect and to see how the main theorem is
used. Build with `lake build GridHam.SpotCheck`, or open the file in VS Code
with the Lean extension to see each result next to its line.

Coordinates are `(x, y)`, 0-indexed; the grid is `width × height`.
-/

namespace GridHam

/-! ## 1. Evaluate the definitions

Each `#eval` prints `true` or `false`. Change the numbers freely. -/

-- 3×3, corner to opposite corner: both colour 0 on an odd grid → acceptable.
#eval decide (IsAcceptable 3 3 (0, 0) (2, 2))    -- expected: true
-- 3×3, corner to an edge midpoint: colour 1 endpoint on an odd grid → not acceptable.
#eval decide (IsAcceptable 3 3 (0, 0) (1, 0))    -- expected: false
-- 1×5 strip, not end to end (forbidden case F1).
#eval decide (IsAcceptable 5 1 (0, 0) (3, 0))    -- expected: false
-- 2×4 ladder, s and t across an interior rung (forbidden case F2).
#eval decide (IsAcceptable 2 4 (0, 1) (1, 1))    -- expected: false
-- The paper's Fig. 3.1(c): 4 wide, 3 high (forbidden case F3).
#eval decide (IsAcceptable 4 3 (1, 0) (3, 1))    -- expected: false

/-! ## 2. Use the theorem to rule a path out

No search happens here. The theorem turns "is there a path?" into "is it
acceptable?", and `decide` evaluates the latter. -/

example : ¬ HasHamPath 4 3 (1, 0) (3, 1) := by
  intro h
  have hacc := (ips_characterization 4 3 (1, 0) (3, 1)
    (by unfold InBounds; decide) (by unfold InBounds; decide) (by decide)).mp h
  revert hacc
  decide

/-! ## 3. Use the theorem to show a path exists (without writing it down) -/

example : HasHamPath 9 7 (0, 0) (8, 6) :=
  (ips_characterization 9 7 (0, 0) (8, 6)
    (by unfold InBounds; decide) (by unfold InBounds; decide) (by decide)).mpr (by decide)

/-! ## 4. Check a concrete path against the definition

`ValidPath w h s t p` says `p` is a Hamiltonian path from `s` to `t`. A path
produced by the Python solver can be pasted here. -/

-- A valid 3×3 path from (0,0) to (2,2).
#eval decide (ValidPath 3 3 (0, 0) (2, 2)
  [(0, 0), (1, 0), (2, 0), (2, 1), (1, 1), (0, 1), (0, 2), (1, 2), (2, 2)])   -- expected: true

-- Same path with one cell missing: rejected.
#eval decide (ValidPath 3 3 (0, 0) (2, 2)
  [(0, 0), (1, 0), (2, 0), (2, 1), (1, 1), (0, 1), (0, 2), (2, 2)])           -- expected: false

-- A path with a diagonal step (1,1) → (0,2): rejected.
#eval decide (ValidPath 3 3 (0, 0) (2, 2)
  [(0, 0), (1, 0), (2, 0), (2, 1), (1, 1), (0, 2), (0, 1), (1, 2), (2, 2)])   -- expected: false

end GridHam
