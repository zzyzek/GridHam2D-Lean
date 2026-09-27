# GridHam: a Lean 4 proof of the Itai–Papadimitriou–Szwarcfiter theorem

A complete, machine-checked proof of the characterization of Hamiltonian paths
in rectangular grid graphs from

> A. Itai, C. H. Papadimitriou, J. L. Szwarcfiter,
> *Hamilton Paths in Grid Graphs*, SIAM J. Comput. 11(4), 1982, 676–686.

[DOI 10.1137/0211056](https://doi.org/10.1137/0211056)

## The theorem

`GridHam/Main.lean`:

```lean
theorem ips_characterization (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t) :
    HasHamPath width height s t ↔ IsAcceptable width height s t
```

For distinct vertices `s`, `t` of the `width × height` grid graph, a Hamiltonian
path from `s` to `t` exists if and only if the problem is *acceptable*: colour
compatible and not forbidden (the paper's conditions F1, F2, F3).

`lake build` prints:

```
'GridHam.ips_sufficiency' depends on axioms: [propext, Classical.choice, Quot.sound]
'GridHam.ips_characterization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. There is no `sorry` anywhere in the
project, and no `native_decide` (all computational checks run in the kernel,
via `decide +kernel`).

## What you have to trust

A compiled proof only certifies the statement as written. To trust that it is
*IPS's* theorem, check these definitions by reading them (they are short):

* `Basic.lean`: `Coord` (`ℕ × ℕ`, 0-indexed), `InBounds`, `Adjacent`,
  `allCoords`, `ValidPath` (right length, starts at `s`, ends at `t`, no
  repeats, all in bounds, covers every cell, consecutive cells adjacent), and
  `HasHamPath`.
* `Coloring.lean`: `parity`, `ColorCompatible`.
* `Forbidden.lean`: `ForbiddenCase1/2/3`, `IsForbidden`, `IsAcceptable`.

The forbidden cases were transcribed from an open-source Rust implementation
and then checked three ways: against exhaustive brute-force search in Python
(every instance up to area 26), in Lean itself (`CrossCheck.lean`: all 10,532
ordered pairs up to area 20), and against the paper's own statement of F3
(103,284 instances on 3 × m grids up to m = 40). The theorem needs `s ≠ t`:
without it the statement is false (3 × 3, `s = t = (0,0)` is acceptable but
has no path).

## File structure

| File | Contents |
|---|---|
| `Basic.lean` | Definitions: grid, adjacency, Hamiltonian path. |
| `Coloring.lean` | Colours alternate along a path; colour compatibility is necessary (even grids by alternation, odd grids by counting colour-1 cells). |
| `Forbidden.lean` | Definitions of the forbidden cases; forbidden case 1 (1-wide grids) is really forbidden. |
| `Arith.lean` | `AccA`: acceptability as a pure arithmetic formula, with `acc_iff` proving the two agree. |
| `StripSplit.lean` | Path constructions: reversal, transpose, reflection; splitting along a cut edge; stripping two columns (degree argument for a boundary edge, then a detour). |
| `PrimeTable.lean` | Base cases: 596 explicit paths for the prime shapes (≤ 3×3, 4×4, 4×5, 5×4), verified by the kernel. |
| `Reduction.lean` | The reduction rule: which strip or split to apply, and that the pieces are acceptable. Symmetries of acceptability. |
| `Main.lean` | Sufficiency by strong induction on `width + height`; the main theorem. |
| `F3.lean` | Tools for reasoning about path neighbours in list-based paths; the case-3 obstruction on 3-high grids. |
| `Necessity.lean` | Necessity: forbidden cases 2 and 3 are really forbidden; assembly of Theorem 3.1. |
| `CrossCheck.lean` | A test, not part of the proof and not in the default build: `IsAcceptable` agrees with brute force up to area 20. Run with `lake build GridHam.CrossCheck`. |
| `SpotCheck.lean` | Some spot checks that include concrete instances you can edit and re-run. Not part of the main proof. |

## How the proof differs from the paper

* **Sufficiency.** The paper strips and splits until a "prime" problem remains
  and argues case by case that prime problems are small. Here the reduction is
  an explicit rule (normalize so width ≥ height and `s` is left of `t`; then
  strip left, strip right, or split after column 1 at a row chosen by colour),
  found and tested in Python on 1.8 million instances before being proved.
  4×4 is treated as a base case because the rule fails on four 4×4 instances.
* **Stripping** needs a hypothesis the paper leaves implicit: the column next
  to the strip must contain a vertex that is not an endpoint (otherwise, e.g.
  on a 5 × 1 grid, the lemma is false).
* **Necessity.** The paper calls Lemma 3.1 "a straightforward case analysis"
  and gives no proof. Here: F2 by an intermediate-value argument (the middle of
  the path must cross the row of `s` and `t`); F3 by induction on the column of
  the colour-1 endpoint, using forced moves in the two leftmost columns and a
  contraction to a grid two columns narrower.
* **Arithmetic.** `omega` cannot handle the fully unfolded acceptability
  formulas (too many disjunctions, and it is incomplete with many free `% 2`
  terms), so the arithmetic lemmas split into regimes first and small grids are
  checked by the kernel.

## Build

```
lake exe cache get   # prebuilt Mathlib
lake build           # a few minutes; PrimeTable and Reduction are the slow files
lake build GridHam.CrossCheck   # optional: the brute-force cross-check test
lake build GridHam.SpotCheck    # optional: run spot checks
```

A clean build prints only the two `#print axioms` lines from `Main.lean`
(no warnings):

```
ℹ [8961/8963] Replayed GridHam.Main
info: GridHam/Main.lean:173:0: 'GridHam.ips_sufficiency' depends on axioms: [propext, Classical.choice, Quot.sound]
info: GridHam/Main.lean:174:0: 'GridHam.ips_characterization' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8963 jobs).
```

The Python files used to design and test the proof (`grid_hampath.py`,
`bruteforce.py`, `verify.py`) are not needed for the build.

## License

Unless explicitly stated otherwise, everything in this directory is put under a CC0 license:

> To the extent possible under law, the person who associated CC0 with
> this project has waived all copyright and related or neighboring rights
> to this project.
> 
> You should have received a copy of the CC0 legalcode along with this
> work.  If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.

