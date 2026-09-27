# GridHam: status

COMPLETE. `ips_characterization` and `ips_sufficiency` depend only on
`propext`, `Classical.choice`, `Quot.sound`. No `sorry` anywhere.
See README.md for the statement, trust base, and structure.

## Possible follow-ups
- (Done) Linter warnings cleaned up; `CrossCheck.lean` removed from the
  default build.
- Optionally state F3 in the paper's literal form ("isomorphic to" a 3 × m
  pattern) and prove it equivalent to `ForbiddenCase3`.
- Extend to the k=2 Zig-Zag Numberlink work: `Basic`, `StripSplit`
  (path constructions), `F3` (path-neighbour toolkit) and the table/kernel
  approach in `PrimeTable` should carry over.

## Lean conventions that worked on this toolchain (v4.35, Mathlib)
- Prefer small own lemmas proved by induction + `rfl` over guessing Mathlib names.
- `subst h` with `h : a = b` eliminates `b`; use `rw` when direction matters.
- Membership: `List.mem_cons.mp/mpr` (one level at a time).
- Bool chains: `simpa [f] using h`, then `simp at h` to split `&&`.
- `omega` chokes on large disjunctive formulas and on many free `% 2` terms:
  split into regimes, fix parities, substitute them, then call `omega`.
- Kernel-checked finite facts: state as `∀ x ∈ List.range n, …` and use
  `decide +kernel`; build `Decidable` instances piece by piece.
- Big list literals: split into several definitions (recursion depth).
