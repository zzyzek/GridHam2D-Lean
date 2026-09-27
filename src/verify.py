"""
verify.py

Cross-checks grid_hampath.py against the exhaustive brute-force search in
bruteforce.py.

Two kinds of checks:

1. EXHAUSTIVE existence check (small grids): for every (width, height, s, e)
   with width*height below a threshold, compare
       grid_hampath.is_acceptable(...)
   against
       bruteforce.hamiltonian_path_exists_exhaustive(...)
   This validates the *mathematical characterization* (the necessary and
   sufficient condition) independent of the strip/split/prime algorithm.

2. STRUCTURAL validity check (larger grids): for a wide range of grid sizes
   and endpoint pairs, whenever grid_hampath.solve(...) returns a path,
   validate it's a genuine Hamiltonian path (right endpoints, no repeats,
   covers every vertex, every step adjacent). This validates the
   *algorithm's construction*, decoupled from existence-checking cost.

Run: python3 verify.py
"""

import itertools
import sys
import time

import grid_hampath as g
import bruteforce as bf


def exhaustive_characterization_check(max_area=30, verbose=True):
    """For every grid with width*height <= max_area, and every ordered pair
    of distinct vertices, check that is_acceptable(...) agrees with genuine
    exhaustive existence search."""
    mismatches = []
    checked = 0
    t0 = time.time()
    for width in range(1, max_area + 1):
        for height in range(1, max_area + 1):
            if width * height > max_area:
                continue
            if width > height:
                continue  # WLOG by symmetry (width,height) ~ (height,width); still test both orientations lightly below
            verts = [(x, y) for x in range(width) for y in range(height)]
            for s, e in itertools.permutations(verts, 2):
                claimed = g.is_acceptable(width, height, s, e)
                exists, _ = bf.hamiltonian_path_exists_exhaustive(width, height, s, e)
                checked += 1
                if exists != claimed:
                    mismatches.append((width, height, s, e, claimed, exists))
    if verbose:
        print(f"[characterization] checked {checked} (w,h,s,e) instances up to area {max_area} "
              f"in {time.time()-t0:.1f}s; mismatches: {len(mismatches)}")
        for m in mismatches[:20]:
            print("   MISMATCH:", m, " (is_acceptable, brute_force_exists)")
    return mismatches


def solve_structural_check(sizes, samples_per_size=None, verbose=True):
    """For each (width,height) in sizes, for a set of (s,e) pairs (all pairs
    if samples_per_size is None, else a deterministic sample), check that
    whenever is_acceptable is True, solve() returns a validated Hamiltonian
    path, and whenever is_acceptable is False, solve() returns None."""
    problems = []
    failures = []
    checked = 0
    t0 = time.time()
    for (width, height) in sizes:
        verts = [(x, y) for x in range(width) for y in range(height)]
        pairs = list(itertools.permutations(verts, 2))
        if samples_per_size is not None and len(pairs) > samples_per_size:
            step = max(1, len(pairs) // samples_per_size)
            pairs = pairs[::step]
        for s, e in pairs:
            checked += 1
            acceptable = g.is_acceptable(width, height, s, e)
            try:
                path = g.solve(width, height, s, e)
            except Exception as exc:
                failures.append((width, height, s, e, f"EXCEPTION: {exc!r}"))
                continue
            if acceptable and path is None:
                failures.append((width, height, s, e, "acceptable but solve() returned None"))
                continue
            if (not acceptable) and path is not None:
                failures.append((width, height, s, e, "not acceptable but solve() returned a path"))
                continue
            if path is not None:
                err = g.validate_hamiltonian_path(width, height, s, e, path)
                if err is not None:
                    failures.append((width, height, s, e, f"INVALID PATH: {err}"))
    if verbose:
        print(f"[structural] checked {checked} (w,h,s,e) instances across {len(sizes)} sizes "
              f"in {time.time()-t0:.1f}s; failures: {len(failures)}")
        for f in failures[:20]:
            print("   FAILURE:", f)
    return failures


if __name__ == "__main__":
    print("=== Prime table self-consistency ===")
    disc = g.prime_table_discrepancies()
    print("discrepancies:", disc)

    print()
    print("=== Exhaustive characterization check (small grids) ===")
    mism = exhaustive_characterization_check(max_area=26)

    print()
    print("=== Structural validity of solve() (wider range of sizes) ===")
    sizes = []
    for w in range(1, 13):
        for h in range(1, 13):
            sizes.append((w, h))
    # A few deliberately elongated / larger cases too
    sizes += [(3, 25), (25, 3), (2, 40), (40, 2), (15, 15), (20, 8), (8, 20)]
    fail = solve_structural_check(sizes, samples_per_size=40)

    print()
    if not disc and not mism and not fail:
        print("ALL CHECKS PASSED")
        sys.exit(0)
    else:
        print("CHECKS FAILED -- see output above")
        sys.exit(1)
