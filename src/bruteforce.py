"""
bruteforce.py

Exhaustive (ground-truth) Hamiltonian path search on rectangular grid
graphs. Used only for verification and for generating/checking the finite
prime-case table -- never as part of the polynomial-time algorithm itself.

find_hamiltonian_path does a full backtracking search with two standard
pruning rules:
  1. Connectivity pruning: after each step, the remaining unvisited vertices
     (plus the current vertex) must still be connected, or no completion is
     possible.
  2. Degree pruning: any unvisited vertex other than the final target that
     has only one remaining unvisited/current neighbor is in trouble if that
     neighbor isn't reachable soon (we use a lighter local check: any
     unvisited non-target vertex with zero remaining neighbors is dead).

This is exponential in the worst case, so it's only used for small grids
(a full exhaustive existence proof) or as a spot-check with a step budget
for larger ones.
"""

from __future__ import annotations
from typing import Optional, List, Tuple, Set

Coord = Tuple[int, int]


def _neighbors(width: int, height: int, v: Coord):
    x, y = v
    if x + 1 < width:
        yield (x + 1, y)
    if x - 1 >= 0:
        yield (x - 1, y)
    if y + 1 < height:
        yield (x, y + 1)
    if y - 1 >= 0:
        yield (x, y - 1)


def _connected_after_removal(width: int, height: int, start: Coord, visited: Set[Coord]) -> bool:
    """Check that the unvisited vertices (plus `start`) form a single
    connected component, via flood fill. `start` itself must not be in
    `visited`."""
    total_remaining = width * height - len(visited)
    stack = [start]
    seen = {start}
    while stack:
        cur = stack.pop()
        for nb in _neighbors(width, height, cur):
            if nb not in visited and nb not in seen:
                seen.add(nb)
                stack.append(nb)
    return len(seen) == total_remaining


def find_hamiltonian_path(
    width: int, height: int, start: Coord, end: Coord,
    step_budget: Optional[int] = None,
) -> Optional[List[Coord]]:
    """
    Exhaustive backtracking search for a Hamiltonian path from `start` to
    `end` in the width x height grid graph. Returns the vertex sequence if
    found, else None (a genuine, exhaustive proof of non-existence, unless
    step_budget cuts the search short, in which case returns None but the
    caller should treat that as "unknown" -- see `budget_exhausted`).

    step_budget: if given, abort (return None) after this many recursive
    calls, to bound runtime on larger grids. Use budget_exhausted() to check
    whether the last call actually proved non-existence or just ran out of
    budget.
    """
    n = width * height
    visited: Set[Coord] = {start}
    path: List[Coord] = [start]
    state = {"steps": 0, "budget_hit": False}

    def backtrack(cur: Coord) -> bool:
        if step_budget is not None:
            state["steps"] += 1
            if state["steps"] > step_budget:
                state["budget_hit"] = True
                return False
        if len(path) == n:
            return cur == end

        # Connectivity pruning over the *remaining* vertices (those not yet
        # visited), from `cur`.
        if not _connected_after_removal(width, height, cur, visited - {cur}):
            return False

        # If `end` is not cur, and end has become unreachable given current
        # visited set... (covered by connectivity check above, since a
        # disconnected `end` fails that check once isolated.)

        neighbors = list(_neighbors(width, height, cur))
        # Degree-based ordering heuristic (Warnsdorff): try the neighbor
        # with the fewest further unvisited options first. This does not
        # affect correctness/exhaustiveness, only speed of finding a path
        # when one exists; the search still backtracks over all options.
        def remaining_degree(v: Coord) -> int:
            return sum(1 for nb in _neighbors(width, height, v) if nb not in visited and nb != cur)

        candidates = [v for v in neighbors if v not in visited]
        candidates.sort(key=remaining_degree)

        for nxt in candidates:
            visited.add(nxt)
            path.append(nxt)
            if backtrack(nxt):
                return True
            path.pop()
            visited.discard(nxt)
            if state["budget_hit"]:
                return False
        return False

    ok = backtrack(start)
    if ok:
        return list(path)
    return None


def hamiltonian_path_exists_exhaustive(width: int, height: int, start: Coord, end: Coord,
                                        step_budget: Optional[int] = None):
    """
    Returns (exists: Optional[bool], path: Optional[list]).
    exists is True/False if determined, or None if step_budget was exhausted
    before the search could conclusively finish (i.e. unknown).
    """
    n = width * height
    visited: Set[Coord] = {start}
    path: List[Coord] = [start]
    state = {"steps": 0, "budget_hit": False}

    def backtrack(cur: Coord) -> bool:
        if step_budget is not None:
            state["steps"] += 1
            if state["steps"] > step_budget:
                state["budget_hit"] = True
                return False
        if len(path) == n:
            return cur == end
        if not _connected_after_removal(width, height, cur, visited - {cur}):
            return False

        neighbors = list(_neighbors(width, height, cur))

        def remaining_degree(v: Coord) -> int:
            return sum(1 for nb in _neighbors(width, height, v) if nb not in visited and nb != cur)

        candidates = [v for v in neighbors if v not in visited]
        candidates.sort(key=remaining_degree)

        for nxt in candidates:
            visited.add(nxt)
            path.append(nxt)
            if backtrack(nxt):
                return True
            path.pop()
            visited.discard(nxt)
            if state["budget_hit"]:
                return False
        return False

    found = backtrack(start)
    if found:
        return True, list(path)
    if state["budget_hit"]:
        return None, None
    return False, None
