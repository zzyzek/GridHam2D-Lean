"""
grid_hampath.py

An independent Python implementation of the Itai-Papadimitriou-Szwarcfiter
(IPS 1982) polynomial-time algorithm for Hamiltonian paths in rectangular
grid graphs, following the structure of the Rust implementation at
https://github.com/whatsacomputertho/grid-solver (strip / split / prime-table
recursion), but with two independent changes:

  1. The finite "prime" base-case table is generated and verified by brute
     force at import time, rather than hand-transcribed. (The original
     hand-transcribed table was found to contain three invalid paths.)
  2. Every function here is designed to be cross-checked against an
     exhaustive Hamiltonian-path search -- see `verify.py`.

Coordinate convention: a vertex is (x, y) with 0 <= x < width, 0 <= y < height.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Optional, List, Tuple, Sequence

Coord = Tuple[int, int]


# ---------------------------------------------------------------------------
# Color compatibility (bipartite / checkerboard argument)
# ---------------------------------------------------------------------------

def are_color_compatible(width: int, height: int, v: Coord, w: Coord) -> bool:
    """
    G(width, height) is bipartite via the (x+y) mod 2 checkerboard coloring.
    If |V1| == |V2| (even number of vertices), a Ham. path must alternate
    colors, so its endpoints must differ in color.
    If |V1| = |V2| + 1 (odd number of vertices), the path must start AND end
    on the majority color, which is parity 0 (since (0,0) has parity 0 and is
    always in the majority class for odd width*height).
    """
    graph_is_odd = (width * height) % 2 == 1
    pv = (v[0] + v[1]) % 2
    pw = (w[0] + w[1]) % 2
    if graph_is_odd:
        return pv == 0 and pw == 0
    return pv != pw


def is_corner_vertex(width: int, height: int, v: Coord) -> bool:
    corners = {(0, 0), (width - 1, 0), (0, height - 1), (width - 1, height - 1)}
    return v in corners


# ---------------------------------------------------------------------------
# Forbidden cases (necessary-condition refinements beyond color compatibility)
# ---------------------------------------------------------------------------

def _is_forbidden_case_1(width: int, height: int, v: Coord, w: Coord) -> bool:
    """width == 1 or height == 1: a Ham. path must be the straight line, so
    {v, w} must be exactly the two extreme corners."""
    is_n = width == 1
    bound = height if is_n else width
    if is_n:
        far = (0, bound - 1)
    else:
        far = (bound - 1, 0)
    origin = (0, 0)
    return not ({v, w} == {origin, far})


def _is_forbidden_case_2(width: int, height: int, v: Coord, w: Coord) -> bool:
    """width == 2 or height == 2: if v,w form a non-boundary edge (i.e. share
    the "across" coordinate and neither is a corner), a Ham. path can't use
    that mandatory crossing without prematurely closing off one side."""
    if is_corner_vertex(width, height, v) or is_corner_vertex(width, height, w):
        return False
    is_n = width == 2
    if is_n and v[1] == w[1]:
        return True
    if (not is_n) and v[0] == w[0]:
        return True
    return False


def _is_forbidden_case_3(width: int, height: int, v: Coord, w: Coord) -> bool:
    """width == 3 or height == 3, with the opposite dimension even."""
    is_n = width == 3
    opp_dim = height if is_n else width
    if opp_dim % 2 == 1:
        return False
    if (v[0] + v[1]) % 2 == (w[0] + w[1]) % 2:
        return False

    if is_n:
        c0, c1 = v[1], w[1]
        opp_coord = v[0]
    else:
        c0, c1 = v[0], w[0]
        opp_coord = v[1]

    is_greater = c0 > c1
    distance = c0 - c1 if is_greater else c1 - c0
    is_dst_sat = distance > 0 if opp_coord == 1 else distance > 1
    if not is_dst_sat:
        return False

    v_parity = (v[0] + v[1]) % 2
    if is_greater and v_parity == 1:
        return False
    if (not is_greater) and v_parity == 0:
        return False
    return True


def is_forbidden(width: int, height: int, v: Coord, w: Coord) -> bool:
    if width == 1 or height == 1:
        return _is_forbidden_case_1(width, height, v, w)
    if width == 2 or height == 2:
        return _is_forbidden_case_2(width, height, v, w)
    if width == 3 or height == 3:
        return _is_forbidden_case_3(width, height, v, w)
    return False


def is_acceptable(width: int, height: int, v: Coord, w: Coord) -> bool:
    return are_color_compatible(width, height, v, w) and not is_forbidden(width, height, v, w)


# ---------------------------------------------------------------------------
# Path validation (independent of how a path was constructed)
# ---------------------------------------------------------------------------

def validate_hamiltonian_path(width: int, height: int, start: Coord, end: Coord,
                               path: Sequence[Coord]) -> Optional[str]:
    """
    Returns None if `path` is a valid Hamiltonian path in the width x height
    grid graph from `start` to `end`; otherwise returns a string describing
    the first problem found.
    """
    n = width * height
    if len(path) != n:
        return f"wrong length: {len(path)} != {n}"
    if path[0] != tuple(start):
        return f"wrong start: {path[0]} != {tuple(start)}"
    if path[-1] != tuple(end):
        return f"wrong end: {path[-1]} != {tuple(end)}"
    seen = set()
    for v in path:
        x, y = v
        if not (0 <= x < width and 0 <= y < height):
            return f"vertex out of bounds: {v}"
        if v in seen:
            return f"duplicate vertex: {v}"
        seen.add(v)
    if len(seen) != n:
        missing = {(x, y) for x in range(width) for y in range(height)} - seen
        return f"missing vertices: {missing}"
    for i in range(1, len(path)):
        (x1, y1), (x2, y2) = path[i - 1], path[i]
        if abs(x1 - x2) + abs(y1 - y2) != 1:
            return f"non-adjacent step: {path[i-1]} -> {path[i]}"
    return None


# ---------------------------------------------------------------------------
# Prime (base-case) table: generated & verified by brute force, NOT
# hand-transcribed. This directly avoids the class of bug found in the
# original Rust implementation's hardcoded JSON table.
# ---------------------------------------------------------------------------

# Per the paper / doc's lemma: an acceptable prime (unstrippable, unsplittable)
# problem has both dimensions <= 3, or is a 4x5 / 5x4 rectangle. Shapes with
# width==1 or height==1 are deliberately excluded here -- they are always
# handled by the direct straight-line construction in _solve_core (matching
# the reference implementation's explicit width==1/height==1 special case),
# not by table lookup.
_PRIME_SHAPES = [(w, h) for w in range(2, 4) for h in range(2, 4)] + [(4, 5), (5, 4)]


@lru_cache(maxsize=None)
def _prime_table():
    """
    dict[(width, height)][(start, end)] -> tuple(path) for every acceptable
    (start, end) pair in every prime shape, found and verified by exhaustive
    brute-force search.
    """
    from bruteforce import find_hamiltonian_path

    table = {}
    for (w, h) in _PRIME_SHAPES:
        shape_table = {}
        verts = [(x, y) for x in range(w) for y in range(h)]
        for s in verts:
            for e in verts:
                if s == e:
                    continue
                if not is_acceptable(w, h, s, e):
                    continue
                p = find_hamiltonian_path(w, h, s, e)
                if p is None:
                    # is_acceptable claims this should be solvable but brute
                    # force found no path -- record as a discrepancy rather
                    # than silently failing.
                    shape_table[(s, e)] = None
                else:
                    err = validate_hamiltonian_path(w, h, s, e, p)
                    assert err is None, f"generated prime path invalid: {err}"
                    shape_table[(s, e)] = tuple(p)
        table[(w, h)] = shape_table
    return table


def prime_table_discrepancies():
    """Return a list of (width, height, start, end) for which is_acceptable
    claims a path should exist in a prime shape, but exhaustive brute force
    search found none. Should be empty if is_acceptable's characterization
    is correct on these shapes."""
    out = []
    table = _prime_table()
    for (w, h), shape_table in table.items():
        for (s, e), p in shape_table.items():
            if p is None:
                out.append((w, h, s, e))
    return out


def is_prime(width: int, height: int, start: Coord, end: Coord) -> bool:
    table = _prime_table()
    shape_table = table.get((width, height))
    if shape_table is None:
        return False
    return (tuple(start), tuple(end)) in shape_table


def get_prime(width: int, height: int, start: Coord, end: Coord) -> Optional[List[Coord]]:
    table = _prime_table()
    shape_table = table.get((width, height))
    if shape_table is None:
        return None
    p = shape_table.get((tuple(start), tuple(end)))
    return list(p) if p is not None else None


# ---------------------------------------------------------------------------
# Stripping: peel a width/height-2 slice off one side, provided the smaller
# problem is still acceptable and neither endpoint is within 2 of that side.
# ---------------------------------------------------------------------------

def _try_strip_right(width, height, start, end):
    bound = width
    if bound - start[0] <= 2 or bound - end[0] <= 2:
        return None
    new_w = width - 2
    if not is_acceptable(new_w, height, start, end):
        return None
    return (new_w, height, start, end, 'R')


def _try_strip_up(width, height, start, end):
    bound = height
    if bound - start[1] <= 2 or bound - end[1] <= 2:
        return None
    new_h = height - 2
    if not is_acceptable(width, new_h, start, end):
        return None
    return (width, new_h, start, end, 'U')


def _try_strip_left(width, height, start, end):
    if start[0] < 2 or end[0] < 2:
        return None
    new_start = (start[0] - 2, start[1])
    new_end = (end[0] - 2, end[1])
    new_w = width - 2
    if not is_acceptable(new_w, height, new_start, new_end):
        return None
    return (new_w, height, new_start, new_end, 'L')


def _try_strip_down(width, height, start, end):
    if start[1] < 2 or end[1] < 2:
        return None
    new_start = (start[0], start[1] - 2)
    new_end = (end[0], end[1] - 2)
    new_h = height - 2
    if not is_acceptable(width, new_h, new_start, new_end):
        return None
    return (width, new_h, new_start, new_end, 'D')


def _try_strip(width, height, start, end):
    for f in (_try_strip_right, _try_strip_up, _try_strip_left, _try_strip_down):
        r = f(width, height, start, end)
        if r is not None:
            return r
    return None


# ---------------------------------------------------------------------------
# Splitting: cut along a row or column edge strictly between start and end,
# such that both halves (each keeping one original endpoint and gaining the
# cut vertex as its other endpoint) are acceptable.
# ---------------------------------------------------------------------------

def _split_horizontally(width, height, start, end):
    """Split along a horizontal (constant-y) edge. Returns
    ((lower_w,lower_h,lower_s,lower_e), (upper_w,upper_h,upper_s,upper_e))
    or None."""
    if start[1] == end[1]:
        return None
    is_start_below = start[1] < end[1]
    lo = start[1] if is_start_below else end[1]
    hi = end[1] if is_start_below else start[1]
    for i in range(lo, hi):
        for j in range(width):
            lower_v = (j, i)
            upper_v = (j, i + 1)
            if lower_v in (start, end) or upper_v in (start, end):
                continue
            if is_start_below:
                lower_sub = (width, upper_v[1], start, lower_v)
                upper_sub = (width, height - upper_v[1], (upper_v[0], 0), (end[0], end[1] - upper_v[1]))
            else:
                lower_sub = (width, upper_v[1], lower_v, end)
                upper_sub = (width, height - upper_v[1], (start[0], start[1] - upper_v[1]), (upper_v[0], 0))
            if is_acceptable(*lower_sub[:2], lower_sub[2], lower_sub[3]) and \
               is_acceptable(*upper_sub[:2], upper_sub[2], upper_sub[3]):
                return (lower_sub, upper_sub)
    return None


def _split_vertically(width, height, start, end):
    """Split along a vertical (constant-x) edge. Returns
    ((left_w,left_h,left_s,left_e), (right_w,right_h,right_s,right_e))
    or None."""
    if start[0] == end[0]:
        return None
    is_start_left = start[0] < end[0]
    lo = start[0] if is_start_left else end[0]
    hi = end[0] if is_start_left else start[0]
    for i in range(lo, hi):
        for j in range(height):
            left_v = (i, j)
            right_v = (i + 1, j)
            if left_v in (start, end) or right_v in (start, end):
                continue
            if is_start_left:
                left_sub = (right_v[0], height, start, left_v)
                right_sub = (width - right_v[0], height, (0, right_v[1]), (end[0] - right_v[0], end[1]))
            else:
                left_sub = (i + 1, height, left_v, end)
                right_sub = (width - (i + 1), height, (start[0] - (i + 1), start[1]), (0, right_v[1]))
            if is_acceptable(*left_sub[:2], left_sub[2], left_sub[3]) and \
               is_acceptable(*right_sub[:2], right_sub[2], right_sub[3]):
                return (left_sub, right_sub)
    return None


# ---------------------------------------------------------------------------
# Reconstruction: given a solved path for a stripped-down problem, extend it
# back outward by the recorded strip directions, in the same order the
# strips were originally applied.
# ---------------------------------------------------------------------------

def _extend_up(path, width, height):
    for i in range(1, len(path)):
        bound = height - 1
        if path[i][1] != bound or path[i - 1][1] != bound:
            continue
        left_first = path[i - 1][0] < path[i][0]
        if left_first:
            start_range = list(reversed(range(0, path[i - 1][0] + 1)))
            mid_range = list(range(0, width))
            end_range = list(reversed(range(path[i][0], width)))
        else:
            start_range = list(range(path[i - 1][0], width))
            mid_range = list(reversed(range(0, width)))
            end_range = list(range(0, path[i][0] + 1))
        ext = [(j, height) for j in start_range] + [(j, height + 1) for j in mid_range] + \
              [(j, height) for j in end_range]
        return path[:i] + ext + path[i:], width, height + 2
    raise ValueError("no edge on upper boundary to extend from")


def _extend_down(path, width, height):
    for i in range(1, len(path)):
        if path[i][1] != 0 or path[i - 1][1] != 0:
            continue
        shifted = [(x, y + 2) for (x, y) in path]
        left_first = shifted[i - 1][0] < shifted[i][0]
        if left_first:
            start_range = list(reversed(range(0, shifted[i - 1][0] + 1)))
            mid_range = list(range(0, width))
            end_range = list(reversed(range(shifted[i][0], width)))
        else:
            start_range = list(range(shifted[i - 1][0], width))
            mid_range = list(reversed(range(0, width)))
            end_range = list(range(0, shifted[i][0] + 1))
        ext = [(j, 1) for j in start_range] + [(j, 0) for j in mid_range] + [(j, 1) for j in end_range]
        return shifted[:i] + ext + shifted[i:], width, height + 2
    raise ValueError("no edge on lower boundary to extend from")


def _extend_right(path, width, height):
    for i in range(1, len(path)):
        bound = width - 1
        if path[i][0] != bound or path[i - 1][0] != bound:
            continue
        down_first = path[i - 1][1] < path[i][1]
        if down_first:
            start_range = list(reversed(range(0, path[i - 1][1] + 1)))
            mid_range = list(range(0, height))
            end_range = list(reversed(range(path[i][1], height)))
        else:
            start_range = list(range(path[i - 1][1], height))
            mid_range = list(reversed(range(0, height)))
            end_range = list(range(0, path[i][1] + 1))
        ext = [(width, j) for j in start_range] + [(width + 1, j) for j in mid_range] + \
              [(width, j) for j in end_range]
        return path[:i] + ext + path[i:], width + 2, height
    raise ValueError("no edge on right boundary to extend from")


def _extend_left(path, width, height):
    for i in range(1, len(path)):
        if path[i][0] != 0 or path[i - 1][0] != 0:
            continue
        shifted = [(x + 2, y) for (x, y) in path]
        down_first = shifted[i - 1][1] < shifted[i][1]
        if down_first:
            start_range = list(reversed(range(0, shifted[i - 1][1] + 1)))
            mid_range = list(range(0, height))
            end_range = list(reversed(range(shifted[i][1], height)))
        else:
            start_range = list(range(shifted[i - 1][1], height))
            mid_range = list(reversed(range(0, height)))
            end_range = list(range(0, shifted[i][1] + 1))
        ext = [(1, j) for j in start_range] + [(0, j) for j in mid_range] + [(1, j) for j in end_range]
        return shifted[:i] + ext + shifted[i:], width + 2, height
    raise ValueError("no edge on left boundary to extend from")


_EXTEND = {'U': _extend_up, 'D': _extend_down, 'R': _extend_right, 'L': _extend_left}


# ---------------------------------------------------------------------------
# Top-level recursive solve
# ---------------------------------------------------------------------------

class UnsolvableError(Exception):
    pass


def solve(width: int, height: int, start: Coord, end: Coord) -> Optional[List[Coord]]:
    """
    Solve the Hamiltonian path problem H(G(width,height), start, end).
    Returns the vertex sequence if a Hamiltonian path exists, else None.
    """
    start = tuple(start)
    end = tuple(end)
    if not is_acceptable(width, height, start, end):
        return None

    # Strip as much as possible, recording the directions in the order
    # applied.
    w, h, s, e = width, height, start, end
    extensions: List[str] = []
    while True:
        r = _try_strip(w, h, s, e)
        if r is None:
            break
        w, h, s, e, d = r
        extensions.append(d)

    base_path = _solve_core(w, h, s, e)

    # Reconstruct by undoing strips in reverse (innermost-first) order: the
    # *last* strip applied removed the innermost layer, so it must be the
    # *first* one added back.
    #
    # NOTE: the reference Rust implementation (gridproblem.rs / gridpath.rs)
    # applies `extend_many` in the *original* push order, not reversed. That
    # was checked here empirically against exhaustive brute-force validation
    # and found to raise "no edge on boundary to extend from" on legitimate
    # acceptable instances (e.g. width=3,height=4,(0,0)->(0,1), which strips
    # Up then Right down to a 1x2 base -- extend_up cannot find a boundary
    # edge on a width-1 path). Reversing fixes it and matches the geometric
    # argument for why reconstruction must undo the *last* strip first.
    path, cw, ch = base_path, w, h
    for d in reversed(extensions):
        path, cw, ch = _EXTEND[d](path, cw, ch)
    assert (cw, ch) == (width, height)
    return path


def _solve_core(width, height, start, end) -> List[Coord]:
    """Solve an already-stripped (start/end fixed, not necessarily prime)
    acceptable problem via prime lookup or splitting."""
    if is_prime(width, height, start, end):
        p = get_prime(width, height, start, end)
        if p is None:
            raise UnsolvableError(
                f"({width},{height},{start},{end}) marked prime but no stored path"
            )
        return p

    h_split = _split_horizontally(width, height, start, end)
    if h_split is not None:
        (lw, lh, ls, le), (uw, uh, us, ue) = h_split
        lower_path = solve(lw, lh, ls, le)
        upper_path = solve(uw, uh, us, ue)
        if lower_path is None or upper_path is None:
            raise UnsolvableError("split_horizontally produced an unsolvable sub-problem")
        is_start_below = start[1] < end[1]
        if is_start_below:
            shifted_upper = [(x, y + lh) for (x, y) in upper_path]
            return lower_path + shifted_upper
        else:
            shifted_upper = [(x, y + lh) for (x, y) in upper_path]
            return shifted_upper + lower_path

    v_split = _split_vertically(width, height, start, end)
    if v_split is not None:
        (lw, lh, ls, le), (rw, rh, rs, re) = v_split
        left_path = solve(lw, lh, ls, le)
        right_path = solve(rw, rh, rs, re)
        if left_path is None or right_path is None:
            raise UnsolvableError("split_vertically produced an unsolvable sub-problem")
        is_start_left = start[0] < end[0]
        if is_start_left:
            shifted_right = [(x + lw, y) for (x, y) in right_path]
            return left_path + shifted_right
        else:
            shifted_right = [(x + lw, y) for (x, y) in right_path]
            return shifted_right + left_path

    if width == 1 or height == 1:
        is_width = width == 1
        bound = height if is_width else width
        reverse = (is_width and start[1] != 0) or ((not is_width) and start[0] != 0)
        rng = list(reversed(range(bound))) if reverse else list(range(bound))
        return [(0, i) for i in rng] if is_width else [(i, 0) for i in rng]

    raise UnsolvableError(
        f"({width},{height},{start},{end}) was acceptable but could not be "
        f"stripped, split, or solved directly -- this should be unreachable"
    )
