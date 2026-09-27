import GridHam.Basic

/-!
# Color compatibility (necessary condition, part 1)

The grid graph is bipartite via the checkerboard coloring `(x+y) mod 2`.
A Hamiltonian path must alternate colors at every step, which forces a
relationship between the colors of its two endpoints and the parity of the
total vertex count -- this file is the Lean counterpart of
`are_color_compatible` / `_is_forbidden_case_*`'s color checks in
`grid_hampath.py`, together with a proof of the direction that actually
matters for a *necessary*-condition theorem: `HasHamPath → ColorCompatible`.

The even case follows from alternation alone. The odd case is a counting
argument: colours alternate along the path, so a path of odd length `n`
starting on colour 1 would visit `(n+1)/2` colour-1 cells, but the grid has
only `(n-1)/2` of them (`cnt1_grid`) and the path has no repeats.
-/

namespace GridHam

/-- The checkerboard color of a vertex: `0` or `1`. -/
def parity (v : Coord) : ℕ := (v.1 + v.2) % 2

/-- Adjacent vertices always have different parity: exactly one coordinate
changes by exactly 1, so the coordinate sum's parity flips. -/
theorem adjacent_parity_ne {v w : Coord} (h : Adjacent v w) :
    parity v ≠ parity w := by
  unfold Adjacent at h
  unfold parity
  rcases h with ⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩ <;> omega

/-- Along a chain of adjacent vertices, parity strictly alternates: the
parity at position `i` is `(parity of position 0) + i`, mod 2. Proved by
induction on the list, peeling one adjacency step at a time. -/
theorem chain_parity_alternates (p : List Coord) (hc : chainAdjacent p = true) :
    ∀ i (hi : i < p.length) (h0 : 0 < p.length),
      parity (p.get ⟨i, hi⟩) = (parity (p.get ⟨0, h0⟩) + i) % 2 := by
  induction p with
  | nil => intro i hi h0; simp at h0
  | cons a l ih =>
    intro i hi h0
    cases i with
    | zero => simp; unfold parity; omega
    | succ n =>
      cases l with
      | nil => simp at hi
      | cons b rest =>
        have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
          simpa [chainAdjacent] using hc
        simp at hc'
        obtain ⟨hab, hcl⟩ := hc'
        have hadj : Adjacent a b := by
          unfold adjacentB at hab
          by_contra hcon
          simp [hcon] at hab
        have hln : n < (b :: rest).length := by
          have hlen : (a :: b :: rest).length = (b :: rest).length + 1 := by simp
          omega
        have key := ih hcl n hln (by omega)
        have hpar : parity a ≠ parity b := adjacent_parity_ne hadj
        have ha2 : parity a < 2 := by unfold parity; omega
        have hbb2 : parity b < 2 := by unfold parity; omega
        have goalLHS : (a :: b :: rest).get ⟨n + 1, hi⟩ = (b :: rest).get ⟨n, hln⟩ := by simp
        have goalRHS0 : (a :: b :: rest).get ⟨0, h0⟩ = a := by simp
        have hb0 : (b :: rest).get ⟨0, (by omega : 0 < (b :: rest).length)⟩ = b := by simp
        rw [goalLHS, goalRHS0]
        simp only [hb0] at key
        omega

/-- Bridges `List.getLast?` (which returns `Option`) to `List.getLast`
(which takes a nonempty-proof and returns the element directly): if the
former says `some x`, the latter computes to `x`. Proved from scratch by
induction rather than by citing a Mathlib lemma name -- see the note above
`chain_parity_head_last` for why. Each step relies only on `rfl` (both
`List.getLast` and `List.getLast?` reduce definitionally on a concrete
`cons`/`cons`/... pattern, exactly like `chainAdjacent` did in
`chain_parity_alternates` above) plus `injection` (a core tactic, not a
named lemma) to extract `a = x` from `some a = some x`. -/
theorem getLast?_eq_getLast_of_ne_nil :
    ∀ (l : List Coord) (hne : l ≠ []) (x : Coord),
      l.getLast? = some x → l.getLast hne = x := by
  intro l
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons a rest ih =>
    intro hne x h
    cases rest with
    | nil =>
      have h1 : ([a] : List Coord).getLast? = some a := rfl
      rw [h1] at h
      injection h with heq
    | cons b rest' =>
      have hgl2 : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
      rw [hgl2] at h
      have hgl3 : (a :: b :: rest').getLast hne = (b :: rest').getLast (by simp) := rfl
      rw [hgl3]
      exact ih (by simp) x h

/-- The head-to-last-element counterpart of `chain_parity_alternates`,
proved independently by front-peeling induction (so `List.getLast`, not
`List.get` at a computed index, is what shows up -- avoiding the need to
separately relate `.get` at the last index to `.getLast`/`.getLast?`, which
would just reintroduce the same bridging problem one level down). Combined
with `getLast?_eq_getLast_of_ne_nil`, this is what `hamPath_implies_diff_parity_of_even`
needs. -/
theorem chain_parity_head_last :
    ∀ (l : List Coord) (a : Coord), chainAdjacent (a :: l) = true →
      ∀ (hne : (a :: l) ≠ []),
        parity ((a :: l).getLast hne) = (parity a + l.length) % 2 := by
  intro l
  induction l with
  | nil =>
    intro a hc hne
    have hgl : (a :: ([] : List Coord)).getLast hne = a := rfl
    rw [hgl]
    simp
    unfold parity
    omega
  | cons b rest ih =>
    intro a hc hne
    have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
      simpa [chainAdjacent] using hc
    simp at hc'
    obtain ⟨hab, hcl⟩ := hc'
    have hadj : Adjacent a b := by
      unfold adjacentB at hab
      by_contra hcon
      simp [hcon] at hab
    have hgetlast : (a :: b :: rest).getLast hne = (b :: rest).getLast (by simp) := rfl
    rw [hgetlast]
    have key := ih b hcl (by simp)
    have hpar : parity a ≠ parity b := adjacent_parity_ne hadj
    have ha2 : parity a < 2 := by unfold parity; omega
    have hbb2 : parity b < 2 := by unfold parity; omega
    have hlen : (b :: rest).length = rest.length + 1 := rfl
    omega

/-- **Necessary condition, color part (even case).** If the grid has an even
number of vertices and a Hamiltonian path exists from `s` to `t`, then `s`
and `t` have different parity. This direction needs no counting lemma: it
follows directly from alternation, since `n - 1` is odd exactly when `n` is
even. -/
theorem hamPath_implies_diff_parity_of_even
    (width height : ℕ) (s t : Coord) (heven : (width * height) % 2 = 0)
    (h : HasHamPath width height s t) : parity s ≠ parity t := by
  obtain ⟨p, hlen, hhead, hlast, _, _, _, hchain⟩ := h
  have hpne : p ≠ [] := by
    intro hcontra; rw [hcontra] at hhead; simp at hhead
  cases p with
  | nil => exact absurd rfl hpne
  | cons a rest =>
    have haseq : (a :: rest).head? = some a := rfl
    rw [haseq] at hhead
    injection hhead with heqas
    subst heqas
    have hne : (a :: rest) ≠ [] := by simp
    have hgl := getLast?_eq_getLast_of_ne_nil (a :: rest) hne t hlast
    have key := chain_parity_head_last rest a hchain hne
    rw [hgl] at key
    have hs2 : parity a < 2 := by unfold parity; omega
    have ht2 : parity t < 2 := by unfold parity; omega
    have hlen2 : rest.length + 1 = width * height := by
      have hcl : (a :: rest).length = rest.length + 1 := rfl
      omega
    omega

/-- The color-compatibility condition from `grid_hampath.py`'s
`are_color_compatible`, ported directly. -/
def ColorCompatible (width height : ℕ) (s t : Coord) : Prop :=
  if (width * height) % 2 = 1 then
    parity s = 0 ∧ parity t = 0
  else
    parity s ≠ parity t

instance : DecidablePred (fun p : Coord × Coord => ColorCompatible width height p.1 p.2) :=
  fun p => by unfold ColorCompatible; infer_instance

/-! ### The odd case: counting colour-1 cells -/

theorem odd_mul_iff_c (w h : ℕ) : (w * h) % 2 = 1 ↔ w % 2 = 1 ∧ h % 2 = 1 := by
  rw [Nat.mul_mod]
  rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hw | hw <;>
    rcases (by omega : h % 2 = 0 ∨ h % 2 = 1) with hh | hh <;>
    simp [hw, hh]

theorem mem_allCoords_iff (w h : ℕ) (v : Coord) :
    v ∈ allCoords w h ↔ v.1 < w ∧ v.2 < h := by
  simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨v.1, hx, v.2, hy, rfl⟩

/-- Number of colour-1 cells in a list. -/
def cnt1 (l : List Coord) : ℕ := l.countP (fun v => decide (parity v = 1))

theorem cnt1_cons (a : Coord) (l : List Coord) :
    cnt1 (a :: l) = cnt1 l + (if parity a = 1 then 1 else 0) := by
  unfold cnt1
  simp [List.countP_cons]

theorem cnt1_append (l1 l2 : List Coord) : cnt1 (l1 ++ l2) = cnt1 l1 + cnt1 l2 := by
  unfold cnt1
  simp [List.countP_append]

/-- Colours alternate along an adjacent-chain, so a chain starting at `a` with
`l.length + 1` cells has `(l.length + 1 + parity a) / 2` cells of colour 1. -/
theorem cnt1_chain : ∀ (l : List Coord) (a : Coord), chainAdjacent (a :: l) = true →
    cnt1 (a :: l) = (l.length + 1 + parity a) / 2 := by
  intro l
  induction l with
  | nil =>
    intro a _
    rw [cnt1_cons, show cnt1 [] = 0 from rfl, List.length_nil]
    have ha2 : parity a < 2 := by unfold parity; omega
    split_ifs <;> omega
  | cons b l' ih =>
    intro a hch
    have hc' : (adjacentB a b && chainAdjacent (b :: l')) = true := by
      simpa [chainAdjacent] using hch
    simp at hc'
    obtain ⟨hab, hcl⟩ := hc'
    have hadj : Adjacent a b := by
      unfold adjacentB at hab
      by_contra hcon
      simp [hcon] at hab
    have hne := adjacent_parity_ne hadj
    have ha2 : parity a < 2 := by unfold parity; omega
    have hb2 : parity b < 2 := by unfold parity; omega
    rw [cnt1_cons, ih b hcl, List.length_cons]
    split_ifs <;> omega

/-- Column `x` of a height-`h` grid has `(h + x % 2) / 2` cells of colour 1. -/
theorem cnt1_col (x : ℕ) : ∀ h, cnt1 ((List.range h).map (fun y => (x, y))) = (h + x % 2) / 2 := by
  intro h
  induction h with
  | zero =>
    rw [show cnt1 ((List.range 0).map (fun y => (x, y))) = 0 from rfl]
    omega
  | succ h ih =>
    rw [List.range_succ, List.map_append, cnt1_append, ih]
    have e : cnt1 (List.map (fun y => (x, y)) [h]) = (if (x + h) % 2 = 1 then 1 else 0) := by
      rw [show List.map (fun y => (x, y)) [h] = [(x, h)] from rfl, cnt1_cons]
      by_cases hc : (x + h) % 2 = 1 <;> simp [cnt1, parity, hc]
    rw [e]
    split_ifs <;> omega

theorem allCoords_succ (w h : ℕ) :
    allCoords (w + 1) h = allCoords w h ++ (List.range h).map (fun y => (w, y)) := by
  simp [allCoords, List.range_succ]

/-- For odd `h`: `2 · (colour-1 cells of the w × h grid) + w % 2 = w · h`. -/
theorem cnt1_grid (h : ℕ) (hh : h % 2 = 1) : ∀ w, 2 * cnt1 (allCoords w h) + w % 2 = w * h := by
  intro w
  induction w with
  | zero => simp [allCoords, cnt1]
  | succ w ih =>
    rw [allCoords_succ, cnt1_append, cnt1_col, Nat.add_mul, Nat.one_mul]
    omega

/-- **Necessary condition, odd case.** On a grid with both sides odd, a
Hamiltonian path starts and ends on colour 0. Colours alternate along the
path, so starting on colour 1 would visit `(n+1)/2` colour-1 cells, but the
grid only has `(n-1)/2` and the path has no repeats. -/
theorem hamPath_odd_parity (width height : ℕ) (s t : Coord)
    (hodd : width % 2 = 1 ∧ height % 2 = 1) (h : HasHamPath width height s t) :
    parity s = 0 ∧ parity t = 0 := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, _, hch⟩ := h
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    have hcount := cnt1_chain l a hch
    have hsub : List.Subperm (a :: l) (allCoords width height) :=
      List.Nodup.subperm hnd (fun v hv => (mem_allCoords_iff width height v).mpr (hin v hv))
    have hle : cnt1 (a :: l) ≤ cnt1 (allCoords width height) := by
      unfold cnt1
      exact List.Subperm.countP_le _ hsub
    have hgrid := cnt1_grid height hodd.2 width
    have hlen' : l.length + 1 = width * height := hlen
    have ha2 : parity a < 2 := by unfold parity; omega
    have hpa : parity a = 0 := by omega
    have hne : (a :: l) ≠ [] := by simp
    have hgl := getLast?_eq_getLast_of_ne_nil (a :: l) hne t hlast
    have key := chain_parity_head_last l a hch hne
    rw [hgl] at key
    refine ⟨by rw [← has]; exact hpa, by omega⟩

/-- **Necessary condition, full color statement.** If a Hamiltonian path
exists, the endpoints are color compatible. -/
theorem hamPath_implies_colorCompatible (width height : ℕ) (s t : Coord)
    (h : HasHamPath width height s t) :
    ColorCompatible width height s t := by
  unfold ColorCompatible
  split
  case isTrue hodd =>
    exact hamPath_odd_parity width height s t ((odd_mul_iff_c width height).mp hodd) h
  case isFalse heven =>
    exact hamPath_implies_diff_parity_of_even width height s t
      (by omega) h

end GridHam
