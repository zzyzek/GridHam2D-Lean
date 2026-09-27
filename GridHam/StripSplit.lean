import GridHam.Forbidden

/-!
# Strip and split: the sufficiency-direction reduction lemmas

This is the Lean counterpart of `_try_strip_{right,up,left,down}` and
`_split_{horizontally,vertically}` in `grid_hampath.py`. Together with the
prime base cases (`PrimeCases.lean`), these are exactly the pieces
`Main.lean`'s strong induction combines to prove sufficiency
(`IsAcceptable → HasHamPath`).

Each lemma states that solvability of a strictly smaller sub-problem
implies solvability of the original -- i.e. these are the *constructive*
direction, matching `_extend_{up,down,left,right}` in the Python (which
build the actual detour path). A full proof of each lemma here would need
to exhibit that detour explicitly and show it's a valid extension, mirroring
`_extend_*`; that construction is not repeated here, only the statements.

STATUS: statements only (`sorry`), mirroring conditions cross-checked
empirically against brute-force search in `verify.py` (1,019,200+ structural
instances, 0 failures) and, separately, against exhaustive existence search
for `width*height ≤ 26` (0 mismatches). Also see `FINDINGS.md` for the one
substantive fix made during the port: reconstruction must undo strips in
*reverse* order, which matters for `Main.lean`'s assembly but not for these
individual lemma statements.

REVISION NOTE: the split lemmas below were rewritten from a previous
version that had a real signature bug (flagged and now fixed): they had
fixed the cut vertex's row/column to `s`'s or `t`'s own coordinate, when
`_split_vertically`/`_split_horizontally` in `grid_hampath.py` actually
*search over* a free cut-row (for a vertical split) or cut-column (for a
horizontal split), independent of either endpoint's coordinate. Each split
direction also has two orientation cases (`s` left/below of `t`, or the
reverse), matching the Python's `is_start_left`/`is_start_below` branches --
stated here as separate lemmas rather than one lemma with a disjunctive
hypothesis, to keep each one's geometry unambiguous.
-/

namespace GridHam

/-! ### List plumbing for splicing two paths -/

/-- `v ∈ allCoords w h` is just "in bounds". -/
theorem mem_allCoords (w h : ℕ) (v : Coord) :
    v ∈ allCoords w h ↔ v.1 < w ∧ v.2 < h := by
  simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨v.1, hx, v.2, hy, rfl⟩

/-- Shift a vertex right by `d` columns. -/
def shiftX (d : ℕ) (v : Coord) : Coord := (v.1 + d, v.2)

theorem adjacent_shiftX (d : ℕ) {v w : Coord} (h : Adjacent v w) :
    Adjacent (shiftX d v) (shiftX d w) := by
  unfold Adjacent at h ⊢
  unfold shiftX
  dsimp only
  omega

/-- Appending two lists with no common element preserves `Nodup`. -/
theorem nodup_append_of : ∀ (l1 l2 : List Coord), l1.Nodup → l2.Nodup →
    (∀ v ∈ l1, ∀ w ∈ l2, v ≠ w) → (l1 ++ l2).Nodup := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h2 _; simpa using h2
  | cons x l ih =>
    intro l2 h1 h2 hd
    obtain ⟨hxn, hl⟩ := List.nodup_cons.mp h1
    show (x :: (l ++ l2)).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hxn h
      · exact hd x (List.mem_cons.mpr (Or.inl rfl)) x h rfl
    · exact ih l2 hl h2 (fun v hv w hw => hd v (List.mem_cons.mpr (Or.inr hv)) w hw)

/-- Mapping an injective function preserves `Nodup`. -/
theorem nodup_map_coord (f : Coord → Coord) (hf : ∀ v w, f v = f w → v = w) :
    ∀ (l : List Coord), l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro hnd
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    show (f a :: l.map f).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
      have hwa : w = a := hf w a hwe
      rw [hwa] at hw
      exact hanot hw
    · exact ih hndt

/-- Shifting preserves grid adjacency along a chain. -/
theorem chainAdjacent_map_shiftX (d : ℕ) : ∀ (l : List Coord),
    chainAdjacent l = true → chainAdjacent (l.map (shiftX d)) = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro hch
    cases l with
    | nil => rfl
    | cons b rest =>
      have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hab, hcl⟩ := hc'
      have hadj : Adjacent a b := by
        unfold adjacentB at hab
        by_contra hcon
        simp [hcon] at hab
      have hA : adjacentB (shiftX d a) (shiftX d b) = true := by
        unfold adjacentB
        exact decide_eq_true (adjacent_shiftX d hadj)
      have hB : chainAdjacent ((b :: rest).map (shiftX d)) = true := ih hcl
      have e : chainAdjacent ((a :: b :: rest).map (shiftX d)) =
          (adjacentB (shiftX d a) (shiftX d b) && chainAdjacent ((b :: rest).map (shiftX d))) :=
        rfl
      simp only [e, hA, hB, Bool.and_self]

/-- Two adjacent-chains joined by an adjacent pair form an adjacent-chain. -/
theorem chainAdjacent_append : ∀ (l1 : List Coord) (b : Coord) (l2 : List Coord) (a : Coord),
    l1.getLast? = some a → chainAdjacent l1 = true → Adjacent a b →
    chainAdjacent (b :: l2) = true → chainAdjacent (l1 ++ b :: l2) = true := by
  intro l1
  induction l1 with
  | nil => intro b l2 a hl; simp at hl
  | cons x l ih =>
    intro b l2 a hl hc hadj hc2
    cases l with
    | nil =>
      have hxa : x = a := by simpa using hl
      have hAB : adjacentB x b = true := by
        unfold adjacentB
        rw [hxa]
        exact decide_eq_true hadj
      have e : chainAdjacent ([x] ++ b :: l2) = (adjacentB x b && chainAdjacent (b :: l2)) := rfl
      simp only [e, hAB, hc2, Bool.and_self]
    | cons y rest =>
      have hc' : (adjacentB x y && chainAdjacent (y :: rest)) = true := by
        simpa [chainAdjacent] using hc
      simp at hc'
      obtain ⟨hxy, hct⟩ := hc'
      have hl' : (y :: rest).getLast? = some a := by
        have e1 : (x :: y :: rest).getLast? = (y :: rest).getLast? := rfl
        rw [e1] at hl
        exact hl
      have hrec := ih b l2 a hl' hct hadj hc2
      have e : chainAdjacent ((x :: y :: rest) ++ b :: l2) =
          (adjacentB x y && chainAdjacent ((y :: rest) ++ b :: l2)) := rfl
      simp only [e, hxy, hrec, Bool.and_self]

/-- The last element of `l1 ++ (c :: m)` is the last element of `c :: m`. -/
theorem getLast?_append_cons : ∀ (l1 : List Coord) (c : Coord) (m : List Coord),
    (l1 ++ c :: m).getLast? = (c :: m).getLast? := by
  intro l1
  induction l1 with
  | nil => intro c m; rfl
  | cons x l ih =>
    intro c m
    cases l with
    | nil => rfl
    | cons y l' =>
      have e : ((x :: y :: l') ++ c :: m).getLast? = ((y :: l') ++ c :: m).getLast? := rfl
      rw [e]
      exact ih c m

/-- The last element of a mapped list (coordinate-valued version). -/
theorem getLast?_map_coord (f : Coord → Coord) : ∀ (l : List Coord) (t : Coord),
    l.getLast? = some t → (l.map f).getLast? = some (f t) := by
  intro l
  induction l with
  | nil => intro t h; simp at h
  | cons a l ih =>
    intro t h
    cases l with
    | nil =>
      have hat : a = t := by simpa using h
      rw [← hat]
      rfl
    | cons b rest =>
      have e1 : (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl
      have e2 : ((a :: b :: rest).map f).getLast? = ((b :: rest).map f).getLast? := rfl
      rw [e1] at h
      rw [e2]
      exact ih t h

/-- Splitting vertically at a column edge `(cut, cutRow) – (cut+1, cutRow)`,
where `s` is the left endpoint (`s.1 < t.1`) and the cut column is strictly
between `s.1` and `t.1`: if the left piece (from `s` to the cut vertex) and
the right piece (from the cut's right-neighbor, in coordinates shifted left
by `cut+1`, to `t`) are both solvable, so is the whole problem. The path is
the left path followed by the right path shifted right by `cut + 1`. -/
theorem splitVertically_preserves_startLeft
    (width height cut cutRow : ℕ) (s t : Coord)
    (_hstartLeft : s.1 < t.1)
    (_hcutRange : s.1 ≤ cut) (hcutRange' : cut < t.1)
    (_hcutRow : cutRow < height)
    (hleft : HasHamPath (cut + 1) height s (cut, cutRow))
    (hright : HasHamPath (width - (cut + 1)) height (0, cutRow)
      (t.1 - (cut + 1), t.2)) :
    HasHamPath width height s t := by
  obtain ⟨pL, lenL, headL, lastL, ndL, inL, covL, chL⟩ := hleft
  obtain ⟨pR, lenR, headR, lastR, ndR, inR, covR, chR⟩ := hright
  cases pR with
  | nil => simp at headR
  | cons b restR =>
    have hb : b = (0, cutRow) := by simpa using headR
    have hbin := inR b (List.mem_cons.mpr (Or.inl rfl))
    unfold InBounds at hbin
    have hwide : cut + 1 < width := by omega
    have hle : cut + 1 ≤ width := by omega
    unfold HasHamPath
    refine ⟨pL ++ (b :: restR).map (shiftX (cut + 1)), ?_⟩
    unfold ValidPath
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- length
      rw [List.length_append, List.length_map, lenL, lenR, ← Nat.add_mul,
        Nat.add_sub_of_le hle]
    · -- head
      cases pL with
      | nil => simp at headL
      | cons a restL => simpa using headL
    · -- last
      rw [show (b :: restR).map (shiftX (cut + 1)) =
          shiftX (cut + 1) b :: restR.map (shiftX (cut + 1)) from rfl,
        getLast?_append_cons,
        show shiftX (cut + 1) b :: restR.map (shiftX (cut + 1)) =
          (b :: restR).map (shiftX (cut + 1)) from rfl,
        getLast?_map_coord (shiftX (cut + 1)) (b :: restR) _ lastR]
      congr 1
      unfold shiftX
      ext
      · show t.1 - (cut + 1) + (cut + 1) = t.1
        omega
      · rfl
    · -- no repeats
      apply nodup_append_of pL _ ndL
      · apply nodup_map_coord (shiftX (cut + 1)) _ (b :: restR) ndR
        intro v w hvw
        unfold shiftX at hvw
        have h1 := congrArg Prod.fst hvw
        have h2 := congrArg Prod.snd hvw
        dsimp only at h1 h2
        ext
        · omega
        · omega
      · intro v hv w hw
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
        have hv' := inL v hv
        unfold InBounds at hv'
        intro heq
        have h1 := congrArg Prod.fst heq
        unfold shiftX at h1
        dsimp only at h1
        omega
    · -- every vertex in bounds
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · have hv' := inL v h
        unfold InBounds at hv' ⊢
        exact ⟨by omega, hv'.2⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
        have hu' := inR u hu
        unfold InBounds at hu' ⊢
        unfold shiftX
        dsimp only
        exact ⟨by omega, hu'.2⟩
    · -- every grid vertex covered
      intro v hv
      obtain ⟨hvx, hvy⟩ := (mem_allCoords width height v).mp hv
      by_cases hc : v.1 ≤ cut
      · exact List.mem_append.mpr (Or.inl
          (covL v ((mem_allCoords (cut + 1) height v).mpr ⟨by omega, hvy⟩)))
      · have hu := covR (v.1 - (cut + 1), v.2)
          ((mem_allCoords (width - (cut + 1)) height _).mpr ⟨by dsimp only; omega, hvy⟩)
        refine List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hu, ?_⟩))
        unfold shiftX
        ext
        · show v.1 - (cut + 1) + (cut + 1) = v.1
          omega
        · rfl
    · -- consecutive vertices adjacent
      have hadj : Adjacent (cut, cutRow) (shiftX (cut + 1) b) := by
        rw [hb]
        unfold Adjacent shiftX
        simp
      have hchR' : chainAdjacent ((b :: restR).map (shiftX (cut + 1))) = true :=
        chainAdjacent_map_shiftX (cut + 1) (b :: restR) chR
      exact chainAdjacent_append pL (shiftX (cut + 1) b) (restR.map (shiftX (cut + 1)))
        (cut, cutRow) lastL chL hadj hchR'

/-! ### Symmetries of Hamiltonian paths: reversal and transpose -/

theorem adjacent_symm {v w : Coord} (h : Adjacent v w) : Adjacent w v := by
  unfold Adjacent at h ⊢
  omega

/-- Any map that preserves adjacency preserves adjacent-chains. -/
theorem chainAdjacent_map (f : Coord → Coord) (hf : ∀ v w, Adjacent v w → Adjacent (f v) (f w)) :
    ∀ (l : List Coord), chainAdjacent l = true → chainAdjacent (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro hch
    cases l with
    | nil => rfl
    | cons b rest =>
      have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hab, hcl⟩ := hc'
      have hadj : Adjacent a b := by
        unfold adjacentB at hab
        by_contra hcon
        simp [hcon] at hab
      have hA : adjacentB (f a) (f b) = true := by
        unfold adjacentB
        exact decide_eq_true (hf a b hadj)
      have hB : chainAdjacent ((b :: rest).map f) = true := ih hcl
      have e : chainAdjacent ((a :: b :: rest).map f) =
          (adjacentB (f a) (f b) && chainAdjacent ((b :: rest).map f)) := rfl
      simp only [e, hA, hB, Bool.and_self]

/-- Reversing an adjacent-chain gives an adjacent-chain. -/
theorem chainAdjacent_reverse : ∀ (l : List Coord),
    chainAdjacent l = true → chainAdjacent l.reverse = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro hch
    cases l with
    | nil => rfl
    | cons b rest =>
      have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hab, hcl⟩ := hc'
      have hadj : Adjacent a b := by
        unfold adjacentB at hab
        by_contra hcon
        simp [hcon] at hab
      rw [List.reverse_cons]
      exact chainAdjacent_append (b :: rest).reverse a [] b (by simp) (ih hcl)
        (adjacent_symm hadj) rfl

/-- Reversing a Hamiltonian path swaps its endpoints. -/
theorem hasHamPath_reverse {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) : HasHamPath width height t s := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := h
  unfold HasHamPath
  refine ⟨p.reverse, ?_⟩
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_reverse]
    exact hlen
  · simpa using hlast
  · simpa using hhead
  · exact List.nodup_reverse.mpr hnd
  · intro v hv
    exact hin v (List.mem_reverse.mp hv)
  · intro v hv
    exact List.mem_reverse.mpr (hcov v hv)
  · exact chainAdjacent_reverse p hch

/-- Swap the two coordinates of a vertex. -/
def swapXY (v : Coord) : Coord := (v.2, v.1)

theorem adjacent_swapXY {v w : Coord} (h : Adjacent v w) : Adjacent (swapXY v) (swapXY w) := by
  unfold Adjacent at h ⊢
  unfold swapXY
  dsimp only
  omega

/-- Transposing a Hamiltonian path on a `width × height` grid gives one on
the `height × width` grid. -/
theorem hasHamPath_transpose {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) :
    HasHamPath height width (swapXY s) (swapXY t) := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := h
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    unfold HasHamPath
    refine ⟨(a :: l).map swapXY, ?_⟩
    unfold ValidPath
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlen, Nat.mul_comm]
    · show (swapXY a :: l.map swapXY).head? = some (swapXY s)
      rw [has]
      rfl
    · exact getLast?_map_coord swapXY (a :: l) t hlast
    · apply nodup_map_coord swapXY _ (a :: l) hnd
      intro v w hvw
      unfold swapXY at hvw
      have h1 := congrArg Prod.fst hvw
      have h2 := congrArg Prod.snd hvw
      dsimp only at h1 h2
      ext
      · omega
      · omega
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have hu' := hin u hu
      unfold InBounds at hu' ⊢
      unfold swapXY
      dsimp only
      exact ⟨hu'.2, hu'.1⟩
    · intro v hv
      obtain ⟨hx, hy⟩ := (mem_allCoords height width v).mp hv
      have hu := hcov (swapXY v) ((mem_allCoords width height _).mpr
        ⟨by unfold swapXY; dsimp only; exact hy, by unfold swapXY; dsimp only; exact hx⟩)
      exact List.mem_map.mpr ⟨swapXY v, hu, rfl⟩
    · exact chainAdjacent_map swapXY (fun v w hvw => adjacent_swapXY hvw) (a :: l) hch

/-- Symmetric to `splitVertically_preserves_startLeft` when `t` is the left
endpoint instead (`t.1 < s.1`). -/
theorem splitVertically_preserves_startRight
    (width height cut cutRow : ℕ) (s t : Coord)
    (hstartRight : t.1 < s.1)
    (hcutRange : t.1 ≤ cut) (hcutRange' : cut < s.1)
    (hcutRow : cutRow < height)
    (hleft : HasHamPath (cut + 1) height (cut, cutRow) t)
    (hright : HasHamPath (width - (cut + 1)) height (0, cutRow)
      (s.1 - (cut + 1), s.2)) :
    HasHamPath width height s t :=
  hasHamPath_reverse (splitVertically_preserves_startLeft width height cut cutRow t s
    hstartRight hcutRange hcutRange' hcutRow (hasHamPath_reverse hleft) hright)

/-- Splitting horizontally at a row edge `(cutCol, cut) – (cutCol, cut+1)`,
symmetric to `splitVertically_preserves_startLeft` with `s` below `t`
(`s.2 < t.2`). `cutCol` is the free parameter here. -/
theorem splitHorizontally_preserves_startBelow
    (width height cut cutCol : ℕ) (s t : Coord)
    (hstartBelow : s.2 < t.2)
    (hcutRange : s.2 ≤ cut) (hcutRange' : cut < t.2)
    (hcutCol : cutCol < width)
    (hlower : HasHamPath width (cut + 1) s (cutCol, cut))
    (hupper : HasHamPath width (height - (cut + 1)) (cutCol, 0)
      (t.1, t.2 - (cut + 1))) :
    HasHamPath width height s t := by
  have hl : HasHamPath (cut + 1) width (swapXY s) (cut, cutCol) :=
    hasHamPath_transpose hlower
  have hu : HasHamPath (height - (cut + 1)) width (0, cutCol)
      ((swapXY t).1 - (cut + 1), (swapXY t).2) :=
    hasHamPath_transpose hupper
  have hT : HasHamPath height width (swapXY s) (swapXY t) :=
    splitVertically_preserves_startLeft height width cut cutCol (swapXY s) (swapXY t)
      hstartBelow hcutRange hcutRange' hcutCol hl hu
  exact hasHamPath_transpose hT

/-- Symmetric to `splitHorizontally_preserves_startBelow` when `t` is below
`s` instead (`t.2 < s.2`). -/
theorem splitHorizontally_preserves_startAbove
    (width height cut cutCol : ℕ) (s t : Coord)
    (hstartAbove : t.2 < s.2)
    (hcutRange : t.2 ≤ cut) (hcutRange' : cut < s.2)
    (hcutCol : cutCol < width)
    (hlower : HasHamPath width (cut + 1) t (cutCol, cut))
    (hupper : HasHamPath width (height - (cut + 1)) (cutCol, 0)
      (s.1, s.2 - (cut + 1))) :
    HasHamPath width height s t :=
  hasHamPath_reverse (splitHorizontally_preserves_startBelow width height cut cutCol t s
    hstartAbove hcutRange hcutRange' hcutCol hlower hupper)

/-! ### Building blocks for stripping -/

/-- Prepending a vertex adjacent to the head keeps an adjacent-chain. -/
theorem chainAdjacent_cons (x y : Coord) (l : List Coord) (hh : l.head? = some y)
    (hadj : Adjacent x y) (hl : chainAdjacent l = true) : chainAdjacent (x :: l) = true := by
  cases l with
  | nil => simp at hh
  | cons z rest =>
    have hzy : z = y := by simpa using hh
    have hA : adjacentB x z = true := by
      unfold adjacentB
      rw [hzy]
      exact decide_eq_true hadj
    have e : chainAdjacent (x :: z :: rest) = (adjacentB x z && chainAdjacent (z :: rest)) := rfl
    simp only [e, hA, hl, Bool.and_self]

/-- `colSeg c lo k` is the vertical run `(c, lo+k), (c, lo+k-1), …, (c, lo)`. -/
def colSeg (c lo : ℕ) : ℕ → List Coord
  | 0 => [(c, lo)]
  | k + 1 => (c, lo + (k + 1)) :: colSeg c lo k

theorem colSeg_head (c lo k : ℕ) : (colSeg c lo k).head? = some (c, lo + k) := by
  cases k with
  | zero => rfl
  | succ k => rfl

theorem colSeg_last (c lo : ℕ) : ∀ k, (colSeg c lo k).getLast? = some (c, lo) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      show (colSeg c lo (k' + 1)).getLast? = some (c, lo)
      exact ih

theorem colSeg_length (c lo : ℕ) : ∀ k, (colSeg c lo k).length = k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((c, lo + (k + 1)) :: colSeg c lo k).length = k + 1 + 1
    rw [List.length_cons, ih]

theorem mem_colSeg (c lo : ℕ) : ∀ k (v : Coord),
    v ∈ colSeg c lo k ↔ v.1 = c ∧ lo ≤ v.2 ∧ v.2 ≤ lo + k := by
  intro k
  induction k with
  | zero =>
    intro v
    rw [show colSeg c lo 0 = [(c, lo)] from rfl, List.mem_singleton]
    constructor
    · intro h
      rw [h]
      exact ⟨rfl, Nat.le_refl _, show lo ≤ lo + 0 by omega⟩
    · rintro ⟨h1, h2, h3⟩
      ext
      · show v.1 = c
        exact h1
      · show v.2 = lo
        omega
  | succ k ih =>
    intro v
    rw [show colSeg c lo (k + 1) = (c, lo + (k + 1)) :: colSeg c lo k from rfl,
      List.mem_cons, ih v]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · rw [h]
        exact ⟨rfl, show lo ≤ lo + (k + 1) by omega, show lo + (k + 1) ≤ lo + (k + 1) by omega⟩
      · exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      by_cases hk : v.2 = lo + (k + 1)
      · left
        ext
        · show v.1 = c
          exact h1
        · show v.2 = lo + (k + 1)
          exact hk
      · right
        exact ⟨h1, h2, by omega⟩

theorem colSeg_nodup (c lo : ℕ) : ∀ k, (colSeg c lo k).Nodup := by
  intro k
  induction k with
  | zero => simp [colSeg]
  | succ k ih =>
    show ((c, lo + (k + 1)) :: colSeg c lo k).Nodup
    rw [List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hm
    have h := (mem_colSeg c lo k _).mp hm
    dsimp only at h
    omega

theorem colSeg_chain (c lo : ℕ) : ∀ k, chainAdjacent (colSeg c lo k) = true := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    exact chainAdjacent_cons (c, lo + (k + 1)) (c, lo + k) (colSeg c lo k) (colSeg_head c lo k)
      (by unfold Adjacent; dsimp only; omega) ih

/-- **Degree argument.** In an adjacent-chain with no repeats lying in
columns `≤ X`, any vertex in column `X` that is neither the first nor the
last element has a neighbour on the chain in the same column (its two chain
neighbours are distinct, and only one can be its left neighbour). So the
chain contains two consecutive vertices in column `X`. -/
theorem exists_col_edge (X : ℕ) : ∀ (l : List Coord), chainAdjacent l = true → l.Nodup →
    (∀ u ∈ l, u.1 ≤ X) → ∀ v ∈ l, v.1 = X → l.head? ≠ some v → l.getLast? ≠ some v →
    ∃ l1 a b l2, l = l1 ++ a :: b :: l2 ∧ a.1 = X ∧ b.1 = X := by
  intro l
  induction l with
  | nil => intro _ _ _ v hv; simp at hv
  | cons a rest ih =>
    intro hch hnd hle v hv hvx hhd hlst
    rcases List.mem_cons.mp hv with hva | hvr
    · exfalso
      apply hhd
      rw [hva]
      rfl
    · cases rest with
      | nil => simp at hvr
      | cons b rest' =>
        have hc' : (adjacentB a b && chainAdjacent (b :: rest')) = true := by
          simpa [chainAdjacent] using hch
        simp at hc'
        obtain ⟨hab, hcl⟩ := hc'
        have hadjab : Adjacent a b := by
          unfold adjacentB at hab
          by_contra hcon
          simp [hcon] at hab
        obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
        have hlst' : (b :: rest').getLast? ≠ some v := by
          have e : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
          rw [e] at hlst
          exact hlst
        have hle' : ∀ u ∈ b :: rest', u.1 ≤ X :=
          fun u hu => hle u (List.mem_cons.mpr (Or.inr hu))
        by_cases hvb : v = b
        · cases rest' with
          | nil =>
            exfalso
            apply hlst'
            rw [hvb]
            rfl
          | cons c rest'' =>
            have hc2 : (adjacentB b c && chainAdjacent (c :: rest'')) = true := by
              simpa [chainAdjacent] using hcl
            simp at hc2
            obtain ⟨hbc, _⟩ := hc2
            have hadjbc : Adjacent b c := by
              unfold adjacentB at hbc
              by_contra hcon
              simp [hcon] at hbc
            have hax := hle a (by simp)
            have hcx := hle c (by simp)
            have hbx : b.1 = X := by
              rw [← hvb]
              exact hvx
            by_cases ha : a.1 = X
            · exact ⟨[], a, b, c :: rest'', rfl, ha, hbx⟩
            · by_cases hc : c.1 = X
              · exact ⟨[a], b, c, rest'', rfl, hbx, hc⟩
              · exfalso
                have hac : a = c := by
                  unfold Adjacent at hadjab hadjbc
                  ext
                  · omega
                  · omega
                apply hanot
                rw [hac]
                simp
        · have hhd' : (b :: rest').head? ≠ some v := by
            intro h
            apply hvb
            have hbv : b = v := by simpa using h
            exact hbv.symm
          obtain ⟨l1, x, y, l2, heq, hx, hy⟩ := ih hcl hndt hle' v hvr hvx hhd' hlst'
          exact ⟨a :: l1, x, y, l2, by simp [heq], hx, hy⟩

/-! ### Stripping: inserting a two-column detour -/

theorem chainAdjacent_tail (x : Coord) (L : List Coord) (h : chainAdjacent (x :: L) = true) :
    chainAdjacent L = true := by
  cases L with
  | nil => rfl
  | cons z r =>
    have hc' : (adjacentB x z && chainAdjacent (z :: r)) = true := by
      simpa [chainAdjacent] using h
    simp at hc'
    exact hc'.2

theorem chainAdjacent_suffix : ∀ (l1 m : List Coord),
    chainAdjacent (l1 ++ m) = true → chainAdjacent m = true := by
  intro l1
  induction l1 with
  | nil => intro m h; exact h
  | cons x l ih => intro m h; exact ih m (chainAdjacent_tail x (l ++ m) h)

/-- Replacing everything after `a` by another chain that starts at `a`. -/
theorem chainAdjacent_replace_tail : ∀ (l1 : List Coord) (a : Coord) (m m' : List Coord),
    chainAdjacent (l1 ++ a :: m) = true → chainAdjacent (a :: m') = true →
    chainAdjacent (l1 ++ a :: m') = true := by
  intro l1
  induction l1 with
  | nil => intro a m m' _ h2; exact h2
  | cons x l ih =>
    intro a m m' h1 h2
    cases l with
    | nil =>
      have hc' : (adjacentB x a && chainAdjacent (a :: m)) = true := by
        simpa [chainAdjacent] using h1
      simp at hc'
      obtain ⟨hxa, _⟩ := hc'
      have hadj : Adjacent x a := by
        unfold adjacentB at hxa
        by_contra hcon
        simp [hcon] at hxa
      exact chainAdjacent_cons x a (a :: m') rfl hadj h2
    | cons z l' =>
      have hc' : (adjacentB x z && chainAdjacent (z :: (l' ++ a :: m))) = true := by
        simpa [chainAdjacent] using h1
      simp at hc'
      obtain ⟨hxz, hcl⟩ := hc'
      have hadj : Adjacent x z := by
        unfold adjacentB at hxz
        by_contra hcon
        simp [hcon] at hxz
      have hrec := ih a m m' hcl h2
      exact chainAdjacent_cons x z _ rfl hadj hrec

/-- Joining two chains whose junction is adjacent (general form). -/
theorem chainAdjacent_append' (l1 M : List Coord) (a b : Coord) (hl : l1.getLast? = some a)
    (h1 : chainAdjacent l1 = true) (hM : M.head? = some b) (hadj : Adjacent a b)
    (h2 : chainAdjacent M = true) : chainAdjacent (l1 ++ M) = true := by
  cases M with
  | nil => simp at hM
  | cons c r =>
    have hcb : c = b := by simpa using hM
    rw [hcb] at h2 ⊢
    exact chainAdjacent_append l1 b r a hl h1 hadj h2

theorem head?_append_of_head (l M : List Coord) (x : Coord) (h : l.head? = some x) :
    (l ++ M).head? = some x := by
  cases l with
  | nil => simp at h
  | cons z r => simpa using h

theorem mem_insert_iff (u : Coord) (l1 D l2 : List Coord) (a b : Coord) :
    u ∈ l1 ++ a :: (D ++ b :: l2) ↔ u ∈ D ∨ u ∈ l1 ++ a :: b :: l2 := by
  simp only [List.mem_append, List.mem_cons]
  tauto

/-- Inserting a `Nodup` list with no common elements between `a` and `b`
keeps `Nodup`. -/
theorem nodup_insert (D : List Coord) (hD : D.Nodup) : ∀ (l1 : List Coord) (a b : Coord)
    (l2 : List Coord), (l1 ++ a :: b :: l2).Nodup → (∀ u ∈ D, u ∉ l1 ++ a :: b :: l2) →
    (l1 ++ a :: (D ++ b :: l2)).Nodup := by
  intro l1
  induction l1 with
  | nil =>
    intro a b l2 h hdisj
    show (a :: (D ++ b :: l2)).Nodup
    have h' : (a :: b :: l2).Nodup := h
    obtain ⟨han, hbl⟩ := List.nodup_cons.mp h'
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hd | hd
      · exact hdisj a hd (by simp)
      · exact han hd
    · apply nodup_append_of D (b :: l2) hD hbl
      intro u hu v hv heq
      apply hdisj u hu
      rw [heq]
      show v ∈ a :: b :: l2
      exact List.mem_cons.mpr (Or.inr hv)
  | cons x l ih =>
    intro a b l2 h hdisj
    show (x :: (l ++ a :: (D ++ b :: l2))).Nodup
    have h' : (x :: (l ++ a :: b :: l2)).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases (mem_insert_iff x l D l2 a b).mp hm with hd | hp
      · exact hdisj x hd (List.mem_cons.mpr (Or.inl rfl))
      · exact hxn hp
    · exact ih a b l2 hrest (fun u hu hm => hdisj u hu (List.mem_cons.mpr (Or.inr hm)))

/-- List-level reversal (keeps track of the actual path). -/
theorem validPath_reverse {width height : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath width height s t p) : ValidPath width height t s p.reverse := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_reverse]
    exact hlen
  · simpa using hlast
  · simpa using hhead
  · exact List.nodup_reverse.mpr hnd
  · intro v hv
    exact hin v (List.mem_reverse.mp hv)
  · intro v hv
    exact List.mem_reverse.mpr (hcov v hv)
  · exact chainAdjacent_reverse p hch

/-- The detour through columns `w` and `w+1`, inserted between `(w-1, y)`
and `(w-1, y+1)`: down column `w` from row `y` to `0`, up column `w+1` from
`0` to `h-1`, down column `w` from `h-1` to `y+1`. -/
def rightDetour (w h y : ℕ) : List Coord :=
  colSeg w 0 y ++ ((colSeg (w + 1) 0 (h - 1)).reverse ++ colSeg w (y + 1) (h - 1 - (y + 1)))

theorem mem_rightDetour (w h y : ℕ) (hy : y + 1 < h) (u : Coord) :
    u ∈ rightDetour w h y ↔ (u.1 = w ∧ u.2 < h) ∨ (u.1 = w + 1 ∧ u.2 < h) := by
  unfold rightDetour
  simp only [List.mem_append, List.mem_reverse, mem_colSeg]
  constructor
  · intro hu
    omega
  · intro hu
    omega

theorem rightDetour_length (w h y : ℕ) (hy : y + 1 < h) :
    (rightDetour w h y).length = 2 * h := by
  unfold rightDetour
  simp only [List.length_append, List.length_reverse, colSeg_length]
  omega

theorem rightDetour_nodup (w h y : ℕ) (_hy : y + 1 < h) : (rightDetour w h y).Nodup := by
  unfold rightDetour
  apply nodup_append_of _ _ (colSeg_nodup w 0 y)
  · apply nodup_append_of _ _ (List.nodup_reverse.mpr (colSeg_nodup (w + 1) 0 (h - 1)))
      (colSeg_nodup w (y + 1) _)
    intro u hu v hv heq
    rw [List.mem_reverse, mem_colSeg] at hu
    rw [mem_colSeg] at hv
    rw [heq] at hu
    omega
  · intro u hu v hv heq
    rw [mem_colSeg] at hu
    rw [List.mem_append, List.mem_reverse, mem_colSeg, mem_colSeg] at hv
    rw [heq] at hu
    omega

theorem chain_detour (w h y : ℕ) (hw : 1 ≤ w) (hy : y + 1 < h) (l2 : List Coord)
    (hb : chainAdjacent ((w - 1, y + 1) :: l2) = true) :
    chainAdjacent ((w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)) = true := by
  unfold rightDetour
  rw [List.append_assoc, List.append_assoc]
  have c3 : chainAdjacent (colSeg w (y + 1) (h - 1 - (y + 1)) ++ (w - 1, y + 1) :: l2) = true :=
    chainAdjacent_append' _ _ (w, y + 1) (w - 1, y + 1) (colSeg_last w (y + 1) _)
      (colSeg_chain _ _ _) rfl (by unfold Adjacent; dsimp only; omega) hb
  have c2 : chainAdjacent ((colSeg (w + 1) 0 (h - 1)).reverse ++
      (colSeg w (y + 1) (h - 1 - (y + 1)) ++ (w - 1, y + 1) :: l2)) = true :=
    chainAdjacent_append' _ _ (w + 1, 0 + (h - 1)) (w, y + 1 + (h - 1 - (y + 1)))
      (by simp [colSeg_head]) (chainAdjacent_reverse _ (colSeg_chain _ _ _))
      (head?_append_of_head _ _ _ (colSeg_head w (y + 1) _))
      (by unfold Adjacent; dsimp only; omega) c3
  have c1 : chainAdjacent (colSeg w 0 y ++ ((colSeg (w + 1) 0 (h - 1)).reverse ++
      (colSeg w (y + 1) (h - 1 - (y + 1)) ++ (w - 1, y + 1) :: l2))) = true :=
    chainAdjacent_append' _ _ (w, 0) (w + 1, 0) (colSeg_last w 0 y) (colSeg_chain _ _ _)
      (head?_append_of_head _ _ _ (by simp [colSeg_last]))
      (by unfold Adjacent; dsimp only; omega) c2
  exact chainAdjacent_cons _ (w, 0 + y) _ (head?_append_of_head _ _ _ (colSeg_head w 0 y))
    (by unfold Adjacent; dsimp only; omega) c1

/-- **Strip extension (edge going up).** A Hamiltonian path on `w × h` with
consecutive vertices `(w-1, y), (w-1, y+1)` extends to one on `(w+2) × h`
with the same endpoints, by inserting `rightDetour w h y` between them. -/
theorem extend_right_up (w h : ℕ) (s t : Coord) (l1 l2 : List Coord) (y : ℕ) (hw : 1 ≤ w)
    (hv : ValidPath w h s t (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2)) :
    ValidPath (w + 2) h s t (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv
  have hbin := hin (w - 1, y + 1) (by simp)
  unfold InBounds at hbin
  dsimp only at hbin
  have hy : y + 1 < h := hbin.2
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length
    have e : (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)).length =
        (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2).length + (rightDetour w h y).length := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [e, hlen, rightDetour_length w h y hy, Nat.add_mul]
  · -- head
    have e : (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)).head? =
        (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2).head? := by
      cases l1 <;> rfl
    exact e.trans hhead
  · -- last
    have e1 : (l1 ++ (w - 1, y) :: (rightDetour w h y ++ (w - 1, y + 1) :: l2)).getLast? =
        ((w - 1, y + 1) :: l2).getLast? :=
      (getLast?_append_cons l1 (w - 1, y) (rightDetour w h y ++ (w - 1, y + 1) :: l2)).trans
        (getLast?_append_cons ((w - 1, y) :: rightDetour w h y) (w - 1, y + 1) l2)
    have e2 : (l1 ++ (w - 1, y) :: (w - 1, y + 1) :: l2).getLast? =
        ((w - 1, y + 1) :: l2).getLast? :=
      (getLast?_append_cons l1 (w - 1, y) ((w - 1, y + 1) :: l2)).trans rfl
    exact e1.trans (e2.symm.trans hlast)
  · -- no repeats
    apply nodup_insert _ (rightDetour_nodup w h y hy) l1 _ _ l2 hnd
    intro u hu hm
    rw [mem_rightDetour w h y hy] at hu
    have hu' := hin u hm
    unfold InBounds at hu'
    omega
  · -- in bounds
    intro u hu
    rcases (mem_insert_iff u l1 _ l2 _ _).mp hu with hd | hp
    · rw [mem_rightDetour w h y hy] at hd
      unfold InBounds
      omega
    · have hu' := hin u hp
      unfold InBounds at hu' ⊢
      omega
  · -- coverage
    intro v hv
    obtain ⟨hvx, hvy⟩ := (mem_allCoords (w + 2) h v).mp hv
    by_cases hc : v.1 < w
    · exact (mem_insert_iff v l1 _ l2 _ _).mpr
        (Or.inr (hcov v ((mem_allCoords w h v).mpr ⟨hc, hvy⟩)))
    · exact (mem_insert_iff v l1 _ l2 _ _).mpr
        (Or.inl ((mem_rightDetour w h y hy v).mpr (by omega)))
  · -- adjacency
    have hb : chainAdjacent ((w - 1, y + 1) :: l2) = true :=
      chainAdjacent_suffix (l1 ++ [(w - 1, y)]) _ (by simpa using hch)
    exact chainAdjacent_replace_tail l1 (w - 1, y) ((w - 1, y + 1) :: l2) _ hch
      (chain_detour w h y hw hy l2 hb)

/-- **Stripping the rightmost two columns.** If the `(width-2) × height`
problem is solvable, neither endpoint lies in the two new columns, and some
vertex of the smaller grid's rightmost column (`x = width - 3`) is neither
`s` nor `t`, then the full problem is solvable. The last hypothesis is what
guarantees an edge of the smaller path along that column (degree argument,
`exists_col_edge`); without it the statement is false (e.g. `5 × 1`). -/
theorem stripRight_preserves (width height : ℕ) (s t : Coord)
    (hs : s.1 + 2 < width) (_ht : t.1 + 2 < width)
    (hfree : ∃ y, y < height ∧ (width - 3, y) ≠ s ∧ (width - 3, y) ≠ t)
    (h : HasHamPath (width - 2) height s t) :
    HasHamPath width height s t := by
  obtain ⟨y0, hy0, hys, hyt⟩ := hfree
  obtain ⟨p, hv⟩ := h
  have hv0 := hv
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hv0
  have hw1 : 1 ≤ width - 2 := by omega
  have hvmem : (width - 3, y0) ∈ p :=
    hcov _ ((mem_allCoords _ _ _).mpr ⟨by dsimp only; omega, hy0⟩)
  have hhd : p.head? ≠ some (width - 3, y0) := by
    intro h
    rw [hhead] at h
    exact hys (Option.some.inj h).symm
  have hlst : p.getLast? ≠ some (width - 3, y0) := by
    intro h
    rw [hlast] at h
    exact hyt (Option.some.inj h).symm
  have hbound : ∀ u ∈ p, u.1 ≤ width - 3 := by
    intro u hu
    have hu' := hin u hu
    unfold InBounds at hu'
    omega
  obtain ⟨l1, a, b, l2, hp, ha, hb⟩ :=
    exists_col_edge (width - 3) p hch hnd hbound _ hvmem rfl hhd hlst
  have hc2 : chainAdjacent (a :: b :: l2) = true :=
    chainAdjacent_suffix l1 _ (by rw [← hp]; exact hch)
  have hc' : (adjacentB a b && chainAdjacent (b :: l2)) = true := by
    simpa [chainAdjacent] using hc2
  simp at hc'
  obtain ⟨hab, _⟩ := hc'
  have hadj : Adjacent a b := by
    unfold adjacentB at hab
    by_contra hcon
    simp [hcon] at hab
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, byy⟩ := b
  dsimp only at ha hb
  unfold Adjacent at hadj
  dsimp only at hadj
  have hax : ax = width - 2 - 1 := by omega
  have hbx : bx = width - 2 - 1 := by omega
  rw [hax, hbx] at hp
  have e : width - 2 + 2 = width := by omega
  rcases (show byy = ay + 1 ∨ ay = byy + 1 by omega) with hup | hdown
  · rw [hup] at hp
    have hv2 : ValidPath (width - 2) height s t
        (l1 ++ (width - 2 - 1, ay) :: (width - 2 - 1, ay + 1) :: l2) := by
      rw [← hp]
      exact hv
    have hN := extend_right_up (width - 2) height s t l1 l2 ay hw1 hv2
    rw [e] at hN
    exact ⟨_, hN⟩
  · rw [hdown] at hp
    have hrev : p.reverse =
        l2.reverse ++ (width - 2 - 1, byy) :: (width - 2 - 1, byy + 1) :: l1.reverse := by
      rw [hp]
      simp
    have hv2 : ValidPath (width - 2) height t s
        (l2.reverse ++ (width - 2 - 1, byy) :: (width - 2 - 1, byy + 1) :: l1.reverse) := by
      rw [← hrev]
      exact validPath_reverse hv
    have hN := extend_right_up (width - 2) height t s l2.reverse l1.reverse byy hw1 hv2
    rw [e] at hN
    exact ⟨_, validPath_reverse hN⟩

/-- **Stripping the top two rows**, by transposing `stripRight_preserves`. -/
theorem stripUp_preserves (width height : ℕ) (s t : Coord)
    (hs : s.2 + 2 < height) (ht : t.2 + 2 < height)
    (hfree : ∃ x, x < width ∧ (x, height - 3) ≠ s ∧ (x, height - 3) ≠ t)
    (h : HasHamPath width (height - 2) s t) :
    HasHamPath width height s t := by
  obtain ⟨x, hx, hxs, hxt⟩ := hfree
  have hT : HasHamPath height width (swapXY s) (swapXY t) :=
    stripRight_preserves height width (swapXY s) (swapXY t) hs ht
      ⟨x, hx, fun heq => hxs (congrArg swapXY heq), fun heq => hxt (congrArg swapXY heq)⟩
      (hasHamPath_transpose h)
  exact hasHamPath_transpose hT

/-! ### Reflection -/

theorem mem_of_getLast? : ∀ (l : List Coord) (t : Coord), l.getLast? = some t → t ∈ l := by
  intro l
  induction l with
  | nil => intro t h; simp at h
  | cons a l ih =>
    intro t h
    cases l with
    | nil =>
      have hat : a = t := by simpa using h
      rw [← hat]
      simp
    | cons b rest =>
      have e1 : (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl
      rw [e1] at h
      exact List.mem_cons.mpr (Or.inr (ih t h))

/-- Both endpoints of a Hamiltonian path are in bounds. -/
theorem hasHamPath_bounds {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) : InBounds width height s ∧ InBounds width height t := by
  obtain ⟨p, _, hhead, hlast, _, hin, _, _⟩ := h
  refine ⟨hin s ?_, hin t (mem_of_getLast? p t hlast)⟩
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    rw [← has]
    simp

theorem nodup_map_coord_on (f : Coord → Coord) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ u ∈ l, f v = f u → v = u) → l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hinj hnd
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    show (f a :: l.map f).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
      have hwa : w = a :=
        hinj w (List.mem_cons.mpr (Or.inr hw)) a (List.mem_cons.mpr (Or.inl rfl)) hwe
      rw [hwa] at hw
      exact hanot hw
    · exact ih (fun v hv u hu =>
        hinj v (List.mem_cons.mpr (Or.inr hv)) u (List.mem_cons.mpr (Or.inr hu))) hndt

theorem chainAdjacent_map_on (f : Coord → Coord) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ u ∈ l, Adjacent v u → Adjacent (f v) (f u)) →
    chainAdjacent l = true → chainAdjacent (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hf hch
    cases l with
    | nil => rfl
    | cons b rest =>
      have hc' : (adjacentB a b && chainAdjacent (b :: rest)) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hab, hcl⟩ := hc'
      have hadj : Adjacent a b := by
        unfold adjacentB at hab
        by_contra hcon
        simp [hcon] at hab
      have hA : adjacentB (f a) (f b) = true := by
        unfold adjacentB
        exact decide_eq_true (hf a (by simp) b (by simp) hadj)
      have hB : chainAdjacent ((b :: rest).map f) = true :=
        ih (fun v hv u hu =>
          hf v (List.mem_cons.mpr (Or.inr hv)) u (List.mem_cons.mpr (Or.inr hu))) hcl
      have e : chainAdjacent ((a :: b :: rest).map f) =
          (adjacentB (f a) (f b) && chainAdjacent ((b :: rest).map f)) := rfl
      simp only [e, hA, hB, Bool.and_self]

/-- Mirror a vertex left-to-right in a grid of width `w`. -/
def reflectX (w : ℕ) (v : Coord) : Coord := (w - 1 - v.1, v.2)

/-- Reflecting a Hamiltonian path left-to-right gives a Hamiltonian path. -/
theorem hasHamPath_reflect {width height : ℕ} {s t : Coord}
    (h : HasHamPath width height s t) :
    HasHamPath width height (reflectX width s) (reflectX width t) := by
  obtain ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := h
  cases p with
  | nil => simp at hhead
  | cons a l =>
    have has : a = s := by simpa using hhead
    unfold HasHamPath
    refine ⟨(a :: l).map (reflectX width), ?_⟩
    unfold ValidPath
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map, hlen]
    · show (reflectX width a :: l.map (reflectX width)).head? = some (reflectX width s)
      rw [has]
      rfl
    · exact getLast?_map_coord (reflectX width) (a :: l) t hlast
    · apply nodup_map_coord_on (reflectX width) (a :: l) _ hnd
      intro v hv u hu hvu
      have hv' := hin v hv
      have hu' := hin u hu
      unfold InBounds at hv' hu'
      unfold reflectX at hvu
      have h1 := congrArg Prod.fst hvu
      have h2 := congrArg Prod.snd hvu
      dsimp only at h1 h2
      ext
      · omega
      · omega
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have hu' := hin u hu
      unfold InBounds at hu' ⊢
      unfold reflectX
      dsimp only
      exact ⟨by omega, hu'.2⟩
    · intro v hv
      obtain ⟨hx, hy⟩ := (mem_allCoords width height v).mp hv
      have hu := hcov (reflectX width v) ((mem_allCoords width height _).mpr
        ⟨by unfold reflectX; dsimp only; omega, by unfold reflectX; dsimp only; exact hy⟩)
      refine List.mem_map.mpr ⟨reflectX width v, hu, ?_⟩
      unfold reflectX
      ext
      · show width - 1 - (width - 1 - v.1) = v.1
        omega
      · rfl
    · apply chainAdjacent_map_on (reflectX width) (a :: l) _ hch
      intro v hv u hu hadj
      have hv' := hin v hv
      have hu' := hin u hu
      unfold InBounds at hv' hu'
      unfold Adjacent at hadj ⊢
      unfold reflectX
      dsimp only
      omega

/-- **Stripping the leftmost two columns**, by reflecting `stripRight_preserves`.
The smaller problem is stated in coordinates shifted left by 2. -/
theorem stripLeft_preserves (width height : ℕ) (s t : Coord)
    (hs : 2 ≤ s.1) (ht : 2 ≤ t.1)
    (hfree : ∃ y, y < height ∧ (2, y) ≠ s ∧ (2, y) ≠ t)
    (h : HasHamPath (width - 2) height (s.1 - 2, s.2) (t.1 - 2, t.2)) :
    HasHamPath width height s t := by
  obtain ⟨y, hy, hys, hyt⟩ := hfree
  have hb := hasHamPath_bounds h
  unfold InBounds at hb
  dsimp only at hb
  obtain ⟨⟨hsx, hsy⟩, ⟨htx, hty⟩⟩ := hb
  have hR := hasHamPath_reflect h
  have es : reflectX (width - 2) (s.1 - 2, s.2) = reflectX width s := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  have et : reflectX (width - 2) (t.1 - 2, t.2) = reflectX width t := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  rw [es, et] at hR
  have hS := stripRight_preserves width height (reflectX width s) (reflectX width t)
    (by unfold reflectX; dsimp only; omega) (by unfold reflectX; dsimp only; omega)
    ⟨y, hy,
      (by
        intro heq
        apply hys
        unfold reflectX at heq
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp only at h1 h2
        ext
        · show 2 = s.1
          omega
        · show y = s.2
          exact h2),
      (by
        intro heq
        apply hyt
        unfold reflectX at heq
        have h1 := congrArg Prod.fst heq
        have h2 := congrArg Prod.snd heq
        dsimp only at h1 h2
        ext
        · show 2 = t.1
          omega
        · show y = t.2
          exact h2)⟩
    hR
  have hB := hasHamPath_reflect hS
  have ss : reflectX width (reflectX width s) = s := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  have tt : reflectX width (reflectX width t) = t := by
    unfold reflectX
    ext
    · dsimp only
      omega
    · rfl
  rw [ss, tt] at hB
  exact hB

/-- **Stripping the bottom two rows**, by transposing `stripLeft_preserves`. -/
theorem stripDown_preserves (width height : ℕ) (s t : Coord)
    (hs : 2 ≤ s.2) (ht : 2 ≤ t.2)
    (hfree : ∃ x, x < width ∧ (x, 2) ≠ s ∧ (x, 2) ≠ t)
    (h : HasHamPath width (height - 2) (s.1, s.2 - 2) (t.1, t.2 - 2)) :
    HasHamPath width height s t := by
  obtain ⟨x, hx, hxs, hxt⟩ := hfree
  have hT : HasHamPath height width (swapXY s) (swapXY t) :=
    stripLeft_preserves height width (swapXY s) (swapXY t) hs ht
      ⟨x, hx, fun heq => hxs (congrArg swapXY heq), fun heq => hxt (congrArg swapXY heq)⟩
      (hasHamPath_transpose h)
  exact hasHamPath_transpose hT

end GridHam
