import GridHam.Coloring

/-!
# Forbidden cases (necessary condition, part 2)

Color compatibility alone is not sufficient: `grid_hampath.py`'s
`is_forbidden` (cases for `width/height ∈ {1,2,3}`) rules out additional
color-compatible pairs. This file ports those three cases directly, then
states (but does not yet prove) the necessity theorem for each.

STATUS: definitions only, transcribed carefully from the Python (which was
itself exhaustively cross-checked against brute-force search for all
`width,height` with `width*height ≤ 26`, including every case-3 instance --
see `verify.py`'s `exhaustive_characterization_check`, 0 mismatches). So
there is strong *empirical* evidence these definitions are correct, even
though the Lean necessity proofs below are `sorry`. Proving `isForbidden →
¬HasHamPath` for each case is a real (if bounded) undertaking: case 1 is a
short argument (a path on a width/height-1 grid literally has no choice but
to be the straight line), case 2 is a cut/separation argument, case 3 is the
most involved (a parity-and-distance argument about which side of a
mandatory 3-wide crossing each color lands on). None attempted here.
-/

namespace GridHam

/-- `v` is one of the four corners of the `width × height` grid. -/
def IsCorner (width height : ℕ) (v : Coord) : Prop :=
  v = (0, 0) ∨ v = (width - 1, 0) ∨ v = (0, height - 1) ∨ v = (width - 1, height - 1)

instance : DecidablePred (fun v => IsCorner width height v) :=
  fun v => by unfold IsCorner; infer_instance

/-- Ported from `_is_forbidden_case_1`: when `width = 1` or `height = 1`, a
Hamiltonian path must be the straight line, so `{s,t}` must be exactly the
two extreme corners.

REVISION NOTE: originally stated using `Set Coord` equality (`{s,t} =
{(0,0), far}`), which is mathematically fine but unnecessarily hard to work
with in an actual proof (`Set` equality needs `Set.ext`-style unfolding, and
isn't `Decidable` in general). Rewritten as a plain `∨`/`∧`/`=` statement on
`Coord` directly, matching every other definition in this file -- this is
what a two-element set equality actually *means* for a two-element set, just
spelled out instead of routed through `Set`. -/
def ForbiddenCase1 (width height : ℕ) (s t : Coord) : Prop :=
  let isW := width = 1
  let bound := if isW then height else width
  let far : Coord := if isW then (0, bound - 1) else (bound - 1, 0)
  ¬ ((s = (0, 0) ∧ t = far) ∨ (s = far ∧ t = (0, 0)))

instance : DecidablePred (fun p : Coord × Coord => ForbiddenCase1 width height p.1 p.2) :=
  fun p => by unfold ForbiddenCase1; infer_instance

/-- Ported from `_is_forbidden_case_2`: when `width = 2` or `height = 2`, a
non-boundary edge between two non-corner vertices can't be the path's
mandatory final crossing. -/
def ForbiddenCase2 (width height : ℕ) (s t : Coord) : Prop :=
  ¬ IsCorner width height s ∧ ¬ IsCorner width height t ∧
  ((width = 2 ∧ s.2 = t.2) ∨ (height = 2 ∧ s.1 = t.1))

/-- Ported from `_is_forbidden_case_3`: when `width = 3` or `height = 3` and
the opposite dimension is even, a distance-and-parity condition on `s`, `t`
relative to the grid's corners rules out a Hamiltonian path even though
`s`,`t` are color-compatible. Transcribed directly from the Rust/Python
index arithmetic; not independently re-derived from the paper here. -/
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

/-- Ported from `is_forbidden`: dispatches to the case matching whichever of
`width`/`height` is `1`, `2`, or `3` (checked in that priority order, as in
the source). -/
def IsForbidden (width height : ℕ) (s t : Coord) : Prop :=
  if width = 1 ∨ height = 1 then ForbiddenCase1 width height s t
  else if width = 2 ∨ height = 2 then ForbiddenCase2 width height s t
  else if width = 3 ∨ height = 3 then ForbiddenCase3 width height s t
  else False

/-- Ported from `is_acceptable`. This is IPS's full necessary-and-sufficient
condition; `Main.lean`'s top-level theorem is `HasHamPath ↔ IsAcceptable`. -/
def IsAcceptable (width height : ℕ) (s t : Coord) : Prop :=
  ColorCompatible width height s t ∧ ¬ IsForbidden width height s t

/-! Direct (non-`DecidablePred`) instances, so `decide`/`#eval` can evaluate
`IsAcceptable w h s t` for concrete arguments (used by `CrossCheck.lean`). -/

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

/-- The core combinatorial fact underlying `forbiddenCase1_implies_no_path`,
isolated as its own self-contained statement about plain `List ℕ` (no
`Coord`/grid vocabulary): a `Nodup`, unit-step-adjacent sequence that covers
exactly the interval `[k, k + length)` must run from one extreme of that
interval to the other, in one direction or the other. This is what forces a
Hamiltonian path on a width-1 (or height-1) grid to be monotonic -- a width-1
grid's vertices, read off by their single free coordinate, are *exactly*
such a sequence.

STATUS: stated, not proved. This is real, nontrivial combinatorial content
(prove by strong induction on length; the crux is that a "unit chain"
covering `[k, k+n)` starting at an *interior* point of that range would,
followed in either direction, run out of room on one side while the other
side stays uncovered and unreachable) -- not the routine index/`Bool`
bookkeeping that closed out `Coloring.lean`'s lemmas. Deliberately left as
its own precisely-scoped lemma rather than attempted inline and possibly
wrong: isolating exactly what's still needed is worth more than a guessed
proof that doesn't compile. -/
def unitStepB (a b : ℕ) : Bool := decide (a + 1 = b ∨ b + 1 = a)

def unitStepChain : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => unitStepB a b && unitStepChain (b :: rest)

/-- **Discrete intermediate value property for unit-step chains.** If `x`
and `y` both appear in a unit-step chain `q`, every value between them also
appears -- regardless of `Nodup`; this is purely about connectivity of the
±1-step walk (to get from `x` to `y` via ±1 steps, you must pass through
every integer in between). This is the crux fact behind
`unitChain_endpoints`: an interior starting point `a` (with both `a-1` and
`a+1` present elsewhere, by full coverage of the range) would force the
walk to pass back through `a` to reach the far one -- contradicting
`Nodup`, since `a` is only visited once, at the start.

Proved by front-peeling induction, mirroring the exact structure already
confirmed working in `Coloring.lean`'s `chain_parity_alternates` (unfold
`unitStepChain` via `simpa [unitStepChain]`, split the `&&` via `simp`,
recover the underlying `Prop` from the `decide`-wrapped `Bool` via
`unfold ... ; by_contra ; simp [...]`). -/
theorem unitStepChain_intermediate :
    ∀ (q : List ℕ), unitStepChain q = true →
      ∀ x y, x ∈ q → y ∈ q →
        ∀ z, (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x) → z ∈ q := by
  intro q
  induction q with
  | nil => intro _ x y hx; simp at hx
  | cons a l ih =>
    intro hchain x y hx hy z hz
    cases l with
    | nil =>
      have hxa : x = a := by simpa using hx
      have hya : y = a := by simpa using hy
      rw [hxa, hya] at hz
      have hza : z = a := by rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      simp [hza]
    | cons b rest =>
      have hc' : (unitStepB a b && unitStepChain (b :: rest)) = true := by
        simpa [unitStepChain] using hchain
      simp at hc'
      obtain ⟨hstepB, hchainRest⟩ := hc'
      have hstep : a + 1 = b ∨ b + 1 = a := by
        unfold unitStepB at hstepB
        by_contra hcon
        simp [hcon] at hstepB
      -- Key sub-fact: for any w in the tail and z' between a and w, z' is in
      -- the whole list (a :: b :: rest).
      have key : ∀ w, w ∈ (b :: rest) →
          ∀ z', (a ≤ z' ∧ z' ≤ w) ∨ (w ≤ z' ∧ z' ≤ a) → z' ∈ (a :: b :: rest) := by
        intro w hw z' hz'
        have hbmem : b ∈ (b :: rest) := by simp
        by_cases hzb : (b ≤ z' ∧ z' ≤ w) ∨ (w ≤ z' ∧ z' ≤ b)
        · exact List.mem_cons.mpr (Or.inr (ih hchainRest b w hbmem hw z' hzb))
        · have hz'eq : z' = a := by
            rcases hstep with hab | hab <;> rcases hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          simp [hz'eq]
      rcases List.mem_cons.mp hx with hxa | hxr
      · rw [hxa] at hz
        rcases List.mem_cons.mp hy with hya | hyr
        · rw [hya] at hz
          have hza : z = a := by rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          simp [hza]
        · exact key y hyr z hz
      · rcases List.mem_cons.mp hy with hya | hyr
        · rw [hya] at hz
          have hz' : (a ≤ z ∧ z ≤ x) ∨ (x ≤ z ∧ z ≤ a) := by
            rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl ⟨h1, h2⟩
          exact key x hxr z hz'
        · exact List.mem_cons.mpr (Or.inr (ih hchainRest x y hxr hyr z hz))

/-- In a `Nodup` unit-step chain covering exactly `[k, k + rest.length]`,
the first element is one of the two ends of that range. An interior first
element `a` would have both `a - 1` and `a + 1` later in the list, so by
`unitStepChain_intermediate` `a` itself would appear later too --
contradicting `Nodup`. -/
theorem unitChain_head_extreme (a : ℕ) (rest : List ℕ) (k : ℕ)
    (hnd : (a :: rest).Nodup) (hch : unitStepChain (a :: rest) = true)
    (hcov : ∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) :
    a = k ∨ a = k + rest.length := by
  have ha := (hcov a).mp (by simp)
  by_cases h1 : a = k
  · exact Or.inl h1
  by_cases h2 : a = k + rest.length
  · exact Or.inr h2
  exfalso
  cases rest with
  | nil =>
    have hl : ([] : List ℕ).length = 0 := rfl
    omega
  | cons b rest' =>
    have hc' : (unitStepB a b && unitStepChain (b :: rest')) = true := by
      simpa [unitStepChain] using hch
    simp at hc'
    obtain ⟨_, hcl⟩ := hc'
    obtain ⟨hanot, _⟩ := List.nodup_cons.mp hnd
    have hlo : a - 1 ∈ b :: rest' := by
      have hm := (hcov (a - 1)).mpr ⟨by omega, by omega⟩
      rcases List.mem_cons.mp hm with h | h
      · exfalso; omega
      · exact h
    have hhi : a + 1 ∈ b :: rest' := by
      have hm := (hcov (a + 1)).mpr ⟨by omega, by omega⟩
      rcases List.mem_cons.mp hm with h | h
      · exfalso; omega
      · exact h
    exact hanot (unitStepChain_intermediate (b :: rest') hcl (a - 1) (a + 1) hlo hhi a
      (Or.inl ⟨by omega, by omega⟩))

/-- A `Nodup` unit-step chain covering `[k, k + rest.length]` that starts at
the bottom `k` ends at the top. The second element is forced to be `k + 1`,
and the tail covers `[k + 1, k + 1 + rest'.length]`; induct. -/
theorem unitChain_last_of_head_min :
    ∀ (rest : List ℕ) (a k : ℕ), (a :: rest).Nodup → unitStepChain (a :: rest) = true →
      (∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) → a = k →
      (a :: rest).getLast? = some (k + rest.length) := by
  intro rest
  induction rest with
  | nil =>
    intro a k _ _ _ hak
    rw [hak]
    rfl
  | cons b rest' ih =>
    intro a k hnd hch hcov hak
    have hc' : (unitStepB a b && unitStepChain (b :: rest')) = true := by
      simpa [unitStepChain] using hch
    simp at hc'
    obtain ⟨hstepB, hcl⟩ := hc'
    have hstep : a + 1 = b ∨ b + 1 = a := by
      unfold unitStepB at hstepB
      by_contra hcon
      simp [hcon] at hstepB
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    have hl : (b :: rest').length = rest'.length + 1 := rfl
    have hbr := (hcov b).mp (by simp)
    have hbk : b = k + 1 := by rcases hstep with h | h <;> omega
    have hcov' : ∀ y, y ∈ b :: rest' ↔ k + 1 ≤ y ∧ y ≤ k + 1 + rest'.length := by
      intro y
      constructor
      · intro hy
        have h1 := (hcov y).mp (List.mem_cons.mpr (Or.inr hy))
        have h2 : y ≠ a := by
          intro hya
          rw [hya] at hy
          exact hanot hy
        exact ⟨by omega, by omega⟩
      · intro hy
        have h1 := (hcov y).mpr ⟨by omega, by omega⟩
        rcases List.mem_cons.mp h1 with h | h
        · exfalso; omega
        · exact h
    have hgl : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
    rw [hgl, ih b (k + 1) hndt hcl hcov' hbk, hl]
    have heq : k + 1 + rest'.length = k + (rest'.length + 1) := by omega
    rw [heq]

/-- Mirror image of `unitChain_last_of_head_min`: starting at the top
`k + rest.length` forces ending at the bottom `k`. -/
theorem unitChain_last_of_head_max :
    ∀ (rest : List ℕ) (a k : ℕ), (a :: rest).Nodup → unitStepChain (a :: rest) = true →
      (∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) → a = k + rest.length →
      (a :: rest).getLast? = some k := by
  intro rest
  induction rest with
  | nil =>
    intro a k _ _ _ hak
    rw [hak]
    rfl
  | cons b rest' ih =>
    intro a k hnd hch hcov hak
    have hc' : (unitStepB a b && unitStepChain (b :: rest')) = true := by
      simpa [unitStepChain] using hch
    simp at hc'
    obtain ⟨hstepB, hcl⟩ := hc'
    have hstep : a + 1 = b ∨ b + 1 = a := by
      unfold unitStepB at hstepB
      by_contra hcon
      simp [hcon] at hstepB
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    have hl : (b :: rest').length = rest'.length + 1 := rfl
    have hbr := (hcov b).mp (by simp)
    have hbk : b = k + rest'.length := by rcases hstep with h | h <;> omega
    have hcov' : ∀ y, y ∈ b :: rest' ↔ k ≤ y ∧ y ≤ k + rest'.length := by
      intro y
      constructor
      · intro hy
        have h1 := (hcov y).mp (List.mem_cons.mpr (Or.inr hy))
        have h2 : y ≠ a := by
          intro hya
          rw [hya] at hy
          exact hanot hy
        exact ⟨by omega, by omega⟩
      · intro hy
        have h1 := (hcov y).mpr ⟨by omega, by omega⟩
        rcases List.mem_cons.mp h1 with h | h
        · exfalso; omega
        · exact h
    have hgl : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
    rw [hgl, ih b k hndt hcl hcov' hbk]

/-- A `Nodup` unit-step chain covering exactly `[k, k + rest.length]` runs
from one end of that range to the other. -/
theorem unitChain_endpoints (a : ℕ) (rest : List ℕ) (k : ℕ)
    (hnd : (a :: rest).Nodup) (hch : unitStepChain (a :: rest) = true)
    (hcov : ∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) :
    (a = k ∧ (a :: rest).getLast? = some (k + rest.length)) ∨
    (a = k + rest.length ∧ (a :: rest).getLast? = some k) := by
  rcases unitChain_head_extreme a rest k hnd hch hcov with h | h
  · exact Or.inl ⟨h, unitChain_last_of_head_min rest a k hnd hch hcov h⟩
  · exact Or.inr ⟨h, unitChain_last_of_head_max rest a k hnd hch hcov h⟩

/-! ### Plumbing: from a grid path on a 1-wide strip to a unit-step chain -/

/-- If `f` is injective on the elements of a `Nodup` list, the mapped list is
`Nodup`. -/
theorem nodup_map_of_injOn (f : Coord → ℕ) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ w ∈ l, f v = f w → v = w) → l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hinj hnd
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    have e : (a :: l).map f = f a :: l.map f := rfl
    rw [e, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
      have hwa : w = a :=
        hinj w (List.mem_cons.mpr (Or.inr hw)) a (List.mem_cons.mpr (Or.inl rfl)) hwe
      rw [hwa] at hw
      exact hanot hw
    · exact ih (fun v hv w hw =>
        hinj v (List.mem_cons.mpr (Or.inr hv)) w (List.mem_cons.mpr (Or.inr hw))) hndt

/-- If every grid-adjacent pair of elements maps to values differing by 1,
a grid-adjacent chain maps to a unit-step chain. -/
theorem unitStepChain_map (f : Coord → ℕ) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ w ∈ l, Adjacent v w → (f v + 1 = f w ∨ f w + 1 = f v)) →
    chainAdjacent l = true → unitStepChain (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hstep hch
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
      have hA : unitStepB (f a) (f b) = true := by
        unfold unitStepB
        exact decide_eq_true (hstep a (by simp) b (by simp) hadj)
      have hB : unitStepChain ((b :: rest).map f) = true :=
        ih (fun v hv w hw =>
          hstep v (List.mem_cons.mpr (Or.inr hv)) w (List.mem_cons.mpr (Or.inr hw))) hcl
      have e : unitStepChain ((a :: b :: rest).map f) =
          (unitStepB (f a) (f b) && unitStepChain ((b :: rest).map f)) := rfl
      simp only [e, hA, hB, Bool.and_self]

/-- The last element of a mapped list is the image of the last element. -/
theorem getLast?_map_of (f : Coord → ℕ) : ∀ (l : List Coord) (t : Coord),
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

/-- `ForbiddenCase1` on a width-1 grid, with the `let`s and `if`s resolved. -/
theorem forbiddenCase1_w1 (height : ℕ) (s t : Coord) :
    ForbiddenCase1 1 height s t ↔
      ¬ ((s = (0, 0) ∧ t = (0, height - 1)) ∨ (s = (0, height - 1) ∧ t = (0, 0))) := by
  unfold ForbiddenCase1
  simp

/-- `ForbiddenCase1` on a height-1 grid whose width is not 1. -/
theorem forbiddenCase1_h1 (width : ℕ) (s t : Coord) (hw : ¬ width = 1) :
    ForbiddenCase1 width 1 s t ↔
      ¬ ((s = (0, 0) ∧ t = (width - 1, 0)) ∨ (s = (width - 1, 0) ∧ t = (0, 0))) := by
  unfold ForbiddenCase1
  simp [hw]

/-- **Forbidden case 1 is really forbidden.** On a width-1 (or height-1)
grid, the free coordinate of a Hamiltonian path, read in order, is a `Nodup`
unit-step chain covering `[0, n-1]`, so by `unitChain_endpoints` the path
runs corner to corner. -/
theorem forbiddenCase1_implies_no_path (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h1 : width = 1 ∨ height = 1) (hf : ForbiddenCase1 width height s t) :
    ¬ HasHamPath width height s t := by
  rintro ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩
  cases p with
  | nil => simp at hhead
  | cons a prest =>
    have has : a = s := by simpa using hhead
    unfold InBounds at hs ht
    by_cases hw : width = 1
    · -- Width 1: every x-coordinate is 0; project to y.
      have hfst : ∀ v ∈ a :: prest, v.1 = 0 := by
        intro v hv
        have hv' := hin v hv
        unfold InBounds at hv'
        omega
      have hnd' : ((a :: prest).map Prod.snd).Nodup :=
        nodup_map_of_injOn Prod.snd (a :: prest) (fun v hv w hw' he => by
          have e1 := hfst v hv
          have e2 := hfst w hw'
          ext <;> omega) hnd
      have hch' : unitStepChain ((a :: prest).map Prod.snd) = true :=
        unitStepChain_map Prod.snd (a :: prest) (fun v hv w hw' hadj => by
          have e1 := hfst v hv
          have e2 := hfst w hw'
          unfold Adjacent at hadj
          rcases hadj with ⟨_, h4⟩ | ⟨_, h4⟩
          · exact h4
          · exfalso
            rcases h4 with h4 | h4 <;> omega) hch
      have hlenp : prest.length + 1 = height := by
        have hl0 : (a :: prest).length = prest.length + 1 := rfl
        rw [hw] at hlen
        omega
      have hl : (prest.map Prod.snd).length = prest.length := by simp
      have hcovq : ∀ y, y ∈ a.2 :: prest.map Prod.snd ↔
          0 ≤ y ∧ y ≤ 0 + (prest.map Prod.snd).length := by
        intro y
        have e : a.2 :: prest.map Prod.snd = (a :: prest).map Prod.snd := rfl
        rw [e]
        constructor
        · intro hy
          obtain ⟨v, hv, hve⟩ := List.mem_map.mp hy
          have hv' := hin v hv
          unfold InBounds at hv'
          exact ⟨by omega, by omega⟩
        · intro hy
          have hmem : ((0, y) : Coord) ∈ allCoords width height := by
            simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
            exact ⟨0, by omega, y, by omega, rfl⟩
          exact List.mem_map.mpr ⟨(0, y), hcov (0, y) hmem, rfl⟩
      have hlastq : (a.2 :: prest.map Prod.snd).getLast? = some t.2 :=
        getLast?_map_of Prod.snd (a :: prest) t hlast
      have hres := unitChain_endpoints a.2 (prest.map Prod.snd) 0 hnd' hch' hcovq
      rw [hw] at hf
      have hf' := (forbiddenCase1_w1 height s t).mp hf
      rw [has] at hres hlastq
      rcases hres with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        left
        constructor
        · ext
          · show s.1 = 0; omega
          · show s.2 = 0; omega
        · ext
          · show t.1 = 0; omega
          · show t.2 = height - 1; omega
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        right
        constructor
        · ext
          · show s.1 = 0; omega
          · show s.2 = height - 1; omega
        · ext
          · show t.1 = 0; omega
          · show t.2 = 0; omega
    · -- Height 1 (and width ≠ 1): every y-coordinate is 0; project to x.
      have hh : height = 1 := h1.resolve_left hw
      have hsnd : ∀ v ∈ a :: prest, v.2 = 0 := by
        intro v hv
        have hv' := hin v hv
        unfold InBounds at hv'
        omega
      have hnd' : ((a :: prest).map Prod.fst).Nodup :=
        nodup_map_of_injOn Prod.fst (a :: prest) (fun v hv w hw' he => by
          have e1 := hsnd v hv
          have e2 := hsnd w hw'
          ext <;> omega) hnd
      have hch' : unitStepChain ((a :: prest).map Prod.fst) = true :=
        unitStepChain_map Prod.fst (a :: prest) (fun v hv w hw' hadj => by
          have e1 := hsnd v hv
          have e2 := hsnd w hw'
          unfold Adjacent at hadj
          rcases hadj with ⟨_, h4⟩ | ⟨_, h4⟩
          · exfalso
            rcases h4 with h4 | h4 <;> omega
          · exact h4) hch
      have hlenp : prest.length + 1 = width := by
        have hl0 : (a :: prest).length = prest.length + 1 := rfl
        rw [hh] at hlen
        omega
      have hl : (prest.map Prod.fst).length = prest.length := by simp
      have hcovq : ∀ x, x ∈ a.1 :: prest.map Prod.fst ↔
          0 ≤ x ∧ x ≤ 0 + (prest.map Prod.fst).length := by
        intro x
        have e : a.1 :: prest.map Prod.fst = (a :: prest).map Prod.fst := rfl
        rw [e]
        constructor
        · intro hx
          obtain ⟨v, hv, hve⟩ := List.mem_map.mp hx
          have hv' := hin v hv
          unfold InBounds at hv'
          exact ⟨by omega, by omega⟩
        · intro hx
          have hmem : ((x, 0) : Coord) ∈ allCoords width height := by
            simp only [allCoords, List.mem_flatMap, List.mem_range, List.mem_map]
            exact ⟨x, by omega, 0, by omega, rfl⟩
          exact List.mem_map.mpr ⟨(x, 0), hcov (x, 0) hmem, rfl⟩
      have hlastq : (a.1 :: prest.map Prod.fst).getLast? = some t.1 :=
        getLast?_map_of Prod.fst (a :: prest) t hlast
      have hres := unitChain_endpoints a.1 (prest.map Prod.fst) 0 hnd' hch' hcovq
      rw [hh] at hf
      have hf' := (forbiddenCase1_h1 width s t hw).mp hf
      rw [has] at hres hlastq
      rcases hres with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        left
        constructor
        · ext
          · show s.1 = 0; omega
          · show s.2 = 0; omega
        · ext
          · show t.1 = width - 1; omega
          · show t.2 = 0; omega
      · rw [hlastq] at e2
        have e3 := Option.some.inj e2
        apply hf'
        right
        constructor
        · ext
          · show s.1 = width - 1; omega
          · show s.2 = 0; omega
        · ext
          · show t.1 = 0; omega
          · show t.2 = 0; omega

end GridHam
