import GridHam.StripSplit

/-!
# Forbidden case 3: tools and base cases

Paths are lists, so "who is next to whom on the path" needs a small toolkit:

* `PNext p x y`: `y` immediately follows `x` in `p`;
* `pnext_adj`: path neighbours are grid-adjacent;
* `pnext_unique_right` / `pnext_unique_left`: in a list without repeats each
  cell has at most one successor and at most one predecessor;
* `no_prev_of_head`: the first cell has no predecessor;
* `interior_two`: a cell that is neither first nor last has a predecessor and
  a successor, and they are different;
* `forced_after_head`: if a middle cell's only possible path neighbours are the
  first cell `u` and one other cell, then it must come right after `u`.

Base case B0 (`b0_no_path`): on a 3-high grid, no Hamiltonian path starts at
`(0, 1)` and ends in a column `≥ 1`. Both corners `(0,0)` and `(0,2)` would
have to come right after `(0,1)`.
-/

namespace GridHam

/-- `y` immediately follows `x` in `p`. -/
def PNext (p : List Coord) (x y : Coord) : Prop := ∃ l1 l2, p = l1 ++ x :: y :: l2

theorem pnext_mem_left {p : List Coord} {x y : Coord} (h : PNext p x y) : x ∈ p := by
  obtain ⟨l1, l2, e⟩ := h
  rw [e]
  simp

theorem pnext_mem_right {p : List Coord} {x y : Coord} (h : PNext p x y) : y ∈ p := by
  obtain ⟨l1, l2, e⟩ := h
  rw [e]
  simp

theorem pnext_adj {p : List Coord} {x y : Coord} (hch : chainAdjacent p = true)
    (h : PNext p x y) : Adjacent x y := by
  obtain ⟨l1, l2, e⟩ := h
  rw [e] at hch
  have hc := chainAdjacent_suffix l1 _ hch
  have hc' : (adjacentB x y && chainAdjacent (y :: l2)) = true := by
    simpa [chainAdjacent] using hc
  simp at hc'
  unfold adjacentB at hc'
  exact of_decide_eq_true hc'.1

/-- In a list without repeats, an element sits at only one position. -/
theorem split_unique : ∀ (l1 l1' r r' : List Coord) (x : Coord),
    (l1 ++ x :: r).Nodup → l1 ++ x :: r = l1' ++ x :: r' → l1 = l1' ∧ r = r' := by
  intro l1
  induction l1 with
  | nil =>
    intro l1' r r' x hnd he
    have hnd' : (x :: r).Nodup := hnd
    cases l1' with
    | nil =>
      have he' : x :: r = x :: r' := he
      exact ⟨rfl, (List.cons.inj he').2⟩
    | cons a l1'' =>
      exfalso
      have he' : x :: r = a :: (l1'' ++ x :: r') := he
      have hr := (List.cons.inj he').2
      apply (List.nodup_cons.mp hnd').1
      rw [hr]
      simp
  | cons a l ih =>
    intro l1' r r' x hnd he
    have hnd' : (a :: (l ++ x :: r)).Nodup := hnd
    obtain ⟨han, hrest⟩ := List.nodup_cons.mp hnd'
    cases l1' with
    | nil =>
      exfalso
      have he' : a :: (l ++ x :: r) = x :: r' := he
      have hax := (List.cons.inj he').1
      apply han
      rw [hax]
      simp
    | cons b l1'' =>
      have he' : a :: (l ++ x :: r) = b :: (l1'' ++ x :: r') := he
      obtain ⟨hab, htl⟩ := List.cons.inj he'
      obtain ⟨hl, hr⟩ := ih l1'' r r' x hrest htl
      exact ⟨by rw [hab, hl], hr⟩

theorem pnext_unique_right {p : List Coord} {x y y' : Coord} (hnd : p.Nodup)
    (h1 : PNext p x y) (h2 : PNext p x y') : y = y' := by
  obtain ⟨l1, l2, e1⟩ := h1
  obtain ⟨l1', l2', e2⟩ := h2
  have hnd' : (l1 ++ x :: y :: l2).Nodup := by rw [← e1]; exact hnd
  have hsu := split_unique l1 l1' (y :: l2) (y' :: l2') x hnd' (e1.symm.trans e2)
  exact (List.cons.inj hsu.2).1

theorem pnext_unique_left {p : List Coord} {x y y' : Coord} (hnd : p.Nodup)
    (h1 : PNext p y x) (h2 : PNext p y' x) : y = y' := by
  obtain ⟨l1, l2, e1⟩ := h1
  obtain ⟨l1', l2', e2⟩ := h2
  have e1' : p = (l1 ++ [y]) ++ x :: l2 := by rw [e1]; simp
  have e2' : p = (l1' ++ [y']) ++ x :: l2' := by rw [e2]; simp
  have hnd' : ((l1 ++ [y]) ++ x :: l2).Nodup := by rw [← e1']; exact hnd
  have hsu := split_unique (l1 ++ [y]) (l1' ++ [y']) l2 l2' x hnd' (e1'.symm.trans e2')
  have hh := congrArg List.getLast? hsu.1
  simpa using hh

/-- The first cell of a path without repeats has no predecessor. -/
theorem no_prev_of_head {p : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hh : p.head? = some x) (h : PNext p y x) : False := by
  cases p with
  | nil => simp at hh
  | cons a rest =>
    have hax : a = x := by simpa using hh
    subst hax
    obtain ⟨l1, l2, e⟩ := h
    have e' : [] ++ a :: rest = (l1 ++ [y]) ++ a :: l2 := by
      show a :: rest = (l1 ++ [y]) ++ a :: l2
      rw [e]
      simp
    have hnd' : ([] ++ a :: rest).Nodup := hnd
    have hsu := split_unique [] (l1 ++ [y]) rest l2 a hnd' e'
    have hl := congrArg List.length hsu.1
    simp at hl

/-- A middle cell has a predecessor and a successor, and they differ. -/
theorem interior_two {p : List Coord} {x : Coord} (hnd : p.Nodup) (hx : x ∈ p)
    (hh : p.head? ≠ some x) (hl : p.getLast? ≠ some x) :
    ∃ a b, a ≠ b ∧ PNext p a x ∧ PNext p x b := by
  obtain ⟨l1, r, e⟩ := List.append_of_mem hx
  cases r with
  | nil =>
    exfalso
    apply hl
    rw [e, getLast?_append_cons]
    rfl
  | cons b r' =>
    by_cases hl1 : l1 = []
    · exfalso
      apply hh
      rw [e, hl1]
      rfl
    · obtain ⟨l0, a, hl0a⟩ : ∃ l0 a, l1 = l0 ++ [a] :=
        ⟨l1.dropLast, l1.getLast hl1, (List.dropLast_append_getLast hl1).symm⟩
      have e2 : p = l0 ++ a :: x :: b :: r' := by
        rw [e, hl0a]
        simp
      refine ⟨a, b, ?_, ⟨l0, b :: r', e2⟩, ⟨l1, r', e⟩⟩
      intro hab
      have hnd' : (l0 ++ a :: (x :: b :: r')).Nodup := by rw [← e2]; exact hnd
      have e3 : l0 ++ a :: (x :: b :: r') = (l0 ++ [a, x]) ++ a :: r' := by
        rw [hab]
        simp
      have hsu := split_unique l0 (l0 ++ [a, x]) (x :: b :: r') r' a hnd' e3
      have hlen := congrArg List.length hsu.1
      simp at hlen

/-- **Forced move.** If a middle cell `x` can only be path-adjacent to the
first cell `u` or to one other cell `z`, then `x` comes right after `u`. -/
theorem forced_after_head {p : List Coord} {u x z : Coord} (hnd : p.Nodup)
    (hch : chainAdjacent p = true) (hh : p.head? = some u) (hx : x ∈ p)
    (hxh : p.head? ≠ some x) (hxl : p.getLast? ≠ some x)
    (hnb : ∀ y ∈ p, Adjacent y x → y = u ∨ y = z) : PNext p u x := by
  obtain ⟨a, b, hab, hpa, hpb⟩ := interior_two hnd hx hxh hxl
  have ha := hnb a (pnext_mem_left hpa) (pnext_adj hch hpa)
  have hb := hnb b (pnext_mem_right hpb) (adjacent_symm (pnext_adj hch hpb))
  rcases ha with ha | ha
  · rw [ha] at hpa
    exact hpa
  · rcases hb with hb | hb
    · rw [hb] at hpb
      exact (no_prev_of_head hnd hh hpb).elim
    · exact absurd (ha.trans hb.symm) hab

/-- **Base case B0.** On a 3-high grid no Hamiltonian path starts at `(0, 1)`
and ends in a column `≥ 1`. -/
theorem b0_no_path (w : ℕ) (v : Coord) (hv : 1 ≤ v.1) : ¬ HasHamPath w 3 (0, 1) v := by
  rintro ⟨p, hlen, hhead, hlast, hnd, hin, hcov, hch⟩
  have hvin := hin v (mem_of_getLast? p v hlast)
  unfold InBounds at hvin
  have hmem : ∀ c : Coord, c.1 < w → c.2 < 3 → c ∈ p :=
    fun c h1 h2 => hcov c ((mem_allCoords w 3 c).mpr ⟨h1, h2⟩)
  have hnothead : ∀ c : Coord, c ≠ (0, 1) → p.head? ≠ some c := by
    intro c hc e
    rw [hhead] at e
    exact hc (Option.some.inj e).symm
  have hnotlast : ∀ c : Coord, c.1 = 0 → p.getLast? ≠ some c := by
    intro c hc e
    rw [hlast] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have h00 : PNext p (0, 1) (0, 0) := by
    apply forced_after_head (z := (1, 0)) hnd hch hhead
      (hmem (0, 0) (by show 0 < w; omega) (by show 0 < 3; omega))
      (hnothead (0, 0) (by simp)) (hnotlast (0, 0) rfl)
    intro y _ hy
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hy
    dsimp only at hy
    simp only [Prod.mk.injEq]
    omega
  have h02 : PNext p (0, 1) (0, 2) := by
    apply forced_after_head (z := (1, 2)) hnd hch hhead
      (hmem (0, 2) (by show 0 < w; omega) (by show 2 < 3; omega))
      (hnothead (0, 2) (by simp)) (hnotlast (0, 2) rfl)
    intro y hyp hy
    have hyb := hin y hyp
    unfold InBounds at hyb
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hy
    dsimp only at hy hyb
    simp only [Prod.mk.injEq]
    omega
  have := pnext_unique_right hnd h00 h02
  simp at this

/-! ### Positions, forced successors, contraction -/

/-- If `x` sits at position `L` and `y` follows `x`, then `y` sits right after. -/
theorem pnext_pos {p L R : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hp : p = L ++ x :: R) (h : PNext p x y) : ∃ R', R = y :: R' := by
  obtain ⟨l1, l2, e⟩ := h
  have hnd' : (L ++ x :: R).Nodup := by rw [← hp]; exact hnd
  have hsu := split_unique L l1 R (y :: l2) x hnd' (hp.symm.trans e)
  exact ⟨l2, hsu.2⟩

/-- **Forced successor.** A middle cell whose predecessor is `a` and whose
only possible path neighbours are `a` and `b` is followed by `b`. -/
theorem next_forced {p : List Coord} {a x b : Coord} (hnd : p.Nodup)
    (hch : chainAdjacent p = true) (hx : x ∈ p) (hxh : p.head? ≠ some x)
    (hxl : p.getLast? ≠ some x) (hprev : PNext p a x)
    (hnb : ∀ y ∈ p, Adjacent x y → y = a ∨ y = b) : PNext p x b := by
  obtain ⟨a', b', hab, hpa, hpb⟩ := interior_two hnd hx hxh hxl
  have ha' : a' = a := pnext_unique_left hnd hpa hprev
  rcases hnb b' (pnext_mem_right hpb) (pnext_adj hch hpb) with hb | hb
  · exact absurd (ha'.trans hb.symm) hab
  · rw [hb] at hpb
    exact hpb

theorem nodup_append_right' : ∀ (l1 l2 : List Coord), (l1 ++ l2).Nodup → l2.Nodup := by
  intro l1
  induction l1 with
  | nil => intro l2 h; exact h
  | cons x l ih =>
    intro l2 h
    have h' : (x :: (l ++ l2)).Nodup := h
    exact ih l2 (List.nodup_cons.mp h').2

theorem nodup_append_disjoint : ∀ (l1 l2 : List Coord), (l1 ++ l2).Nodup →
    ∀ c ∈ l1, c ∉ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ c hc; simp at hc
  | cons x l ih =>
    intro l2 h c hc hc2
    have h' : (x :: (l ++ l2)).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    rcases List.mem_cons.mp hc with e | e
    · rw [e] at hc2
      exact hxn (List.mem_append.mpr (Or.inr hc2))
    · exact ih l2 hrest c e hc2

/-- Shift a vertex two columns left. -/
def shiftL2 (v : Coord) : Coord := (v.1 - 2, v.2)

/-- **Prefix contraction.** If a path on a 3-high grid begins with a block `M`
that is exactly the cells of columns 0–1, dropping `M` and shifting two
columns left gives a Hamiltonian path of the grid two columns narrower. -/
theorem contract_prefix (w : ℕ) (u v a : Coord) (M R : List Coord)
    (hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 → c ∈ M) (hMx : ∀ c ∈ M, c.1 < 2)
    (hMl : M.length = 6) (hv : ValidPath w 3 u v (M ++ a :: R)) :
    ValidPath (w - 2) 3 (shiftL2 a) (shiftL2 v) ((a :: R).map shiftL2) := by
  obtain ⟨hlen, _, hlast, hnd, hin, hcov, hch⟩ := hv
  have hdisj := nodup_append_disjoint M (a :: R) hnd
  have hnd2 := nodup_append_right' M (a :: R) hnd
  have hge : ∀ c ∈ a :: R, 2 ≤ c.1 := by
    intro c hc
    by_contra hlt
    have hcb := hin c (List.mem_append.mpr (Or.inr hc))
    unfold InBounds at hcb
    exact hdisj c (hM c (by omega) hcb.2) hc
  have haw : 2 ≤ a.1 := hge a (by simp)
  have hab := hin a (List.mem_append.mpr (Or.inr (by simp)))
  unfold InBounds at hab
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (M ++ a :: R).length = M.length + (R.length + 1) := by simp
    rw [List.length_map, List.length_cons]
    omega
  · rfl
  · rw [getLast?_append_cons] at hlast
    exact getLast?_map_coord shiftL2 (a :: R) v hlast
  · apply nodup_map_coord_on shiftL2 (a :: R) _ hnd2
    intro c hc d hd hcd
    have hc2 := hge c hc
    have hd2 := hge d hd
    unfold shiftL2 at hcd
    have h1 := congrArg Prod.fst hcd
    have h2 := congrArg Prod.snd hcd
    dsimp only at h1 h2
    ext
    · omega
    · omega
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hdb := hin d (List.mem_append.mpr (Or.inr hd))
    have hd2 := hge d hd
    unfold InBounds at hdb ⊢
    unfold shiftL2
    dsimp only
    exact ⟨by omega, hdb.2⟩
  · intro c hc
    obtain ⟨hcx, hcy⟩ := (mem_allCoords (w - 2) 3 c).mp hc
    have hd := hcov (c.1 + 2, c.2) ((mem_allCoords w 3 _).mpr ⟨by dsimp only; omega, hcy⟩)
    rcases List.mem_append.mp hd with hdM | hdR
    · have := hMx _ hdM
      dsimp only at this
      omega
    · refine List.mem_map.mpr ⟨_, hdR, ?_⟩
      unfold shiftL2
      ext
      · show c.1 + 2 - 2 = c.1
        omega
      · rfl
  · apply chainAdjacent_map_on shiftL2 (a :: R) _ (chainAdjacent_suffix M _ hch)
    intro x hx y hy hadj
    have hx2 := hge x hx
    have hy2 := hge y hy
    unfold Adjacent at hadj ⊢
    unfold shiftL2
    dsimp only
    omega

/-- Flip a Hamiltonian path top to bottom (via transpose, reflect, transpose). -/
theorem hasHamPath_flipY {w h : ℕ} {s t : Coord} (hp : HasHamPath w h s t) :
    HasHamPath w h (s.1, h - 1 - s.2) (t.1, h - 1 - t.2) :=
  hasHamPath_transpose (hasHamPath_reflect (hasHamPath_transpose hp))

/-- **Forced opening (C2).** On a 3-high grid, a Hamiltonian path from `(1, 0)`
to a cell in column `≥ 2` begins `(1,0),(0,0),(0,1),(0,2),(1,2),(1,1),(2,1)`. -/
theorem c2_prefix (w : ℕ) (v : Coord) (p : List Coord) (hv2 : 2 ≤ v.1)
    (hvp : ValidPath w 3 (1, 0) v p) :
    ∃ R, p = (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (1, 1) :: (2, 1) :: R := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp
  have hvin := hin v (mem_of_getLast? p v hlast)
  unfold InBounds at hvin
  have hmem : ∀ c : Coord, c.1 < w → c.2 < 3 → c ∈ p :=
    fun c h1 h2 => hcov c ((mem_allCoords w 3 c).mpr ⟨h1, h2⟩)
  have hnothead : ∀ c : Coord, c ≠ (1, 0) → p.head? ≠ some c := by
    intro c hc e
    rw [hhead] at e
    exact hc (Option.some.inj e).symm
  have hnotlast : ∀ c : Coord, c.1 < 2 → p.getLast? ≠ some c := by
    intro c hc e
    rw [hlast] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have hbd : ∀ y ∈ p, y.1 < w ∧ y.2 < 3 := fun y hy => hin y hy
  have m00 := hmem (0, 0) (by show 0 < w; omega) (by show 0 < 3; omega)
  have m02 := hmem (0, 2) (by show 0 < w; omega) (by show 2 < 3; omega)
  have m11 := hmem (1, 1) (by show 1 < w; omega) (by show 1 < 3; omega)
  -- (0,0) comes right after the start, then (0,1)
  have s1 : PNext p (1, 0) (0, 0) := by
    apply forced_after_head (z := (0, 1)) hnd hch hhead m00 (hnothead (0, 0) (by simp))
      (hnotlast (0, 0) (by show 0 < 2; omega))
    intro y hy hadj
    have hyb := hbd y hy
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hadj
    dsimp only at hadj hyb
    simp only [Prod.mk.injEq]
    omega
  have s2 : PNext p (0, 0) (0, 1) := by
    apply next_forced hnd hch m00 (hnothead (0, 0) (by simp))
      (hnotlast (0, 0) (by show 0 < 2; omega)) s1
    intro y hy hadj
    have hyb := hbd y hy
    obtain ⟨y1, y2⟩ := y
    unfold Adjacent at hadj
    dsimp only at hadj hyb
    simp only [Prod.mk.injEq]
    omega
  -- (0,2) sits between (0,1) and (1,2)
  obtain ⟨s3, s4⟩ : PNext p (0, 1) (0, 2) ∧ PNext p (0, 2) (1, 2) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m02 (hnothead (0, 2) (by simp)) (hnotlast (0, 2) (by show 0 < 2; omega))
    have ha : a = (0, 1) ∨ a = (1, 2) := by
      have hadj := pnext_adj hch hpa
      have hyb := hbd a (pnext_mem_left hpa)
      clear hpa hpb hab
      obtain ⟨a1, a2⟩ := a
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    have hb : b = (0, 1) ∨ b = (1, 2) := by
      have hadj := pnext_adj hch hpb
      have hyb := hbd b (pnext_mem_right hpb)
      clear hpa hpb hab
      obtain ⟨b1, b2⟩ := b
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      rw [hb] at hpb
      exact ⟨hpa, hpb⟩
    · exfalso
      rw [hb] at hpb
      have := pnext_unique_left hnd hpb s2
      simp at this
    · exact absurd (ha.trans hb.symm) hab
  -- (1,1) sits between (1,2) and (2,1)
  obtain ⟨s5, s6⟩ : PNext p (1, 2) (1, 1) ∧ PNext p (1, 1) (2, 1) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m11 (hnothead (1, 1) (by simp)) (hnotlast (1, 1) (by show 1 < 2; omega))
    have ha : a = (1, 2) ∨ a = (2, 1) := by
      have hcand : a = (0, 1) ∨ a = (1, 0) ∨ a = (1, 2) ∨ a = (2, 1) := by
        have hadj := pnext_adj hch hpa
        have hyb := hbd a (pnext_mem_left hpa)
        clear hpa hpb hab
        obtain ⟨a1, a2⟩ := a
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h | h
      · exfalso
        rw [h] at hpa
        have := pnext_unique_right hnd hpa s3
        simp at this
      · exfalso
        rw [h] at hpa
        have := pnext_unique_right hnd hpa s1
        simp at this
      · exact Or.inl h
      · exact Or.inr h
    have hb : b = (1, 2) ∨ b = (2, 1) := by
      have hcand : b = (0, 1) ∨ b = (1, 0) ∨ b = (1, 2) ∨ b = (2, 1) := by
        have hadj := pnext_adj hch hpb
        have hyb := hbd b (pnext_mem_right hpb)
        clear hpa hpb hab
        obtain ⟨b1, b2⟩ := b
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h | h
      · exfalso
        rw [h] at hpb
        have := pnext_unique_left hnd hpb s2
        simp at this
      · exfalso
        rw [h] at hpb
        exact no_prev_of_head hnd hhead hpb
      · exact Or.inl h
      · exact Or.inr h
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      rw [hb] at hpb
      exact ⟨hpa, hpb⟩
    · exfalso
      rw [hb] at hpb
      have := pnext_unique_left hnd hpb s4
      simp at this
    · exact absurd (ha.trans hb.symm) hab
  -- read the forced opening off the list
  cases p with
  | nil => simp at hhead
  | cons c0 r0 =>
    have hc0 : c0 = (1, 0) := by simpa using hhead
    subst hc0
    obtain ⟨r1, h1⟩ := pnext_pos (L := []) hnd rfl s1
    subst h1
    obtain ⟨r2, h2⟩ := pnext_pos (L := [(1, 0)]) hnd rfl s2
    subst h2
    obtain ⟨r3, h3⟩ := pnext_pos (L := [(1, 0), (0, 0)]) hnd rfl s3
    subst h3
    obtain ⟨r4, h4⟩ := pnext_pos (L := [(1, 0), (0, 0), (0, 1)]) hnd rfl s4
    subst h4
    obtain ⟨r5, h5⟩ := pnext_pos (L := [(1, 0), (0, 0), (0, 1), (0, 2)]) hnd rfl s5
    subst h5
    obtain ⟨r6, h6⟩ := pnext_pos (L := [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2)]) hnd rfl s6
    subst h6
    exact ⟨r6, rfl⟩

/-- **Base case B1.** On a 3-high grid no Hamiltonian path starts at `(1, 0)`
and ends in a column `≥ 3`: the forced opening leaves a path from `(0, 1)` on
the grid two columns narrower, which B0 rules out. -/
theorem b1_no_path (w : ℕ) (v : Coord) (hv : 3 ≤ v.1) : ¬ HasHamPath w 3 (1, 0) v := by
  rintro ⟨p, hvp⟩
  obtain ⟨R, hR⟩ := c2_prefix w v p (by omega) hvp
  rw [hR] at hvp
  have hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 →
      c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] := by
    intro c h1 h2
    obtain ⟨c1, c2⟩ := c
    dsimp only at h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  have hMx : ∀ c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)], c.1 < 2 := by
    intro c hc
    obtain ⟨c1, c2⟩ := c
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    show c1 < 2
    omega
  have hq := contract_prefix w (1, 0) v (2, 1) [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] R
    hM hMx rfl hvp
  exact b0_no_path (w - 2) (shiftL2 v) (by unfold shiftL2; dsimp only; omega) ⟨_, hq⟩

/-- **Base case B1, mirrored.** Same for a start at `(1, 2)`. -/
theorem b1_no_path' (w : ℕ) (v : Coord) (hv : 3 ≤ v.1) : ¬ HasHamPath w 3 (1, 2) v := by
  intro h
  exact b1_no_path w (v.1, 3 - 1 - v.2) hv (hasHamPath_flipY h)

/-! ### C1: the six cells of columns 0–1 form one run in the middle -/

theorem pnext_step {p L R : List Coord} {x y : Coord} (hnd : p.Nodup)
    (hp : p = L ++ x :: R) (h : PNext p x y) : ∃ R', p = (L ++ [x]) ++ y :: R' := by
  obtain ⟨R', e⟩ := pnext_pos hnd hp h
  exact ⟨R', by rw [hp, e]; simp⟩

theorem pnext_reverse {p : List Coord} {x y : Coord} (h : PNext p x y) :
    PNext p.reverse y x := by
  obtain ⟨l1, l2, e⟩ := h
  exact ⟨l2.reverse, l1.reverse, by rw [e]; simp⟩

theorem nodup_remove_mid : ∀ (L : List Coord) (a b : Coord) (M R : List Coord),
    (L ++ a :: (M ++ b :: R)).Nodup →
    (L ++ a :: b :: R).Nodup ∧ ∀ c ∈ M, c ∉ L ++ a :: b :: R := by
  intro L
  induction L with
  | nil =>
    intro a b M R h
    have h' : (a :: (M ++ b :: R)).Nodup := h
    obtain ⟨han, hrest⟩ := List.nodup_cons.mp h'
    have hbr := nodup_append_right' M (b :: R) hrest
    have hdis := nodup_append_disjoint M (b :: R) hrest
    refine ⟨?_, ?_⟩
    · show (a :: b :: R).Nodup
      rw [List.nodup_cons]
      exact ⟨fun hm => han (List.mem_append.mpr (Or.inr hm)), hbr⟩
    · intro c hc hcq
      have hcq' : c ∈ a :: b :: R := hcq
      rcases List.mem_cons.mp hcq' with e | e
      · rw [e] at hc
        exact han (List.mem_append.mpr (Or.inl hc))
      · exact hdis c hc e
  | cons x L ih =>
    intro a b M R h
    have h' : (x :: (L ++ a :: (M ++ b :: R))).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    obtain ⟨hq, hd⟩ := ih a b M R hrest
    refine ⟨?_, ?_⟩
    · show (x :: (L ++ a :: b :: R)).Nodup
      rw [List.nodup_cons]
      exact ⟨fun hm => hxn ((mem_insert_iff x L M R a b).mpr (Or.inr hm)), hq⟩
    · intro c hc hcq
      have hcq' : c ∈ x :: (L ++ a :: b :: R) := hcq
      rcases List.mem_cons.mp hcq' with e | e
      · rw [e] at hc
        exact hxn ((mem_insert_iff x L M R a b).mpr (Or.inl hc))
      · exact hd c hc e

theorem head?_map_of (f : Coord → Coord) (l : List Coord) (x : Coord)
    (h : l.head? = some x) : (l.map f).head? = some (f x) := by
  cases l with
  | nil => simp at h
  | cons y l =>
    have hyx : y = x := by simpa using h
    subst hyx
    rfl

/-- **Middle contraction.** If a path on a 3-high grid contains a block `M`,
exactly the cells of columns 0–1, between two adjacent cells `a` and `b`,
then removing `M` and shifting two columns left gives a Hamiltonian path of the
grid two columns narrower. -/
theorem contract_mid (w : ℕ) (u v a b : Coord) (L M R : List Coord)
    (hM : ∀ c : Coord, c.1 < 2 → c.2 < 3 → c ∈ M) (hMx : ∀ c ∈ M, c.1 < 2)
    (hMl : M.length = 6) (hab : Adjacent a b)
    (hvp : ValidPath w 3 u v (L ++ a :: (M ++ b :: R))) :
    ValidPath (w - 2) 3 (shiftL2 u) (shiftL2 v) ((L ++ a :: b :: R).map shiftL2) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp
  obtain ⟨hndQ, hdis⟩ := nodup_remove_mid L a b M R hnd
  have hsubQ : ∀ c ∈ L ++ a :: b :: R, c ∈ L ++ a :: (M ++ b :: R) :=
    fun c hc => (mem_insert_iff c L M R a b).mpr (Or.inr hc)
  have hge : ∀ c ∈ L ++ a :: b :: R, 2 ≤ c.1 := by
    intro c hc
    by_contra hlt
    have hcb := hin c (hsubQ c hc)
    unfold InBounds at hcb
    exact hdis c (hM c (by omega) hcb.2) hc
  have ha2 : 2 ≤ a.1 := hge a (by simp)
  have haw := hin a (hsubQ a (by simp))
  unfold InBounds at haw
  unfold ValidPath
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map]
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  · have e : (L ++ a :: b :: R).head? = (L ++ a :: (M ++ b :: R)).head? := by
      cases L <;> rfl
    exact head?_map_of shiftL2 _ u (e.trans hhead)
  · have e1 : (L ++ a :: b :: R).getLast? = (b :: R).getLast? :=
      (getLast?_append_cons L a (b :: R)).trans rfl
    have e2 : (L ++ a :: (M ++ b :: R)).getLast? = (b :: R).getLast? :=
      (getLast?_append_cons L a (M ++ b :: R)).trans (getLast?_append_cons (a :: M) b R)
    exact getLast?_map_coord shiftL2 _ v (e1.trans (e2.symm.trans hlast))
  · apply nodup_map_coord_on shiftL2 _ _ hndQ
    intro c hc d hd hcd
    have hc2 := hge c hc
    have hd2 := hge d hd
    unfold shiftL2 at hcd
    have h1 := congrArg Prod.fst hcd
    have h2 := congrArg Prod.snd hcd
    dsimp only at h1 h2
    ext
    · omega
    · omega
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hdb := hin d (hsubQ d hd)
    have hd2 := hge d hd
    unfold InBounds at hdb ⊢
    unfold shiftL2
    dsimp only
    exact ⟨by omega, hdb.2⟩
  · intro c hc
    obtain ⟨hcx, hcy⟩ := (mem_allCoords (w - 2) 3 c).mp hc
    have hd := hcov (c.1 + 2, c.2) ((mem_allCoords w 3 _).mpr ⟨by dsimp only; omega, hcy⟩)
    rcases (mem_insert_iff _ L M R a b).mp hd with hdM | hdQ
    · have := hMx _ hdM
      dsimp only at this
      omega
    · refine List.mem_map.mpr ⟨_, hdQ, ?_⟩
      unfold shiftL2
      ext
      · show c.1 + 2 - 2 = c.1
        omega
      · rfl
  · have hbR : chainAdjacent (b :: R) = true :=
      chainAdjacent_suffix (L ++ a :: M) (b :: R) (by simpa using hch)
    have habR : chainAdjacent (a :: b :: R) = true := chainAdjacent_cons a b (b :: R) rfl hab hbR
    have hQ := chainAdjacent_replace_tail L a (M ++ b :: R) (b :: R) hch habR
    apply chainAdjacent_map_on shiftL2 _ _ hQ
    intro x hx y hy hadj
    have hx2 := hge x hx
    have hy2 := hge y hy
    unfold Adjacent at hadj ⊢
    unfold shiftL2
    dsimp only
    omega

/-- **The run (C1).** On a 3-high grid, a Hamiltonian path with both endpoints
in columns `≥ 2`, in which `(0, 1)` follows `(0, 0)`, contains one of two
8-cell runs through all of columns 0–1. -/
theorem c1_run (w : ℕ) (u v : Coord) (p : List Coord) (hu : 2 ≤ u.1) (hv2 : 2 ≤ v.1)
    (hvp : ValidPath w 3 u v p) (t1 : PNext p (0, 0) (0, 1)) :
    (∃ L R, p = L ++ (2, 1) :: (1, 1) :: (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (2, 2) :: R) ∨
    (∃ L R, p = L ++ (2, 0) :: (1, 0) :: (0, 0) :: (0, 1) :: (0, 2) :: (1, 2) :: (1, 1) :: (2, 1) :: R) := by
  obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp
  have hum : u ∈ p := by
    cases p with
    | nil => simp at hhead
    | cons a l =>
      have hau : a = u := by simpa using hhead
      rw [hau]
      simp
  have huin := hin u hum
  unfold InBounds at huin
  have hmem : ∀ c : Coord, c.1 < w → c.2 < 3 → c ∈ p :=
    fun c h1 h2 => hcov c ((mem_allCoords w 3 c).mpr ⟨h1, h2⟩)
  have hnh : ∀ c : Coord, c.1 < 2 → p.head? ≠ some c := by
    intro c hc e
    rw [hhead] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have hnl : ∀ c : Coord, c.1 < 2 → p.getLast? ≠ some c := by
    intro c hc e
    rw [hlast] at e
    have := congrArg Prod.fst (Option.some.inj e)
    omega
  have hbd : ∀ y ∈ p, y.1 < w ∧ y.2 < 3 := fun y hy => hin y hy
  have m00 := hmem (0, 0) (by show 0 < w; omega) (by show 0 < 3; omega)
  have m02 := hmem (0, 2) (by show 0 < w; omega) (by show 2 < 3; omega)
  have m10 := hmem (1, 0) (by show 1 < w; omega) (by show 0 < 3; omega)
  have m11 := hmem (1, 1) (by show 1 < w; omega) (by show 1 < 3; omega)
  have m12 := hmem (1, 2) (by show 1 < w; omega) (by show 2 < 3; omega)
  -- (1,0) → (0,0)
  have t0 : PNext p (1, 0) (0, 0) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m00 (hnh (0, 0) (by show 0 < 2; omega)) (hnl (0, 0) (by show 0 < 2; omega))
    have hb := pnext_unique_right hnd hpb t1
    have ha : a = (0, 1) ∨ a = (1, 0) := by
      have hadj := pnext_adj hch hpa
      have hyb := hbd a (pnext_mem_left hpa)
      clear hpa hpb hab hb
      obtain ⟨a1, a2⟩ := a
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases ha with ha | ha
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      exact hpa
  -- (0,1) → (0,2) → (1,2)
  obtain ⟨t2, t3⟩ : PNext p (0, 1) (0, 2) ∧ PNext p (0, 2) (1, 2) := by
    obtain ⟨a, b, hab, hpa, hpb⟩ :=
      interior_two hnd m02 (hnh (0, 2) (by show 0 < 2; omega)) (hnl (0, 2) (by show 0 < 2; omega))
    have ha : a = (0, 1) ∨ a = (1, 2) := by
      have hadj := pnext_adj hch hpa
      have hyb := hbd a (pnext_mem_left hpa)
      clear hpa hpb hab
      obtain ⟨a1, a2⟩ := a
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    have hb : b = (0, 1) ∨ b = (1, 2) := by
      have hadj := pnext_adj hch hpb
      have hyb := hbd b (pnext_mem_right hpb)
      clear hpa hpb hab
      obtain ⟨b1, b2⟩ := b
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha] at hpa
      rw [hb] at hpb
      exact ⟨hpa, hpb⟩
    · exfalso
      rw [hb] at hpb
      have := pnext_unique_left hnd hpb t1
      simp at this
    · exact absurd (ha.trans hb.symm) hab
  -- (1,1): predecessor in {(1,2),(2,1)}, successor in {(1,0),(2,1)}
  obtain ⟨e0, e1, hne, hpe0, hpe1⟩ :=
    interior_two hnd m11 (hnh (1, 1) (by show 1 < 2; omega)) (hnl (1, 1) (by show 1 < 2; omega))
  have he0 : e0 = (1, 2) ∨ e0 = (2, 1) := by
    have hcand : e0 = (0, 1) ∨ e0 = (1, 0) ∨ e0 = (1, 2) ∨ e0 = (2, 1) := by
      have hadj := pnext_adj hch hpe0
      have hyb := hbd e0 (pnext_mem_left hpe0)
      clear hpe0 hpe1 hne
      obtain ⟨a1, a2⟩ := e0
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases hcand with h | h | h | h
    · exfalso
      rw [h] at hpe0
      have := pnext_unique_right hnd hpe0 t2
      simp at this
    · exfalso
      rw [h] at hpe0
      have := pnext_unique_right hnd hpe0 t0
      simp at this
    · exact Or.inl h
    · exact Or.inr h
  have he1 : e1 = (1, 0) ∨ e1 = (2, 1) := by
    have hcand : e1 = (0, 1) ∨ e1 = (1, 0) ∨ e1 = (1, 2) ∨ e1 = (2, 1) := by
      have hadj := pnext_adj hch hpe1
      have hyb := hbd e1 (pnext_mem_right hpe1)
      clear hpe0 hpe1 hne
      obtain ⟨a1, a2⟩ := e1
      unfold Adjacent at hadj
      dsimp only at hadj hyb
      simp only [Prod.mk.injEq]
      omega
    rcases hcand with h | h | h | h
    · exfalso
      rw [h] at hpe1
      have := pnext_unique_left hnd hpe1 t1
      simp at this
    · exact Or.inl h
    · exfalso
      rw [h] at hpe1
      have := pnext_unique_left hnd hpe1 t3
      simp at this
    · exact Or.inr h
  rcases he0 with he0 | he0 <;> rcases he1 with he1 | he1
  · -- (1,2) → (1,1) → (1,0): a cycle through all six cells, impossible
    exfalso
    rw [he0] at hpe0
    rw [he1] at hpe1
    obtain ⟨L, R, hp⟩ := List.append_of_mem m10
    obtain ⟨R1, q1⟩ := pnext_step hnd hp t0
    obtain ⟨R2, q2⟩ := pnext_step hnd q1 t1
    obtain ⟨R3, q3⟩ := pnext_step hnd q2 t2
    obtain ⟨R4, q4⟩ := pnext_step hnd q3 t3
    obtain ⟨R5, q5⟩ := pnext_step hnd q4 hpe0
    obtain ⟨R6, q6⟩ := pnext_step hnd q5 hpe1
    have hnd' : (L ++ (1, 0) :: R).Nodup := by rw [← hp]; exact hnd
    have hsu := split_unique L _ R R6 (1, 0) hnd' (hp.symm.trans q6)
    have hl := congrArg List.length hsu.1
    simp at hl
  · -- (1,2) → (1,1) → (2,1): the run starts (2,0) → (1,0)
    rw [he0] at hpe0
    rw [he1] at hpe1
    have t4 : PNext p (2, 0) (1, 0) := by
      obtain ⟨a, b, hab, hpa, hpb⟩ :=
        interior_two hnd m10 (hnh (1, 0) (by show 1 < 2; omega)) (hnl (1, 0) (by show 1 < 2; omega))
      have hb := pnext_unique_right hnd hpb t0
      have hcand : a = (0, 0) ∨ a = (1, 1) ∨ a = (2, 0) := by
        have hadj := pnext_adj hch hpa
        have hyb := hbd a (pnext_mem_left hpa)
        clear hpa hpb hab hb
        obtain ⟨a1, a2⟩ := a
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h
      · exact absurd (h.trans hb.symm) hab
      · exfalso
        rw [h] at hpa
        have := pnext_unique_right hnd hpa hpe1
        simp at this
      · rw [h] at hpa
        exact hpa
    have m20 := hmem (2, 0) (by show 2 < w; omega) (by show 0 < 3; omega)
    obtain ⟨L, R, hp⟩ := List.append_of_mem m20
    obtain ⟨R1, q1⟩ := pnext_step hnd hp t4
    obtain ⟨R2, q2⟩ := pnext_step hnd q1 t0
    obtain ⟨R3, q3⟩ := pnext_step hnd q2 t1
    obtain ⟨R4, q4⟩ := pnext_step hnd q3 t2
    obtain ⟨R5, q5⟩ := pnext_step hnd q4 t3
    obtain ⟨R6, q6⟩ := pnext_step hnd q5 hpe0
    obtain ⟨R7, q7⟩ := pnext_step hnd q6 hpe1
    exact Or.inr ⟨L, R7, by rw [q7]; simp⟩
  · -- (2,1) → (1,1) → (1,0): the run ends (1,2) → (2,2)
    rw [he0] at hpe0
    rw [he1] at hpe1
    have t5 : PNext p (1, 2) (2, 2) := by
      obtain ⟨a, b, hab, hpa, hpb⟩ :=
        interior_two hnd m12 (hnh (1, 2) (by show 1 < 2; omega)) (hnl (1, 2) (by show 1 < 2; omega))
      have ha := pnext_unique_left hnd hpa t3
      have hcand : b = (0, 2) ∨ b = (1, 1) ∨ b = (2, 2) := by
        have hadj := pnext_adj hch hpb
        have hyb := hbd b (pnext_mem_right hpb)
        clear hpa hpb hab ha
        obtain ⟨b1, b2⟩ := b
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      rcases hcand with h | h | h
      · exact absurd (ha.trans h.symm) hab
      · exfalso
        rw [h] at hpb
        have := pnext_unique_left hnd hpb hpe0
        simp at this
      · rw [h] at hpb
        exact hpb
    have m21 := hmem (2, 1) (by show 2 < w; omega) (by show 1 < 3; omega)
    obtain ⟨L, R, hp⟩ := List.append_of_mem m21
    obtain ⟨R1, q1⟩ := pnext_step hnd hp hpe0
    obtain ⟨R2, q2⟩ := pnext_step hnd q1 hpe1
    obtain ⟨R3, q3⟩ := pnext_step hnd q2 t0
    obtain ⟨R4, q4⟩ := pnext_step hnd q3 t1
    obtain ⟨R5, q5⟩ := pnext_step hnd q4 t2
    obtain ⟨R6, q6⟩ := pnext_step hnd q5 t3
    obtain ⟨R7, q7⟩ := pnext_step hnd q6 t5
    exact Or.inl ⟨L, R7, by rw [q7]; simp⟩
  · exact absurd (he0.trans he1.symm) hne

/-- **Contraction step.** On a 3-high grid, a Hamiltonian path with both
endpoints in columns `≥ 2` gives one on the grid two columns narrower, with
both endpoints shifted two columns left. -/
theorem c1_contract (w : ℕ) (u v : Coord) (hu : 2 ≤ u.1) (hv : 2 ≤ v.1)
    (h : HasHamPath w 3 u v) : HasHamPath (w - 2) 3 (shiftL2 u) (shiftL2 v) := by
  have hM1 : ∀ c : Coord, c.1 < 2 → c.2 < 3 →
      c ∈ [(1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (1, 2)] := by
    intro c h1 h2
    obtain ⟨c1, c2⟩ := c
    dsimp only at h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  have hMx1 : ∀ c ∈ [(1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (1, 2)], c.1 < 2 := by
    intro c hc
    obtain ⟨c1, c2⟩ := c
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    show c1 < 2
    omega
  have hM2 : ∀ c : Coord, c.1 < 2 → c.2 < 3 →
      c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] := by
    intro c h1 h2
    obtain ⟨c1, c2⟩ := c
    dsimp only at h1 h2
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
    omega
  have hMx2 : ∀ c ∈ [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)], c.1 < 2 := by
    intro c hc
    obtain ⟨c1, c2⟩ := c
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
    show c1 < 2
    omega
  have core : ∀ (u v : Coord) (p : List Coord), 2 ≤ u.1 → 2 ≤ v.1 →
      ValidPath w 3 u v p → PNext p (0, 0) (0, 1) →
      HasHamPath (w - 2) 3 (shiftL2 u) (shiftL2 v) := by
    intro u v p hu hv hvp t1
    rcases c1_run w u v p hu hv hvp t1 with ⟨L, R, e⟩ | ⟨L, R, e⟩
    · rw [e] at hvp
      exact ⟨_, contract_mid w u v (2, 1) (2, 2) L [(1, 1), (1, 0), (0, 0), (0, 1), (0, 2), (1, 2)] R
        hM1 hMx1 rfl (by unfold Adjacent; dsimp only; omega) hvp⟩
    · rw [e] at hvp
      exact ⟨_, contract_mid w u v (2, 0) (2, 1) L [(1, 0), (0, 0), (0, 1), (0, 2), (1, 2), (1, 1)] R
        hM2 hMx2 rfl (by unfold Adjacent; dsimp only; omega) hvp⟩
  obtain ⟨p, hvp⟩ := h
  by_cases hor : PNext p (0, 0) (0, 1)
  · exact core u v p hu hv hvp hor
  · -- then (0,1) comes right before (0,0); reverse the path
    have hBA : PNext p (0, 1) (0, 0) := by
      have hvp' := hvp
      obtain ⟨hlen, hhead, hlast, hnd, hin, hcov, hch⟩ := hvp'
      have hum : u ∈ p := by
        cases p with
        | nil => simp at hhead
        | cons a l =>
          have hau : a = u := by simpa using hhead
          rw [hau]
          simp
      have huin := hin u hum
      unfold InBounds at huin
      have m00 := hcov (0, 0) ((mem_allCoords w 3 _).mpr ⟨by show 0 < w; omega, by show 0 < 3; omega⟩)
      have hnh : p.head? ≠ some (0, 0) := by
        intro e
        rw [hhead] at e
        have := congrArg Prod.fst (Option.some.inj e)
        dsimp only at this
        omega
      have hnl : p.getLast? ≠ some (0, 0) := by
        intro e
        rw [hlast] at e
        have := congrArg Prod.fst (Option.some.inj e)
        dsimp only at this
        omega
      obtain ⟨a, b, hab, hpa, hpb⟩ := interior_two hnd m00 hnh hnl
      have hcand : ∀ y ∈ p, (Adjacent y (0, 0) ∨ Adjacent (0, 0) y) → y = (0, 1) ∨ y = (1, 0) := by
        intro y hy hadj
        have hyb := hin y hy
        unfold InBounds at hyb
        obtain ⟨y1, y2⟩ := y
        unfold Adjacent at hadj
        dsimp only at hadj hyb
        simp only [Prod.mk.injEq]
        omega
      have ha := hcand a (pnext_mem_left hpa) (Or.inl (pnext_adj hch hpa))
      have hb := hcand b (pnext_mem_right hpb) (Or.inr (pnext_adj hch hpb))
      rcases hb with hb | hb
      · rw [hb] at hpb
        exact absurd hpb hor
      · rcases ha with ha | ha
        · rw [ha] at hpa
          exact hpa
        · exact absurd (ha.trans hb.symm) hab
    have hvr := validPath_reverse hvp
    exact hasHamPath_reverse (core v u p.reverse hv hu hvr (pnext_reverse hBA))

/-! ### The obstruction -/

/-- **Case-3 obstruction on 3-high grids.** If `u` has colour 1, lies left of
`v`, and either `u` is in the middle row or `v` is at least two columns
further right, there is no Hamiltonian path from `u` to `v`. Induction on
`u.x`: B0 for `u.x = 0`, B1 for `u.x = 1`, and the contraction C1 otherwise. -/
theorem obs_no_path (k : ℕ) : ∀ (w : ℕ) (u v : Coord), u.1 ≤ k → (u.1 + u.2) % 2 = 1 →
    u.2 < 3 → u.1 < v.1 → (u.2 = 1 ∨ u.1 + 1 < v.1) → ¬ HasHamPath w 3 u v := by
  induction k with
  | zero =>
    intro w u v hk hc hu3 hlt hcond h
    obtain ⟨u1, u2⟩ := u
    dsimp only at hk hc hu3 hlt hcond
    have e1 : u1 = 0 := by omega
    have e2 : u2 = 1 := by omega
    subst e1
    subst e2
    exact b0_no_path w v (by omega) h
  | succ k ih =>
    intro w u v hk hc hu3 hlt hcond h
    by_cases hk' : u.1 ≤ k
    · exact ih w u v hk' hc hu3 hlt hcond h
    · obtain ⟨u1, u2⟩ := u
      dsimp only at hk hc hu3 hlt hcond hk'
      by_cases h1 : u1 = 1
      · subst h1
        have hv3 : 3 ≤ v.1 := by omega
        rcases (by omega : u2 = 0 ∨ u2 = 2) with e | e
        · subst e
          exact b1_no_path w v hv3 h
        · subst e
          exact b1_no_path' w v hv3 h
      · have hu2 : 2 ≤ u1 := by omega
        have hc1 := c1_contract w (u1, u2) v hu2 (by omega) h
        exact ih (w - 2) (shiftL2 (u1, u2)) (shiftL2 v)
          (by unfold shiftL2; dsimp only; omega) (by unfold shiftL2; dsimp only; omega)
          (by unfold shiftL2; dsimp only; omega) (by unfold shiftL2; dsimp only; omega)
          (by unfold shiftL2; dsimp only; omega) hc1

end GridHam
