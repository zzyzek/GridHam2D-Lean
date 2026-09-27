import GridHam.Arith
import GridHam.StripSplit
import GridHam.F3

/-!
# Necessity (IPS Theorem 3.1): a Hamiltonian path forces acceptability

* colour compatibility: `hamPath_implies_colorCompatible` (`Coloring.lean`);
* forbidden case 1: `forbiddenCase1_implies_no_path` (`Forbidden.lean`);
* forbidden case 2: `forbiddenCase2_implies_no_path` (below);
* forbidden case 3: `forbiddenCase3_implies_no_path` (below, via `obs_no_path` in `F3.lean`).

Case 2 is a separation argument. On a 2-wide grid with `s = (0, y)`,
`t = (1, y)` in an interior row, the part of the path strictly between `s`
and `t` visits both a cell below row `y` and a cell above it. Consecutive
cells differ by at most 1 in row, so that part passes through row `y`, whose
only cells are `s` and `t`: impossible. The 2-high case is the same with
columns.
-/

namespace GridHam

/-- Intermediate values along an adjacent-chain, for any coordinate-like `f`
that changes by at most 1 per grid step. -/
theorem chain_proj_intermediate (f : Coord → ℕ)
    (hf : ∀ a b, Adjacent a b → f a ≤ f b + 1 ∧ f b ≤ f a + 1) :
    ∀ (l : List Coord), chainAdjacent l = true →
      ∀ a ∈ l, ∀ b ∈ l, ∀ z, f a ≤ z → z ≤ f b → ∃ c ∈ l, f c = z := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x rest ih =>
    intro hch a ha b hb z hz1 hz2
    cases rest with
    | nil =>
      have hax : a = x := by simpa using ha
      have hbx : b = x := by simpa using hb
      rw [hax] at hz1
      rw [hbx] at hz2
      exact ⟨x, by simp, by omega⟩
    | cons y rest' =>
      have hc' : (adjacentB x y && chainAdjacent (y :: rest')) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hxy, hcl⟩ := hc'
      have hadj : Adjacent x y := by
        unfold adjacentB at hxy
        by_contra hcon
        simp [hcon] at hxy
      have hstep := hf x y hadj
      have lift : ∀ c, c ∈ y :: rest' → c ∈ x :: y :: rest' :=
        fun c hc => List.mem_cons.mpr (Or.inr hc)
      have hymem : y ∈ y :: rest' := by simp
      have key : ∀ w ∈ y :: rest', ∀ z',
          ((f x ≤ z' ∧ z' ≤ f w) ∨ (f w ≤ z' ∧ z' ≤ f x)) →
          ∃ c ∈ x :: y :: rest', f c = z' := by
        intro w hw z' hz'
        by_cases h1 : f y ≤ z' ∧ z' ≤ f w
        · obtain ⟨c, hc, hfc⟩ := ih hcl y hymem w hw z' h1.1 h1.2
          exact ⟨c, lift c hc, hfc⟩
        · by_cases h2 : f w ≤ z' ∧ z' ≤ f y
          · obtain ⟨c, hc, hfc⟩ := ih hcl w hw y hymem z' h2.1 h2.2
            exact ⟨c, lift c hc, hfc⟩
          · exact ⟨x, by simp, by omega⟩
      rcases List.mem_cons.mp ha with hax | har
      · rcases List.mem_cons.mp hb with hbx | hbr
        · rw [hax] at hz1
          rw [hbx] at hz2
          exact ⟨x, by simp, by omega⟩
        · rw [hax] at hz1
          exact key b hbr z (Or.inl ⟨hz1, hz2⟩)
      · rcases List.mem_cons.mp hb with hbx | hbr
        · rw [hbx] at hz2
          exact key a har z (Or.inr ⟨hz1, hz2⟩)
        · obtain ⟨c, hc, hfc⟩ := ih hcl a har b hbr z hz1 hz2
          exact ⟨c, lift c hc, hfc⟩

theorem chainAdjacent_prefix : ∀ (l1 l2 : List Coord),
    chainAdjacent (l1 ++ l2) = true → chainAdjacent l1 = true := by
  intro l1
  induction l1 with
  | nil => intro _ _; rfl
  | cons x l ih =>
    intro l2 h
    cases l with
    | nil => rfl
    | cons y l' =>
      have hc' : (adjacentB x y && chainAdjacent (y :: (l' ++ l2))) = true := by
        simpa [chainAdjacent] using h
      simp at hc'
      obtain ⟨hxy, hcl⟩ := hc'
      have hrec : chainAdjacent (y :: l') = true := ih l2 hcl
      have e : chainAdjacent (x :: y :: l') = (adjacentB x y && chainAdjacent (y :: l')) := rfl
      simp only [e, hxy, hrec, Bool.and_self]

theorem nodup_not_mem_last : ∀ (m : List Coord) (t : Coord), (m ++ [t]).Nodup → t ∉ m := by
  intro m
  induction m with
  | nil => intro t _; simp
  | cons x m' ih =>
    intro t h
    have h' : (x :: (m' ++ [t])).Nodup := h
    obtain ⟨hxn, hrest⟩ := List.nodup_cons.mp h'
    intro hm
    rcases List.mem_cons.mp hm with e | e
    · apply hxn
      rw [← e]
      simp
    · exact ih t hrest e

/-- Splitting a Hamiltonian path `s :: rest` into `s :: (m ++ [t])`. -/
theorem path_split_ends {width height : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath width height s t p) (hbig : 2 ≤ width * height) :
    ∃ m, p = s :: (m ++ [t]) := by
  obtain ⟨hlen, hhead, hlast, _, _, _, _⟩ := hv
  cases p with
  | nil => simp at hhead
  | cons a rest =>
    have has : a = s := by simpa using hhead
    have hlen' : rest.length + 1 = width * height := hlen
    have hrne : rest ≠ [] := by
      intro e
      rw [e, List.length_nil] at hlen'
      omega
    have hlast' : rest.getLast? = some t := by
      cases rest with
      | nil => exact absurd rfl hrne
      | cons b r => exact hlast
    have hdl := List.dropLast_append_getLast hrne
    rw [getLast?_eq_getLast_of_ne_nil rest hrne t hlast'] at hdl
    exact ⟨rest.dropLast, by rw [has, hdl]⟩

/-- Forbidden case 2, width 2: `s`, `t` in the same interior row. -/
theorem f2_width2_no_path (h : ℕ) (s t : Coord) (hsb : s.1 < 2 ∧ s.2 < h)
    (htb : t.1 < 2 ∧ t.2 < h) (hrow : s.2 = t.2) (hy0 : 0 < s.2) (hy1 : s.2 + 1 < h) :
    ¬ HasHamPath 2 h s t := by
  rintro ⟨p, hv⟩
  obtain ⟨m, hpm⟩ := path_split_ends hv (by omega)
  obtain ⟨_, _, _, hnd, hin, hcov, hch⟩ := hv
  rw [hpm] at hnd hin hcov hch
  obtain ⟨hsn, hndr⟩ := List.nodup_cons.mp hnd
  have hchm : chainAdjacent m = true := chainAdjacent_prefix m [t] (chainAdjacent_tail s _ hch)
  have htm : t ∉ m := nodup_not_mem_last m t hndr
  have hsm : s ∉ m := fun hm => hsn (List.mem_append.mpr (Or.inl hm))
  have hst : s.1 ≠ t.1 := by
    intro e
    apply hsn
    have hst' : s = t := by
      ext
      · exact e
      · exact hrow
    rw [hst']
    simp
  have inm : ∀ v : Coord, v.1 < 2 → v.2 < h → v ≠ s → v ≠ t → v ∈ m := by
    intro v hvx hvy hvs hvt
    have hv := hcov v ((mem_allCoords 2 h v).mpr ⟨hvx, hvy⟩)
    rcases List.mem_cons.mp hv with e | e
    · exact absurd e hvs
    · rcases List.mem_append.mp e with e2 | e2
      · exact e2
      · exact absurd (List.mem_singleton.mp e2) hvt
  have ha0 : ((0, 0) : Coord) ∈ m :=
    inm (0, 0) (by show 0 < 2; omega) (by show 0 < h; omega)
      (fun e => by rw [← e] at hy0; exact absurd hy0 (by show ¬ 0 < 0; omega))
      (fun e => by rw [← e] at hrow; exact absurd hy0 (by show ¬ 0 < s.2; rw [hrow]; omega))
  have hb0 : ((0, h - 1) : Coord) ∈ m :=
    inm (0, h - 1) (by show 0 < 2; omega) (by show h - 1 < h; omega)
      (fun e => by rw [← e] at hy1; exact absurd hy1 (by show ¬ h - 1 + 1 < h; omega))
      (fun e => by
        rw [← e] at hrow
        exact absurd hy1 (by show ¬ s.2 + 1 < h; rw [hrow]; show ¬ h - 1 + 1 < h; omega))
  obtain ⟨c, hc, hcy⟩ := chain_proj_intermediate Prod.snd
    (fun u v huv => by unfold Adjacent at huv; omega) m hchm (0, 0) ha0 (0, h - 1) hb0 s.2
    (by show 0 ≤ s.2; omega) (by show s.2 ≤ h - 1; omega)
  have hcb := hin c (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hc))))
  unfold InBounds at hcb
  have hcy' : c.2 = s.2 := hcy
  rcases (by omega : c.1 = s.1 ∨ c.1 = t.1) with h1 | h1
  · have hcs : c = s := by
      ext
      · exact h1
      · exact hcy'
    rw [hcs] at hc
    exact hsm hc
  · have hct : c = t := by
      ext
      · exact h1
      · rw [hcy', hrow]
    rw [hct] at hc
    exact htm hc

/-- Forbidden case 2, height 2: `s`, `t` in the same interior column. -/
theorem f2_height2_no_path (w : ℕ) (s t : Coord) (hsb : s.1 < w ∧ s.2 < 2)
    (htb : t.1 < w ∧ t.2 < 2) (hcol : s.1 = t.1) (hx0 : 0 < s.1) (hx1 : s.1 + 1 < w) :
    ¬ HasHamPath w 2 s t := by
  rintro ⟨p, hv⟩
  obtain ⟨m, hpm⟩ := path_split_ends hv (by omega)
  obtain ⟨_, _, _, hnd, hin, hcov, hch⟩ := hv
  rw [hpm] at hnd hin hcov hch
  obtain ⟨hsn, hndr⟩ := List.nodup_cons.mp hnd
  have hchm : chainAdjacent m = true := chainAdjacent_prefix m [t] (chainAdjacent_tail s _ hch)
  have htm : t ∉ m := nodup_not_mem_last m t hndr
  have hsm : s ∉ m := fun hm => hsn (List.mem_append.mpr (Or.inl hm))
  have hst : s.2 ≠ t.2 := by
    intro e
    apply hsn
    have hst' : s = t := by
      ext
      · exact hcol
      · exact e
    rw [hst']
    simp
  have inm : ∀ v : Coord, v.1 < w → v.2 < 2 → v ≠ s → v ≠ t → v ∈ m := by
    intro v hvx hvy hvs hvt
    have hv := hcov v ((mem_allCoords w 2 v).mpr ⟨hvx, hvy⟩)
    rcases List.mem_cons.mp hv with e | e
    · exact absurd e hvs
    · rcases List.mem_append.mp e with e2 | e2
      · exact e2
      · exact absurd (List.mem_singleton.mp e2) hvt
  have ha0 : ((0, 0) : Coord) ∈ m :=
    inm (0, 0) (by show 0 < w; omega) (by show 0 < 2; omega)
      (fun e => by rw [← e] at hx0; exact absurd hx0 (by show ¬ 0 < 0; omega))
      (fun e => by rw [← e] at hcol; exact absurd hx0 (by show ¬ 0 < s.1; rw [hcol]; omega))
  have hb0 : ((w - 1, 0) : Coord) ∈ m :=
    inm (w - 1, 0) (by show w - 1 < w; omega) (by show 0 < 2; omega)
      (fun e => by rw [← e] at hx1; exact absurd hx1 (by show ¬ w - 1 + 1 < w; omega))
      (fun e => by
        rw [← e] at hcol
        exact absurd hx1 (by show ¬ s.1 + 1 < w; rw [hcol]; show ¬ w - 1 + 1 < w; omega))
  obtain ⟨c, hc, hcx⟩ := chain_proj_intermediate Prod.fst
    (fun u v huv => by unfold Adjacent at huv; omega) m hchm (0, 0) ha0 (w - 1, 0) hb0 s.1
    (by show 0 ≤ s.1; omega) (by show s.1 ≤ w - 1; omega)
  have hcb := hin c (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hc))))
  unfold InBounds at hcb
  have hcx' : c.1 = s.1 := hcx
  rcases (by omega : c.2 = s.2 ∨ c.2 = t.2) with h1 | h1
  · have hcs : c = s := by
      ext
      · exact hcx'
      · exact h1
    rw [hcs] at hc
    exact hsm hc
  · have hct : c = t := by
      ext
      · rw [hcx', hcol]
      · exact h1
    rw [hct] at hc
    exact htm hc

/-- **Forbidden case 2 is really forbidden.** -/
theorem forbiddenCase2_implies_no_path (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hf : ForbiddenCase2 width height s t) :
    ¬ HasHamPath width height s t := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < width ∧ sy < height := hs
  have ht' : tx < width ∧ ty < height := ht
  rw [forbiddenCase2_iff] at hf
  unfold F2A cornerA at hf
  obtain ⟨hcs, _, hrc⟩ := hf
  rcases hrc with ⟨hw, hrow⟩ | ⟨hh, hcol⟩
  · subst hw
    exact f2_width2_no_path height (sx, sy) (tx, ty) hs' ht' hrow (by show 0 < sy; omega)
      (by show sy + 1 < height; omega)
  · subst hh
    exact f2_height2_no_path width (sx, sy) (tx, ty) hs' ht' hcol (by show 0 < sx; omega)
      (by show sx + 1 < width; omega)

/-- The case-3 pattern on a 3-high grid of width `m` has no Hamiltonian path.
Whichever endpoint has colour 1 is the left one; it plays `u` in
`obs_no_path` (for `t`, through the reversed path). -/
theorem g3_no_path (m sx sy tx ty : ℕ) (hs : sx < m ∧ sy < 3) (ht : tx < m ∧ ty < 3)
    (hg : G3 m sx tx sy ((sx + sy) % 2) ((tx + ty) % 2)) :
    ¬ HasHamPath m 3 (sx, sy) (tx, ty) := by
  intro hp
  unfold G3 at hg
  by_cases hlt : tx < sx
  · exact obs_no_path tx m (tx, ty) (sx, sy) (Nat.le_refl _)
      (by show (tx + ty) % 2 = 1; omega) (by show ty < 3; omega) (by show tx < sx; omega)
      (by show ty = 1 ∨ tx + 1 < sx; omega) (hasHamPath_reverse hp)
  · exact obs_no_path sx m (sx, sy) (tx, ty) (Nat.le_refl _)
      (by show (sx + sy) % 2 = 1; omega) (by show sy < 3; omega) (by show sx < tx; omega)
      (by show sy = 1 ∨ sx + 1 < tx; omega) hp

/-- **Forbidden case 3 is really forbidden.** Height 3 directly; width 3 by
transposing. -/
theorem forbiddenCase3_implies_no_path (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h3 : width = 3 ∨ height = 3) (hf : ForbiddenCase3 width height s t) :
    ¬ HasHamPath width height s t := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < width ∧ sy < height := hs
  have ht' : tx < width ∧ ty < height := ht
  rw [forbiddenCase3_iff] at hf
  unfold F3A at hf
  rcases hf with ⟨hw3, hg⟩ | ⟨hw3, hg⟩
  · subst hw3
    have hg' : G3 height sy ty sx ((sy + sx) % 2) ((ty + tx) % 2) := by
      rw [Nat.add_comm sy sx, Nat.add_comm ty tx]
      exact hg
    intro hp
    exact g3_no_path height sy sx ty tx ⟨hs'.2, hs'.1⟩ ⟨ht'.2, ht'.1⟩ hg'
      (hasHamPath_transpose hp)
  · have hh3 : height = 3 := by omega
    subst hh3
    exact g3_no_path width sx sy tx ty hs' ht' hg

/-- **Necessity, assembled (IPS Theorem 3.1).** If a Hamiltonian path exists,
the problem is acceptable. -/
theorem hamPath_implies_acceptable (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (h : HasHamPath width height s t) :
    IsAcceptable width height s t := by
  refine ⟨hamPath_implies_colorCompatible width height s t h, ?_⟩
  intro hforb
  unfold IsForbidden at hforb
  split_ifs at hforb with h1 h2 h3
  · exact forbiddenCase1_implies_no_path width height s t hs ht h1 hforb h
  · exact forbiddenCase2_implies_no_path width height s t hs ht hforb h
  · exact forbiddenCase3_implies_no_path width height s t hs ht h3 hforb h

end GridHam
