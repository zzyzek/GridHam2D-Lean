import GridHam.PrimeTable
import GridHam.Arith
import GridHam.StripSplit
import GridHam.Reduction
import GridHam.Necessity

/-!
# Main theorem: IPS's characterization of Hamiltonian paths in rectangular
grid graphs

```
theorem ips_characterization (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t) (hst : s ≠ t) :
    HasHamPath width height s t ↔ IsAcceptable width height s t
```

* (⇐) `ips_sufficiency`: strong induction on `width + height`. Normalize so
  that `height ≤ width` (transpose) and `s.x ≤ t.x` (swap endpoints, reverse
  the path). Then: prime shape → `prime_solvable`; otherwise strip left
  (`branchA`), strip right (`branchC`), or split after column 1 (`branchB`),
  and apply the induction hypothesis to the smaller pieces.
* (⇒) `hamPath_implies_acceptable` in `Necessity.lean`.
-/

namespace GridHam

/-- The statement proved by induction on `n`. -/
def SuffP (n : ℕ) : Prop :=
  ∀ (w h : ℕ) (s t : Coord), w + h ≤ n → InBounds w h s → InBounds w h t → s ≠ t →
    IsAcceptable w h s t → HasHamPath w h s t

/-- A free vertex in column `c`, in the form the strip lemmas want. -/
theorem freeCol_exists (c h sx sy tx ty : ℕ) (hf : FreeCol c h sx sy tx ty) :
    ∃ y, y < h ∧ (c, y) ≠ (sx, sy) ∧ (c, y) ≠ (tx, ty) := by
  unfold FreeCol at hf
  rcases hf with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨0, h0, fun e => h1 ?_, fun e => h2 ?_⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
  · refine ⟨1, h0, fun e => h1 ?_, fun e => h2 ?_⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
  · refine ⟨2, h0, fun e => h1 ?_, fun e => h2 ?_⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩
    · exact ⟨(Prod.mk.inj e).1.symm, (Prod.mk.inj e).2.symm⟩

/-- **Induction step, normalized case** (`h ≤ w`, `s.x ≤ t.x`). -/
theorem step_normalized (n : ℕ) (IH : SuffP n) (w h : ℕ) (s t : Coord)
    (hsz : w + h ≤ n + 1) (hwh : h ≤ w) (hle : s.1 ≤ t.1)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : HasHamPath w h s t := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  have hs' : sx < w ∧ sy < h := hs
  have ht' : tx < w ∧ ty < h := ht
  have hle' : sx ≤ tx := hle
  have hst' : ¬ (sx = tx ∧ sy = ty) := by
    rintro ⟨e1, e2⟩
    apply hst
    rw [e1, e2]
  have hA : AccA w h sx sy tx ty := (acc_iff w h (sx, sy) (tx, ty)).mp hacc
  by_cases hnp : NotPrime w h
  · have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
    by_cases hA2 : 2 ≤ sx
    · -- (A) strip the two leftmost columns
      obtain ⟨hsub, hfree⟩ := branchA w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA hA2
      apply stripLeft_preserves w h (sx, sy) (tx, ty) hA2 (by show 2 ≤ tx; omega)
        (freeCol_exists 2 h sx sy tx ty hfree)
      apply IH (w - 2) h (sx - 2, sy) (tx - 2, ty) (by omega)
        (show sx - 2 < w - 2 ∧ sy < h by omega) (show tx - 2 < w - 2 ∧ ty < h by omega)
      · intro e
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact hst' ⟨by omega, e2⟩
      · exact (acc_iff (w - 2) h (sx - 2, sy) (tx - 2, ty)).mpr hsub
    · by_cases hC : tx + 2 < w
      · -- (C) strip the two rightmost columns
        obtain ⟨hsub, hfree⟩ :=
          branchC w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) hC
        apply stripRight_preserves w h (sx, sy) (tx, ty) (by show sx + 2 < w; omega) hC
          (freeCol_exists (w - 3) h sx sy tx ty hfree)
        apply IH (w - 2) h (sx, sy) (tx, ty) (by omega)
          (show sx < w - 2 ∧ sy < h by omega) (show tx < w - 2 ∧ ty < h by omega) hst
        exact (acc_iff (w - 2) h (sx, sy) (tx, ty)).mpr hsub
      · -- (B) split after column 1 at row `rChoice sx sy h`
        have hB := branchB w h sx sy tx ty hs' ht' hst' hwh hle' hnp hA (by omega) (by omega)
        unfold BConcl at hB
        obtain ⟨hr, hs1, hq, haccL, haccR⟩ := hB
        have hleft : HasHamPath 2 h (sx, sy) (1, rChoice sx sy h) := by
          apply IH 2 h (sx, sy) (1, rChoice sx sy h) (by omega)
            (show sx < 2 ∧ sy < h by omega) (show 1 < 2 ∧ rChoice sx sy h < h by omega)
          · intro e
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            exact hs1 ⟨e1, e2⟩
          · exact (acc_iff 2 h (sx, sy) (1, rChoice sx sy h)).mpr haccL
        have hright : HasHamPath (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) := by
          apply IH (w - 2) h (0, rChoice sx sy h) (tx - 2, ty) (by omega)
            (show 0 < w - 2 ∧ rChoice sx sy h < h by omega)
            (show tx - 2 < w - 2 ∧ ty < h by omega)
          · intro e
            obtain ⟨e1, e2⟩ := Prod.mk.inj e
            exact hq ⟨e1, e2⟩
          · exact (acc_iff (w - 2) h (0, rChoice sx sy h) (tx - 2, ty)).mpr haccR
        exact splitVertically_preserves_startLeft w h 1 (rChoice sx sy h) (sx, sy) (tx, ty)
          (by show sx < tx; omega) (by show sx ≤ 1; omega) (by show 1 < tx; omega)
          hr hleft hright
  · -- prime shape
    exact prime_solvable w h (sx, sy) (tx, ty)
      (mem_primeShapes_of w h (by omega) (by omega) hnp) hs ht hst hacc

/-- **Induction step, `h ≤ w`, any order of endpoints.** -/
theorem step_wide (n : ℕ) (IH : SuffP n) (w h : ℕ) (s t : Coord)
    (hsz : w + h ≤ n + 1) (hwh : h ≤ w)
    (hs : InBounds w h s) (ht : InBounds w h t) (hst : s ≠ t)
    (hacc : IsAcceptable w h s t) : HasHamPath w h s t := by
  by_cases hle : s.1 ≤ t.1
  · exact step_normalized n IH w h s t hsz hwh hle hs ht hst hacc
  · have hacc' : IsAcceptable w h t s :=
      (acc_iff w h t s).mpr ((accA_swap w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
    exact hasHamPath_reverse
      (step_normalized n IH w h t s hsz hwh (by omega) ht hs (Ne.symm hst) hacc')

/-- **Induction step.** -/
theorem suff_step (n : ℕ) (IH : SuffP n) : SuffP (n + 1) := by
  intro w h s t hsz hs ht hst hacc
  by_cases hwh : h ≤ w
  · exact step_wide n IH w h s t hsz hwh hs ht hst hacc
  · have hs0 : s.1 < w ∧ s.2 < h := hs
    have ht0 : t.1 < w ∧ t.2 < h := ht
    have hsT : InBounds h w (swapXY s) := show s.2 < h ∧ s.1 < w from ⟨hs0.2, hs0.1⟩
    have htT : InBounds h w (swapXY t) := show t.2 < h ∧ t.1 < w from ⟨ht0.2, ht0.1⟩
    have hstT : swapXY s ≠ swapXY t := fun e => hst (congrArg swapXY e)
    have haccT : IsAcceptable h w (swapXY s) (swapXY t) :=
      (acc_iff h w (swapXY s) (swapXY t)).mpr
        ((accA_transpose w h s.1 s.2 t.1 t.2 hs ht).mp ((acc_iff w h s t).mp hacc))
    exact hasHamPath_transpose
      (step_wide n IH h w (swapXY s) (swapXY t) (by omega) (by omega) hsT htT hstT haccT)

theorem suff_all : ∀ n, SuffP n
  | 0 => by
    intro w h s t hsz hs _ _ _
    have hs0 : s.1 < w ∧ s.2 < h := hs
    omega
  | n + 1 => suff_step n (suff_all n)

/-- **Sufficiency (IPS Theorem 3.2, ⇐).** Every acceptable problem with
`s ≠ t` has a Hamiltonian path. -/
theorem ips_sufficiency (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t)
    (hacc : IsAcceptable width height s t) :
    HasHamPath width height s t :=
  suff_all (width + height) width height s t (Nat.le_refl _) hs ht hst hacc

/-- **Main theorem.** IPS's characterization: a Hamiltonian path exists
between distinct vertices `s` and `t` of the `width × height` grid graph if
and only if the problem is acceptable (colour compatible and not forbidden).

The hypothesis `s ≠ t` is required: without it the statement is false (e.g.
on a 3×3 grid, `s = t = (0,0)` is `IsAcceptable` -- both endpoints have
parity 0 and no forbidden case applies -- but no Hamiltonian path starts and
ends at the same vertex of a 9-vertex grid). Only the sufficiency direction
needs it. -/
theorem ips_characterization (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t) :
    HasHamPath width height s t ↔ IsAcceptable width height s t :=
  ⟨hamPath_implies_acceptable width height s t hs ht,
   ips_sufficiency width height s t hs ht hst⟩

end GridHam

-- Which axioms each result depends on. `sorryAx` means an unfinished proof.
#print axioms GridHam.ips_sufficiency
#print axioms GridHam.ips_characterization
