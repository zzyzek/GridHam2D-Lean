import GridHam.Arith
import GridHam.PrimeTable

/-!
# Reduction lemmas (arithmetic)

The main induction normalizes a problem so that `h ≤ w` and `s.x ≤ t.x`, and
then, unless the shape is prime, applies one of three moves:

* (A) `s.x ≥ 2`: strip the two leftmost columns;
* (C) `s.x ≤ 1` and `t.x + 2 < w`: strip the two rightmost columns;
* (B) `s.x ≤ 1` and `t.x ≥ w - 2`: split after column 1, at row `rChoice`.

This file proves that each move produces acceptable subproblems (and, for
strips, the free vertex the strip lemmas need), plus the two symmetries of
acceptability used for normalization. The rule was tested in Python on
1.8 million instances up to 22×22 before being formalized.

`omega` cannot handle a fully unfolded `AccA` (too many disjunctions), so the
proofs go through "regime" lemmas that collapse `AccA` once one dimension is
known (≥ 4, or exactly 1, 2 or 3). Grids with width 4 or 5 (in the reduction
lemmas) and with both sides ≤ 3 (in the symmetry lemmas) are checked by the
kernel directly.
-/

namespace GridHam

/-! Decidability, built piece by piece (a single instance for the fully
unfolded `AccA` is too large for instance search). -/

instance instDecG3 (m c0 c1 oc ps pt : ℕ) : Decidable (G3 m c0 c1 oc ps pt) := by
  unfold G3; infer_instance

instance instDecCornerA (w h x y : ℕ) : Decidable (cornerA w h x y) := by
  unfold cornerA; infer_instance

instance instDecF1A (w h sx sy tx ty : ℕ) : Decidable (F1A w h sx sy tx ty) := by
  unfold F1A; infer_instance

instance instDecF2A (w h sx sy tx ty : ℕ) : Decidable (F2A w h sx sy tx ty) := by
  unfold F2A; infer_instance

instance instDecF3A (w h sx sy tx ty : ℕ) : Decidable (F3A w h sx sy tx ty) := by
  unfold F3A; infer_instance

instance instDecForbA (w h sx sy tx ty : ℕ) : Decidable (ForbA w h sx sy tx ty) := by
  unfold ForbA; infer_instance

instance instDecAccA (w h sx sy tx ty : ℕ) : Decidable (AccA w h sx sy tx ty) := by
  unfold AccA; infer_instance

/-- The colour condition alone. -/
def CCA (w h sx sy tx ty : ℕ) : Prop :=
  (w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
  (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)

/-- Endpoints are the two ends of a single row. -/
def EndsA (w sx sy tx ty : ℕ) : Prop :=
  (sx = 0 ∧ sy = 0 ∧ tx = w - 1 ∧ ty = 0) ∨ (sx = w - 1 ∧ sy = 0 ∧ tx = 0 ∧ ty = 0)

/-- Endpoints are the two ends of a single column. -/
def EndsV (h sx sy tx ty : ℕ) : Prop :=
  (sx = 0 ∧ sy = 0 ∧ tx = 0 ∧ ty = h - 1) ∨ (sx = 0 ∧ sy = h - 1 ∧ tx = 0 ∧ ty = 0)

theorem accA_eq (w h sx sy tx ty : ℕ) :
    AccA w h sx sy tx ty ↔ CCA w h sx sy tx ty ∧ ¬ ForbA w h sx sy tx ty := Iff.rfl

/-! ### Regime lemmas -/

theorem accA_big (w h sx sy tx ty : ℕ) (hw : 4 ≤ w) (hh : 4 ≤ h) :
    AccA w h sx sy tx ty ↔ CCA w h sx sy tx ty := by
  rw [accA_eq]
  have hf : ¬ ForbA w h sx sy tx ty := by
    unfold ForbA
    rintro (⟨hc, _⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩) <;> omega
  exact ⟨fun H => H.1, fun hc => ⟨hc, hf⟩⟩

theorem accA_h1 (w sx sy tx ty : ℕ) (hw : 2 ≤ w) :
    AccA w 1 sx sy tx ty ↔ CCA w 1 sx sy tx ty ∧ EndsA w sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA F1A EndsA
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    by_contra hn
    exact hf (Or.inl ⟨Or.inr rfl, Or.inr ⟨by omega, hn⟩⟩)
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    rintro (⟨_, hf⟩ | ⟨hn, _⟩ | ⟨hn, _⟩)
    · rcases hf with ⟨hw1, _⟩ | ⟨_, hne⟩
      · omega
      · exact hne he
    · exact hn (Or.inr rfl)
    · exact hn (Or.inr rfl)

theorem accA_h2 (w sx sy tx ty : ℕ) (hw : 3 ≤ w) :
    AccA w 2 sx sy tx ty ↔ CCA w 2 sx sy tx ty ∧ ¬ F2A w 2 sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun h2 => hf (Or.inr (Or.inl ⟨by omega, Or.inr rfl, h2⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, _, h2⟩ | ⟨_, hn, _⟩)
    · omega
    · exact hf h2
    · exact hn (Or.inr rfl)

theorem accA_h3 (w sx sy tx ty : ℕ) (hw : 4 ≤ w) :
    AccA w 3 sx sy tx ty ↔
      CCA w 3 sx sy tx ty ∧ ¬ G3 w sx tx sy ((sx + sy) % 2) ((tx + ty) % 2) := by
  rw [accA_eq]
  unfold ForbA F3A
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun g => hf (Or.inr (Or.inr ⟨by omega, by omega, Or.inr rfl, Or.inr ⟨by omega, g⟩⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, hn, _⟩ | ⟨_, _, _, h3⟩)
    · omega
    · omega
    · rcases h3 with ⟨hw3, _⟩ | ⟨_, g⟩
      · omega
      · exact hf g

theorem accA_w1 (h sx sy tx ty : ℕ) (_hh : 2 ≤ h) :
    AccA 1 h sx sy tx ty ↔ CCA 1 h sx sy tx ty ∧ EndsV h sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA F1A EndsV
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    by_contra hn
    exact hf (Or.inl ⟨Or.inl rfl, Or.inl ⟨rfl, hn⟩⟩)
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    rintro (⟨_, hf⟩ | ⟨hn, _⟩ | ⟨hn, _⟩)
    · rcases hf with ⟨_, hne⟩ | ⟨h1, _⟩
      · exact hne he
      · exact h1 rfl
    · exact hn (Or.inl rfl)
    · exact hn (Or.inl rfl)

theorem accA_w2 (h sx sy tx ty : ℕ) (hh : 2 ≤ h) :
    AccA 2 h sx sy tx ty ↔ CCA 2 h sx sy tx ty ∧ ¬ F2A 2 h sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun h2 => hf (Or.inr (Or.inl ⟨by omega, Or.inl rfl, h2⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, _, h2⟩ | ⟨_, hn, _⟩)
    · omega
    · exact hf h2
    · exact hn (Or.inl rfl)

theorem accA_w3 (h sx sy tx ty : ℕ) (hh : 4 ≤ h) :
    AccA 3 h sx sy tx ty ↔
      CCA 3 h sx sy tx ty ∧ ¬ G3 h sy ty sx ((sx + sy) % 2) ((tx + ty) % 2) := by
  rw [accA_eq]
  unfold ForbA F3A
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun g => hf (Or.inr (Or.inr ⟨by omega, by omega, Or.inl rfl, Or.inl ⟨rfl, g⟩⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, hn, _⟩ | ⟨_, _, _, h3⟩)
    · omega
    · omega
    · rcases h3 with ⟨_, g⟩ | ⟨hn, _⟩
      · exact hf g
      · exact hn rfl

/-! ### Symmetries of acceptability -/

set_option maxRecDepth 100000 in
theorem accA_swap_small : ∀ w ∈ List.range 4, ∀ h ∈ List.range 4, ∀ sx ∈ List.range w,
    ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    (AccA w h sx sy tx ty ↔ AccA w h tx ty sx sy) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem accA_transpose_small : ∀ w ∈ List.range 4, ∀ h ∈ List.range 4, ∀ sx ∈ List.range w,
    ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    (AccA w h sx sy tx ty ↔ AccA h w sy sx ty tx) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
/-- Acceptability does not depend on which endpoint is called `s`. -/
theorem accA_swap (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h) :
    AccA w h sx sy tx ty ↔ AccA w h tx ty sx sy := by
  rcases (by omega : (4 ≤ w ∧ 4 ≤ h) ∨ (4 ≤ w ∧ h ≤ 3) ∨ (w ≤ 3 ∧ 4 ≤ h) ∨ (w ≤ 3 ∧ h ≤ 3))
    with hc | hc | hc | hc
  · rw [accA_big w h sx sy tx ty hc.1 hc.2, accA_big w h tx ty sx sy hc.1 hc.2]
    unfold CCA
    constructor <;> intro H <;> omega
  · rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3) with hh | hh | hh <;> subst hh
    · rw [accA_h1 w sx sy tx ty (by omega), accA_h1 w tx ty sx sy (by omega)]
      unfold CCA EndsA
      constructor <;> intro H <;> omega
    · rw [accA_h2 w sx sy tx ty (by omega), accA_h2 w tx ty sx sy (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_h3 w sx sy tx ty (by omega), accA_h3 w tx ty sx sy (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3) with hw | hw | hw <;> subst hw
    · rw [accA_w1 h sx sy tx ty (by omega), accA_w1 h tx ty sx sy (by omega)]
      unfold CCA EndsV
      constructor <;> intro H <;> omega
    · rw [accA_w2 h sx sy tx ty (by omega), accA_w2 h tx ty sx sy (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_w3 h sx sy tx ty (by omega), accA_w3 h tx ty sx sy (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · exact accA_swap_small w (List.mem_range.mpr (by omega)) h (List.mem_range.mpr (by omega))
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)

set_option maxHeartbeats 2000000 in
/-- Acceptability is invariant under transposing the grid. -/
theorem accA_transpose (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h) :
    AccA w h sx sy tx ty ↔ AccA h w sy sx ty tx := by
  rcases (by omega : (4 ≤ w ∧ 4 ≤ h) ∨ (4 ≤ w ∧ h ≤ 3) ∨ (w ≤ 3 ∧ 4 ≤ h) ∨ (w ≤ 3 ∧ h ≤ 3))
    with hc | hc | hc | hc
  · rw [accA_big w h sx sy tx ty hc.1 hc.2, accA_big h w sy sx ty tx hc.2 hc.1]
    unfold CCA
    constructor <;> intro H <;> omega
  · rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3) with hh | hh | hh <;> subst hh
    · rw [accA_h1 w sx sy tx ty (by omega), accA_w1 w sy sx ty tx (by omega)]
      unfold CCA EndsA EndsV
      constructor <;> intro H <;> omega
    · rw [accA_h2 w sx sy tx ty (by omega), accA_w2 w sy sx ty tx (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_h3 w sx sy tx ty (by omega), accA_w3 w sy sx ty tx (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3) with hw | hw | hw <;> subst hw
    · rw [accA_w1 h sx sy tx ty (by omega), accA_h1 h sy sx ty tx (by omega)]
      unfold CCA EndsA EndsV
      constructor <;> intro H <;> omega
    · rw [accA_w2 h sx sy tx ty (by omega), accA_h2 h sy sx ty tx (by omega)]
      unfold CCA F2A cornerA
      constructor <;> intro H <;> omega
    · rw [accA_w3 h sx sy tx ty (by omega), accA_h3 h sy sx ty tx (by omega)]
      unfold CCA G3
      constructor <;> intro H <;> omega
  · exact accA_transpose_small w (List.mem_range.mpr (by omega)) h (List.mem_range.mpr (by omega))
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)

/-! ### Prime shapes -/

/-- Not a prime shape, as inequalities. -/
def NotPrime (w h : ℕ) : Prop :=
  ¬ ((w ≤ 3 ∧ h ≤ 3) ∨ (w = 4 ∧ h = 4) ∨ (w = 4 ∧ h = 5) ∨ (w = 5 ∧ h = 4))

instance instDecNotPrime (w h : ℕ) : Decidable (NotPrime w h) := by
  unfold NotPrime
  infer_instance

/-- A shape that is not `NotPrime` (and has both sides ≥ 1) is in `primeShapes`. -/
theorem mem_primeShapes_of (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) (hp : ¬ NotPrime w h) :
    (w, h) ∈ primeShapes := by
  unfold NotPrime at hp
  have hp' : (w ≤ 3 ∧ h ≤ 3) ∨ (w = 4 ∧ h = 4) ∨ (w = 4 ∧ h = 5) ∨ (w = 5 ∧ h = 4) := by
    by_contra hn
    exact hp hn
  rcases hp' with ⟨hw3, hh3⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl <;>
      rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3) with rfl | rfl | rfl <;> decide
  · decide
  · decide
  · decide

/-! ### The three branches -/

/-- The free-vertex condition for a strip, in rows 0–2 of column `c`. -/
def FreeCol (c h sx sy tx ty : ℕ) : Prop :=
  (0 < h ∧ ¬ (sx = c ∧ sy = 0) ∧ ¬ (tx = c ∧ ty = 0)) ∨
  (1 < h ∧ ¬ (sx = c ∧ sy = 1) ∧ ¬ (tx = c ∧ ty = 1)) ∨
  (2 < h ∧ ¬ (sx = c ∧ sy = 2) ∧ ¬ (tx = c ∧ ty = 2))

instance instDecFreeCol (c h sx sy tx ty : ℕ) : Decidable (FreeCol c h sx sy tx ty) := by
  unfold FreeCol
  infer_instance

set_option maxRecDepth 100000 in
theorem branchA_small : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → 2 ≤ sx →
    AccA (w - 2) h (sx - 2) sy (tx - 2) ty ∧ FreeCol 2 h sx sy tx ty := by
  decide +kernel

/-- **Branch (A).** `s` at column ≥ 2: the problem with the two leftmost
columns removed is acceptable, and column 2 has a vertex that is neither
endpoint. -/
theorem branchA (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hA : 2 ≤ sx) :
    AccA (w - 2) h (sx - 2) sy (tx - 2) ty ∧ FreeCol 2 h sx sy tx ty := by
  have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
  by_cases hw6 : w < 6
  · exact branchA_small w (List.mem_range.mpr hw6) hw4 h (List.mem_range.mpr (by omega)) hnp
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
      hst hle hacc hA
  · unfold FreeCol
    rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3 ∨ 4 ≤ h) with hh | hh | hh | hh
    · subst hh
      rw [accA_h1 w sx sy tx ty (by omega)] at hacc
      unfold CCA EndsA at hacc
      exfalso
      omega
    · subst hh
      rw [accA_h2 w sx sy tx ty (by omega)] at hacc
      rw [accA_h2 (w - 2) (sx - 2) sy (tx - 2) ty (by omega)]
      unfold CCA F2A cornerA at hacc ⊢
      constructor
      · omega
      · omega
    · subst hh
      rw [accA_h3 w sx sy tx ty (by omega)] at hacc
      rw [accA_h3 (w - 2) (sx - 2) sy (tx - 2) ty (by omega)]
      unfold CCA G3 at hacc ⊢
      constructor
      · omega
      · omega
    · rw [accA_big w h sx sy tx ty (by omega) hh] at hacc
      rw [accA_big (w - 2) h (sx - 2) sy (tx - 2) ty (by omega) hh]
      unfold CCA at hacc ⊢
      constructor
      · omega
      · omega

set_option maxRecDepth 100000 in
theorem branchC_small : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → sx ≤ 1 → tx + 2 < w →
    AccA (w - 2) h sx sy tx ty ∧ FreeCol (w - 3) h sx sy tx ty := by
  decide +kernel

/-- **Branch (C).** `s` in column 0 or 1 and `t` at least three columns from
the right: the problem with the two rightmost columns removed is acceptable,
and column `w - 3` has a vertex that is neither endpoint. -/
theorem branchC (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hC1 : sx ≤ 1) (hC2 : tx + 2 < w) :
    AccA (w - 2) h sx sy tx ty ∧ FreeCol (w - 3) h sx sy tx ty := by
  have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
  by_cases hw6 : w < 6
  · exact branchC_small w (List.mem_range.mpr hw6) hw4 h (List.mem_range.mpr (by omega)) hnp
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
      hst hle hacc hC1 hC2
  · unfold FreeCol
    rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3 ∨ 4 ≤ h) with hh | hh | hh | hh
    · subst hh
      rw [accA_h1 w sx sy tx ty (by omega)] at hacc
      unfold CCA EndsA at hacc
      exfalso
      omega
    · subst hh
      rw [accA_h2 w sx sy tx ty (by omega)] at hacc
      rw [accA_h2 (w - 2) sx sy tx ty (by omega)]
      unfold CCA F2A cornerA at hacc ⊢
      constructor
      · omega
      · omega
    · subst hh
      rw [accA_h3 w sx sy tx ty (by omega)] at hacc
      rw [accA_h3 (w - 2) sx sy tx ty (by omega)]
      unfold CCA G3 at hacc ⊢
      constructor
      · omega
      · omega
    · rw [accA_big w h sx sy tx ty (by omega) hh] at hacc
      rw [accA_big (w - 2) h sx sy tx ty (by omega) hh]
      unfold CCA at hacc ⊢
      constructor
      · omega
      · omega

/-- The split row for branch (B): row 0 if `s` has colour 0; otherwise row 1,
unless `s–(1,1)` would be a forbidden edge of the 2-wide piece, then row 3. -/
def rChoice (sx sy h : ℕ) : ℕ :=
  if (sx + sy) % 2 = 0 then 0 else if sx = 0 ∧ sy = 1 ∧ 1 < h - 1 then 3 else 1

/-- What branch (B) needs of the split row `r`. -/
def BConcl (w h sx sy tx ty r : ℕ) : Prop :=
  r < h ∧ ¬ (sx = 1 ∧ sy = r) ∧ ¬ (0 = tx - 2 ∧ r = ty) ∧
    AccA 2 h sx sy 1 r ∧ AccA (w - 2) h 0 r (tx - 2) ty

instance instDecBConcl (w h sx sy tx ty r : ℕ) : Decidable (BConcl w h sx sy tx ty r) := by
  unfold BConcl
  infer_instance

set_option maxRecDepth 100000 in
theorem branchB_small : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → sx ≤ 1 → w ≤ tx + 2 →
    BConcl w h sx sy tx ty (rChoice sx sy h) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **Branch (B).** `s` in column 0 or 1 and `t` in one of the last two
columns: splitting after column 1 at row `rChoice` gives two acceptable
pieces, the left one `2 × h` from `s` to `(1, r)`, the right one `(w-2) × h`
from `(0, r)` to `t` shifted left by 2. -/
theorem branchB (w h sx sy tx ty : ℕ) (hs : sx < w ∧ sy < h) (ht : tx < w ∧ ty < h)
    (hst : ¬ (sx = tx ∧ sy = ty)) (hwh : h ≤ w) (hle : sx ≤ tx) (hnp : NotPrime w h)
    (hacc : AccA w h sx sy tx ty) (hB1 : sx ≤ 1) (hB2 : w ≤ tx + 2) :
    BConcl w h sx sy tx ty (rChoice sx sy h) := by
  have hw4 : 4 ≤ w := by unfold NotPrime at hnp; omega
  by_cases hw6 : w < 6
  · exact branchB_small w (List.mem_range.mpr hw6) hw4 h (List.mem_range.mpr (by omega)) hnp
      sx (List.mem_range.mpr hs.1) sy (List.mem_range.mpr hs.2)
      tx (List.mem_range.mpr ht.1) ty (List.mem_range.mpr ht.2)
      hst hle hacc hB1 hB2
  · -- Fix every parity up front: `omega` is incomplete on problems with many
    -- free `% 2` terms, so give it only known parities.
    have hw2 : (w - 2) % 2 = w % 2 := by omega
    have ht2 : (tx - 2 + ty) % 2 = (tx + ty) % 2 := by omega
    unfold BConcl
    rcases (by omega : h = 1 ∨ h = 2 ∨ h = 3 ∨ 4 ≤ h) with hh | hh | hh | hh
    · subst hh
      rw [accA_h1 w sx sy tx ty (by omega)] at hacc
      rw [accA_h1 2 sx sy 1 (rChoice sx sy 1) (by omega),
        accA_h1 (w - 2) 0 (rChoice sx sy 1) (tx - 2) ty (by omega)]
      unfold CCA EndsA at hacc ⊢
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hsp, htp] at hacc ⊢) <;> omega)
    · subst hh
      rw [accA_h2 w sx sy tx ty (by omega)] at hacc
      rw [accA_w2 2 sx sy 1 (rChoice sx sy 2) (by omega),
        accA_h2 (w - 2) 0 (rChoice sx sy 2) (tx - 2) ty (by omega)]
      unfold CCA F2A cornerA at hacc ⊢
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hsp, htp] at hacc ⊢) <;> omega)
    · subst hh
      rw [accA_h3 w sx sy tx ty (by omega)] at hacc
      rw [accA_w2 3 sx sy 1 (rChoice sx sy 3) (by omega),
        accA_h3 (w - 2) 0 (rChoice sx sy 3) (tx - 2) ty (by omega)]
      unfold CCA G3 at hacc
      unfold CCA F2A cornerA G3
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hsp, htp] at hacc ⊢) <;> omega)
    · rw [accA_big w h sx sy tx ty (by omega) hh] at hacc
      rw [accA_w2 h sx sy 1 (rChoice sx sy h) (by omega),
        accA_big (w - 2) h 0 (rChoice sx sy h) (tx - 2) ty (by omega) hh]
      unfold CCA at hacc
      unfold CCA F2A cornerA
      rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hwp | hwp <;>
      rcases (by omega : h % 2 = 0 ∨ h % 2 = 1) with hhp | hhp <;>
      rcases (by omega : (sx + sy) % 2 = 0 ∨ (sx + sy) % 2 = 1) with hsp | hsp <;>
      rcases (by omega : (tx + ty) % 2 = 0 ∨ (tx + ty) % 2 = 1) with htp | htp <;>
      (unfold rChoice; split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        (try simp [hw2, ht2, hwp, hhp, hsp, htp] at hacc ⊢) <;> omega)

end GridHam
