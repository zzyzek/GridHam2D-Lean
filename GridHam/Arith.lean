import GridHam.Forbidden

/-!
# Arithmetic normal form of `IsAcceptable`

`AccA w h sx sy tx ty` restates `IsAcceptable w h (sx, sy) (tx, ty)` using only
`=`, `<`, `≤`, `% 2`, `∧`, `∨`, `¬` on natural numbers: no `if`, no `let`, no
pairs, and no product `w * h` (odd area is `w % 2 = 1 ∧ h % 2 = 1`). That is the
shape `omega` can decide, which is what the reduction lemmas need.

`acc_iff` proves the two agree, so any transcription slip here fails to
compile rather than silently changing the theorem. (It was also checked in
Python against `is_acceptable` on all 422,500 instances up to 12×12.)
-/

namespace GridHam

theorem mul_mod_two_eq_one (w h : ℕ) : (w * h) % 2 = 1 ↔ w % 2 = 1 ∧ h % 2 = 1 := by
  rw [Nat.mul_mod]
  rcases (by omega : w % 2 = 0 ∨ w % 2 = 1) with hw | hw <;>
    rcases (by omega : h % 2 = 0 ∨ h % 2 = 1) with hh | hh <;>
    simp [hw, hh]

/-- The case-3 obstruction, with `m` the even dimension, `c0 c1` the
endpoints' coordinates along it, `oc` the start's other coordinate, and
`ps pt` the endpoint colours. -/
def G3 (m c0 c1 oc ps pt : ℕ) : Prop :=
  m % 2 = 0 ∧ ps ≠ pt ∧
  ((oc = 1 ∧ c0 ≠ c1) ∨ (oc ≠ 1 ∧ (c0 + 1 < c1 ∨ c1 + 1 < c0))) ∧
  ((c1 < c0 ∧ ps ≠ 1) ∨ (¬ c1 < c0 ∧ ps ≠ 0))

def cornerA (w h x y : ℕ) : Prop := (x = 0 ∨ x = w - 1) ∧ (y = 0 ∨ y = h - 1)

def F1A (w h sx sy tx ty : ℕ) : Prop :=
  (w = 1 ∧ ¬ ((sx = 0 ∧ sy = 0 ∧ tx = 0 ∧ ty = h - 1) ∨ (sx = 0 ∧ sy = h - 1 ∧ tx = 0 ∧ ty = 0))) ∨
  (w ≠ 1 ∧ ¬ ((sx = 0 ∧ sy = 0 ∧ tx = w - 1 ∧ ty = 0) ∨ (sx = w - 1 ∧ sy = 0 ∧ tx = 0 ∧ ty = 0)))

def F2A (w h sx sy tx ty : ℕ) : Prop :=
  ¬ cornerA w h sx sy ∧ ¬ cornerA w h tx ty ∧ ((w = 2 ∧ sy = ty) ∨ (h = 2 ∧ sx = tx))

def F3A (w h sx sy tx ty : ℕ) : Prop :=
  (w = 3 ∧ G3 h sy ty sx ((sx + sy) % 2) ((tx + ty) % 2)) ∨
  (w ≠ 3 ∧ G3 w sx tx sy ((sx + sy) % 2) ((tx + ty) % 2))

def ForbA (w h sx sy tx ty : ℕ) : Prop :=
  ((w = 1 ∨ h = 1) ∧ F1A w h sx sy tx ty) ∨
  (¬ (w = 1 ∨ h = 1) ∧ (w = 2 ∨ h = 2) ∧ F2A w h sx sy tx ty) ∨
  (¬ (w = 1 ∨ h = 1) ∧ ¬ (w = 2 ∨ h = 2) ∧ (w = 3 ∨ h = 3) ∧ F3A w h sx sy tx ty)

def AccA (w h sx sy tx ty : ℕ) : Prop :=
  ((w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
    (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)) ∧
  ¬ ForbA w h sx sy tx ty

theorem colorCompatible_iff (w h sx sy tx ty : ℕ) :
    ColorCompatible w h (sx, sy) (tx, ty) ↔
      ((w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
        (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)) := by
  unfold ColorCompatible parity
  split_ifs with hodd
  · rw [mul_mod_two_eq_one] at hodd
    try dsimp only
    constructor <;> intro h <;> omega
  · rw [mul_mod_two_eq_one] at hodd
    try dsimp only
    constructor <;> intro h <;> omega

theorem forbiddenCase1_iff (w h sx sy tx ty : ℕ) :
    ForbiddenCase1 w h (sx, sy) (tx, ty) ↔ F1A w h sx sy tx ty := by
  unfold ForbiddenCase1 F1A
  dsimp only
  split_ifs <;> simp only [Prod.mk.injEq] <;> constructor <;> intro h <;> omega

theorem isCorner_iff (w h x y : ℕ) : IsCorner w h (x, y) ↔ cornerA w h x y := by
  unfold IsCorner cornerA
  simp only [Prod.mk.injEq]
  constructor <;> intro h <;> omega

theorem forbiddenCase2_iff (w h sx sy tx ty : ℕ) :
    ForbiddenCase2 w h (sx, sy) (tx, ty) ↔ F2A w h sx sy tx ty := by
  unfold ForbiddenCase2 F2A
  rw [isCorner_iff, isCorner_iff]

theorem forbiddenCase3_iff (w h sx sy tx ty : ℕ) :
    ForbiddenCase3 w h (sx, sy) (tx, ty) ↔ F3A w h sx sy tx ty := by
  unfold ForbiddenCase3 F3A G3 parity
  dsimp only
  split_ifs <;> constructor <;> intro h <;> omega

theorem isForbidden_iff (w h sx sy tx ty : ℕ) :
    IsForbidden w h (sx, sy) (tx, ty) ↔ ForbA w h sx sy tx ty := by
  unfold IsForbidden ForbA
  rw [← forbiddenCase1_iff, ← forbiddenCase2_iff, ← forbiddenCase3_iff]
  split_ifs with h1 h2 h3
  · constructor
    · intro hf
      exact Or.inl ⟨h1, hf⟩
    · rintro (⟨_, hf⟩ | ⟨hn, _⟩ | ⟨hn, _⟩)
      · exact hf
      · exact absurd h1 hn
      · exact absurd h1 hn
  · constructor
    · intro hf
      exact Or.inr (Or.inl ⟨h1, h2, hf⟩)
    · rintro (⟨hy, _⟩ | ⟨_, _, hf⟩ | ⟨_, hn, _⟩)
      · exact absurd hy h1
      · exact hf
      · exact absurd h2 hn
  · constructor
    · intro hf
      exact Or.inr (Or.inr ⟨h1, h2, h3, hf⟩)
    · rintro (⟨hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, _, _, hf⟩)
      · exact absurd hy h1
      · exact absurd hy h2
      · exact hf
  · constructor
    · intro hf
      exact hf.elim
    · rintro (⟨hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, _, hy, _⟩)
      · exact absurd hy h1
      · exact absurd hy h2
      · exact absurd hy h3

/-- **`IsAcceptable` in arithmetic form.** -/
theorem acc_iff (w h : ℕ) (s t : Coord) :
    IsAcceptable w h s t ↔ AccA w h s.1 s.2 t.1 t.2 := by
  obtain ⟨sx, sy⟩ := s
  obtain ⟨tx, ty⟩ := t
  show IsAcceptable w h (sx, sy) (tx, ty) ↔ AccA w h sx sy tx ty
  unfold IsAcceptable AccA
  rw [colorCompatible_iff, isForbidden_iff]

end GridHam
