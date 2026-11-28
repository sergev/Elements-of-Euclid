import Elements.Book9.Prop14

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- Prop. 2.3 for numbers: `(x + y) * x = x * x + y * x` [Prop. 7.5]. -/
theorem sum_mul_left (x y : ℕ) : (x + y) * x = x * x + y * x :=
  (Elements.Book7.proposition_5' x y x).symm

/-- Prop. 2.4 for numbers: `(x + y) * (x + y)` is `x * x`, `y * y`, and twice `y * x`
[Props. 7.5, 7.16]. -/
theorem sum_mul_self {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    (x + y) * (x + y) = x * x + y * y + y * x + y * x := by
  rw [← Elements.Book7.proposition_5' x y (x + y),
    Elements.Book7.proposition_16 (Nat.add_pos_left hx y) hx,
    Elements.Book7.proposition_16 (Nat.add_pos_left hx y) hy, sum_mul_left,
    ← Elements.Book7.proposition_5' x y y, Elements.Book7.proposition_16 hy hx]
  omega

/-- If `s` added to `b` twice is prime to `b`, so is `s` added once, and `s` alone: a
number measuring `s + b` (or `s`) and `b` measures `s + b + b` [Prop. 7.28]. -/
theorem primeTo_of_add {s b : ℕ} (h : PrimeTo (s + b) b) : PrimeTo s b := by
  have h' : PrimeTo (b + s) b := by rwa [Nat.add_comm]
  exact (Elements.Book7.proposition_28' h').symm

/--
If three continuously proportional numbers `a`, `b`, `c` are the least of those having
the same ratio, any two added together are prime to the third.

Euclid cites Props. 2.3 and 2.4, of lines, for the numbers; here they are by Book 7's
multiplication (7.5, 7.16). His last step, "by separation", takes the sum of the squares
on `x`, `y` and twice `y * x` prime to `y * x`, to the sum with `y * x` once, and then
none: a number measuring `y * x` and the lesser sum measures the greater.
-/
theorem proposition_15 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcon : a ∶ b ∷ b ∶ c) (hl : LeastSeq (three a b c)) :
    PrimeTo (a + b) c ∧ PrimeTo (b + c) a ∧ PrimeTo (a + c) b := by
  -- the least numbers `x`, `y` in their ratio: `x` multiplying itself makes `a`, and `y`
  -- makes `b`; `y` multiplying itself makes `c` [Prop. 8.2]
  obtain ⟨x, y, hx, hy, hxy, h⟩ :=
    eq_powers (three_pos ha hb hc) (three_continued ha hb hcon) hl
  have hA : a = x * x := (congrFun h 0).trans (by show 1 * x * x = _; rw [Nat.one_mul])
  have hB : b = y * x := (congrFun h 1).trans (by show 1 * y * x = _; rw [Nat.one_mul])
  have hC : c = y * y := (congrFun h 2).trans (by show 1 * y * y = _; rw [Nat.one_mul])
  subst hA hB hC
  -- `x`, `y` are prime to one another [Prop. 7.22], and `x + y` to each [Prop. 7.28]
  have hp := Elements.Book7.proposition_22 hx hy hxy
  obtain ⟨hsx, hsy⟩ := Elements.Book7.proposition_28 hp
  have hs : 0 < x + y := Nat.add_pos_left hx y
  refine ⟨?_, ?_, ?_⟩
  · -- `(x + y) * x` is prime to `y` [Prop. 7.24], and to `y * y` [Prop. 7.25]; and it is
    -- `x * x` and `y * x` [Prop. 2.3]
    have h₁ := Elements.Book7.proposition_24 hx hs hy hp hsy
    have h₂ := Elements.Book7.proposition_25 hy (Nat.mul_pos hs hx) h₁
    rwa [sum_mul_left] at h₂
  · -- similarly, `(x + y) * y` is prime to `x * x`, and it is `y * x` and `y * y`
    have h₁ := Elements.Book7.proposition_24 hy hs hx hp.symm hsx
    have h₂ := Elements.Book7.proposition_25 hx (Nat.mul_pos hs hy) h₁
    rwa [← Elements.Book7.proposition_5' x y y, Elements.Book7.proposition_16 hy hx] at h₂
  · -- `x + y` is prime to `x` and `y`, so `(x + y) * (x + y)` is prime to `y * x`
    -- [Props. 7.25, 7.24]
    have h₁ := Elements.Book7.proposition_25 hs hx hsx
    have h₂ := Elements.Book7.proposition_25 hs hy hsy
    have h₃ := Elements.Book7.proposition_24 hx hy (Nat.mul_pos hs hs) h₁ h₂
    -- and it is `x * x`, `y * y` and twice `y * x` [Prop. 2.4]; by separation, `x * x`
    -- and `y * y` are prime to `y * x` [Prop. 7.28] -- Missed by Euclid.
    rw [sum_mul_self hx hy] at h₃
    exact primeTo_of_add (primeTo_of_add h₃)

end Elements.Book9
