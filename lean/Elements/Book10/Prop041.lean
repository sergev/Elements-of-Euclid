import Elements.Book10.Prop040

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- If two lines incommensurable in square, with the sum of the squares on them medial,
the rectangle contained by them medial, and incommensurable with the sum of the squares,
are added together, the whole is irrational: let it be called the square root of two
medial areas (`SideTwoMedials`). -/
theorem proposition_41 {x y : Length} (_h : ¬ CommensurableInSquare x y)
    (hs : MedialArea ρ (sq x + sq y)) (hr : MedialArea ρ (rect x y))
    (hi : ¬ Commensurable (sq x + sq y) (rect x y)) : ¬ Rational ρ (x + y) := by
  -- the squares and twice the rectangle, both medial and incommensurable, applied to a
  -- rational line, make a binomial as breadth; so the square on the whole is irrational
  -- [Props. 2.4, 10.22, 10.36, 10.20], and the whole [Def. 10.4]
  have h₁ : ¬ Commensurable (sq x + sq y) ((2 : ℕ+) • rect x y) :=
    fun h' => hi (proposition_12 Area.divisible h' (twice_commensurable _).symm)
  have h₂ := medial_add_medial hs hr.twice h₁
  rw [← sq_add] at h₂
  exact fun h' => h₂ h'.sq_rational

/--
10.41, lemma: if a line is cut unequally at `C` and at `D`, `A C` greater than `D B`, and
`D` between `A` and `C`, the squares on `A C` and `C B` are greater than the squares on
`A D` and `D B`. Here `x`, `y` are the pieces at `C`, and `x'`, `y'` at `D`.
-/
theorem proposition_41_lemma {x y x' y' : Length} (hl : x + y = x' + y') (hxx : x' < x)
    (hyx : y' < x) : sq x' + sq y' < sq x + sq y := by
  -- of sums equal, the one with the lesser part has the greater other part
  have key : ∀ {M : Type} [Magnitude M] {a b a' b' : M}, a + b = a' + b' → b <
    b' → a' < a :=
    fun {M} _ {a b a' b'} h hb => lt_of_not_ge fun h' =>
      absurd h (ne_of_lt (add_lt_add_of_le_of_lt h' hb))
  -- `A D` is greater than `C B`, `D C` being taken from both
  have hxy : y < x' := key (show x' + y' = y + x by rw [← hl, add_comm]) hyx
  -- let the line be cut in half at `E`, `e` the half; `A C` is greater than it
  obtain ⟨e, he⟩ := Length.part (x + y) 2
  rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult] at he
  have hex : e < x := lt_of_not_ge fun h' =>
    absurd (hl.symm.trans he) (ne_of_lt (add_lt_add (lt_of_lt_of_le hxx h')
      (lt_of_lt_of_le hyx h')))
  obtain ⟨t, ht⟩ := remainder e x hex
  have hyt : y + t = e := add_right_cancel (b := e) (by
    rw [add_assoc, add_comm t e, ht, add_comm y x, he])
  -- the rectangle contained by `A C`, `C B`, with the square on `E C`, is the square on
  -- `E B` [Prop. 2.5]
  have h₁ := rect_add_sq ht hyt
  -- and so for `A D`, `D B`, with the square on `D E`, less than that on `E C`: so the
  -- rectangle contained by `A C`, `C B` is less than that contained by `A D`, `D B`
  have h₂ : rect x y < rect x' y' := by
    rcases lt_trichotomy e x' with hlt | rfl | hlt
    · obtain ⟨s, hs⟩ := remainder e x' hlt
      have hys : y' + s = e := add_right_cancel (b := e) (by
        rw [add_assoc, add_comm s e, hs, add_comm y' x', ← hl, he])
      have hst : s < t := lt_of_add_lt_add_left (a := e) (by rw [hs, ht]; exact hxx)
      exact key ((rect_add_sq hs hys).trans h₁.symm) (sq_lt_sq.mpr hst)
    · have : y' = e := add_left_cancel (a := e) (by rw [← hl, he])
      subst this
      rw [← sq_eq_rect, ← h₁]
      exact Magnitude.lt_add _ _
    · obtain ⟨s, hs⟩ := remainder x' e hlt
      have hys : e + s = y' := add_left_cancel (a := x') (by
        rw [← add_assoc, add_comm x' e, add_assoc, hs, ← hl, he])
      have hst : s < t := lt_of_add_lt_add_left (a := e) (by rw [hys, ht]; exact hyx)
      have h₃ := rect_add_sq hys hs
      rw [rect_comm] at h₃
      exact key (h₃.trans h₁.symm) (sq_lt_sq.mpr hst)
  -- so twice the rectangle, and the remaining squares are greater [Prop. 2.4]
  have h₃ :
      sq x + sq y + (2 : ℕ+) • rect x y = sq x' + sq y' + (2 : ℕ+) • rect x' y' := by
    rw [← sq_add, ← sq_add, hl]
  exact key h₃ (mult_lt_mult 2 h₂)

end Elements.Book10
