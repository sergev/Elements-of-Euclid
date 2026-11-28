import Elements.Book10.Prop043

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- The squares on unequal lines exceed twice the rectangle contained by them, by the
square on their difference [Prop. 2.7]: the lemma after 10.59, which Euclid cites in
10.44. -/
theorem twice_rect_lt_squares {x y : Length} (h : y < x) :
    (2 : ℕ+) • rect x y < sq x + sq y := by
  obtain ⟨l, hl⟩ := remainder y x h
  rw [sq_add_sq_of_sub ((add_comm l y).trans hl)]
  exact lt_add _ _

/-- Two medial areas incommensurable with one another, applied to a rational line, make as
breadths rational lines commensurable in square only [Props. 10.22, 6.1, 10.11]. -/
theorem medial_breadths {S T : Area} {a b : Length} (hS : MedialArea ρ S)
    (hT : MedialArea ρ T) (h : ¬ Commensurable S T) (ha : rect ρ a = S)
      (hb : rect ρ b = T) :
    Rational ρ a ∧ Rational ρ b ∧ InSquareOnly a b := by
  obtain ⟨har, -⟩ := proposition_22' hS (Rational.self ρ) ha
  obtain ⟨hbr, -⟩ := proposition_22' hT (Rational.self ρ) hb
  have h₁ := rect_proportion' a b ρ
  rw [ha, hb] at h₁
  exact ⟨har, hbr, har.inSquare_of hbr,
    (proposition_11 h₁ Area.divisible Length.divisible).2 h⟩

/--
If two medial areas `S`, `A`, incommensurable, the first greater, make the same sum as two
others `S'`, `A'` so, the first are the others: applied to a rational line, each pair
makes a binomial as breadth, divided at the point between them [Prop. 10.36]; the binomial
is the same, and it is divided at one point only [Prop. 10.42]. The argument of 10.44 and
10.47.
-/
theorem medial_add_medial_eq {S S' A A' : Area} (hS : MedialArea ρ S)
    (hS' : MedialArea ρ S') (hA : MedialArea ρ A) (hA' : MedialArea ρ A')
    (hi : ¬ Commensurable S A) (hi' : ¬ Commensurable S' A') (hlt : A < S)
      (hlt' : A' < S')
    (h : S + A = S' + A') : S = S' := by
  -- let `S`, `A` be applied to the rational line, making `a`, `b` as breadths, and `S'`,
  -- `A'`, making `a'`, `b'` [Prop. 1.44]
  obtain ⟨a, ha⟩ := Area.apply ρ S
  obtain ⟨b, hb⟩ := Area.apply ρ A
  obtain ⟨a', ha'⟩ := Area.apply ρ S'
  obtain ⟨b', hb'⟩ := Area.apply ρ A'
  obtain ⟨har, hbr, hab⟩ := medial_breadths hS hA hi ha hb
  obtain ⟨har', hbr', hab'⟩ := medial_breadths hS' hA' hi' ha' hb'
  -- the breadths of the greater areas are the greater [Prop. 6.1]
  have hba : b < a := rect_lt_rect.mp (by rw [ha, hb]; exact hlt)
  have hba' : b' < a' := rect_lt_rect.mp (by rw [ha', hb']; exact hlt')
  -- the whole breadths are the same, the breadth of the whole area
  have he : a + b = a' + b' := rect_inj (by rw [rect_add, rect_add, ha, hb, ha', hb', h])
  -- so the binomial is divided at the same point [Prop. 10.42]
  obtain ⟨rfl, -⟩ := proposition_42 ⟨har, hbr, hab, hba⟩ ⟨har', hbr', hab', hba'⟩ he
  exact ha.symm.trans ha'

/-- A second bimedial can be divided into its terms at one point only. -/
theorem proposition_44 {x y x' y' : Length} (h : SecondBimedialTerms ρ x y)
    (h' : SecondBimedialTerms ρ x' y') (he : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨hx, -, hxy, hr, hyx⟩ := h
  obtain ⟨hx', -, hxy', hr', hyx'⟩ := h'
  -- the squares are medial, twice the rectangles medial, and incommensurable with them
  -- [Props. 10.21 lem., 10.11, 10.15, 10.6, 10.13]; the squares exceed twice the
  -- rectangles [Prop. 10.59 lem.]
  have h₁ :
      sq x + sq y + (2 : ℕ+) • rect x y = sq x' + sq y' + (2 : ℕ+) • rect x' y' := by
    rw [← sq_add, ← sq_add, he]
  have h₂ := medial_add_medial_eq (proposition_23_corollary hx (proposition_15.1 hxy.1).1)
    (proposition_23_corollary hx' (proposition_15.1 hxy'.1).1) hr.twice hr'.twice
    hxy.squares_twice_rect hxy'.squares_twice_rect (twice_rect_lt_squares hyx)
    (twice_rect_lt_squares hyx') h₁
  exact eq_of_squares_eq hyx hyx' he h₂

end Elements.Book10
