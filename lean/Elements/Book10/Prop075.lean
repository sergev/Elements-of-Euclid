import Elements.Book10.Prop074

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/--
If a medial area `T`, incommensurable with a medial area `S`, is taken from it, the
remainder `U` is irrational: applied to a rational line, `S`, `T` make rational breadths
incommensurable with it [Prop. 10.22] and with one another [Props. 6.1, 10.11]; the
remaining breadth is an apotome [Prop. 10.73], and the rectangle contained by a rational
line and an apotome is irrational [Prop. 10.20]. 10.75's and 10.78's argument, the mirror
of `medial_add_medial`.
-/
theorem medial_sub_medial {S T U : Area} (hS : MedialArea ρ S) (hT : MedialArea ρ T)
    (h : ¬ Commensurable S T) (hU : T + U = S) : ¬ RationalArea ρ U := by
  obtain ⟨a, ha⟩ := Area.apply ρ S
  obtain ⟨b, hb⟩ := Area.apply ρ T
  obtain ⟨har, hbr, hab⟩ := medial_breadths hS hT h ha hb
  have hba : b < a := rect_lt_rect.mp (by rw [ha, hb, ← hU]; exact lt_add _ _)
  obtain ⟨c, hc⟩ := remainder b a hba
  have hcU : rect ρ c = U := add_left_cancel (a := T)
    (by rw [hU, ← hb, ← rect_add, hc, ha])
  have h₁ := proposition_73 har hbr hab ((add_comm c b).trans hc)
  rw [← hcU]
  exact fun h' => h₁ (proposition_20 (Rational.self ρ) h' rfl).1

/-- If a medial line `y`, commensurable in square only with the whole `x` and containing a
medial area with it, is taken from the medial `x`, the remainder `l` is irrational: let it
be called a second apotome of a medial (`SecondApotomeOfMedial`). The mirror of 10.38. -/
theorem proposition_75 {l x y : Length} (hx : Medial ρ x) (_hy : Medial ρ y)
    (h : InSquareOnly x y) (hr : MedialArea ρ (rect x y)) (hl : l + y = x) :
    ¬ Rational ρ l := by
  -- the squares are medial, and twice the rectangle, and they are incommensurable: twice
  -- the rectangle taken from the squares leaves the square on `l` [Prop. 2.7], irrational
  have h₁ : MedialArea ρ (sq x + sq y) :=
    proposition_23_corollary hx (proposition_15.1 h.1).1
  have h₂ := medial_sub_medial h₁ hr.twice h.squares_twice_rect (sq_add_sq_of_sub hl).symm
  exact fun h' => h₂ h'.sq_rational

end Elements.Book10
