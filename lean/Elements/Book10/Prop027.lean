import Elements.Book10.Prop026

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If four lines are proportional, and the first two are commensurable in square only,
so are the last two [Props. 6.22, 10.11]. -/
theorem InSquareOnly.of_proportion {a b c d : Length} (h : Proportion a b c d)
    (hab : InSquareOnly a b) : InSquareOnly c d :=
  ⟨(proposition_11 (proportion_sq.mp h) Area.divisible Area.divisible).1 hab.1,
    (proposition_11 h Length.divisible Length.divisible).2 hab.2⟩

/-- Rational lines commensurable in square only, `ρ` and another [Prop. 10.10]. -/
theorem exists_inSquareOnly (ρ : Length) :
    ∃ b, Rational ρ b ∧ InSquareOnly ρ b := by
  obtain ⟨b, -, hb, -⟩ := proposition_10 ρ
  exact ⟨b, Or.inr hb.1.symm, hb⟩

/-- To find two medial lines commensurable in square only, containing a rational area. -/
theorem proposition_27 :
    ∃ c d, Medial ρ c ∧ Medial ρ d ∧ InSquareOnly c d ∧ RationalArea ρ (rect c d) := by
  -- let the rational lines `a`, `b`, commensurable in square only, be laid down
  obtain ⟨b, hb, hab⟩ := exists_inSquareOnly ρ
  have ha := Rational.self ρ
  -- the mean proportional `c` [Prop. 6.13], and `d` with `a ∶ b ∷ c ∶ d` [Prop. 6.12]
  obtain ⟨c, hc⟩ := Length.mean ρ b
  obtain ⟨d, hd⟩ := Length.fourth' ρ b c
  -- the rectangle contained by `a`, `b`, the square on `c` [Prop. 6.17], is medial, and
  -- `c` is medial [Prop. 10.21]
  have hcm : Medial ρ c := ⟨ρ, b, ha, hb, hab, (rect_eq_sq_of_proportion hc).symm⟩
  -- `c`, `d` are commensurable in square only [Prop. 10.11], and `d` is medial [Prop.
  -- 10.23]
  have hcd := hab.of_proportion hd
  have hdm := proposition_23 hcm hcd.1.symm
  -- alternately, as `a` is to `c`, so `b` to `d` [Prop. 5.16]; and as `a` to `c`, so `c`
  -- to `b`: so as `c` to `b`, so `b` to `d` [Prop. 5.11], and the rectangle contained by
  -- `c`, `d` is the square on `b` [Prop. 6.17], rational
  have h₁ := Elements.Book5.proposition_11 hc.symm (Elements.Book5.proposition_16 hd)
  exact ⟨c, d, hcm, hdm, hcd, rect_eq_sq_of_proportion h₁ ▸ hb.sq_rational⟩

end Elements.Book10
