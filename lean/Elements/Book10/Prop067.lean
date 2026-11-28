import Elements.Book10.Prop066

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- For terms in the same ratio, `x` commensurable with `x'`, the rectangles are
commensurable: as the square on `x` is to the rectangle, so the square on `x'` to the
other [Prop. 10.21 lem.]; alternately [Prop. 5.16], and the squares on `x`, `x'` are
commensurable [Props. 10.9 corr., 10.11]. -/
theorem rect_comm_of_terms {x y x' y' : Length} (hp : Proportion x y x' y')
    (hx : Commensurable x x') : Commensurable (rect x y) (rect x' y') := by
  have h₁ := Elements.Book5.proposition_11 (proposition_21_lemma x y).1.symm
    (Elements.Book5.proposition_11 hp (proposition_21_lemma x' y').1)
  exact (proposition_11 (Elements.Book5.proposition_16 h₁) Area.divisible
    Area.divisible).1 (proposition_9_corollary hx)

theorem medial_of_comm {a a' : Length} (ha : Medial ρ a) (h : Commensurable a a') :
    Medial ρ a' :=
  proposition_23 ha (proposition_9_corollary h.symm)

/-- The terms of a first and of a second bimedial carry over: the terms are medial [Prop.
10.23], commensurable in square only [Prop. 10.11], and the rectangles commensurable, both
rational, or both medial [Props. 10.23, 10.37, 10.38]. -/
theorem firstBimedialTerms_transfers : Transfers (FirstBimedialTerms ρ) :=
  fun ⟨h₁, h₂, h₃, h₄, h₅⟩ hp hx hy =>
    ⟨medial_of_comm h₁ hx, medial_of_comm h₂ hy, h₃.of_proportion hp,
      h₄.of_comm (rect_comm_of_terms hp hx).symm, lt_of_proportion hp h₅⟩

theorem secondBimedialTerms_transfers : Transfers (SecondBimedialTerms ρ) :=
  fun ⟨h₁, h₂, h₃, h₄, h₅⟩ hp hx hy =>
    ⟨medial_of_comm h₁ hx, medial_of_comm h₂ hy, h₃.of_proportion hp,
      proposition_23_corollary h₄ (rect_comm_of_terms hp hx).symm, lt_of_proportion hp h₅⟩

/-- A line commensurable in length with a bimedial is a bimedial, and of the same order:
first, or second. -/
theorem proposition_67 {l l' : Length} (h : Commensurable l l') :
    (FirstBimedial ρ l → FirstBimedial ρ l') ∧
      (SecondBimedial ρ l → SecondBimedial ρ l') :=
  ⟨Transfers.sum firstBimedialTerms_transfers h,
    Transfers.sum secondBimedialTerms_transfers h⟩

end Elements.Book10
