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

/-- A line commensurable in length with a bimedial is a bimedial, and of the same order:
first, or second. -/
theorem proposition_67 {l l' : Length} (h : Commensurable l l') :
    (FirstBimedial ρ l → FirstBimedial ρ l') ∧
      (SecondBimedial ρ l → SecondBimedial ρ l') := by
  -- the terms are medial [Prop. 10.23], commensurable in square only [Prop. 10.11], and
  -- the rectangles commensurable: both rational, or both medial [Props. 10.23, 10.37,
  -- 10.38]
  have hm : ∀ {a a' : Length}, Medial ρ a → Commensurable a a' → Medial ρ a' :=
    fun ha h => proposition_23 ha (proposition_9_corollary h.symm)
  exact ⟨Transfers.sum (fun ⟨h₁, h₂, h₃, h₄, h₅⟩ hp hx hy =>
      ⟨hm h₁ hx, hm h₂ hy, h₃.of_proportion hp, h₄.of_comm
        (rect_comm_of_terms hp hx).symm,
        lt_of_proportion hp h₅⟩) h,
    Transfers.sum (fun ⟨h₁, h₂, h₃, h₄, h₅⟩ hp hx hy =>
      ⟨hm h₁ hx, hm h₂ hy, h₃.of_proportion hp,
        proposition_23_corollary h₄ (rect_comm_of_terms hp hx).symm,
        lt_of_proportion hp h₅⟩) h⟩

end Elements.Book10
