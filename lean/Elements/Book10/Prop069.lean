import Elements.Book10.Prop068

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable in length with the square root of a rational plus a medial area
is the square root of a rational plus a medial area. -/
theorem proposition_69 {l l' : Length} (hl : SideRationalMedial ρ l)
    (h : Commensurable l l') : SideRationalMedial ρ l' :=
  -- similarly, the squares are medial, the rectangle rational [Props. 10.23 corr., Def.
  -- 10.4]
  Transfers.sum (fun ⟨h₁, h₂, h₃, h₄⟩ hp hx _ =>
    ⟨notInSquare_of_terms hp h₁, proposition_23_corollary h₂
      (squares_comm_of_terms hp hx).symm,
      h₃.of_comm (rect_comm_of_terms hp hx).symm, lt_of_proportion hp h₄⟩) h hl

end Elements.Book10
