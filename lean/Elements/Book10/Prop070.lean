import Elements.Book10.Prop069

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable in length with the square root of two medial areas is the square
root of two medial areas. -/
theorem proposition_70 {l l' : Length} (hl : SideTwoMedials ρ l)
    (h : Commensurable l l') :
    SideTwoMedials ρ l' :=
  -- similarly, the squares and the rectangle are medial, and the squares incommensurable
  -- with the rectangle [Props. 10.23 corr., 10.13]
  Transfers.sum (fun ⟨h₁, h₂, h₃, h₄, h₅⟩ hp hx _ => by
    have hs := squares_comm_of_terms hp hx
    have hr := rect_comm_of_terms hp hx
    refine ⟨notInSquare_of_terms hp h₁, proposition_23_corollary h₂ hs.symm,
      proposition_23_corollary h₃ hr.symm, fun h' => h₄ ?_, lt_of_proportion hp h₅⟩
    exact proposition_12 Area.divisible
      (proposition_12 Area.divisible hs h'.symm) hr) h hl

end Elements.Book10
