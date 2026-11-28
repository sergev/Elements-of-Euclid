import Elements.Book10.Prop106

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable in length with that which with a medial area makes a medial
whole is itself such a line. The mirror of 10.70. -/
theorem proposition_107 {l l' : Length} (hl : MedialWholeWithMedial ρ l)
    (h : Commensurable l l') : MedialWholeWithMedial ρ l' :=
  Transfers.diff twoMedialTerms_transfers h hl

end Elements.Book10
