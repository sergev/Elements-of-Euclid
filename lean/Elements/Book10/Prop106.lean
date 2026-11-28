import Elements.Book10.Prop105

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable in length with that which with a rational area makes a medial
whole is itself such a line. The mirror of 10.69. -/
theorem proposition_106 {l l' : Length} (hl : MedialWholeWithRational ρ l)
    (h : Commensurable l l') : MedialWholeWithRational ρ l' :=
  Transfers.diff rationalMedialTerms_transfers h hl

end Elements.Book10
