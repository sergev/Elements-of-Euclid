import Elements.Book10.Prop104

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable in length with a minor line is a minor line. The mirror of
10.68. -/
theorem proposition_105 {l l' : Length} (hl : Minor ρ l) (h : Commensurable l l') :
    Minor ρ l' :=
  Transfers.diff majorTerms_transfers h hl

end Elements.Book10
