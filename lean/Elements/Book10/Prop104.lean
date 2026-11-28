import Elements.Book10.Prop103

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- A line commensurable in length with an apotome of a medial is an apotome of a medial,
and of the same order. The mirror of 10.67. -/
theorem proposition_104 {l l' : Length} (h : Commensurable l l') :
    (FirstApotomeOfMedial ρ l → FirstApotomeOfMedial ρ l') ∧
      (SecondApotomeOfMedial ρ l → SecondApotomeOfMedial ρ l') :=
  ⟨Transfers.diff firstBimedialTerms_transfers h,
    Transfers.diff secondBimedialTerms_transfers h⟩

end Elements.Book10
