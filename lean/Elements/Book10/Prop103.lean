import Elements.Book10.Prop102

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The construction of 10.103–10.107: `l` with `y` attached, `l + y = x`, commensurable
in length with `l'`; as `l` is to `l'`, so `y` to `y'` [Prop. 6.12], and `x'` is `l'` with
`y'` attached: as `l` is to `l'`, so the wholes `x` to `x'` [Prop. 5.12]. The terms are
commensurable, each with each [Prop. 10.11], and `x ∶ y ∷ x' ∶ y'` [Props. 5.11, 5.16]. -/
theorem comm_terms_sub {l l' x y : Length} (h : Commensurable l l') (hl : l + y = x) :
    ∃ x' y', l' + y' = x' ∧ Proportion x y x' y' ∧ Commensurable x x' ∧
      Commensurable y y' := by
  obtain ⟨y', hy'⟩ := Length.fourth' l l' y
  have h₁ := proportion_add hy'
  rw [hl] at h₁
  have h₂ := (proposition_11 h₁ Length.divisible Length.divisible).1 h
  have h₃ := (proposition_11 hy' Length.divisible Length.divisible).1 h
  exact ⟨l' + y', y', rfl, Elements.Book5.proposition_16
    (Elements.Book5.proposition_11 h₁.symm hy'), h₂, h₃⟩

/-- A line commensurable in length with a difference of terms of a kind that carries over
is a difference of terms of the kind. -/
theorem Transfers.diff {P : Length → Length → Prop} (hP : Transfers P) {l l' : Length}
    (h : Commensurable l l') (hl : ∃ x y, P x y ∧ l + y = x) : ∃ x y, P x y ∧
      l' + y = x := by
  obtain ⟨x, y, hxy, hl⟩ := hl
  obtain ⟨x', y', hl', hp, hx, hy⟩ := comm_terms_sub h hl
  exact ⟨x', y', hP hxy hp hx hy, hl'⟩

/-- A line commensurable in length with an apotome is an apotome, and of the same order.
The mirror of 10.66. -/
theorem proposition_103 {l l' : Length} (hl : Apotome ρ l) (h : Commensurable l l') :
    Apotome ρ l' ∧ ∀ r,
      (FirstApotome ρ r l → FirstApotome ρ r l') ∧
      (SecondApotome ρ r l → SecondApotome ρ r l') ∧
      (ThirdApotome ρ r l → ThirdApotome ρ r l') ∧
      (FourthApotome ρ r l → FourthApotome ρ r l') ∧
      (FifthApotome ρ r l → FifthApotome ρ r l') ∧
      (SixthApotome ρ r l → SixthApotome ρ r l') :=
  ⟨Transfers.diff binomialTerms_transfers h hl, fun _ =>
    ⟨Transfers.diff firstTerms_transfers h, Transfers.diff secondTerms_transfers h,
      Transfers.diff thirdTerms_transfers h, Transfers.diff fourthTerms_transfers h,
      Transfers.diff fifthTerms_transfers h, Transfers.diff sixthTerms_transfers h⟩⟩

end Elements.Book10
