import Elements.Book10.Prop065

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The construction of 10.66–10.70 (and 10.103–10.107): `l = x + y` commensurable in
length with `l'`; as `l` is to `l'`, so `x` to `x'` [Prop. 6.12], and `y'` the remainder:
so the remainder `y` is to `y'` as `l` to `l'` [Props. 6.16, 5.19 corr.]. The terms are
commensurable, each with each [Prop. 10.11], and `x ∶ y ∷ x' ∶ y'` [Props. 5.11,
5.16]. -/
theorem comm_terms {l l' x y : Length} (h : Commensurable l l') (hl : x + y = l) :
    ∃ x' y', x' + y' = l' ∧ Proportion x y x' y' ∧ Commensurable x x' ∧
      Commensurable y y' := by
  obtain ⟨x', hx'⟩ := Length.fourth' l l' x
  have hlt : x' < l' := lt_of_proportion (Elements.Book5.proposition_16 hx')
    (hl ▸ Magnitude.lt_add x y)
  obtain ⟨y', hy'⟩ := Magnitude.remainder x' l' hlt
  have h₁ : Proportion y y' l l' := by
    rw [← hl, ← hy'] at hx' ⊢
    exact Elements.Book5.proposition_19 hx'
  have h₂ := (proposition_11 hx' Length.divisible Length.divisible).1 h
  have h₃ := (proposition_11 h₁.symm Length.divisible Length.divisible).1 h
  exact ⟨x', y', hy', Elements.Book5.proposition_16
    (Elements.Book5.proposition_11 hx'.symm h₁.symm), h₂, h₃⟩

/-- Terms of a kind carry over to terms commensurable with them, in the same ratio. -/
def Transfers (P : Length → Length → Prop) : Prop :=
  ∀ {x y x' y'}, P x y → Proportion x y x' y' → Commensurable x x' → Commensurable y y' →
    P x' y'

/-- A line commensurable in length with a sum of terms of a kind that carries over is a
sum of terms of the kind. -/
theorem Transfers.sum {P : Length → Length → Prop} (hP : Transfers P) {l l' : Length}
    (h : Commensurable l l') (hl : ∃ x y, P x y ∧ l = x + y) : ∃ x y, P x y ∧
      l' = x + y := by
  obtain ⟨x, y, hxy, rfl⟩ := hl
  obtain ⟨x', y', rfl, hp, hx, hy⟩ := comm_terms h rfl
  exact ⟨x', y', hP hxy hp hx hy, rfl⟩

/-- Binomial terms carry over: commensurable with rational lines, `x'`, `y'` are rational
[Def. 10.3]; commensurable in square only [Prop. 10.11]; and in the same order [Prop.
5.14]. -/
theorem binomialTerms_transfers : Transfers (BinomialTerms ρ) :=
  fun ⟨hx, hy, hxy, hyx⟩ hp hxx hyy =>
    ⟨hx.of_comm hxx.symm, hy.of_comm hyy.symm, hxy.of_proportion hp,
      lt_of_proportion hp hyx⟩

theorem exceedsComm_transfers {x y x' y' : Length} (hp : Proportion x y x' y') :
    ExceedsComm x y → ExceedsComm x' y' := (proposition_14' hp).1

theorem exceedsIncomm_transfers {x y x' y' : Length} (hp : Proportion x y x' y') :
    ExceedsIncomm x y → ExceedsIncomm x' y' := (proposition_14' hp).2

/-- A line commensurable in length with a binomial is a binomial, and of the same order:
the square on the greater term exceeds that on the lesser by the square on a line
commensurable or incommensurable with it, as before [Prop. 10.14], and the terms are
commensurable with `r`, or not, as before [Props. 10.12, 10.13]. -/
theorem proposition_66 {l l' : Length} (hl : Binomial ρ l) (h : Commensurable l l') :
    Binomial ρ l' ∧ ∀ r,
      (FirstBinomial ρ r l → FirstBinomial ρ r l') ∧
      (SecondBinomial ρ r l → SecondBinomial ρ r l') ∧
      (ThirdBinomial ρ r l → ThirdBinomial ρ r l') ∧
      (FourthBinomial ρ r l → FourthBinomial ρ r l') ∧
      (FifthBinomial ρ r l → FifthBinomial ρ r l') ∧
      (SixthBinomial ρ r l → SixthBinomial ρ r l') := by
  have hB : Transfers (BinomialTerms ρ) := binomialTerms_transfers
  have hc : ∀ {a a' r : Length}, Commensurable a a' → Commensurable a r →
      Commensurable a' r := fun ha h => proposition_12 Length.divisible ha.symm h.symm
  have hi : ∀ {a a' r : Length}, Commensurable a a' → ¬ Commensurable a r →
      ¬ Commensurable a' r := fun ha h => proposition_13 Length.divisible ha h
  refine ⟨Transfers.sum hB h hl, fun r => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Transfers.sum (fun ⟨h₁, h₂, h₃⟩ hp hx hy =>
      ⟨hB h₁ hp hx hy, exceedsComm_transfers hp h₂, hc hx h₃⟩) h
  · exact Transfers.sum (fun ⟨h₁, h₂, h₃⟩ hp hx hy =>
      ⟨hB h₁ hp hx hy, exceedsComm_transfers hp h₂, hc hy h₃⟩) h
  · exact Transfers.sum (fun ⟨h₁, h₂, h₃, h₄⟩ hp hx hy =>
      ⟨hB h₁ hp hx hy, exceedsComm_transfers hp h₂, hi hx h₃, hi hy h₄⟩) h
  · exact Transfers.sum (fun ⟨h₁, h₂, h₃⟩ hp hx hy =>
      ⟨hB h₁ hp hx hy, exceedsIncomm_transfers hp h₂, hc hx h₃⟩) h
  · exact Transfers.sum (fun ⟨h₁, h₂, h₃⟩ hp hx hy =>
      ⟨hB h₁ hp hx hy, exceedsIncomm_transfers hp h₂, hc hy h₃⟩) h
  · exact Transfers.sum (fun ⟨h₁, h₂, h₃, h₄⟩ hp hx hy =>
      ⟨hB h₁ hp hx hy, exceedsIncomm_transfers hp h₂, hi hx h₃, hi hy h₄⟩) h

end Elements.Book10
