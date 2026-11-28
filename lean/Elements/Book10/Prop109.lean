import Elements.Book10.Prop108

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- When a rational area is taken from a medial area, the square root `z` of the remainder
is a first apotome of a medial, or that which with a rational area makes a medial whole.
The mirror of 10.71. -/
theorem proposition_109 {A B C : Area} {z : Length} (hA : MedialArea ρ A)
    (hB : RationalArea ρ B) (hC : B + C = A) (hz : sq z = C) :
    FirstApotomeOfMedial ρ z ∨ MedialWholeWithRational ρ z := by
  -- similarly: `e` rational, incommensurable with `ρ` [Prop. 10.22], `k` rational,
  -- commensurable with it [Prop. 10.20]; the remaining breadth is an apotome
  obtain ⟨e, he⟩ := Area.apply ρ A
  obtain ⟨k, hk⟩ := Area.apply ρ B
  obtain ⟨her, heρ⟩ := proposition_22' hA (Rational.self ρ) he
  obtain ⟨hkr, hkρ⟩ := proposition_20 (Rational.self ρ) hB hk
  have hek : ¬ Commensurable e k := fun h' => heρ (comm_of_comm h'.symm hkρ)
  obtain ⟨hke, c, hc, hcC⟩ := breadth_sub he hk hC
  have ht : BinomialTerms ρ e k := ⟨her, hkr, ⟨her.inSquare_of hkr, hek⟩, hke⟩
  rw [← hcC] at hz
  -- the attached `k` is commensurable with `ρ`: a second apotome, or a fifth [Defs.
  -- 10.III.2, 10.III.5]; the square root is a first apotome of a medial [Prop. 10.92], or
  -- that which with a rational area makes a medial whole [Prop. 10.95]
  rcases exceeds_cases hke with hx | hx
  · exact Or.inl (proposition_92 (Rational.self ρ) ⟨e, k, ⟨ht, hx, hkρ⟩, hc⟩ hz)
  · exact Or.inr (proposition_95 (Rational.self ρ) ⟨e, k, ⟨ht, hx, hkρ⟩, hc⟩ hz)

end Elements.Book10
