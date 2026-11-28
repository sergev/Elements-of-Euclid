import Elements.Book10.Prop109

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- When a medial area incommensurable with the whole is taken from a medial area, the
square root `z` of the remainder is a second apotome of a medial, or that which with a
medial area makes a medial whole. The mirror of 10.72. -/
theorem proposition_110 {A B C : Area} {z : Length} (hA : MedialArea ρ A)
    (hB : MedialArea ρ B) (hi : ¬ Commensurable A B) (hC : B + C = A) (hz : sq z = C) :
    SecondApotomeOfMedial ρ z ∨ MedialWholeWithMedial ρ z := by
  -- `e`, `k` rational, incommensurable with `ρ` [Prop. 10.22], and with one another
  -- [Props. 6.1, 10.11]: the remaining breadth is an apotome [Prop. 10.73]
  obtain ⟨e, he⟩ := Area.apply ρ A
  obtain ⟨k, hk⟩ := Area.apply ρ B
  obtain ⟨her, heρ⟩ := proposition_22' hA (Rational.self ρ) he
  obtain ⟨hkr, hkρ⟩ := proposition_22' hB (Rational.self ρ) hk
  have hek : ¬ Commensurable e k := by rw [← rect_commensurable_iff ρ, he, hk]; exact hi
  obtain ⟨hke, c, hc, hcC⟩ := breadth_sub he hk hC
  have ht : BinomialTerms ρ e k := ⟨her, hkr, ⟨her.inSquare_of hkr, hek⟩, hke⟩
  rw [← hcC] at hz
  -- neither is commensurable with `ρ`: a third apotome, or a sixth [Defs. 10.III.3,
  -- 10.III.6]; the square root is a second apotome of a medial [Prop. 10.93], or that
  -- which with a medial area makes a medial whole [Prop. 10.96]
  rcases exceeds_cases hke with hx | hx
  · exact Or.inl (proposition_93 (Rational.self ρ) ⟨e, k, ⟨ht, hx, heρ, hkρ⟩, hc⟩ hz)
  · exact Or.inr (proposition_96 (Rational.self ρ) ⟨e, k, ⟨ht, hx, heρ, hkρ⟩, hc⟩ hz)

end Elements.Book10
