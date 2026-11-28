import Elements.Book10.Prop071

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- When two medial areas incommensurable with one another are added together, the square
root `z` of the whole is a second bimedial, or the square root of two medial areas. -/
theorem proposition_72 {A B : Area} {z : Length} (hA : MedialArea ρ A)
    (hB : MedialArea ρ B)
    (hi : ¬ Commensurable A B) (hz : sq z = A + B) :
    SecondBimedial ρ z ∨ SideTwoMedials ρ z := by
  -- let `A` be the greater; similarly if it is the less
  wlog hBA : B < A generalizing A B
  · rcases (not_lt.mp hBA).lt_or_eq with hlt | rfl
    · exact this hB hA (fun h => hi h.symm) (add_comm A B ▸ hz) hlt
    · exact absurd (Commensurable.refl A) hi
  -- applied to the rational line `ρ`, `A`, `B` make `e`, `k` as breadths, rational,
  -- incommensurable with `ρ` [Prop. 10.22], and with one another [Props. 6.1, 10.11]: so
  -- `e + k` is a binomial [Prop. 10.36], `e` the greater term [Prop. 5.14]
  obtain ⟨e, he⟩ := Area.apply ρ A
  obtain ⟨k, hk⟩ := Area.apply ρ B
  obtain ⟨her, heρ⟩ := proposition_22' hA (Rational.self ρ) he
  obtain ⟨hkr, hkρ⟩ := proposition_22' hB (Rational.self ρ) hk
  have hek : ¬ Commensurable e k := by rw [← rect_commensurable_iff ρ, he, hk]; exact hi
  have hlt : k < e := rect_lt_rect.mp (by rw [he, hk]; exact hBA)
  have ht : BinomialTerms ρ e k := ⟨her, hkr, ⟨her.inSquare_of hkr, hek⟩, hlt⟩
  have hz' : sq z = rect ρ (e + k) := by rw [rect_add, he, hk, hz]
  -- neither is commensurable with `ρ`: a third binomial, or a sixth [Defs. 10.II.3,
  -- 10.II.6]; the square root is a second bimedial [Prop. 10.56], or the square root of
  -- two medial areas [Prop. 10.59]
  rcases exceeds_cases hlt with hc | hc
  · exact Or.inl (proposition_56 (Rational.self ρ) ⟨e, k, ⟨ht, hc, heρ, hkρ⟩, rfl⟩ hz')
  · exact Or.inr (proposition_59 (Rational.self ρ) ⟨e, k, ⟨ht, hc, heρ, hkρ⟩, rfl⟩ hz')

end Elements.Book10
