import Elements.Book10.Prop070

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on the greater of two unequal lines exceeds that on the lesser by the
square on a line commensurable or incommensurable in length with the greater [Prop. 10.13
lem.]. -/
theorem exceeds_cases {x y : Length} (h : y < x) : ExceedsComm x y ∨
    ExceedsIncomm x y := by
  obtain ⟨z, hz⟩ := Length.exceeds h
  by_cases hc : Commensurable z x
  · exact Or.inl ⟨z, hz, hc⟩
  · exact Or.inr ⟨z, hz, hc⟩

/-- When a rational and a medial area are added together, the square root `z` of the whole
is a binomial, or a first bimedial, or a major line, or the square root of a rational plus
a medial area. -/
theorem proposition_71 {A B : Area} {z : Length} (hA : RationalArea ρ A)
    (hB : MedialArea ρ B) (hz : sq z = A + B) :
    Binomial ρ z ∨ FirstBimedial ρ z ∨ Major ρ z ∨ SideRationalMedial ρ z := by
  -- let the rational line `ρ` be laid down, and `A`, `B` applied to it, making `e`, `k`
  -- as breadths [Prop. 1.44]: `e` is rational, commensurable in length with `ρ` [Prop.
  -- 10.20], `k` rational, incommensurable with `ρ` [Prop. 10.22]
  obtain ⟨e, he⟩ := Area.apply ρ A
  obtain ⟨k, hk⟩ := Area.apply ρ B
  obtain ⟨her, heρ⟩ := proposition_20 (Rational.self ρ) hA he
  obtain ⟨hkr, -⟩ := proposition_22' hB (Rational.self ρ) hk
  -- `A` is incommensurable with `B`, so `e` with `k` [Props. 6.1, 10.11]: `e + k` is a
  -- binomial [Prop. 10.36], and the area applied with breadth `e + k` is the whole
  have hAB : ¬ Commensurable A B := fun h' => hB.not_rational (hA.of_comm h'.symm)
  have hek : ¬ Commensurable e k := by rw [← rect_commensurable_iff ρ, he, hk]; exact hAB
  have hsq : CommensurableInSquare e k := her.inSquare_of hkr
  have hz' : sq z = rect ρ (e + k) := by rw [rect_add, he, hk, hz]
  rcases lt_trichotomy k e with hlt | rfl | hlt
  · -- `A` greater: the greater term `e` is commensurable with `ρ`; a first binomial, or a
    -- fourth [Defs. 10.II.1, 10.II.4]; the square root is a binomial [Prop. 10.54], or a
    -- major line [Prop. 10.57]
    have ht : BinomialTerms ρ e k := ⟨her, hkr, ⟨hsq, hek⟩, hlt⟩
    rcases exceeds_cases hlt with hc | hc
    · exact Or.inl (proposition_54 (Rational.self ρ) ⟨e, k, ⟨ht, hc, heρ⟩, rfl⟩ hz')
    · exact Or.inr (Or.inr (Or.inl
        (proposition_57 (Rational.self ρ) ⟨e, k, ⟨ht, hc, heρ⟩, rfl⟩ hz')))
  · exact absurd (Commensurable.refl k) hek
  · -- `A` less: the lesser term `e` is commensurable with `ρ`; a second binomial, or a
    -- fifth [Defs. 10.II.2, 10.II.5]; the square root is a first bimedial [Prop. 10.55],
    -- or the square root of a rational plus a medial area [Prop. 10.58]
    have ht : BinomialTerms ρ k e :=
      ⟨hkr, her, ⟨hsq.symm, fun h' => hek h'.symm⟩, hlt⟩
    rw [add_comm] at hz'
    rcases exceeds_cases hlt with hc | hc
    · exact Or.inr (Or.inl (proposition_55 (Rational.self ρ)
        ⟨k, e, ⟨ht, hc, heρ⟩, rfl⟩ hz'))
    · exact Or.inr (Or.inr (Or.inr
        (proposition_58 (Rational.self ρ) ⟨k, e, ⟨ht, hc, heρ⟩, rfl⟩ hz')))

end Elements.Book10
