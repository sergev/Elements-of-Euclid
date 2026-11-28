import Elements.Book10.Prop107

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- The areas `A` and `B` applied to `ρ` with breadths `e` and `k`, `B` taken from `A`
leaving `C`: `C` applied to `ρ` makes `e - k` as breadth. -/
theorem breadth_sub {A B C : Area} {e k : Length} (he : rect ρ e = A) (hk : rect ρ k = B)
    (hC : B + C = A) : k < e ∧ ∃ c, c + k = e ∧ rect ρ c = C := by
  have hke : k < e := rect_lt_rect.mp (by rw [he, hk, ← hC]; exact lt_add _ _)
  obtain ⟨c, hc⟩ := remainder k e hke
  refine ⟨hke, c, (add_comm c k).trans hc, add_left_cancel (a := B) ?_⟩
  rw [hC, ← hk, ← rect_add, hc, he]

/-- When a medial area is taken from a rational area, the square root `z` of the remainder
is an apotome or a minor line. The mirror of 10.71. -/
theorem proposition_108 {A B C : Area} {z : Length} (hA : RationalArea ρ A)
    (hB : MedialArea ρ B) (hC : B + C = A) (hz : sq z = C) : Apotome ρ z ∨ Minor ρ z := by
  -- let `A` and `B` be applied to the rational line `ρ`, making `e`, `k` as breadths: `e`
  -- rational, commensurable with `ρ` [Prop. 10.20], `k` rational, incommensurable with it
  -- [Prop. 10.22]; so `e`, `k` are incommensurable [Prop. 10.13], and the remaining
  -- breadth is an apotome [Prop. 10.73]
  obtain ⟨e, he⟩ := Area.apply ρ A
  obtain ⟨k, hk⟩ := Area.apply ρ B
  obtain ⟨her, heρ⟩ := proposition_20 (Rational.self ρ) hA he
  obtain ⟨hkr, hkρ⟩ := proposition_22' hB (Rational.self ρ) hk
  have hek : ¬ Commensurable e k := fun h' => hkρ (comm_of_comm h' heρ)
  obtain ⟨hke, c, hc, hcC⟩ := breadth_sub he hk hC
  have ht : BinomialTerms ρ e k := ⟨her, hkr, ⟨her.inSquare_of hkr, hek⟩, hke⟩
  rw [← hcC] at hz
  -- the whole `e` is commensurable with `ρ`: a first apotome, or a fourth [Defs.
  -- 10.III.1, 10.III.4]; the square root is an apotome [Prop. 10.91], or a minor line
  -- [Prop. 10.94]
  rcases exceeds_cases hke with hx | hx
  · exact Or.inl (proposition_91 (Rational.self ρ) ⟨e, k, ⟨ht, hx, heρ⟩, hc⟩ hz)
  · exact Or.inr (proposition_94 (Rational.self ρ) ⟨e, k, ⟨ht, hx, heρ⟩, hc⟩ hz)

end Elements.Book10
