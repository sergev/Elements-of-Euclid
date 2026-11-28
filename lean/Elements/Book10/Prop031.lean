import Elements.Book10.Prop030

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The construction of 10.31: from rational `a`, `b` commensurable in square only, the
square on `c` equal to the rectangle contained by them [Prop. 2.14], and the rectangle
contained by `c`, `d` equal to the square on `b` [Prop. 1.44]: `c`, `d` are medial,
commensurable in square only, contain a rational area, and `a ∶ b ∷ c ∶ d`. -/
theorem proposition_31_construction {a b : Length} (h : BinomialTerms ρ a b) :
    ∃ c d, FirstBimedialTerms ρ c d ∧ Proportion a b c d := by
  obtain ⟨ha, hb, hab, hba⟩ := h
  obtain ⟨c, hc⟩ := Area.side (rect a b)
  -- the rectangle contained by `a`, `b` is medial, so the square on `c`, and `c` is
  -- medial [Prop. 10.21]
  have hcm : Medial ρ c := ⟨a, b, ha, hb, hab, hc⟩
  obtain ⟨d, hd⟩ := Area.apply c (sq b)
  -- as `a` is to `b`, so the rectangle to the square on `b` [Prop. 10.21 lem.], that is,
  -- the square on `c` to the rectangle contained by `c`, `d`, that is, `c` to `d` [Prop.
  -- 10.21 lem.]
  have h₁ : Proportion a b c d := by
    have h₂ := (proposition_21_lemma b a).2
    rw [← hc, ← hd] at h₂
    exact Elements.Book5.proposition_11 h₂.symm (proposition_21_lemma c d).1.symm
  -- `c`, `d` are commensurable in square only [Prop. 10.11], and `d` is medial [Prop.
  -- 10.23]
  have hcd := hab.of_proportion h₁
  exact ⟨c, d, ⟨hcm, proposition_23 hcm hcd.1.symm, hcd, hd ▸ hb.sq_rational,
    lt_of_proportion h₁ hba⟩, h₁⟩

/-- To find two medial lines commensurable in square only, containing a rational area, the
square on the greater exceeding that on the lesser by the square on a line commensurable
in length with the greater. -/
theorem proposition_31 : ∃ x y, FirstBimedialTerms ρ x y ∧ ExceedsComm x y := by
  -- let rational `a`, `b`, commensurable in square only, be laid out, the square on `a`
  -- exceeding that on `b` by the square on a line commensurable with `a` [Prop. 10.29]
  obtain ⟨a, b, hab, he⟩ := proposition_29 (ρ := ρ)
  obtain ⟨c, d, hcd, h⟩ := proposition_31_construction hab
  -- so the square on `c` exceeds that on `d` by the square on a line commensurable with
  -- `c` [Prop. 10.14]
  exact ⟨c, d, hcd, (proposition_14' h).1 he⟩

/-- 10.31, Euclid's closing remark: the same with a line incommensurable in length, from
10.30. -/
theorem proposition_31' : ∃ x y, FirstBimedialTerms ρ x y ∧ ExceedsIncomm x y := by
  obtain ⟨a, b, hab, he⟩ := proposition_30 (ρ := ρ)
  obtain ⟨c, d, hcd, h⟩ := proposition_31_construction hab
  exact ⟨c, d, hcd, (proposition_14' h).2 he⟩

end Elements.Book10
