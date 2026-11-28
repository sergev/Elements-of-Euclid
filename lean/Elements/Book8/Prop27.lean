import Elements.Book8.Prop26

namespace Elements.Book8

open Elements.Book7

/-- Similar solid numbers `c * d * e`, `f * g * h` (`c ∶ d ∷ f ∶ g`, `d ∶ e ∷ g ∶ h`)
have to one another the ratio which some cube number has to some cube number. The cubes
may be of the unit. -/
theorem proposition_27 {c d e f g h : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hf : 0 < f) (hg : 0 < g) (hh : 0 < h) (h₁ : c ∶ d ∷ f ∶ g) (h₂ : d ∶ e ∷ g ∶ h) :
    ∃ x y, 0 < x ∧ 0 < y ∧ c * d * e ∶ f * g * h ∷ x * x * x ∶ y * y * y := by
  -- two numbers fall between them in mean proportion [Prop. 8.19]
  obtain ⟨k, hk, hcon, h0, h3⟩ := (proposition_19 hc hd he hf hg hh h₁ h₂).1
  -- let the least numbers having the same ratio as these four be taken [Prop. 8.2]:
  -- their outermost are cubes [Prop. 8.2 corollary], and as the one is to the other, so
  -- `c * d * e` to `f * g * h` [Prop. 7.14]
  obtain ⟨x, y, -, hx, hy, -, h14, -, -⟩ := continued_outer hk hcon
  rw [h0, h3, (powers_three x y).1] at h14
  exact ⟨x, y, hx, hy, by rw [← (powers_three x y).2]; exact h14⟩

end Elements.Book8
