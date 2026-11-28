import Elements.Book8.Prop25

namespace Elements.Book8

open Elements.Book7

/-- Similar plane numbers `c * d`, `e * f` (`c ∶ d ∷ e ∶ f`) have to one another the
ratio which some square number has to some square number. The squares may be of the
unit (`2 ∶ 8 ∷ 1 ∶ 4`). -/
theorem proposition_26 {c d e f : ℕ} (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h : c ∶ d ∷ e ∶ f) : ∃ x y, 0 < x ∧ 0 < y ∧ c * d ∶ e * f ∷ x * x ∶ y * y := by
  -- one number falls between them in mean proportion [Prop. 8.18]
  obtain ⟨g, hg, hcon, h0, h2⟩ := (proposition_18 hc hd he hf h).1
  -- let the least numbers having the same ratio as `c * d`, the mean, and `e * f` be
  -- taken [Prop. 8.2]: their outermost are squares [Prop. 8.2 corollary], and as the one
  -- is to the other, so `c * d` to `e * f` [Prop. 7.14]
  obtain ⟨x, y, -, hx, hy, -, h14, -, -⟩ := continued_outer hg hcon
  rw [h0, h2, (powers_two x y).1] at h14
  exact ⟨x, y, hx, hy, by rw [← (powers_two x y).2]; exact h14⟩

end Elements.Book8
