import Elements.Book7.Prop34

namespace Elements.Book7

/-- If `a` and `b` measure `c`, the least number `e` they measure measures `c`. -/
theorem proposition_35 {a b c e : ℕ} (he : LeastMeasured e a b) (hac : a ∣ c)
    (hbc : b ∣ c) : e ∣ c := by
  obtain ⟨he0, hae, hbe, hleast⟩ := he
  -- if not, `e` measuring `c` leaves a remainder `r` less than itself
  obtain ⟨q, r, hc, hr⟩ := exists_remainder c he0
  by_contra hec
  have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact hec ⟨q, hc⟩)
  -- `a` and `b` measure `e`, and `e` measures `e * q`: they measure `e * q`
  have haq := measures_trans hae ⟨q, rfl⟩
  have hbq := measures_trans hbe ⟨q, rfl⟩
  -- and the whole `c`: they measure the remainder `r`, which is less than `e`
  have har := measures_sub hac haq
  have hbr := measures_sub hbc hbq
  rw [hc, Nat.add_sub_cancel_left] at har hbr
  have := hleast r hr0 har hbr
  omega

end Elements.Book7
