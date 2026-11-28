import Elements.Book7.Prop38

namespace Elements.Book7

/--
To find the least number `g` that has given parts: an `a`th part, a `b`th part and a `c`th
part.
-/
theorem proposition_39 {a b c : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    ∃ g, 0 < g ∧ (∃ x, PartOf x g a) ∧ (∃ y, PartOf y g b) ∧ (∃ z, PartOf z g c) ∧
      ∀ h, 0 < h → (∃ x, PartOf x h a) → (∃ y, PartOf y h b) → (∃ z, PartOf z h c) →
        g ≤ h := by
  -- the numbers called the same as the parts are `a`, `b`, `c`; the least number `g`
  -- they measure [Prop. 7.36]
  obtain ⟨g, hg, hag, hbg, hcg, hleast⟩ := proposition_36 (a := a) (b := b) (c := c)
    (by omega) (by omega) (by omega)
  -- `g` has parts called the same as `a`, `b`, `c` [Prop. 7.37]
  refine ⟨g, hg, proposition_37 ha hag, proposition_37 hb hbg, proposition_37 hc hcg,
    fun h hh ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ => ?_⟩
  -- a number `h` less than `g` with these parts is measured by `a`, `b`, `c`
  -- [Prop. 7.38]: impossible
  have pos : ∀ {u n}, PartOf u h n → 0 < u := fun {u n} hu =>
    Nat.pos_of_ne_zero (by rintro rfl; rw [hu.2, Nat.zero_mul] at hh; omega)
  exact hleast h hh (proposition_38 (pos hx) hx) (proposition_38 (pos hy) hy)
    (proposition_38 (pos hz) hz)

end Elements.Book7
