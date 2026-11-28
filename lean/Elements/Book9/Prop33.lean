import Elements.Book9.Prop32

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- If a number `h + h` has an odd half `h`, it is even-times-odd only: not
even-times-even. The half is an odd number, greater than the unit (Def. 7.9). -/
theorem proposition_33 {h : ℕ} (hh : OddNumber h) (hh1 : 1 < h) :
    EvenTimesOdd (h + h) ∧ ¬ EvenTimesEven (h + h) := by
  constructor
  · -- its half, odd, measures it an even number of times, twice [Defs. 7.9, 7.16]
    exact ⟨2, h, ⟨1, Nat.one_pos, rfl⟩, hh, hh1, by omega⟩
  · -- if it is measured by an even number `k + k` according to an even number `f`, its
    -- half is measured by the even `f` according to `k`, and is even [Prop. 9.21]
    rintro ⟨e, f, ⟨k, hk, rfl⟩, hf, hef⟩
    have hf0 : 0 < f := by have := hf.one_lt; omega
    have hhk : h = f * k := by
      rw [← Elements.Book7.proposition_5' k k f] at hef
      rw [Elements.Book7.proposition_16 hk hf0]
      omega
    exact hh.2 (hhk ▸ hf.mul hk)

end Elements.Book9
