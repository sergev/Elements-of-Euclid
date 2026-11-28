import Elements.Book9.Prop31

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- The dyad is prime: it is measured by the unit and itself alone (Def. 7.11). -/
theorem prime_two : PrimeNumber 2 := by
  refine ⟨by omega, fun d hd => ?_⟩
  have := le_of_measures (by omega) hd
  obtain ⟨k, hk⟩ := hd
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> omega

/-- The numbers doubled from the unit, the dyad among them, are continuously
proportional from the unit, and the number after the unit is the dyad. -/
theorem powers_two_continued (n : ℕ) :
    Continued (powers 1 2 n) ∧ powers 1 2 n 0 = 1 ∧ (1 ≤ n → powers 1 2 n 1 = 2) := by
  have hpos := powers_pos Nat.one_pos (show 0 < 2 by omega) n
  have hin := powers_continuedIn Nat.one_pos (show 0 < 2 by omega) n
  refine ⟨hin.continued hpos Nat.one_pos (by omega), powers_one_zero 2 n, fun hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : powers 1 2 (m + 1) 0 ∶ powers 1 2 (m + 1) 1 ∷ 1 ∶ 2 := hin 0
  rw [powers_one_zero] at h
  rw [eq_mul_of_unit h.symm, Nat.one_mul]

/-- Each of the numbers doubled from the unit, after the unit, is even: it is the one
before it taken twice. -/
theorem powers_two_even {n : ℕ} (i : Fin (n + 1)) (hi : 0 < i.val) :
    EvenNumber (powers 1 2 n i) := by
  obtain ⟨hcon, h0, h1⟩ := powers_two_continued n
  have hpos := powers_pos Nat.one_pos (show 0 < 2 by omega) n
  obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
  have := unit_succ hcon h0 (k := k) (by have := i.isLt; omega)
  rw [h1 (by have := i.isLt; omega), show (⟨k + 1, by omega⟩ : Fin (n + 1)) = i from
    Fin.ext hk.symm] at this
  exact ⟨powers 1 2 n ⟨k, by omega⟩, hpos _, by rw [this]; omega⟩

/--
Each of the numbers doubled from a dyad is even-times-even only: not even-times-odd.
The dyad is `powers 1 2 1`, and Euclid's numbers are those after it, `powers 1 2 n` with
`2 ≤ n`.
-/
theorem proposition_32 {n : ℕ} (hn : 2 ≤ n) :
    EvenTimesEven (powers 1 2 n (Fin.last n)) ∧
      ¬ EvenTimesOdd (powers 1 2 n (Fin.last n)) := by
  obtain ⟨hcon, h0, h1⟩ := powers_two_continued n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  constructor
  · -- it is doubled from a dyad: the one before it, even, taken twice [Def. 7.8]
    rw [powers_last]
    refine ⟨_, 2, powers_two_even (Fin.last m) (by simp only [Fin.val_last]; omega),
      ⟨1, Nat.one_pos, rfl⟩, rfl⟩
  · -- the last is measured by none but the numbers doubled from the unit, the dyad
    -- being prime [Prop. 9.13]; and they are all even, but the unit
    rintro ⟨e, f, -, hf, hf1, hef⟩
    have hp : PrimeNumber (powers 1 2 (m + 1) 1) := by rw [h1 (by omega)]; exact prime_two
    obtain ⟨i, rfl⟩ := proposition_13 hcon h0 hp ⟨e, by
      rw [hef, Elements.Book7.proposition_16 (by have := hf.1; omega)
        (Nat.pos_of_ne_zero fun h => by
          have := powers_pos Nat.one_pos (show 0 < 2 by omega) (m + 1) (Fin.last _)
          rw [hef, h, Nat.zero_mul] at this; omega)]⟩
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · rw [show i = 0 from Fin.ext hi, h0] at hf1; omega
    · exact hf.2 (powers_two_even i hi)

end Elements.Book9
