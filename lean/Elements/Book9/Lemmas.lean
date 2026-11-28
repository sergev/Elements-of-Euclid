import Elements.Book9.Definitions

/-
What Book 9 takes from Book 7 and does again: Def. 7.7's second reading, the least number
measured by any multitude (7.36, for any multitude), and the sums of 9.35, 9.36.
-/

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-! Odd and even. -/

/-- Every number, and the unit, is even or odd (Defs. 7.6, 7.7). -/
theorem even_or_odd {a : ℕ} (ha : 0 < a) : EvenNumber a ∨ OddNumber a := by
  by_cases h : EvenNumber a
  · exact Or.inl h
  · exact Or.inr ⟨ha, h⟩

/-- An even number is not odd. -/
theorem EvenNumber.not_odd {a : ℕ} (h : EvenNumber a) : ¬ OddNumber a :=
  fun ho => ho.2 h

/-- An even number is a number, greater than the unit. -/
theorem EvenNumber.one_lt {a : ℕ} (h : EvenNumber a) : 1 < a := by
  obtain ⟨h, hh, rfl⟩ := h
  omega

/-- Def. 7.7, the second reading: an odd number differs from an even number by a unit,
`a = h + h + 1`; for the unit, `h` is nothing. -/
theorem odd_iff {a : ℕ} : OddNumber a ↔ ∃ h, a = h + h + 1 := by
  constructor
  · rintro ⟨ha, hne⟩
    refine ⟨a / 2, ?_⟩
    by_contra hne'
    exact hne ⟨a / 2, by omega, by omega⟩
  · rintro ⟨h, rfl⟩
    exact ⟨by omega, fun ⟨k, _, hk⟩ => by omega⟩

/-- An odd number less a unit is even, or nothing for the unit (Def. 7.7). -/
theorem OddNumber.sub_unit {a : ℕ} (h : OddNumber a) (ha : 1 < a) :
    EvenNumber (a - 1) := by
  obtain ⟨k, rfl⟩ := odd_iff.mp h
  exact ⟨k, by omega, by omega⟩

/-- An even number less a unit is odd (Def. 7.7). -/
theorem EvenNumber.sub_unit {a : ℕ} (h : EvenNumber a) : OddNumber (a - 1) := by
  obtain ⟨k, hk, rfl⟩ := h
  exact odd_iff.mpr ⟨k - 1, by omega⟩

/-- An even number and a unit make an odd number (Def. 7.7). -/
theorem EvenNumber.add_unit {a : ℕ} (h : EvenNumber a) : OddNumber (a + 1) := by
  obtain ⟨k, -, rfl⟩ := h
  exact odd_iff.mpr ⟨k, rfl⟩

/-- As the unit is to `a`, so `b` is to `b * a`: the unit measures `a`, and `b` measures
`b * a`, according to the units in `a` (Defs. 7.15, 7.20). -/
theorem unit_proportion {a : ℕ} (b : ℕ) (ha : 0 < a) : 1 ∶ a ∷ b ∶ b * a :=
  proportion_iff.mpr ⟨1, a, 1, b, Nat.one_pos, ha, rfl, (Nat.one_mul a).symm,
    (Nat.mul_one b).symm, rfl⟩

/-- A cube of a number is a number. -/
theorem one_lt_cube {c : ℕ} (hc : 1 < c) : 1 < c * c * c := by
  have := Nat.mul_le_mul (Nat.mul_le_mul hc hc) hc
  omega

/-! The least number measured by any multitude: Euclid's 7.36, done once more for each
number added. -/

/-- The least number measured by `a 0`, …, `a n` measures every number they all measure,
as 7.35 for two. -/
theorem exists_leastMeasuredSeq' {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i) :
    ∃ c, LeastMeasuredSeq c a ∧ ∀ d, (∀ i, a i ∣ d) → c ∣ d := by
  induction n with
  | zero =>
    refine ⟨a 0, ⟨ha 0, fun i => ?_, fun d _ hd => ?_⟩, fun d hd => ?_⟩
    · rw [Fin.fin_one_eq_zero i]
    · exact le_of_measures (by assumption) (hd 0)
    · exact hd 0
  | succ n ih =>
    -- the least number `c` the first `n + 1` measure, and the least `e` that `c` and the
    -- last measure [Prop. 7.34]
    obtain ⟨c, ⟨hc, hac, -⟩, hcd⟩ := ih (a := fun i => a i.castSucc) fun i => ha _
    obtain ⟨e, he⟩ := Elements.Book7.proposition_34 hc (ha (Fin.last _))
    have hmeas : ∀ d, (∀ i, a i ∣ d) → e ∣ d := fun d hd =>
      -- `c` measures every number they measure, and so does `e` [Prop. 7.35]
      Elements.Book7.proposition_35 he (hcd d fun i => hd _) (hd _)
    refine ⟨e, ⟨he.1, fun i => ?_, fun d hd hdi => le_of_measures hd (hmeas d hdi)⟩,
      hmeas⟩
    induction i using Fin.lastCases with
    | last => exact he.2.2.1
    | cast i => exact measures_trans (hac i) he.2.1

/-- There is a least number measured by any multitude of numbers [Prop. 7.36]. -/
theorem exists_leastMeasuredSeq {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i) :
    ∃ c, LeastMeasuredSeq c a :=
  (exists_leastMeasuredSeq' ha).imp fun _ h => h.1

/-- The least number measured by any multitude measures every number they all measure
[Prop. 7.35]. -/
theorem LeastMeasuredSeq.measures {n c d : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hc : LeastMeasuredSeq c a) (hd : ∀ i, a i ∣ d) : c ∣ d := by
  obtain ⟨c', hc', hm⟩ := exists_leastMeasuredSeq' ha
  have h₁ : c' ∣ c := hm c hc.2.1
  have h₂ : c ≤ c' := hc.2.2 c' hc'.1 hc'.2.1
  have : c' = c := Nat.le_antisymm (le_of_measures hc.1 h₁) h₂
  exact this ▸ hm d hd

/-! Continued proportion, and from a unit (9.8–9.13). -/

/-- Numbers continuously proportional are, any number of steps apart, in the same ratio:
`a i ∶ a i'` as `a j ∶ a j'` when `i' - i = j' - j`, via equality [Prop. 7.14], a step at
a time. -/
theorem continued_ratio {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hcon : Continued a) {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') (h : i' + j = j' + i)
    (hi' : i' ≤ n) (hj' : j' ≤ n) :
    a ⟨i, by omega⟩ ∶ a ⟨i', by omega⟩ ∷ a ⟨j, by omega⟩ ∶ a ⟨j', by omega⟩ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain rfl : j' = j + r := by omega
  induction r with
  | zero => exact proportion_self _ _
  | succ r ih =>
    have h₁ := ih (by omega) (by omega) (by omega) (by omega) (by omega)
    have hi₁ : a ⟨i + r, by omega⟩ ∶ a ⟨i + r + 1, by omega⟩ ∷ a 0 ∶ a 1 :=
      hcon ⟨i + r, by omega⟩
    have hj₁ : a ⟨j + r, by omega⟩ ∶ a ⟨j + r + 1, by omega⟩ ∷ a 0 ∶ a 1 :=
      hcon ⟨j + r, by omega⟩
    exact Elements.Book7.proposition_14' (ha _) (ha _) (ha _) (ha _) (ha _) (ha _) h₁
      (proportion_trans (ha _) (ha _) (ha 0) (ha 1) hi₁ hj₁.symm)

/-- The number after the unit, by its place. -/
theorem fin_one_eq {n : ℕ} (h : 1 ≤ n) : (⟨1, by omega⟩ : Fin (n + 1)) = 1 :=
  Fin.ext (Nat.mod_eq_of_lt (by omega)).symm

/-- From a unit, each number is the one before multiplied by the number after the unit:
as the unit is to `a 1`, so `a k` is to `a (k + 1)` [Def. 7.20]. -/
theorem unit_succ {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    {k : ℕ} (hk : k + 1 ≤ n) : a ⟨k + 1, by omega⟩ = a ⟨k, by omega⟩ * a 1 := by
  have h : a ⟨k, by omega⟩ ∶ a ⟨k + 1, by omega⟩ ∷ a 0 ∶ a 1 := hcon ⟨k, by omega⟩
  rw [h0] at h
  exact eq_mul_of_unit h.symm

/-- From a unit, the third is the number after the unit multiplied by itself. -/
theorem unit_two {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (hn : 2 ≤ n) : a ⟨2, by omega⟩ = a 1 * a 1 := by
  rw [unit_succ hcon h0 (k := 1) hn, fin_one_eq (by omega)]

/-- From a unit, with a number after it, all are numbers but the unit. -/
theorem unit_one_lt {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (h1 : 1 < a 1) {k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) : 1 < a ⟨k, by omega⟩ := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [unit_succ hcon h0 hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [show (⟨0, by omega⟩ : Fin (n + 1)) = 0 from rfl, h0, Nat.one_mul]; exact h1
    · have := Nat.mul_lt_mul_of_pos_left h1 (show 0 < a ⟨k, by omega⟩ by
        have := ih (by omega) hk'; omega)
      have := ih (by omega) hk'
      omega

/-- From a unit, with a number after it, all are positive. -/
theorem unit_pos {n : ℕ} {a : Fin (n + 1) → ℕ} (hcon : Continued a) (h0 : a 0 = 1)
    (h1 : 1 < a 1) (i : Fin (n + 1)) : 0 < a i := by
  rcases Nat.eq_zero_or_pos i.val with h | h
  · rw [show i = 0 from Fin.ext h, h0]; exact Nat.one_pos
  · have := unit_one_lt hcon h0 h1 (k := i.val) (by omega) h
    rw [Fin.eta] at this
    omega

/-! Sums (9.35, 9.36). -/

/-- All of `n + 2` numbers are all but the last, and the last (Book 7's `sum`). -/
theorem sum_succ {n : ℕ} (a : Fin (n + 2) → ℕ) :
    sum a = sum (fun i : Fin (n + 1) => a i.castSucc) + a (Fin.last (n + 1)) := rfl

/-- The sums of two multitudes, each to each, added: `sum (f + g)` is `sum f` and
`sum g`. -/
theorem sum_add {n : ℕ} (f g : Fin (n + 1) → ℕ) :
    sum (fun i => f i + g i) = sum f + sum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, sum_succ f, sum_succ g,
      ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

/-- The excesses of each over the one before, added together, and the first, make the
last, for numbers `g 0`, …, `g (n + 1)` increasing. -/
theorem sum_excess_nat {n : ℕ} {g : ℕ → ℕ} (h : ∀ k, k ≤ n → g k ≤ g (k + 1)) :
    sum (fun i : Fin (n + 1) => g (i.val + 1) - g i.val) + g 0 = g (n + 1) := by
  induction n with
  | zero => have := h 0 le_rfl; show g (0 + 1) - g 0 + g 0 = g (0 + 1); omega
  | succ n ih =>
    rw [sum_succ]
    have := ih fun k hk => h k (by omega)
    have := h (n + 1) le_rfl
    simp only [Fin.val_castSucc, Fin.val_last] at *
    omega

/-- The excesses of each over the one before, added together, and the first, make the
last: `a 0`, …, `a (n + 1)` increasing. -/
theorem sum_excess {n : ℕ} {a : Fin (n + 2) → ℕ}
    (h : ∀ i : Fin (n + 1), a i.castSucc ≤ a i.succ) :
    sum (fun i : Fin (n + 1) => a i.succ - a i.castSucc) + a 0 =
      a (Fin.last (n + 1)) := by
  let g : ℕ → ℕ := fun k => if hk : k < n + 2 then a ⟨k, hk⟩ else 0
  have hg : ∀ i : Fin (n + 2), a i = g i.val := fun i => by
    simp only [g, i.isLt, ↓reduceDIte, Fin.eta]
  have := sum_excess_nat (n := n) (g := g) fun k hk => by
    have := h ⟨k, by omega⟩
    rwa [hg, hg] at this
  have hs : (fun i : Fin (n + 1) => a i.succ - a i.castSucc) =
      fun i : Fin (n + 1) => g (i.val + 1) - g i.val := funext fun i => by
    rw [hg, hg, Fin.val_succ, Fin.val_castSucc]
  rw [hs, hg (Fin.last _), hg 0]
  exact this

/-- The unit and the numbers doubled from it, up to the last, are a unit less than the
last doubled once more. -/
theorem sum_powers_two (n : ℕ) :
    sum (powers 1 2 n) + 1 = powers 1 2 (n + 1) (Fin.last (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, powers_last, powers_last]
    have : (fun i : Fin (n + 1) => powers 1 2 (n + 1) i.castSucc) = powers 1 2 n := by
      funext i; rw [powers_castSucc, Nat.mul_one]
    rw [this, powers_last] at *
    omega

/-- All of `n + 2` numbers are the first, and the rest. -/
theorem sum_succ' {n : ℕ} (a : Fin (n + 2) → ℕ) :
    sum a = a 0 + sum (fun i : Fin (n + 1) => a i.succ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, ih, sum_succ (fun i : Fin (n + 2) => a i.succ)]
    simp only [Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc, Nat.succ_eq_add_one]
    omega

/-! Def. 7.22: the parts of a number, as a list. -/

/-- The numbers `a 0`, …, `a n` as a list have the same sum. -/
theorem sum_ofFn {n : ℕ} (a : Fin (n + 1) → ℕ) : (List.ofFn a).sum = sum a := by
  induction n with
  | zero => rw [List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil]; rfl
  | succ n ih => rw [List.ofFn_succ, List.sum_cons, ih, sum_succ']

/-- Numbers each less than the next are distinct. -/
theorem nodup_ofFn_of_lt {n : ℕ} {a : Fin n → ℕ} (h : ∀ i j, i < j → a i < a j) :
    (List.ofFn a).Nodup := by
  induction n with
  | zero => rw [List.ofFn_zero]; exact List.nodup_nil
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons, List.mem_ofFn]
    refine ⟨fun ⟨i, hi⟩ => ?_, ih fun i j hij => h _ _ (Fin.succ_lt_succ_iff.mpr hij)⟩
    have := h 0 i.succ (Fin.succ_pos i)
    omega

/-- If the parts of `a` (the numbers less than `a` measuring it, Def. 7.22) are the
distinct numbers of a list `l`, their sum is the sum of `l`. -/
theorem sum_parts {a : ℕ} {l : List ℕ} (hl : l.Nodup)
    (h : ∀ x, x ∈ l ↔ x < a ∧ x ∣ a) : ((List.range a).filter (· ∣ a)).sum = l.sum := by
  apply List.Perm.sum_nat
  rw [List.perm_ext_iff_of_nodup (List.nodup_range.sublist List.filter_sublist) hl]
  intro x
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq, h]

end Elements.Book9
