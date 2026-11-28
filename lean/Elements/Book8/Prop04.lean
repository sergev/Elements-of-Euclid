import Elements.Book8.Prop03

namespace Elements.Book8

open Elements.Book7

/--
Euclid's construction in 8.4, a ratio at a time: numbers continuously proportional in the
ratios of `p i` to `q i` (in least numbers), which measure an equal number of times any
numbers continuously proportional in those ratios. Euclid finds them for three ratios; to
add the ratio of `e` to `f`, he takes the least number `l` measured by `e` and the last,
`k` (7.34), and `l` and `f` taken as many times as the last and `e` measure `l`. His two
cases, `e` measuring `k` or not, are one: if it does, `l` is `k`. Starting from the unit,
alone, the first ratio gives `p 0`, `q 0`.
-/
theorem exists_continued_measuring {n : ℕ} {p q : Fin n → ℕ} (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 < q i) (hl : ∀ i, Least (p i) (q i)) :
    ∃ s : Fin (n + 1) → ℕ, (∀ i, 0 < s i) ∧
      (∀ i, s i.castSucc ∶ s i.succ ∷ p i ∶ q i) ∧
      ∀ t : Fin (n + 1) → ℕ, (∀ i, 0 < t i) → (∀ i, t i.castSucc ∶ t i.succ ∷ p i ∶ q i) →
        ∃ m, ∀ i, t i = s i * m := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => Nat.one_pos, fun i => i.elim0, fun t _ _ => ⟨t 0, ?_⟩⟩
    intro i
    obtain rfl : i = 0 := Fin.ext (by have := i.isLt; omega)
    exact (Nat.one_mul _).symm
  | succ n ih =>
    obtain ⟨s, hs, hrat, hmeas⟩ := ih (p := fun i => p i.castSucc)
      (q := fun i => q i.castSucc) (fun i => hp _) (fun i => hq _) (fun i => hl _)
    -- the least number `l` measured by the last of `s` and `e`, the next antecedent
    -- [Prop. 7.34]
    have hsl := hs (Fin.last n)
    have he := hp (Fin.last n)
    have hf := hq (Fin.last n)
    obtain ⟨l, hl0, hu, hv, hlmin⟩ := Elements.Book7.proposition_34 hsl he
    obtain ⟨u, hu⟩ := id hu
    obtain ⟨v, hv⟩ := id hv
    have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hv0 : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; omega)
    -- as many times as the last measures `l`, so many times let each of `s` measure the
    -- new numbers; and as many times as `e` measures `l`, so many times let `f` measure
    -- the last
    refine ⟨fun i => Fin.lastCases (q (Fin.last n) * v) (fun j => s j * u) i,
      fun i => ?_, fun i => ?_, fun t ht hrt => ?_⟩
    · induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact Nat.mul_pos hf hv0
      | cast j => simp only [Fin.lastCases_castSucc]; exact Nat.mul_pos (hs j) hu0
    · induction i using Fin.lastCases with
      | last =>
        -- `e`, `f` taken `v` times are in the ratio of `e` to `f` [Def. 7.20, Prop. 7.17]
        simp only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
        rw [← hu, hv]
        exact (Elements.Book7.proposition_17 hv0 he hf).symm
      | cast j =>
        -- two of `s` taken `u` times are in the same ratio as they [Prop. 7.17]
        simp only [Fin.succ_castSucc, Fin.lastCases_castSucc]
        exact proportion_trans (Nat.mul_pos (hs _) hu0) (Nat.mul_pos (hs _) hu0) (hs _)
          (hs _) (Elements.Book7.proposition_17 hu0 (hs _) (hs _)).symm (hrat j)
    · -- numbers `t` in the same ratios: the first of them are `s` taken some `m` times
      obtain ⟨m, hm⟩ := hmeas (fun i => t i.castSucc) (fun _ => ht _) (fun _ => hrt _)
      -- `e`, `f` are the least, so they measure the last two of `t` an equal number of
      -- times, `w` [Prop. 7.20]
      obtain ⟨w, hw₁, hw₂⟩ := Elements.Book7.proposition_20 (ht _) (ht _) he hf
        (hl (Fin.last n)) (hrt (Fin.last n)).symm
      -- the last of `s` and `e` both measure the last but one of `t`, so `l` does
      -- [Prop. 7.35]
      obtain ⟨z, hz⟩ := Elements.Book7.proposition_35 ⟨hl0, ⟨u, hu⟩, ⟨v, hv⟩, hlmin⟩
        ⟨m, hm (Fin.last n)⟩ ⟨w, hw₁⟩
      -- so `m` is `u` taken `z` times, and `w` is `v` taken `z` times (associativity
      -- -- Missed by Euclid.)
      have hmuz : m = u * z := Nat.eq_of_mul_eq_mul_left hsl (by
        rw [← hm (Fin.last n), hz, hu, Nat.mul_assoc])
      have hwvz : w = v * z := Nat.eq_of_mul_eq_mul_left he (by
        rw [← hw₁, hz, hv, Nat.mul_assoc])
      -- so `t` is the new numbers taken `z` times (associativity -- Missed by Euclid.)
      refine ⟨z, fun i => ?_⟩
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        rw [← Fin.succ_last, hw₂, hwvz, Nat.mul_assoc]
      | cast j =>
        simp only [Fin.lastCases_castSucc]
        rw [hm j, hmuz, Nat.mul_assoc]

/--
For any multitude whatsoever of given ratios, of `p i` to `q i` in least numbers, to find
the least numbers continuously proportional in these ratios. Euclid takes three ratios;
the construction adds one ratio at a time, so it is for any multitude. The numbers found
measure any others in the same ratios, so none are less: if they were, the greater would
measure the lesser.
-/
theorem proposition_4 {n : ℕ} {p q : Fin n → ℕ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hl : ∀ i, Least (p i) (q i)) :
    ∃ s : Fin (n + 1) → ℕ, (∀ i, 0 < s i) ∧
      (∀ i, s i.castSucc ∶ s i.succ ∷ p i ∶ q i) ∧ LeastSeq s := by
  obtain ⟨s, hs, hrat, hmeas⟩ := exists_continued_measuring hp hq hl
  refine ⟨s, hs, hrat, fun t ht hts hlt => ?_⟩
  -- numbers `t` less than `s`, in the same ratios, are measured by `s`
  obtain ⟨m, hm⟩ := hmeas t ht fun i =>
    proportion_trans (ht _) (ht _) (hs _) (hs _) (hts i) (hrat i)
  -- the greater measuring the lesser: impossible
  exact not_measures_of_lt (ht 0) (hlt 0) ⟨m, hm 0⟩

end Elements.Book8
