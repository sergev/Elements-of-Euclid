import Elements.Book9.Prop35

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/-- The numbers doubled from the unit: each measures the last, and each is less than any
after it [Prop. 9.11 corollary]. -/
theorem powers_two_measures (n : ℕ) :
    (∀ i, powers 1 2 n i ∣ powers 1 2 n (Fin.last n)) ∧
      ∀ i j, i < j → powers 1 2 n i < powers 1 2 n j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => ⟨1, rfl⟩, fun i j hij => by
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j] at hij; simp at hij⟩
  obtain ⟨hcon, h0, h1⟩ := powers_two_continued n
  have h1' : 1 < powers 1 2 n 1 := by rw [h1 hn]; omega
  have hpos := powers_pos Nat.one_pos (show 0 < 2 by omega) n
  constructor
  · intro i
    have := proposition_11_corollary hcon h0 h1' (i := i.val) (j := n) (by omega) le_rfl
    rw [Fin.eta] at this
    exact ⟨_, this⟩
  · intro i j hij
    have hij' : i.val < j.val := hij
    have h := proposition_11_corollary hcon h0 h1' (i := i.val) (j := j.val) (by omega)
      (by omega)
    rw [Fin.eta, Fin.eta] at h
    have := unit_one_lt hcon h0 h1' (k := j.val - i.val) (by omega) (by omega)
    rw [h]
    exact lt_mul (hpos _) this

/--
If any multitude of numbers are set out from a unit in double proportion until all of them
added together make a prime, and the sum multiplied by the last makes some number, the
number made is perfect (Def. 7.22): the sum of its parts.

The numbers are `powers 1 2 n`, the unit and the dyad among them; the sum `e` is
`sum (powers 1 2 n)`, and the number made is the last `d` multiplied by `e`. Euclid takes
as many numbers doubled from `e` as there are from the dyad to `d`, and the number made
is double the last of them; here they are each of `powers 1 2 n` multiplied by `e`
[Prop. 7.17], the number made being the last. By 9.35 it is the sum of the unit, the
numbers doubled from it, and those doubled from `e`; and it is measured by no others
(9.13, 7.19, 7.20). So its parts are those numbers, and their sum is the number
(`sum_parts`).
-/
theorem proposition_36 {n : ℕ} (hp : PrimeNumber (sum (powers 1 2 n))) :
    Perfect (powers 1 2 n (Fin.last n) * sum (powers 1 2 n)) := by
  -- with the unit alone, the sum is not prime
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have := hp.1; exact absurd this (by show ¬ 1 < 1; omega)
    · omega⟩
  obtain ⟨hcon, h0, h1⟩ := powers_two_continued (m + 1)
  have h1 := h1 (by omega)
  have hpos := powers_pos Nat.one_pos (show 0 < 2 by omega) (m + 1)
  obtain ⟨hPD, hPlt⟩ := powers_two_measures (m + 1)
  have hED := sum_powers_two (m + 1)
  rw [powers_last] at hED
  set P := powers 1 2 (m + 1) with hPdef
  set E := sum P with hEdef
  set D := P (Fin.last (m + 1)) with hDdef
  have hp2 : PrimeNumber (P 1) := by rw [h1]; exact prime_two
  have hD : 2 ≤ D := by
    have := hPlt 0 (Fin.last _) (Fin.last_pos); rw [h0] at this; omega
  -- the sum is a unit less than `d` doubled
  replace hED : E + 1 = D + D := by omega
  have hE0 : 0 < E := by omega
  have hE1 : 1 < E := hp.1
  -- let `e` multiplying each of them make `e`, `e` doubled, …, the last being `d * e`:
  -- they are continuously proportional in double proportion [Prop. 7.17]
  let c : Fin (m + 2) → ℕ := fun i => P i * E
  have hc : ∀ i, 0 < c i := fun i => Nat.mul_pos (hpos i) hE0
  have hccon : Continued c := fun i => by
    have h17 := Elements.Book7.proposition_17 hE0 (hpos i.castSucc) (hpos i.succ)
    have h17' := Elements.Book7.proposition_17 hE0 (hpos 0) (hpos 1)
    exact proportion_trans (hc _) (hc _) (hpos _) (hpos _) h17.symm
      (proportion_trans (hpos _) (hpos _) (hpos 0) (hpos 1) (hcon i) h17')
  have hc0 : c 0 = E := by show P 0 * E = E; rw [h0, Nat.one_mul]
  have hc1 : c 1 = E + E := by show P 1 * E = E + E; rw [h1]; omega
  -- as the excess of the second is to the first, so the excess of the last to all
  -- before it [Prop. 9.35]; and the excess of the second is the first, so the excess of
  -- the last is all before it
  have h35 := proposition_35 hc hccon (by omega)
  rw [hc0, hc1, show E + E - E = E by omega] at h35
  set S := sum (fun i : Fin (m + 1) => c i.castSucc) with hSdef
  have hS0 : 0 < S := sum_pos fun i => hc _
  have hFG : E < D * E := by
    have := lt_mul hE0 (show 1 < D by omega)
    rwa [Elements.Book7.proposition_16 (show 0 < D by omega) hE0] at this
  have hlast : c (Fin.last (m + 1)) = D * E := rfl
  rw [hlast] at h35
  have hSE : S = D * E - E := by
    rw [Elements.Book7.proposition_19 hE0 hE0 (by omega) hS0] at h35
    exact Nat.eq_of_mul_eq_mul_right hE0 h35
  -- the parts: the unit and the numbers doubled from it, and those doubled from `e`
  let L₁ := List.ofFn P
  let L₂ := List.ofFn fun i : Fin (m + 1) => c i.castSucc
  have hsum : (L₁ ++ L₂).sum = D * E := by
    rw [List.sum_append, sum_ofFn, sum_ofFn]
    show E + S = D * E
    omega
  -- the numbers doubled from `e`, but the last, are less than the last of them
  have hc_lt : ∀ i : Fin (m + 1), c i.castSucc < D * E := fun i =>
    Nat.mul_lt_mul_of_pos_right (hPlt _ _ (Fin.castSucc_lt_last i)) hE0
  have hmem : ∀ x, x ∈ L₁ ++ L₂ ↔ x < D * E ∧ x ∣ D * E := by
    intro x
    rw [List.mem_append, List.mem_ofFn, List.mem_ofFn]
    constructor
    · -- all of them measure the number made, and are less
      rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Nat.lt_of_le_of_lt (le_of_measures (by omega) (hPD i)) (by
          have := lt_mul (show 0 < D by omega) hE1; omega),
          measures_trans (hPD i) ⟨E, rfl⟩⟩
      · exact ⟨hc_lt i, Nat.mul_dvd_mul_right (hPD _) E⟩
    · -- and no others measure it
      rintro ⟨hx, q, hq⟩
      have hx0 : 0 < x := Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hq; omega
      have hq0 : 0 < q := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hq; omega
      -- `x` multiplying `q` makes what `e` multiplying `d` makes: as `e` is to `q`, so
      -- `x` is to `d` [Prop. 7.19]
      have hprop : E ∶ q ∷ x ∶ D := proportion_of_mul_eq hE0 (by omega) hq0 hx0 (by
        rw [Elements.Book7.proposition_16 (by omega) hE0, hq,
          Elements.Book7.proposition_16 hx0 hq0])
      -- if possible, let `x` be none of them; then it does not measure `d`, which is
      -- measured by none but the numbers doubled from the unit [Prop. 9.13]
      by_contra hnot
      have hxD : ¬ x ∣ D := fun h => by
        obtain ⟨i, hi⟩ := proposition_13 hcon h0 hp2 h
        exact hnot (Or.inl ⟨i, hi.symm⟩)
      -- so `e` does not measure `q` [Def. 7.20]; `e`, prime, is prime to `q`
      -- [Prop. 7.29], and `e`, `q` are the least [Prop. 7.21]: `e` measures `x` as `q`
      -- measures `d` [Prop. 7.20]
      have hEq : ¬ E ∣ q := fun h =>
        hxD (measures_of_proportion hE0 hq0 hx0 (by omega) hprop h)
      obtain ⟨t, hxt, hDt⟩ := Elements.Book7.proposition_20 hx0 (by omega) hE0 hq0
        (Elements.Book7.proposition_21 hE0 hq0
          (Elements.Book7.proposition_29 hp hEq).symm) hprop
      -- `q` measures `d`, so it is some `P j` [Prop. 9.13], not the unit, as `x` is less
      -- than the number made
      obtain ⟨j, rfl⟩ := proposition_13 hcon h0 hp2 ⟨t, hDt⟩
      have hj : 0 < j.val := Nat.pos_of_ne_zero fun h => by
        rw [show j = 0 from Fin.ext h, h0, Nat.mul_one] at hq; omega
      -- and `P j` measures `d` according to `P (m + 1 - j)` [Prop. 9.11 corollary]; so
      -- `x` is `e` multiplying it [Prop. 7.19], one of them: impossible
      have h11 := proposition_11_corollary hcon h0 (by rw [h1]; omega) (i := j.val)
        (j := m + 1) (by omega) le_rfl
      rw [Fin.eta] at h11
      have ht : t = P ⟨m + 1 - j.val, by omega⟩ :=
        Nat.eq_of_mul_eq_mul_left (hpos j) (hDt.symm.trans h11)
      refine hnot (Or.inr ⟨⟨m + 1 - j.val, by omega⟩, ?_⟩)
      rw [hxt, ht]
      exact Elements.Book7.proposition_16 hE0 (hpos _)
  -- they are distinct: those doubled from the unit, and from `e`, increase; and none of
  -- the first is one of the second, else `e` would measure `d`, and be the dyad
  -- [Prop. 9.13]
  have hnodup : (L₁ ++ L₂).Nodup := by
    rw [List.nodup_append]
    refine ⟨nodup_ofFn_of_lt hPlt, nodup_ofFn_of_lt fun i j hij =>
      Nat.mul_lt_mul_of_pos_right (hPlt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij)) hE0,
      ?_⟩
    intro x hx y hy hxy
    rw [List.mem_ofFn] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hEd : E ∣ D := measures_trans ⟨P j.castSucc, by
      rw [hxy]; exact Elements.Book7.proposition_16 hE0 (hpos _)⟩ (hPD i)
    obtain ⟨k, hk⟩ := proposition_13 hcon h0 hp2 hEd
    rcases Nat.eq_zero_or_pos k.val with hk0 | hk0
    · rw [show k = 0 from Fin.ext hk0, h0] at hk; omega
    · obtain ⟨h, -, hh⟩ := powers_two_even k hk0
      rcases hp.2 2 ⟨h, by rw [hk]; show powers 1 2 (m + 1) k = 2 * h; omega⟩ with h2 | h2
        <;> omega
  refine ⟨by have := lt_mul (show 0 < D by omega) hE1; omega, ?_⟩
  rw [sum_parts hnodup hmem, hsum]

end Elements.Book9
