import Elements.Book8.Prop05

namespace Elements.Book8

open Elements.Book7

/-- Continuously proportional numbers whose first does not measure the second: the first
does not measure the last. Euclid's argument, for `A`, `B`, `C`. -/
theorem not_measures_last {m : ℕ} {c : Fin (m + 1) → ℕ} (hc : ∀ i, 0 < c i)
    (hcon : Continued c) (h : ¬ c 0 ∣ c 1) : ¬ c 0 ∣ c (Fin.last m) := by
  intro hlast
  -- as many as `c`, let so many least numbers `f` be taken, of those having the same
  -- ratio [Props. 7.33, 8.2]
  obtain ⟨e, f, he, hf, hef, hlef⟩ := Elements.Book7.proposition_33' (hc 0) (hc 1)
  obtain ⟨hp, hpin, hpl⟩ := proposition_2 he hf hlef m
  have hcin : ContinuedIn c e f :=
    fun i => proportion_trans (hc _) (hc _) (hc 0) (hc 1) (hcon i) hef.symm
  have hsame := hpin.sameRatios he hf hc hcin
  -- via equality, as the first of `c` is to the last, so the first of `f` to the last
  -- [Prop. 7.14]
  have h14 := hsame.extremes hp hc (Fin.last m)
  -- as `c 0` is to `c 1`, so `f 0` to `f 1`: and `c 0` does not measure `c 1`, so `f 0`
  -- does not measure `f 1` [Def. 7.20]
  have h01 : ¬ powers e f m 0 ∣ powers e f m 1 := fun hd =>
    h (measures_of_proportion (hp 0) (hp 1) (hc 0) (hc 1)
      (hsame.extremes hp hc 1).symm hd)
  -- so `f 0` is not a unit, for a unit measures all numbers
  have h1 : powers e f m 0 ≠ 1 := fun h1 => h01 (by rw [h1]; exact unit_measures _)
  -- `f 0` and the last are prime to one another [Prop. 8.3], so `f 0` does not measure
  -- the last; nor does `c 0` [Def. 7.20]
  have hprime := proposition_3 hp (hpin.continued hp he hf) hpl
  exact h1 (hprime _ (measures_self _)
    (measures_of_proportion (hc 0) (hc _) (hp 0) (hp _) h14 hlast))

/--
If there are any multitude whatsoever of continuously proportional numbers, and the first
does not measure the second, no other will measure any other: no `a i` measures a later
`a j`. (A later one may measure an earlier, as `2` measures `4` in `4`, `2`, `1`: Euclid
means the earlier.) He shows that `A` does not measure `C`, and says "similarly": `a i`,
…, `a j` are continuously proportional, and the first does not measure the second.
-/
theorem proposition_6 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hc : Continued a) (h : ¬ a 0 ∣ a 1) (i j : Fin (n + 1)) (hij : i < j) :
    ¬ a i ∣ a j := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij : i < j := hij
  -- `a i`, …, `a j`
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  let c : Fin (m + 2) → ℕ := fun k => a ⟨i + k, by omega⟩
  have hc' : ∀ k, 0 < c k := fun k => ha _
  -- each is to the next as `a 0` to `a 1`
  have hstep : ∀ k (hk : k < n), a ⟨k, by omega⟩ ∶ a ⟨k + 1, by omega⟩ ∷ a 0 ∶ a 1 :=
    fun k hk => hc ⟨k, hk⟩
  have hcin : ContinuedIn c (a 0) (a 1) := fun k => hstep (i + k) (by omega)
  have hc0 : c 0 = a ⟨i, hi⟩ := congrArg a (Fin.ext (by simp))
  have hc1 : c 1 = a ⟨i + 1, by omega⟩ := congrArg a (Fin.ext (by simp))
  -- `a i` does not measure `a (i + 1)`, for `a 0` does not measure `a 1` [Def. 7.20]
  have h01 : ¬ c 0 ∣ c 1 := fun hd => h (measures_of_proportion (hc' 0) (hc' 1)
    (ha 0) (ha 1) (by rw [hc0, hc1]; exact hstep i (by omega)) hd)
  have := not_measures_last hc' (hcin.continued hc' (ha 0) (ha 1)) h01
  rwa [hc0] at this

end Elements.Book8
