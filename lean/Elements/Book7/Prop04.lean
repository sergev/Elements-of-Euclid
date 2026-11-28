import Elements.Book7.Prop03

namespace Elements.Book7

/-- Any number `b` is either part or parts of any greater number `a`. -/
theorem proposition_4 {a b : ℕ} (hb : 1 < b) (hba : b < a) :
    (∃ n, PartOf b a n) ∨ (∃ m n, PartsOf b a m n) := by
  by_cases hp : PrimeTo a b
  · -- prime to one another: each of the units in `b` is some part of `a`
    exact Or.inr ⟨b, a, hb, hba, 1, (Nat.one_mul b).symm, (Nat.one_mul a).symm⟩
  by_cases hm : b ∣ a
  · -- `b` measures `a`: it is part of it
    obtain ⟨n, hn⟩ := hm
    refine Or.inl ⟨n, ?_, hn⟩
    rcases n with _ | _ | n
    · rw [Nat.mul_zero] at hn
      omega
    · rw [Nat.mul_one] at hn
      omega
    · omega
  · -- the greatest common measure `d` of `a` and `b` [Prop. 7.2]
    obtain ⟨d, -, ⟨⟨n, hn⟩, ⟨m, hm'⟩, -⟩⟩ := proposition_2 (by omega) (by omega) hp
    -- `b` divided into `m` numbers equal to `d`, each a part of `a`
    refine Or.inr ⟨m, n, ?_, ?_, d, hm', hn⟩
    · rcases m with _ | _ | m
      · rw [Nat.mul_zero] at hm'
        omega
      · rw [Nat.mul_one] at hm'
        exact absurd ⟨n, hm' ▸ hn⟩ hm
      · omega
    · exact Nat.lt_of_mul_lt_mul_left (hm' ▸ hn ▸ hba)

end Elements.Book7
