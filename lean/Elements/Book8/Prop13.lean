import Elements.Book8.Prop12

namespace Elements.Book8

open Elements.Book7

/-- Euclid's step in 8.13: if `a ∶ b ∷ c ∶ d`, their squares are proportional. `a * a`,
`b * a`, `b * b` are continuously proportional in the ratio of `a` to `b`, and `c * c`,
`d * c`, `d * d` in that of `c` to `d`, the same; so, via equality, as `a * a` is to
`b * b`, so `c * c` to `d * d` [Prop. 7.14]. -/
theorem squares_proportion {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h : a ∶ b ∷ c ∶ d) : a * a ∶ b * b ∷ c * c ∶ d * d := by
  obtain ⟨h₁, h₂⟩ := squares_continued ha hb
  obtain ⟨h₃, h₄⟩ := squares_continued hc hd
  have hc' := Nat.mul_pos hc hc
  have hdc := Nat.mul_pos hd hc
  have hd' := Nat.mul_pos hd hd
  exact Elements.Book7.proposition_14' (Nat.mul_pos ha ha) (Nat.mul_pos hb ha)
    (Nat.mul_pos hb hb) hc' hdc hd'
    (proportion_trans (Nat.mul_pos ha ha) (Nat.mul_pos hb ha) ha hb h₁
      (proportion_trans ha hb hc hd h h₃.symm))
    (proportion_trans (Nat.mul_pos hb ha) (Nat.mul_pos hb hb) ha hb h₂
      (proportion_trans ha hb hc hd h h₄.symm))

/-- The same for cubes, with four numbers each: `a * a * a`, `b * a * a`, `b * a * b`,
`b * b * b` in the ratio of `a` to `b`, and the same for `c`, `d` [Props. 8.12,
7.14]. -/
theorem cubes_proportion {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h : a ∶ b ∷ c ∶ d) :
    a * a * a ∶ b * b * b ∷ c * c * c ∶ d * d * d := by
  obtain ⟨h₁, h₂, h₃⟩ := cubes_continued ha hb
  obtain ⟨h₄, h₅, h₆⟩ := cubes_continued hc hd
  have p₁ := Nat.mul_pos (Nat.mul_pos ha ha) ha
  have p₂ := Nat.mul_pos (Nat.mul_pos hb ha) ha
  have p₃ := Nat.mul_pos (Nat.mul_pos hb ha) hb
  have p₄ := Nat.mul_pos (Nat.mul_pos hb hb) hb
  have q₁ := Nat.mul_pos (Nat.mul_pos hc hc) hc
  have q₂ := Nat.mul_pos (Nat.mul_pos hd hc) hc
  have q₃ := Nat.mul_pos (Nat.mul_pos hd hc) hd
  have q₄ := Nat.mul_pos (Nat.mul_pos hd hd) hd
  -- each of the one is to the next as each of the other to the next
  have k : ∀ {x y z w}, 0 < x → 0 < y → x ∶ y ∷ a ∶ b → z ∶ w ∷ c ∶ d → x ∶ y ∷ z ∶ w :=
    fun hx hy hxy hzw =>
      proportion_trans hx hy ha hb hxy (proportion_trans ha hb hc hd h hzw.symm)
  exact Elements.Book7.proposition_14' p₁ p₃ p₄ q₁ q₃ q₄
    (Elements.Book7.proposition_14' p₁ p₂ p₃ q₁ q₂ q₃ (k p₁ p₂ h₁ h₄) (k p₂ p₃ h₂ h₅))
    (k p₃ p₄ h₃ h₆)

/--
If there are any multitude whatsoever of continuously proportional numbers `a`, and each
makes some number by multiplying itself, the numbers created are continuously
proportional; and so are those the original numbers make by multiplying the created.
Euclid takes three numbers and says "similarly"; each pair is the same step, so the
statement is for any multitude.
-/
theorem proposition_13 {n : ℕ} {a : Fin (n + 1) → ℕ} (ha : ∀ i, 0 < a i)
    (hc : Continued a) :
    Continued (fun i => a i * a i) ∧ Continued (fun i => a i * a i * a i) :=
  ⟨fun i => squares_proportion (ha _) (ha _) (ha 0) (ha 1) (hc i),
    fun i => cubes_proportion (ha _) (ha _) (ha 0) (ha 1) (hc i)⟩

end Elements.Book8
