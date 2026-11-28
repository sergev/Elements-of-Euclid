import Elements.Book10.Prop037

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/--
Two medial areas incommensurable with one another make an irrational area: applied to a
rational line, they make rational breadths incommensurable in length with it [Prop.
10.22], and with one another [Props. 6.1, 10.11]; so the whole breadth is a binomial,
irrational [Prop. 10.36], and the rectangle contained by a rational and an irrational line
is irrational [Prop. 10.20]. 10.38's and 10.41's argument.
-/
theorem medial_add_medial {S T : Area} (hS : MedialArea ρ S) (hT : MedialArea ρ T)
    (h : ¬ Commensurable S T) : ¬ RationalArea ρ (S + T) := by
  obtain ⟨a, ha⟩ := Area.apply ρ S
  obtain ⟨b, hb⟩ := Area.apply ρ T
  obtain ⟨har, -⟩ := proposition_22' hS (Rational.self ρ) ha
  obtain ⟨hbr, -⟩ := proposition_22' hT (Rational.self ρ) hb
  have hab : ¬ Commensurable a b := by
    have h₁ := rect_proportion' a b ρ
    rw [ha, hb] at h₁
    exact (proposition_11 h₁ Area.divisible Length.divisible).2 h
  have h₁ := proposition_36 har hbr ⟨har.inSquare_of hbr, hab⟩
  rw [← ha, ← hb, ← rect_add]
  exact fun h' => h₁ (proposition_20 (Rational.self ρ) h' rfl).1

/-- If two medial lines commensurable in square only, containing a medial area, are added
together, the whole is irrational: let it be called a second bimedial
(`SecondBimedial`). -/
theorem proposition_38 {x y : Length} (hx : Medial ρ x) (_hy : Medial ρ y)
    (h : InSquareOnly x y) (hr : MedialArea ρ (rect x y)) : ¬ Rational ρ (x + y) := by
  -- the squares are medial [Props. 10.15, 10.23 corr.], and twice the rectangle
  have h₁ : MedialArea ρ (sq x + sq y) := proposition_23_corollary hx
    (proposition_15.1 h.1).1
  -- they are incommensurable [Props. 10.21 lem., 10.11, 10.15, 10.6, 10.13]
  have h₂ := h.squares_twice_rect
  -- the square on the whole is irrational, and so the whole [Prop. 2.4, Def. 10.4]
  have h₃ := medial_add_medial h₁ hr.twice h₂
  rw [← sq_add] at h₃
  exact fun h' => h₃ h'.sq_rational

end Elements.Book10
