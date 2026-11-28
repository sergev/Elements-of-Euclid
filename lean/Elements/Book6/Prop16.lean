import SystemE
import Elements.Book1.Prop01
import Elements.Book2.Lemmas
import Elements.Book6.Prop14

namespace Elements.Book6

open Elements.Book5

/--
The rectangles of Prop. 6.16, laid down as Prop. 6.14 takes them: `ab` and `be`, equal to
`cd`, straight-on; on `ab` the rectangle `pqab` with height `f₁f₂`, and on `be` the
rectangle `rsbe`, with height `e₁e₂`, on the other side (Book 2's `rectangle_on`).
-/
theorem proposition_16_figure : ∀ (a b c d e₁ e₂ f₁ f₂ : Point),
  a ≠ b ∧ c ≠ d ∧ e₁ ≠ e₂ ∧ f₁ ≠ f₂ →
  ∃ (e p q r s : Point) (PQ L AP BQ RS ES BR : Line),
  formParallelogram p q a b PQ L AP BQ ∧ formParallelogram s e r b ES BR RS L ∧
  between a b e ∧ q.opposingSides r L ∧ ∠ a:b:q = ∠ r:b:e ∧
  |(b─e)| = |(c─d)| ∧ |(r─b)| = |(e₁─e₂)| ∧ |(b─q)| = |(f₁─f₂)| ∧
  ▱ p:q:a:b = |(a─b)| * |(f₁─f₂)| ∧ ▱ s:e:r:b = |(c─d)| * |(e₁─e₂)| :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as L
  euclid_apply (lay_beyond a b c d L) as e
  euclid_apply (Elements.Book1.proposition_1 a b L) as x
  euclid_apply (Elements.Book2.rectangle_on a b x f₁ f₂ L) as (p, q, PQ, AP, BQ)
  euclid_apply (Elements.Book2.rectangle_on b e p e₁ e₂ L) as (r, s, RS, BR, ES)
  euclid_apply (parallelogram_area r s b e RS L BR ES)
  use e, p, q, r, s, PQ, L, AP, BQ, RS, ES, BR
  euclid_finish

/--
If four straight lines are proportional, `ab : cd :: e₁e₂ : f₁f₂`, the rectangle
contained by the outermost is equal to the rectangle contained by the middle two.
Rectangles are products of lengths, as in Book 2; the proof draws them.
-/
theorem proposition_16 : ∀ (a b c d e₁ e₂ f₁ f₂ : Point),
  (a─b) ∶ (c─d) ∷ (e₁─e₂) ∶ (f₁─f₂) →
  |(a─b)| * |(f₁─f₂)| = |(c─d)| * |(e₁─e₂)| :=
by
  euclid_intros
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := ‹(a─b) ∶ (c─d) ∷ (e₁─e₂) ∶ (f₁─f₂)›
  euclid_apply (proposition_16_figure a b c d e₁ e₂ f₁ f₂
    ⟨size_segment_pos.mp h₁, size_segment_pos.mp h₂, size_segment_pos.mp h₃,
      size_segment_pos.mp h₄⟩) as (e, p, q, r, s, PQ, L, AP, BQ, RS, ES, BR)
  -- `AB : BE :: RB : BQ`: the parallelograms are equiangular, with the sides about the
  -- equal angles reciprocally proportional; so they are equal [Prop. 6.14]
  have h₅ : (a─b) ∶ (b─e) ∷ (r─b) ∶ (b─q) :=
    ‹(a─b) ∶ (c─d) ∷ (e₁─e₂) ∶ (f₁─f₂)›.congr rfl ‹|(b─e)| = |(c─d)|›.symm
      ‹|(r─b)| = |(e₁─e₂)|›.symm ‹|(b─q)| = |(f₁─f₂)|›.symm
  euclid_apply (proposition_14' p b s a e q r PQ L AP BQ ES BR RS)
  euclid_finish

/--
If the rectangle contained by the outermost of four straight lines is equal to the
rectangle contained by the middle two, the four are proportional:
`ab : cd :: e₁e₂ : f₁f₂`.
-/
theorem proposition_16' : ∀ (a b c d e₁ e₂ f₁ f₂ : Point),
  a ≠ b ∧ c ≠ d ∧ e₁ ≠ e₂ ∧ f₁ ≠ f₂ ∧ |(a─b)| * |(f₁─f₂)| = |(c─d)| * |(e₁─e₂)| →
  (a─b) ∶ (c─d) ∷ (e₁─e₂) ∶ (f₁─f₂) :=
by
  euclid_intros
  euclid_apply (proposition_16_figure a b c d e₁ e₂ f₁ f₂ (by euclid_finish))
    as (e, p, q, r, s, PQ, L, AP, BQ, RS, ES, BR)
  -- the parallelograms `PB`, `SB` are equal and equiangular: `AB : BE :: RB : BQ`
  -- [Prop. 6.14], that is, `AB : CD :: E : F`
  have h := proposition_14 p b s a e q r PQ L AP BQ ES BR RS (by euclid_finish)
  exact h.congr rfl ‹_› ‹_› ‹_›

end Elements.Book6
