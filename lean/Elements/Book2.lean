import Elements.Book2.Lemmas
import Elements.Book2.Prop01
import Elements.Book2.Prop02
import Elements.Book2.Prop03
import Elements.Book2.Prop04
import Elements.Book2.Prop05
import Elements.Book2.Prop06
import Elements.Book2.Prop07
import Elements.Book2.Prop08
import Elements.Book2.Prop09
import Elements.Book2.Prop10
import Elements.Book2.Prop11
import Elements.Book2.Prop12
import Elements.Book2.Prop13
import Elements.Book2.Prop14

/-
Book 2: geometric algebra.

Convention. "The rectangle contained by AB and CD" is written `|(a─b)| * |(c─d)|`,
"the square on AB" `|(a─b)| * |(a─b)|`, "twice" `2 * …`, as in Prop. 1.47.
System E's `rectangle_area` turns the area of a constructed rectangle into such a product.

With lengths added by `between`, Props. 2.1–2.10 are algebraic identities, and
`euclid_finish` can prove them with no figure at all. The proofs here do not take
that shortcut: they build Euclid's figure and argue with its areas, as he does.

Trial statements (proved bare by the solvers, to be proved Euclid's way):

  2.1: ∀ (a₁ a₂ b c d e : Point), a₁ ≠ a₂ ∧ between b d c ∧ between d e c →
         |(a₁─a₂)| * |(b─c)| = |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)|
  2.4: ∀ (a b c : Point), between a c b →
         |(a─b)| * |(a─b)| = |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)

In 2.1 the uncut line A is a separate segment a₁a₂.
-/
