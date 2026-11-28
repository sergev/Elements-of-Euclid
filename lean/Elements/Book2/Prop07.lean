import SystemE
import Elements.Book2.Prop04

namespace Elements.Book2

theorem proposition_7 : ∀ (a b c : Point),
  between a c b →
  |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| = 2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)| :=
by
  euclid_intros
  -- the figure of Prop. 2.4
  euclid_apply (proposition_4_figure a b c) as (d, e, f, g, h, k)
  -- AG = GE; add CK: AK = CE
  euclid_assert ▱ h:k:a:b = ▱ f:e:c:b
  -- the gnomon and CK are twice AK
  euclid_assert ▱ h:g:a:c + ▱ g:k:c:b + ▱ k:g:e:f + ▱ g:k:c:b = 2 * ▱ h:k:a:b
  -- add HF, the square on AC
  euclid_assert ▱ d:e:a:b + ▱ g:k:c:b = 2 * ▱ h:k:a:b + ▱ d:f:h:g
  euclid_finish

end Elements.Book2
