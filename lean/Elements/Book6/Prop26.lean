import SystemE
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book6.Prop24

namespace Elements.Book6

open Elements.Book5

/--
If from a parallelogram `abdc` (vertices `a`, `b`, `c`, `d` in order) a parallelogram
`aefg` is taken away, similar and similarly laid down to the whole, with the common angle
`dab`, it is about the same diagonal: `f` is on `ac`.
-/
theorem proposition_26 : ∀ (a b c d e f g : Point) (AB CD DA BC EF FG : Line),
  formParallelogram a b d c AB CD DA BC ∧ formParallelogram a e g f AB FG DA EF ∧
  between a e b ∧ between a g d ∧ similarQuadrilaterals a b c d a e f g → between a f c :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_30 FG CD AB)
  euclid_apply (Elements.Book1.proposition_30 EF BC DA)
  -- if not, let `AHC` be the diagonal, `GF` produced meeting it at `h`, and `HK` drawn
  -- through `h` parallel to `AD` [Prop. 1.31]
  by_contra
  euclid_apply (line_from_points a c) as AC
  euclid_apply (parallel_meets a FG AB AC)
  euclid_apply (intersection_lines FG AC) as h
  euclid_assert between a h c
  euclid_apply (Elements.Book1.proposition_31 h a d DA) as KH
  euclid_apply (parallel_meets a KH DA AB)
  euclid_apply (intersection_lines KH AB) as k
  euclid_apply (Elements.Book1.proposition_30 KH BC DA)
  -- `ABCD` is about the same diagonal as `KG`: `DA : AB :: GA : AK` [Prop. 6.24]; and
  -- `DA : AB :: GA : AE`, by the similarity of `ABCD` and `EG`
  obtain ⟨-, h₁, -, -, -⟩ := proposition_24_one a b c d k h g AB CD DA BC KH FG
    (by euclid_finish)
  -- so `AE` is equal to `AK` [Props. 5.11, 5.9], the lesser to the greater: impossible
  have : |(a─k)| = |(a─e)| := (h₁.symm.trans ‹(d─a) ∶ (a─b) ∷ (g─a) ∶ (a─e)›).eq_right rfl
  euclid_assert between a k b
  have := proposition_1_ray_eq a k e AB (by euclid_finish)
  subst this
  euclid_assert KH = EF
  euclid_finish

end Elements.Book6
