import SystemE
import Elements.Book1.Prop14
import Elements.Book1.Prop29
import Elements.Book6.Prop06

namespace Elements.Book6

open Elements.Book5

/--
If two triangles `abc`, `dce`, with two sides proportional to two sides,
`ab : ac :: dc : de`, are placed together at the angle `c` so that the corresponding
sides are parallel, `AB` to `DC` and `AC` to `DE`, then the remaining sides `bc`, `ce` are
straight-on.
-/
theorem proposition_32 : ∀ (a b c d e : Point) (AB BC CA DC CE ED : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d c e DC CE ED ∧ ¬(AB.intersectsLine DC) ∧
  ¬(CA.intersectsLine ED) ∧ b.opposingSides d CA ∧ a.opposingSides e DC ∧
  (a─b) ∶ (a─c) ∷ (d─c) ∶ (d─e) → between b c e :=
by
  euclid_intros
  -- the alternate angles `BAC`, `ACD` are equal, and `CDE`, `ACD` [Prop. 1.29]
  euclid_apply (Elements.Book1.proposition_29_alternate b d a c AB DC CA)
  euclid_apply (Elements.Book1.proposition_29_alternate a e c d CA ED DC)
  -- `ABC` is equiangular to `DCE` [Prop. 6.6]: `ABC` is equal to `DCE`
  have := proposition_6 a b c d c e AB BC CA DC CE ED ⟨by euclid_finish, by euclid_finish,
    by euclid_finish, ‹(a─b) ∶ (a─c) ∷ (d─c) ∶ (d─e)›.congr (by size_perm) rfl
      (by size_perm) rfl⟩
  -- the whole `ACE` is equal to `ABC`, `BAC`; add `ACB`: two right angles [Prop. 1.32]
  euclid_apply (triangle_angles a b c AB BC CA)
  euclid_apply (sum_angles_onlyif c a e d CA CE)
  -- so `BC` is straight-on to `CE` [Prop. 1.14]
  euclid_apply (Elements.Book1.proposition_14 a c b e CA BC CE)
  euclid_finish

end Elements.Book6
