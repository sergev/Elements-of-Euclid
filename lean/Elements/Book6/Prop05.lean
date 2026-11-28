import SystemE
import Elements.Book1.Prop08
import Elements.Book6.Prop04

namespace Elements.Book6

open Elements.Book5

/--
If two triangles `abc`, `def` have proportional sides, `ab : bc :: de : ef` and
`bc : ca :: ef : fd`, they are equiangular, with the angles which corresponding sides
subtend equal. Euclid also has `ba : ac :: ed : df`, which follows and is not used.
-/
theorem proposition_5 : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧
  (a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f) ∧ (b─c) ∶ (c─a) ∷ (e─f) ∶ (f─d) →
  equiangularTriangles a b c d e f :=
by
  euclid_intros
  -- on `EF`, away from `d`, the angles `FEG`, `EFG` equal to `ABC`, `ACB` [Prop. 1.23];
  -- the remaining angle at `g` is equal to that at `a` [Prop. 1.32]
  euclid_apply (extend_point DE d e) as y
  euclid_apply (triangle_on a b c e f y AB BC CA EF) as g
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  -- so `ABC` is equiangular to `GEF`: `AB : BC :: GE : EF` and `BC : CA :: EF : FG`
  -- [Prop. 6.4]
  obtain ⟨-, h₁, h₂, -⟩ := proposition_4 a b c g e f AB BC CA EG EF FG
    ⟨by euclid_finish, by euclid_finish, by euclid_finish⟩
  -- so `DE : EF :: GE : EF`, and `DE` is equal to `GE`; and `EF : FD :: EF : FG`, and
  -- `FD` is equal to `FG` [Props. 5.11, 5.9]
  have e₁ : |(d─e)| = |(g─e)| :=
    (‹(a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f)›.symm.trans h₁).eq_left rfl
  have e₂ : |(f─d)| = |(f─g)| :=
    (‹(b─c) ∶ (c─a) ∷ (e─f) ∶ (f─d)›.symm.trans h₂).eq_right rfl
  -- so the triangles `DEF`, `GEF` have their angles equal [Prop. 1.8]
  euclid_apply (Elements.Book1.proposition_8 d e f g e f DE EF FD EG EF FG)
  euclid_apply (Elements.Book1.proposition_8 e d f e g f DE FD EF EG FG EF)
  euclid_apply (Elements.Book1.proposition_8 f d e f g e FD DE EF FG EG EF)
  euclid_finish

end Elements.Book6
