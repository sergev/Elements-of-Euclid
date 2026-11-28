import SystemE
import Elements.Book1.Prop04
import Elements.Book6.Prop04

namespace Elements.Book6

open Elements.Book5

/--
If two triangles `abc`, `def` have one angle equal to one angle, `bac` to `edf`, and the
sides about the equal angles proportional, `ba : ac :: ed : df`, they are equiangular,
with the angles which corresponding sides subtend equal.
-/
theorem proposition_6 : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧ ∠ b:a:c = ∠ e:d:f ∧
  (b─a) ∶ (a─c) ∷ (e─d) ∶ (d─f) → equiangularTriangles a b c d e f :=
by
  euclid_intros
  -- on `DF`, away from `e`, the angles `FDG`, `DFG` equal to `BAC`, `ACB` [Prop. 1.23];
  -- the remaining angle at `g` is equal to that at `b` [Prop. 1.32]
  euclid_apply (extend_point DE e d) as y
  euclid_apply (triangle_on b a c d f y AB CA BC FD) as g
  euclid_apply (line_from_points d g) as DG
  euclid_apply (line_from_points f g) as FG
  -- so `ABC` is equiangular to `DGF`: `BA : AC :: GD : DF` [Prop. 6.4]
  obtain ⟨-, h₁, -, -⟩ := proposition_4 b a c g d f AB CA BC DG FD FG
    ⟨by euclid_finish, by euclid_finish, by euclid_finish⟩
  -- so `ED : DF :: GD : DF` [Prop. 5.11], and `ED` is equal to `GD` [Prop. 5.9]
  have e₁ : |(e─d)| = |(g─d)| :=
    (‹(b─a) ∶ (a─c) ∷ (e─d) ∶ (d─f)›.symm.trans h₁).eq_left rfl
  -- and `DF` is common, and the angle `EDF` is equal to `GDF`: the triangles `DEF`, `DGF`
  -- are equal in all respects [Prop. 1.4]
  euclid_apply (Elements.Book1.proposition_4 d e f d g f DE EF FD DG FG FD)
  euclid_finish

end Elements.Book6
