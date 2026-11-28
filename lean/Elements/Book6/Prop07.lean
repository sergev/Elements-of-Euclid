import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop13
import Elements.Book1.Prop17
import Elements.Book1.Prop23
import Elements.Book6.Prop04

namespace Elements.Book6

open Elements.Book5

/--
Prop. 6.7 when the angle `abc` is greater than `def`: impossible. Construct `abg` equal to
`def` [Prop. 1.23], `g` on `ac`; `abg` is equiangular to `def` [Prop. 1.32], so
`ab : bg :: de : ef` [Prop. 6.4], and `bg` is equal to `bc` [Props. 5.11, 5.9], and the
angle `bgc` to `bcg` [Prop. 1.5].
-/
theorem proposition_7_greater : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧ ∠ b:a:c = ∠ e:d:f ∧
  (a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f) ∧
  ((∠ a:c:b < ∟ ∧ ∠ d:f:e < ∟) ∨ (¬(∠ a:c:b < ∟) ∧ ¬(∠ d:f:e < ∟))) →
  ¬(∠ a:b:c > ∠ d:e:f) :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_23_side b a e d f c AB DE EF) as p
  euclid_apply (line_from_points b p) as BP
  euclid_apply (crossbar a b c p AB BC CA BP) as g
  euclid_apply (equal_angles b p g a a BP AB)
  euclid_apply (equal_angles a c g b b CA AB)
  euclid_apply (line_from_points b g) as BG
  euclid_apply (triangle_angles a b g AB BG CA)
  euclid_apply (triangle_angles d e f DE EF FD)
  -- the remaining angle `AGB` is equal to `DFE` [Prop. 1.32]: `ABG`, `DEF` are
  -- equiangular, and `AB : BG :: DE : EF` [Prop. 6.4]
  obtain ⟨-, h₁, -, -⟩ := proposition_4 a b g d e f AB BG CA DE EF FD
    ⟨by euclid_finish, by euclid_finish, by euclid_finish⟩
  -- so `AB : BC :: AB : BG` [Prop. 5.11], and `BC` is equal to `BG` [Prop. 5.9]
  have : |(b─c)| = |(b─g)| :=
    (‹(a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f)›.trans h₁.symm).eq_right rfl
  -- so the angle `BCG` is equal to `BGC` [Prop. 1.5]
  euclid_apply (Elements.Book1.proposition_5' b c g BC CA BG)
  euclid_apply (equal_angles c b b a g BC CA)
  euclid_apply (Elements.Book1.proposition_13 b g a c BG CA)
  rcases ‹(∠ a:c:b < ∟ ∧ ∠ d:f:e < ∟) ∨ (¬(∠ a:c:b < ∟) ∧ ¬(∠ d:f:e < ∟))› with h | h
  · -- the angle at `c` is less than a right angle, so `BGC` is too, and `AGB` greater
    -- [Prop. 1.13]; but it is equal to the angle at `f`, less than a right angle
    euclid_finish
  · -- the angle at `c` is not less than a right angle: so neither is `BGC`, and two
    -- angles of the triangle `BGC` are not less than two right angles [Prop. 1.17]
    euclid_apply (Elements.Book1.proposition_17 b g c BG CA BC)
    euclid_finish

/--
If two triangles `abc`, `def` have one angle equal to one angle, `bac` to `edf`, the sides
about other angles proportional, `ab : bc :: de : ef`, and the remaining angles, at `c`
and `f`, both less than, or both not less than, right angles, they are equiangular, with
the angles about which the sides are proportional equal.
-/
theorem proposition_7 : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧ ∠ b:a:c = ∠ e:d:f ∧
  (a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f) ∧
  ((∠ a:c:b < ∟ ∧ ∠ d:f:e < ∟) ∨ (¬(∠ a:c:b < ∟) ∧ ¬(∠ d:f:e < ∟))) →
  equiangularTriangles a b c d e f :=
by
  euclid_intros
  -- if `ABC` is not equal to `DEF`, one of them is greater
  have h₁ := proposition_7_greater a b c d e f AB BC CA DE EF FD ⟨by euclid_finish,
    by euclid_finish, ‹_›, ‹_›, ‹_›⟩
  have h₂ := proposition_7_greater d e f a b c DE EF FD AB BC CA ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, ‹(a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f)›.symm,
    by rcases ‹(∠ a:c:b < ∟ ∧ ∠ d:f:e < ∟) ∨ (¬(∠ a:c:b < ∟) ∧ ¬(∠ d:f:e < ∟))› with
        h | h <;> [left; right] <;> exact ⟨h.2, h.1⟩⟩
  -- so `ABC` is equal to `DEF`, and the remaining angle at `c` to that at `f`
  -- [Prop. 1.32]
  euclid_apply (triangle_angles a b c AB BC CA)
  euclid_apply (triangle_angles d e f DE EF FD)
  euclid_finish

end Elements.Book6
