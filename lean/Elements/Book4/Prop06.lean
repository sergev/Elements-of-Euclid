import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop11
import Elements.Book3.Prop31
import Elements.Book4.Lemmas

namespace Elements.Book4

/-- To inscribe a square `ABCD` in a given circle `α`, with center `e`. -/
theorem proposition_6 : ∀ (e : Point) (α : Circle),
  e.isCentre α →
  ∃ (a b c d : Point) (AB BC CD DA : Line), square a b c d AB BC CD DA ∧
  inscribedQuadrilateral a b c d α :=
by
  euclid_intros
  -- two diameters AC, BD at right angles to one another [Props. 3.1, 1.11]
  euclid_apply (exists_point_on_circle α) as a
  euclid_apply (line_from_points a e) as AC
  euclid_apply (intersection_circle_line_extending_points α AC e a) as c
  euclid_apply (Elements.Book1.proposition_11 a c e AC) as x
  euclid_apply (line_from_points e x) as BD
  euclid_apply (intersection_circle_line_extending_points α BD e x) as b
  euclid_apply (intersection_circle_line_extending_points α BD e b) as d
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points c d) as CD
  euclid_apply (line_from_points d a) as DA
  euclid_apply (point_on_circle_onlyif e a b α)
  euclid_apply (point_on_circle_onlyif e a c α)
  euclid_apply (point_on_circle_onlyif e a d α)
  -- BE = ED, EA common and at right angles: AB = AD [Prop. 1.4]; and so for BC, CD
  euclid_apply (right_angle_on_lines a e x a b AC BD)
  euclid_apply (right_angle_on_lines a e x a d AC BD)
  euclid_apply (right_angle_on_lines a e x c b AC BD)
  euclid_apply (right_angle_on_lines a e x c d AC BD)
  euclid_apply (Elements.Book1.proposition_4 e a b e a d AC AB BD AC DA BD)
  euclid_apply (Elements.Book1.proposition_4 e c b e c d AC BC BD AC CD BD)
  euclid_apply (Elements.Book1.proposition_4 e b a e b c BD AB AC BD BC AC)
  -- BD is a diameter: BAD, in a semicircle, is right [Prop. 3.31]; and so ABC, BCD, CDA
  euclid_apply (Elements.Book3.proposition_31 a b d e BD α)
  euclid_apply (Elements.Book3.proposition_31 b a c e AC α)
  euclid_apply (Elements.Book3.proposition_31 c b d e BD α)
  euclid_apply (Elements.Book3.proposition_31 d a c e AC α)
  -- a square [Def. 1.22]
  euclid_apply (quadrilateral_of_diagonals a b c d e AB BC CD DA AC)
  use a, b, c, d, AB, BC, CD, DA
  euclid_finish

end Elements.Book4
