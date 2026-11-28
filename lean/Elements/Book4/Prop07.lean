import SystemE
import Elements.Book1.Prop11
import Elements.Book1.Prop27
import Elements.Book1.Prop34
import Elements.Book3.Prop18
import Elements.Book4.Lemmas

namespace Elements.Book4

/--
A corner of the square: `GBEA`, with right angles at `E`, `A`, `B`, is a parallelogram
[Prop. 1.27], so `GA = EB`, `GB = EA`, and `AGB` is right [Prop. 1.34].
-/
theorem proposition_7_lemma : ∀ (a b e g : Point) (EA EB AG BG : Line),
  distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB ∧
  distinctPointsOnLine a g AG ∧ distinctPointsOnLine b g BG ∧ ∠ a:e:b = ∟ ∧
  ∠ e:a:g = ∟ ∧ ∠ e:b:g = ∟ ∧ g.sameSide b EA ∧ g.sameSide a EB →
  |(g─a)| = |(e─b)| ∧ |(g─b)| = |(e─a)| ∧ ∠ a:g:b = ∟ :=
by
  euclid_intros
  euclid_apply (not_on_line_of_right_angle e a g AG)
  euclid_apply (not_on_line_of_right_angle e b g BG)
  euclid_apply (extend_point EB b e) as b'
  euclid_apply (extend_point EA a e) as a'
  euclid_apply (right_angle_on_lines a e b a b' EA EB)
  euclid_apply (right_angle_on_lines b e a b a' EB EA)
  euclid_apply (Elements.Book1.proposition_27 g b' a e AG EB EA)
  euclid_apply (Elements.Book1.proposition_27 g a' b e BG EA EB)
  euclid_apply (Elements.Book1.proposition_34' g a b e AG EB BG EA)
  euclid_finish

/-- To circumscribe a square `FGHK` about a given circle `α`, with center `e`; its sides
touch the circle at `A`, `B`, `C`, `D`. -/
theorem proposition_7 : ∀ (e : Point) (α : Circle),
  e.isCentre α →
  ∃ (f g h k a b c d : Point) (FG GH HK KF : Line), square f g h k FG GH HK KF ∧
  circumscribedQuadrilateral f g h k FG GH HK KF a b c d α :=
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
  euclid_apply (point_on_circle_onlyif e a b α)
  euclid_apply (point_on_circle_onlyif e a c α)
  euclid_apply (point_on_circle_onlyif e a d α)
  euclid_apply (right_angle_on_lines a e x a b AC BD)
  euclid_apply (right_angle_on_lines a e x c b AC BD)
  euclid_apply (right_angle_on_lines a e x c d AC BD)
  euclid_apply (right_angle_on_lines a e x a d AC BD)
  -- FG, GH, HK, KF touching the circle at A, B, C, D. Missed by Euclid: they meet
  -- (Post. 5).
  euclid_apply (exists_tangent a e α) as FG
  euclid_apply (exists_tangent b e α) as GH
  euclid_apply (exists_tangent c e α) as HK
  euclid_apply (exists_tangent d e α) as KF
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points c d) as CD
  euclid_apply (line_from_points d a) as DA
  euclid_apply (tangents_meet a b e FG GH AB AC BD α) as g
  euclid_apply (tangents_meet b c e GH HK BC BD AC α) as h
  euclid_apply (tangents_meet c d e HK KF CD AC BD α) as k
  euclid_apply (tangents_meet d a e KF FG DA BD AC α) as f
  -- the angles at A, B, C, D are right [Prop. 3.18]
  euclid_apply (Elements.Book3.proposition_18 a g e FG α)
  euclid_apply (Elements.Book3.proposition_18 a f e FG α)
  euclid_apply (Elements.Book3.proposition_18 b g e GH α)
  euclid_apply (Elements.Book3.proposition_18 b h e GH α)
  euclid_apply (Elements.Book3.proposition_18 c h e HK α)
  euclid_apply (Elements.Book3.proposition_18 c k e HK α)
  euclid_apply (Elements.Book3.proposition_18 d k e KF α)
  euclid_apply (Elements.Book3.proposition_18 d f e KF α)
  -- GBEA, HCEB, KDEC, FAED are parallelograms: their opposite sides are equal, and
  -- the angles at G, H, K, F right [Prop. 1.34]
  euclid_apply (proposition_7_lemma a b e g AC BD FG GH)
  euclid_apply (proposition_7_lemma b c e h BD AC GH HK)
  euclid_apply (proposition_7_lemma c d e k AC BD HK KF)
  euclid_apply (proposition_7_lemma d a e f BD AC KF FG)
  -- Missed by Euclid: A, B, C, D are between the vertices, and the figure is convex.
  euclid_assert between f a g
  euclid_assert between g b h
  euclid_assert between h c k
  euclid_assert between k d f
  euclid_apply (between_if f a g)
  euclid_apply (between_if g b h)
  euclid_apply (between_if h c k)
  euclid_apply (between_if k d f)
  euclid_apply (equal_angles g a f b h FG GH)
  euclid_apply (equal_angles h b g c k GH HK)
  euclid_apply (equal_angles k c h d f HK KF)
  euclid_apply (equal_angles f d k a g KF FG)
  euclid_assert h.sameSide k FG
  euclid_assert k.sameSide f GH
  euclid_assert f.sameSide g HK
  euclid_assert g.sameSide h KF
  -- the sides are each equal to the diameter: FGHK is equilateral, and right-angled,
  -- a square [Def. 1.22]
  use f, g, h, k, a, b, c, d, FG, GH, HK, KF
  euclid_finish

end Elements.Book4
