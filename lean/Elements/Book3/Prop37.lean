import SystemE
import Elements.Book1.Prop08
import Elements.Book3.Lemmas
import Elements.Book3.Prop08
import Elements.Book3.Prop16
import Elements.Book3.Prop17
import Elements.Book3.Prop36

namespace Elements.Book3

/--
Missed by Euclid in Prop. 3.37: `DB` is not through the center `F`; else, of the lines
from `D` to the circle, `DE` would be between the least and the greatest, `DB`
[Prop. 3.8].
-/
theorem proposition_37_lemma : ∀ (b d e f : Point) (DB DE : Line) (α : Circle),
  DE.touchesCircleAt α e ∧ d.onLine DE ∧ d.outsideCircle α ∧ b.onCircle α ∧ d.onLine DB ∧
  b.onLine DB ∧ f.isCentre α ∧ f.onLine DB ∧ |(d─e)| = |(d─b)| → False :=
by
  euclid_intros
  euclid_apply (intersection_circle_line_extending_points α DB f b) as b₂
  euclid_assert e ≠ b
  euclid_assert e ≠ b₂
  euclid_apply (between_points d b f DB)
  rcases ‹_ ∨ _ ∨ _› with _ | _ | _
  · euclid_apply (proposition_8 b₂ d e b f DB α)
    euclid_finish
  · euclid_apply (circle_points_between b f d α)
    euclid_finish
  · euclid_apply (between_points d b₂ f DB)
    rcases ‹_ ∨ _ ∨ _› with _ | _ | _
    · euclid_apply (proposition_8 b d e b₂ f DB α)
      euclid_finish
    · euclid_apply (circle_points_between b₂ f d α)
      euclid_finish
    · euclid_finish

/--
From a point `D` outside, `DCA` cutting the circle and `DB` meeting it at `B`: if the
rectangle `AD`, `DC` is equal to the square on `DB`, then `DB` touches the circle.
-/
theorem proposition_37 : ∀ (a b c d f : Point) (AC DB : Line) (α : Circle),
  a.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine a c AC ∧ between d c a ∧
  b.onCircle α ∧ d.onLine DB ∧ b.onLine DB ∧ f.isCentre α ∧
  |(a─d)| * |(d─c)| = |(d─b)| * |(d─b)| → DB.touchesCircleAt α b :=
by
  euclid_intros
  -- let DE be drawn touching the circle [Prop. 3.17]
  euclid_apply (circle_points_extend a d c α)
  euclid_apply (proposition_17 d f α) as (e, DE)
  -- the rectangle AD, DC is equal to the square on DE [Prop. 3.36], and on DB: DE = DB
  euclid_apply (proposition_36 a e c d f AC DE α)
  euclid_apply (length_eq_of_square_eq d e d b)
  -- Missed by Euclid: DB is not through the center F [Prop. 3.8].
  have : ¬(f.onLine DB) := fun _ =>
    proposition_37_lemma b d e f DB DE α (by euclid_finish)
  -- DE, EF are equal to DB, BF, and FD is common: DEF = DBF [Prop. 1.8], a right angle
  -- [Prop. 3.18]
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points b f) as BF
  euclid_apply (line_from_points d f) as DF
  euclid_apply (point_on_circle_onlyif f e b α)
  euclid_apply (Elements.Book1.proposition_8 e d f b d f DE DF EF DB DF BF)
  euclid_apply (proposition_18 e d f DE α)
  euclid_apply (angle_symm f e d)
  -- FB produced is a diameter; DB is at right angles to it at its end: DB touches the
  -- circle [Prop. 3.16 corollary]
  euclid_apply (intersection_circle_line_extending_points α BF f b) as b'
  euclid_apply (right_angle_on_lines f b d b' d BF DB)
  euclid_apply (proposition_16_corollary b b' f d DB α)
  euclid_finish

end Elements.Book3
