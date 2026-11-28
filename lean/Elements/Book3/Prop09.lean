import SystemE
import Elements.Book1.Prop08
import Elements.Book1.Prop10
import Elements.Book1.Prop17
import Elements.Book3.Prop01

namespace Elements.Book3

/--
Prop. 3.9 on two chords `AB`, `BC` not through `D`: if `DA = DB = DC`, a center `O` of the
circle is `D`.
-/
theorem proposition_9_chords : ∀ (a b c d o : Point) (AB BC : Line) (α : Circle),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ c ≠ a ∧
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ ¬(d.onLine AB) ∧ ¬(d.onLine BC) ∧
  |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| ∧ o.isCentre α → o = d :=
by
  euclid_intros
  -- bisect AB at E and BC at F [Prop. 1.10], and join ED, FD
  euclid_apply (Elements.Book1.proposition_10 a b AB) as e
  euclid_apply (Elements.Book1.proposition_10 b c BC) as f
  euclid_apply (line_from_points e d) as GK
  euclid_apply (line_from_points f d) as HL
  euclid_apply (line_from_points d a) as DA
  euclid_apply (line_from_points d b) as DB
  euclid_apply (line_from_points d c) as DC
  -- AE = EB, ED common, DA = DB: the angles at E are equal [Prop. 1.8], so right
  euclid_apply (Elements.Book1.proposition_8 e a d e b d AB DA GK AB DB GK)
  euclid_apply (perpendicular_if a b e d AB)
  -- GK cuts AB in half at right angles: the center is on GK [Prop. 3.1 corollary]
  euclid_apply (proposition_1_corollary a b d e o AB GK α)
  -- likewise for HL and BC
  euclid_apply (Elements.Book1.proposition_8 f b d f c d BC DB HL BC DC HL)
  euclid_apply (perpendicular_if b c f d BC)
  euclid_apply (proposition_1_corollary b c d f o BC HL α)
  -- Missed by Euclid: GK and HL are different lines.
  have : GK ≠ HL := by
    intro
    by_cases (e = f)
    · euclid_apply (two_points_determine_line e b AB BC)
      exfalso
      euclid_finish
    · -- the triangle BEF would have two right angles [Prop. 1.17]
      euclid_apply (right_angle_on_lines a e d b f AB GK)
      euclid_apply (right_angle_on_lines b f d b e BC HL)
      euclid_apply (Elements.Book1.proposition_17 b e f AB GK BC)
      exfalso
      euclid_finish
  -- they meet only at D, which is thus the center
  euclid_finish

/--
A point from which three equal lines fall on a circle is its center. Euclid takes the
point inside, but the proof does not use it; Prop. 3.10 needs this form.
-/
theorem proposition_9' : ∀ (a b c d o : Point) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
  |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| ∧ o.isCentre α → d.isCentre α :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points c a) as CA
  -- Missed by Euclid: D is on at most one of the chords; take the other two.
  by_cases (d.onLine AB)
  · euclid_apply (proposition_9_chords b c a d o BC CA α)
    euclid_finish
  · by_cases (d.onLine BC)
    · euclid_apply (proposition_9_chords c a b d o CA AB α)
      euclid_finish
    · euclid_apply (proposition_9_chords a b c d o AB BC α)
      euclid_finish

/-- A point inside a circle with three equal lines to the circle is its center. -/
theorem proposition_9 : ∀ (a b c d o : Point) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ d.insideCircle α ∧
  |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| ∧ o.isCentre α → d.isCentre α :=
by
  euclid_intros
  euclid_apply (proposition_9' a b c d o α)
  euclid_finish

end Elements.Book3
