import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop09
import Elements.Book4.Lemmas
import Elements.Book4.Prop04

namespace Elements.Book4

/--
In an equilateral and equiangular pentagon, `CF`, `DF` cutting the angles at `C`, `D` in
half: `BC = CD`, `CF` common, so `CBF = CDF` [Prop. 1.4], and `BF` cuts the angle at `B`,
equal to that at `D`, in half. Missed by Euclid: `F` is on `C`'s side of `AB`.
-/
theorem proposition_13_vertex : ∀ (a b c d e f : Point) (AB BC CD DE : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧
  distinctPointsOnLine d e DE ∧ ¬(a.onLine BC) ∧ |(b─c)| = |(c─d)| ∧
  ∠ a:b:c = ∠ c:d:e ∧ ∠ b:c:f = ∠ f:c:d ∧ ∠ c:d:f = ∠ f:d:e ∧
  ∠ c:d:e = ∠ c:d:f + ∠ f:d:e ∧ f.sameSide a BC ∧ f.sameSide b CD →
  ∠ a:b:f = ∠ f:b:c ∧ ∠ a:b:c = ∠ a:b:f + ∠ f:b:c ∧ f.sameSide c AB :=
by
  euclid_intros
  euclid_apply (line_from_points c f) as CF
  euclid_apply (line_from_points b f) as BF
  euclid_apply (line_from_points d f) as DF
  euclid_apply (Elements.Book1.proposition_4 c b f c d f BC BF CF CD DF CF)
  have : f.sameSide c AB := by
    by_cases (f.onLine AB)
    · exfalso
      euclid_apply (equal_angles b a f c c AB BC)
      euclid_finish
    · by_cases (f.sameSide c AB)
      · assumption
      · exfalso
        euclid_apply (sum_angles_onlyif b c f a BC BF)
        euclid_finish
  euclid_apply (sum_angles_onlyif b a c f AB BC)
  euclid_finish

/--
In an equilateral and equiangular pentagon `ABCDE`, the lines `CF`, `DF` cutting the
angles at `C`, `D` in half [Prop. 1.9] meet at `F`, and `FB`, `FA`, `FE` cut the other
angles in half. Missed by Euclid: `CF`, `DF` meet, within the pentagon.
-/
theorem proposition_13_centre : ∀ (a b c d e : Point) (AB BC CD DE EA : Line),
  pentagon a b c d e AB BC CD DE EA ∧ equilateralPentagon a b c d e ∧
  equiangularPentagon a b c d e →
  ∃ f : Point, ∠ e:a:f = ∠ f:a:b ∧ ∠ a:b:f = ∠ f:b:c ∧ ∠ b:c:f = ∠ f:c:d ∧
  ∠ c:d:f = ∠ f:d:e ∧ ∠ d:e:f = ∠ f:e:a ∧
  ∠ e:a:b = ∠ e:a:f + ∠ f:a:b ∧ ∠ a:b:c = ∠ a:b:f + ∠ f:b:c ∧
  ∠ b:c:d = ∠ b:c:f + ∠ f:c:d ∧ ∠ c:d:e = ∠ c:d:f + ∠ f:d:e ∧
  ∠ d:e:a = ∠ d:e:f + ∠ f:e:a ∧
  f.sameSide c AB ∧ f.sameSide a BC ∧ f.sameSide b CD ∧ f.sameSide c DE ∧
  f.sameSide d EA ∧ f.sameSide d AB ∧ f.sameSide e BC ∧ f.sameSide a CD ∧
  f.sameSide b DE ∧ f.sameSide c EA :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_9 c b d BC CD) as x
  euclid_apply (Elements.Book1.proposition_9 d c e CD DE) as y
  euclid_apply (line_from_points c x) as CF
  euclid_apply (line_from_points d y) as DF
  euclid_apply (sum_angles_onlyif c b d x BC CD)
  euclid_apply (sum_angles_onlyif d c e y CD DE)
  euclid_apply (angle_lt_flat b c d CD)
  euclid_apply (angle_lt_flat e d c CD)
  euclid_assert b.sameSide e CD
  euclid_assert x.sameSide y CD
  euclid_apply (lines_intersect x c d y CF CD DF) as f
  euclid_apply (equal_angles c x f b b CF BC)
  euclid_apply (equal_angles c x f d d CF CD)
  euclid_apply (equal_angles d y f c c DF CD)
  euclid_apply (equal_angles d y f e e DF DE)
  euclid_apply (sum_angles_onlyif c b d f BC CD)
  euclid_apply (sum_angles_onlyif d c e f CD DE)
  -- FB, FA, FE cut the angles at B, A, E in half
  euclid_apply (proposition_13_vertex a b c d e f AB BC CD DE)
  euclid_apply (proposition_13_vertex e a b c d f EA AB BC CD)
  euclid_apply (proposition_13_vertex d e a b c f DE EA AB BC)
  use f
  euclid_finish

/-- To inscribe a circle `α`, with center `f`, in a given equilateral and equiangular
pentagon `ABCDE`; it touches `AB`, `BC`, `CD`, `DE`, `EA` at `G`, `H`, `K`, `L`, `M`. -/
theorem proposition_13 : ∀ (a b c d e : Point) (AB BC CD DE EA : Line),
  pentagon a b c d e AB BC CD DE EA ∧ equilateralPentagon a b c d e ∧
  equiangularPentagon a b c d e →
  ∃ (f g h k l m : Point) (α : Circle), f.isCentre α ∧
  circumscribedPentagon a b c d e AB BC CD DE EA g h k l m α :=
by
  euclid_intros
  -- the angles at C, D cut in half by CF, DF, and so those at B, A, E by FB, FA, FE
  euclid_apply (proposition_13_centre a b c d e AB BC CD DE EA) as f
  -- FG, FH, FK, FL, FM drawn perpendicular to the sides [Prop. 1.12]. Missed by Euclid:
  -- they fall on the sides, the halves of the angles being less than right angles.
  euclid_apply (angle_lt_flat e a b AB)
  euclid_apply (angle_lt_flat a b c BC)
  euclid_apply (angle_lt_flat b c d CD)
  euclid_apply (angle_lt_flat c d e DE)
  euclid_apply (angle_lt_flat d e a EA)
  euclid_apply (foot_between a b f AB) as g
  euclid_apply (foot_between b c f BC) as h
  euclid_apply (foot_between c d f CD) as k
  euclid_apply (foot_between d e f DE) as l
  euclid_apply (foot_between e a f EA) as m
  -- HCF = KCF, the angles at H, K right, FC common: FH = FK [Prop. 1.26]; and so FL,
  -- FM, FG
  euclid_apply (proposition_4_equal a b c f g h AB BC)
  euclid_apply (proposition_4_equal b c d f h k BC CD)
  euclid_apply (proposition_4_equal c d e f k l CD DE)
  euclid_apply (proposition_4_equal d e a f l m DE EA)
  -- the circle with center F and radius FG goes through H, K, L, M, and touches the
  -- sides, the angles at G, H, K, L, M being right [Prop. 3.16 corollary]
  euclid_apply (circle_from_points f g) as α
  euclid_apply (point_on_circle_if f g h α)
  euclid_apply (point_on_circle_if f g k α)
  euclid_apply (point_on_circle_if f g l α)
  euclid_apply (point_on_circle_if f g m α)
  euclid_apply (touches_of_perpendicular f g a AB α)
  euclid_apply (touches_of_perpendicular f h b BC α)
  euclid_apply (touches_of_perpendicular f k c CD α)
  euclid_apply (touches_of_perpendicular f l d DE α)
  euclid_apply (touches_of_perpendicular f m e EA α)
  use f, g, h, k, l, m, α

end Elements.Book4
