import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop13
import Elements.Book1.Prop32

namespace Elements.Book3

/--
Euclid's step in Prop. 3.20: with `AE` produced to `F` through the center `E`, the angle
`BEF` is double `EAB`, since `EA = EB` [Props. 1.5, 1.32].
-/
theorem proposition_20_lemma : ∀ (a b e f : Point) (AE : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ e.isCentre α ∧ a.onLine AE ∧ e.onLine AE ∧
  between a e f ∧ ¬(b.onLine AE) → ∠ b:e:f = ∠ e:a:b + ∠ e:a:b :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b e) as BE
  euclid_apply (point_on_circle_onlyif e a b α)
  -- EA = EB, so EAB = EBA [Prop. 1.5]; BEF is equal to both [Prop. 1.32]
  euclid_apply (Elements.Book1.proposition_5' e a b AE AB BE)
  euclid_apply (Elements.Book1.proposition_32 b a e f AB AE BE)
  euclid_finish

/--
The angle `BEC` at the center is double the angle `BAC` at the circumference on the same
base `BC`, with the center on the side of `A`.
-/
theorem proposition_20 : ∀ (a b c e : Point) (BC : Line) (α : Circle),
  a.onSegment α b c BC e ∧ e.isCentre α → ∠ b:e:c = ∠ b:a:c + ∠ b:a:c :=
by
  euclid_intros
  -- join AE and produce it to F
  euclid_apply (line_from_points a e) as AE
  euclid_apply (intersection_circle_line_extending_points α AE e a) as f
  by_cases (b.onLine AE)
  · -- Missed by Euclid: AB is the diameter AF; BEC is the exterior angle of AEC.
    euclid_assert b = f
    euclid_apply (line_from_points a c) as AC
    euclid_apply (proposition_20_lemma a c e f AE α)
    euclid_apply (equal_angles a e b c c AE AC)
    euclid_finish
  · by_cases (c.onLine AE)
    · -- Missed by Euclid: likewise with AC the diameter.
      euclid_assert c = f
      euclid_apply (line_from_points a b) as AB
      euclid_apply (proposition_20_lemma a b e f AE α)
      euclid_apply (equal_angles a e c b b AE AB)
      euclid_finish
    · euclid_apply (proposition_20_lemma a b e f AE α)
      euclid_apply (proposition_20_lemma a c e f AE α)
      euclid_apply (line_from_points a b) as AB
      euclid_apply (line_from_points a c) as AC
      euclid_apply (line_from_points e b) as EB
      euclid_apply (line_from_points e c) as EC
      by_cases (b.sameSide c AE)
      · -- let it be bent: the angle BEC is the difference of FEC and FEB, each double
        -- EAC and EAB
        by_cases (b.sameSide e AC)
        · euclid_apply (sum_angles_onlyif a e c b AE AC)
          euclid_apply (sum_angles_onlyif e f c b AE EC)
          euclid_finish
        · euclid_apply (sum_angles_onlyif a e b c AE AB)
          euclid_apply (sum_angles_onlyif e f b c AE EB)
          euclid_finish
      · -- Missed by Euclid: AE meets BC at M between B and C, inside the circle, so
        -- not on the other side of A from E; E is within the angle BAC.
        euclid_apply (intersection_lines_opposing b c AE BC)
        euclid_apply (intersection_lines AE BC) as m
        euclid_apply (circle_points_between b c m α)
        euclid_assert ¬(between m a e)
        -- BEF and FEC make BEC, and BAE and EAC make BAC
        euclid_apply (sum_angles_onlyif a b c e AB AC)
        euclid_apply (sum_angles_onlyif e b c f EB EC)
        euclid_finish

/--
Missed by Euclid: with the center `E` on the other side of `BC` from `A`, the angle at the
center standing on the base `BC` is the reflex angle, four right angles less `BEC`; it
is again double `BAC`. Prop. 3.21 needs this case, for a segment less than a semicircle.
-/
theorem proposition_20' : ∀ (a b c e : Point) (BC : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c BC ∧
  e.isCentre α ∧ a.opposingSides e BC → ∠ b:a:c + ∠ b:a:c + ∠ b:e:c = 4 * ∟ :=
by
  euclid_intros
  -- join AE and produce it to F; AE meets BC at M, between B and C
  euclid_apply (line_from_points a e) as AE
  euclid_apply (intersection_circle_line_extending_points α AE e a) as f
  euclid_apply (intersection_lines_opposing a e BC AE)
  euclid_apply (intersection_lines BC AE) as m
  euclid_apply (circle_points_between a e m α)
  euclid_apply (circle_line_intersections m b c BC α)
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e c) as EC
  -- BEF and CEF are double EAB and EAC
  euclid_apply (proposition_20_lemma a b e f AE α)
  euclid_apply (proposition_20_lemma a c e f AE α)
  -- BAM and MAC make BAC; BEM and MEC make BEC
  euclid_apply (sum_angles_onlyif a b c m AB AC)
  euclid_apply (sum_angles_onlyif e b c m EB EC)
  euclid_apply (equal_angles a b b m e AB AE)
  euclid_apply (equal_angles a c c m e AC AE)
  euclid_apply (equal_angles e b b m a EB AE)
  euclid_apply (equal_angles e c c m a EC AE)
  -- AEB and BEF make two right angles, as do AEC and CEF [Prop. 1.13]
  euclid_apply (Elements.Book1.proposition_13 b e a f EB AE)
  euclid_apply (Elements.Book1.proposition_13 c e a f EC AE)
  euclid_finish

/--
Missed by Euclid: with the center `E` on `BC`, the angle `BAC` is half of two right angles
(Prop. 3.31).
-/
theorem proposition_20'' : ∀ (a b c e : Point) (BC : Line) (α : Circle),
  a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c BC ∧
  e.isCentre α ∧ e.onLine BC ∧ ¬(a.onLine BC) → ∠ b:a:c = ∟ :=
by
  euclid_intros
  euclid_apply (circle_line_intersections e b c BC α)
  euclid_apply (line_from_points a e) as AE
  euclid_apply (intersection_circle_line_extending_points α AE e a) as f
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points e f) as EF
  -- BEF and CEF are double EAB and EAC, and make two right angles [Prop. 1.13]
  euclid_apply (proposition_20_lemma a b e f AE α)
  euclid_apply (proposition_20_lemma a c e f AE α)
  euclid_apply (Elements.Book1.proposition_13 f e c b EF BC)
  -- BAE and EAC make BAC
  euclid_apply (sum_angles_onlyif a b c e AB AC)
  euclid_finish

end Elements.Book3
