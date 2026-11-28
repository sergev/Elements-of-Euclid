import SystemE
import Elements.Book1.Prop04
import Elements.Book1.Prop20
import Elements.Book1.Prop23
import Elements.Book1.Prop24

namespace Elements.Book3

/-
Prop. 3.7. `F` is a point on the diameter `AD` of a circle with center `E`, not the
center, with `E` between `A` and `F`. Of the straight lines from `F` to the circle, `FA`
is the greatest and `FD` the least (`proposition_7`); a line nearer to `FA` is greater
(`proposition_7_nearer`); and only two equal lines fall from `F`, one on each side of
`FD` (`proposition_7_equal`, `proposition_7_only`).
-/

/-- `FA` is the greatest, and `FD` the least, of the lines from `F` to the circle. -/
theorem proposition_7 : ∀ (a b d e f : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ d.onLine AD ∧ a.onCircle α ∧ d.onCircle α ∧ b.onCircle α ∧ e.isCentre α ∧
  between a e f ∧ between e f d ∧ b ≠ a ∧ b ≠ d →
  |(f─b)| < |(f─a)| ∧ |(f─d)| < |(f─b)| :=
by
  euclid_intros
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points f b) as FB
  euclid_apply (point_on_circle_onlyif e a b α)
  euclid_apply (point_on_circle_onlyif e d b α)
  -- EB and EF are greater than BF [Prop. 1.20], and AE = BE; so AF is greater than BF
  euclid_apply (Elements.Book1.proposition_20 e b f EB FB AD)
  euclid_apply (between_if a e f)
  -- BF and FE are greater than EB = ED [Prop. 1.20]; take away EF: BF is greater than FD
  euclid_apply (Elements.Book1.proposition_20 f b e FB EB AD)
  euclid_apply (between_if e f d)
  euclid_finish

/-- Of two lines `FB`, `FC`, the one nearer to `FA` (by the angle at `E`) is greater. -/
theorem proposition_7_nearer : ∀ (a b c d e f : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ d.onLine AD ∧ a.onCircle α ∧ d.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  e.isCentre α ∧ between a e f ∧ between e f d ∧ ¬(b.onLine AD) ∧ ¬(c.onLine AD) ∧
  ∠ c:e:f < ∠ b:e:f → |(f─c)| < |(f─b)| :=
by
  euclid_intros
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points e c) as EC
  euclid_apply (line_from_points f c) as FC
  -- BE = CE, EF common, and the angle BEF greater than CEF [Prop. 1.24]
  euclid_apply (point_on_circle_onlyif e b c α)
  euclid_apply (Elements.Book1.proposition_24 e b f e c f EB FB AD EC FC AD)
  euclid_finish

/-- A line `FH` equal to `FG` falls on the other side of `FD`. -/
theorem proposition_7_equal : ∀ (a d e f g : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ d.onLine AD ∧ a.onCircle α ∧ d.onCircle α ∧ g.onCircle α ∧ e.isCentre α ∧
  between a e f ∧ between e f d ∧ ¬(g.onLine AD) →
  ∃ h : Point, h.onCircle α ∧ h.opposingSides g AD ∧ |(f─h)| = |(f─g)| :=
by
  euclid_intros
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  -- the angle FEH equal to GEF, on the other side [Prop. 1.23]
  euclid_apply (exists_point_opposite AD g) as x
  euclid_apply (Elements.Book1.proposition_23_side e f e g f x AD EG AD) as h'
  euclid_apply (line_from_points e h') as EH
  euclid_apply (extend_point EH h' e) as h''
  euclid_apply (intersection_circle_line_extending_points α EH e h'') as h
  euclid_apply (equal_angles e f f h' h AD EH)
  euclid_apply (line_from_points f h) as FH
  -- GE = EH, EF common, and the angles at E equal: FG = FH [Prop. 1.4]
  euclid_apply (point_on_circle_onlyif e g h α)
  euclid_apply (Elements.Book1.proposition_4 e g f e h f EG FG AD EH FH AD)
  use h
  euclid_finish

/-- On one side of `AD`, a line `FK` equal to `FG` is `FG`. -/
theorem proposition_7_side : ∀ (a d e f g k : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ d.onLine AD ∧ a.onCircle α ∧ d.onCircle α ∧ g.onCircle α ∧ k.onCircle α ∧
  e.isCentre α ∧ between a e f ∧ between e f d ∧ g.sameSide k AD ∧
  |(f─k)| = |(f─g)| → k = g :=
by
  euclid_intros
  -- otherwise the nearer to FA would equal the further
  rcases lt_trichotomy (∠ k:e:f) (∠ g:e:f) with _ | _ | _
  · euclid_apply (proposition_7_nearer a g k d e f AD α)
    exfalso
    euclid_finish
  · -- Missed by Euclid: with equal angles at E, K is on EG, and EK = EG.
    euclid_apply (line_from_points e g) as EG
    euclid_apply (on_line_of_eq_angle k EG e g f AD)
    euclid_apply (point_on_circle_onlyif e g k α)
    euclid_apply (eq_of_same_ray k g e EG)
    euclid_finish
  · euclid_apply (proposition_7_nearer a k g d e f AD α)
    exfalso
    euclid_finish

/-- No other line from `F` is equal to `FG`: the nearer would equal the further. -/
theorem proposition_7_only : ∀ (a d e f g h k : Point) (AD : Line) (α : Circle),
  a.onLine AD ∧ d.onLine AD ∧ a.onCircle α ∧ d.onCircle α ∧ g.onCircle α ∧ h.onCircle α ∧
  k.onCircle α ∧ e.isCentre α ∧ between a e f ∧ between e f d ∧ g.opposingSides h AD ∧
  |(f─h)| = |(f─g)| ∧ |(f─k)| = |(f─g)| → k = g ∨ k = h :=
by
  euclid_intros
  -- Missed by Euclid: FK is neither FA nor FD, so K is off AD, on the side of G or of H.
  euclid_apply (proposition_7 a g d e f AD α)
  by_cases (k.onLine AD)
  · by_cases (k = a)
    · exfalso
      euclid_finish
    · euclid_assert k = d
      exfalso
      euclid_finish
  · by_cases (g.sameSide k AD)
    · euclid_apply (proposition_7_side a d e f g k AD α)
      euclid_finish
    · euclid_apply (proposition_7_side a d e f h k AD α)
      euclid_finish

end Elements.Book3
