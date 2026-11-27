import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop04
import Elements.Book1.Prop05
import Elements.Book1.Prop13
import Elements.Book1.Prop17
import Elements.Book1.Prop19
import Elements.Book1.Prop23

namespace Elements.Book1

theorem proposition_24 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| :=
by
  euclid_intros
  obtain ⟨g', hg', hside, hang⟩ := proposition_23' d e a b c f DE AB AC (by euclid_finish)
  -- Omitted by Euclid: G' is off DE, since the angle BAC is neither nothing nor two right angles.
  have : ¬(g'.onLine DE) := by
    intro h
    by_cases (between g' d e)
    · euclid_apply (flat_angle_onlyif g' d e)
      euclid_apply (flat_angle_if b a c)
      euclid_finish
    · euclid_apply (degenerated_angle_if d g' e DE)
      euclid_finish
  have : g'.sameSide f DE := hside.resolve_left this
  euclid_apply (line_from_points d g') as DG
  euclid_apply (extend_point_longer DG d g' (a─c)) as g''
  euclid_apply (proposition_3 d g'' a c DG AC) as g
  euclid_apply (equal_angles d g' g e e DG DE)
  -- Omitted by Euclid: G is off DF, or angles EDG and EDF would be equal.
  have : ¬(g.onLine DF) := by
    intro h
    euclid_apply (equal_angles d g f e e DF DE)
    euclid_finish
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_4 a b c d e g AB BC AC DE EG DG)
  euclid_apply (proposition_5' d g f DG FG DF)
  -- If g were between the rays DE and DF, angle addition would contradict
  -- the strict angle comparison. Expose this before the diagrammatic case split.
  euclid_assert ∠ e:d:g > ∠ e:d:f
  euclid_assert g.sameSide f DE
  have hgf : ¬ g.sameSide e DF := by
    by_contra h
    euclid_apply (sum_angles_onlyif d e f g DE DF)
    euclid_finish
  euclid_apply (triple_incidence_2 DE DF DG d e f g)
  euclid_assert f.sameSide e DG
  by_cases (d.sameSide g EF)
  · euclid_assert (∠ d:f:g > ∠ e:g:f)
    euclid_assert (∠ e:f:g > ∠ e:g:f)
    euclid_apply (proposition_19 e f g EF FG EG)
    euclid_finish
  · -- Omitted by Euclid.
    by_cases g.onLine EF
    · euclid_finish
    · euclid_apply (extend_point FG g f) as h
      -- G and H relative to DF, for the angle sums at F [Prop. 1.13].
      euclid_assert ¬(g.onLine DF)
      euclid_assert ¬(e.onLine DF)
      euclid_assert (g.opposingSides e DF)
      euclid_assert h.sameSide e DF
      euclid_apply (proposition_13 d f g h DF FG)
      euclid_apply (proposition_13 e f g h EF FG)
      euclid_apply (proposition_17 d g e DG EG DE)
      euclid_apply (proposition_17 d f e DF EF DE)
      euclid_assert (∠ d:g:e < ∟ + ∟)
      euclid_assert (∠ d:f:e < ∟ + ∟)
      euclid_assert (∠ e:f:g + ∠ g:f:d + ∠ d:f:e = ∟ + ∟ + ∟ + ∟)
      euclid_assert (∠ e:f:g > ∠ e:g:f)
      euclid_apply (proposition_19 e f g EF FG EG)
      euclid_finish

end Elements.Book1
