import SystemE
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop29
import Elements.Book1.Prop31
import Elements.Book5.Prop07
import Elements.Book5.Prop09
import Elements.Book6.Prop02

namespace Elements.Book6

open Elements.Book5

/--
The figure of Prop. 6.3: through `c`, `CE` parallel to `DA` [Prop. 1.31], meeting `BA`
produced at `e`: if `BA` did not meet it, `BA` and `AD` would be two parallels to `CE`
through `a` (Post. 5). The angle `ace` is equal to `cad`, alternate, and `bad` to `aec`,
exterior and interior [Prop. 1.29].
-/
theorem proposition_3_figure : ∀ (a b c d : Point) (AB BC CA AD : Line),
  formTriangle a b c AB BC CA ∧ between b d c ∧ a.onLine AD ∧ d.onLine AD →
  ∃ (e : Point) (CE : Line), e.onLine AB ∧ e.onLine CE ∧ c.onLine CE ∧ between b a e ∧
  ¬(AD.intersectsLine CE) ∧ ∠ a:c:e = ∠ c:a:d ∧ ∠ b:a:d = ∠ a:e:c :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CE
  have : AB.intersectsLine CE := by
    by_contra
    euclid_apply (parallel_line_unique a CE AB AD)
    euclid_finish
  euclid_apply (intersection_lines AB CE) as e
  euclid_assert between b a e
  euclid_apply (Elements.Book1.proposition_29_alternate e d c a CE AD CA)
  euclid_apply (Elements.Book1.proposition_29_exterior d c b a e AD CE AB)
  use e, CE
  euclid_finish

/--
If the angle `bac` of the triangle `abc` is cut in half by `AD`, meeting the base at `d`,
the segments of the base have the same ratio as the remaining sides: `bd : dc :: ba : ac`.
-/
theorem proposition_3 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ between b d c ∧ ∠ b:a:d = ∠ d:a:c →
  (b─d) ∶ (d─c) ∷ (b─a) ∶ (a─c) :=
by
  euclid_intros
  euclid_apply (line_from_points a d) as AD
  euclid_apply (proposition_3_figure a b c d AB BC CA AD) as (e, CE)
  -- `ACE` is equal to `CAD`, and `BAD` to `AEC` [Prop. 1.29]; so `ACE` is equal to `AEC`,
  -- and `AE` to `AC` [Prop. 1.6]
  euclid_apply (Elements.Book1.proposition_6 a e c AB CE CA)
  -- `AD` is parallel to the side `EC` of the triangle `BCE`: `BD : DC :: BA : AE`
  -- [Props. 6.2, 5.7 corollary]
  obtain ⟨hcd, hdb, hea, hab, h₁⟩ := proposition_2 b c e d a BC CE AB AD
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›, by euclid_finish⟩
  have h₁ := proposition_7_corollary h₁
  -- `BA : AE :: BA : AC` [Prop. 5.7], so `BD : DC :: BA : AC` [Prop. 5.11]
  have hac : 0 < size (a─c) := size_segment_pos.mpr (by euclid_finish)
  have h₂ := (proposition_7 (mag (a─b) hab) (mag_congr (hp := hea) (hq := hac)
    (by rw [size_segment, size_segment]; euclid_finish))).2
  have hbd : 0 < size (b─d) := by rw [size_segment_symm]; exact hdb
  have hdc : 0 < size (d─c) := by rw [size_segment_symm]; exact hcd
  have hba : 0 < size (b─a) := by rw [size_segment_symm]; exact hab
  refine ⟨hbd, hdc, hba, hac, ?_⟩
  rw [mag_congr (hq := hdb) (size_segment_symm b d), mag_congr (hq := hcd)
    (size_segment_symm d c), mag_congr (hq := hab) (size_segment_symm b a)]
  exact proposition_11 h₁ h₂

/--
If the segments of the base have the same ratio as the remaining sides of the triangle,
`bd : dc :: ba : ac`, the straight line `AD` cuts the angle `bac` in half.
-/
theorem proposition_3' : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ between b d c ∧ (b─d) ∶ (d─c) ∷ (b─a) ∶ (a─c) →
  ∠ b:a:d = ∠ d:a:c :=
by
  euclid_intros
  euclid_apply (line_from_points a d) as AD
  euclid_apply (proposition_3_figure a b c d AB BC CA AD) as (e, CE)
  -- `BD : DC :: BA : AE` [Props. 6.2, 5.7 corollary]
  obtain ⟨hcd, hdb, hea, hab, h₁⟩ := proposition_2 b c e d a BC CE AB AD
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›, by euclid_finish⟩
  have h₁ := proposition_7_corollary h₁
  obtain ⟨hbd, hdc, hba, hac, h₂⟩ := ‹(b─d) ∶ (d─c) ∷ (b─a) ∶ (a─c)›
  rw [mag_congr (hq := hdb) (size_segment_symm b d), mag_congr (hq := hcd)
    (size_segment_symm d c), mag_congr (hq := hab) (size_segment_symm b a)] at h₂
  -- so `BA : AC :: BA : AE` [Prop. 5.11], and `AC` is equal to `AE` [Prop. 5.9]
  have h₃ := proposition_9' (proposition_11 h₂.symm h₁)
  have : |(a─c)| = |(e─a)| := mag_inj.mp h₃
  -- so `AEC` is equal to `ACE` [Prop. 1.5], and they are equal to `BAD`, `CAD`
  -- [Prop. 1.29]
  euclid_apply (Elements.Book1.proposition_5' a e c AB CE CA)
  euclid_finish

end Elements.Book6
