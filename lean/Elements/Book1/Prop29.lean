import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop15

namespace Elements.Book1

theorem proposition_29 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD)
  → ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  have hne : AB ≠ CD := by euclid_finish
  have : ∠ a:g:h = ∠ g:h:d := by
    by_contra
    by_cases ∠ a:g:h > ∠ g:h:d
    · euclid_assert ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d
      euclid_apply (proposition_13 h g a b EF AB)
      euclid_assert ∠ b:g:h + ∠ g:h:d < ∟ + ∟
      -- [Post. 5]
      obtain ⟨k, hk, hk', -⟩ := lines_intersect b g h d AB EF CD (by euclid_finish)
      exact ‹¬AB.intersectsLine CD› (intersection_lines_common_point k AB CD ⟨hk, hk', hne⟩)
    · -- Omitted by Euclid.
      euclid_assert ∠ a:g:h < ∠ g:h:d
      euclid_assert ∠ a:g:h + ∠ c:h:g < ∠ g:h:d + ∠ c:h:g
      euclid_apply (proposition_13 g h c d EF CD)
      euclid_assert ∠ a:g:h + ∠ c:h:g < ∟ + ∟
      -- [Post. 5]
      obtain ⟨k, hk, hk', -⟩ := lines_intersect a g h c AB EF CD (by euclid_finish)
      exact ‹¬AB.intersectsLine CD› (intersection_lines_common_point k AB CD ⟨hk, hk', hne⟩)

  euclid_apply (proposition_15 a b e h g AB EF)
  euclid_apply (proposition_13 b g e h AB EF)
  euclid_finish

theorem proposition_29' : ∀ (a b c d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine g h EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point EF g h) as f
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

-- Alternate angles: AGH equals GHD.
theorem proposition_29_alternate : ∀ (a d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a g AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  a.opposingSides d GH ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d :=
by
  euclid_intros
  euclid_apply (extend_point AB a g) as b
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point GH g h) as f
  euclid_apply (extend_point GH h g) as e
  euclid_apply (proposition_29 a b c d e f g h AB CD GH)
  euclid_finish

-- The exterior angle EGB equals the interior and opposite angle GHD.
theorem proposition_29_exterior : ∀ (b d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine e h EF ∧
  between e g h ∧ b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ e:g:b = ∠ g:h:d :=
by
  euclid_intros
  euclid_apply (extend_point AB b g) as a
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point EF g h) as f
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

-- The internal angles on the same side, BGH and GHD, make two right angles.
theorem proposition_29_interior : ∀ (b d g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h EF ∧
  b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point AB b g) as a
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point EF g h) as f
  euclid_apply (extend_point EF h g) as e
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

end Elements.Book1
