import SystemE
import Elements.Book1.Prop30
import Elements.Book1.Prop43
import Elements.Book6.Prop26

namespace Elements.Book6

open Elements.Book5 Magnitude

/-- Parallelograms `lpac`, `phcb` on equal bases `ac`, `cb` of `AB`, between the same
parallels, are equal [Prop. 6.1, Def. 5.5]. -/
theorem proposition_27_equal : ∀ (a b c l p h : Point) (LH AB AG CD BE : Line),
  formParallelogram l p a c LH AB AG CD ∧ formParallelogram p h c b LH AB CD BE ∧
  between a c b ∧ |(a─c)| = |(c─b)| → ▱ l:p:a:c = ▱ p:h:c:b :=
by
  euclid_intros
  obtain ⟨hac, hcb, h₁, h₂, hp⟩ := proposition_1' p a c b l h LH AB AG CD BE
    (by euclid_finish)
  have := (hp.eq 1 1).mp (by rw [one_mult, one_mult]; exact mag_congr ‹_›)
  rw [one_mult, one_mult] at this
  have := mag_inj.mp this
  rw [size_quadrilateral, size_quadrilateral] at this
  euclid_apply (parallelogram_area p h c b LH AB CD BE)
  area_linarith

set_option maxHeartbeats 1000000 in
/--
Of the parallelograms applied to a straight line `ab` and falling short by parallelograms
similar, and similarly laid down, to the one on half of it, the greatest is the one on
the half. `c` halves `ab`; `adbe`... the parallelogram `gdac` on `ac` falls short by
`dcbe` on `cb`; `lfak` on `ak` falls short by `fkbh`, similar to `dcbe`. Euclid's figure:
the deficit `fkbh` is less than `dcbe`, `k` between `c` and `b`.
-/
theorem proposition_27 : ∀ (a b c d e f g h k l : Point) (AB DE AG CD BE KM LH : Line),
  between a c b ∧ |(a─c)| = |(c─b)| ∧
  formParallelogram d e c b DE AB CD BE ∧ formParallelogram g d a c DE AB AG CD ∧
  formParallelogram f h k b LH AB KM BE ∧ formParallelogram l f a k LH AB AG KM ∧
  between c k b ∧ f.sameSide d AB ∧ similarQuadrilaterals b c d e b k f h →
  ▱ l:f:a:k < ▱ g:d:a:c :=
by
  euclid_intros
  euclid_apply (parallelogram_same_side f h k b LH AB KM BE)
  -- `BK` is less than `BC`, so `BH` than `BE` [Prop. 5.14]
  have hbh : |(b─h)| < |(b─e)| := by
    obtain ⟨heb, hbc, hhb, hbk, r⟩ := ‹(e─b) ∶ (b─c) ∷ (h─b) ∶ (b─k)›
    have r := Elements.Book5.proposition_14 r
    have hkc : |(b─k)| < |(b─c)| := by
      have := between_if c k b ‹_›
      have : 0 < |(c─k)| := size_segment_pos.mpr (by euclid_finish)
      have := segment_symmetric c b
      have := segment_symmetric k b
      linarith
    rcases lt_trichotomy (mag (h─b) hhb) (mag (e─b) heb) with x | x | x
    · have y : |(h─b)| < |(e─b)| := mag_lt.mp x
      have := segment_symmetric h b
      have := segment_symmetric e b
      linarith
    · have y : |(b─c)| = |(b─k)| := mag_inj.mp (r.2.1 x.symm)
      linarith
    · have y : |(b─c)| < |(b─k)| := mag_lt.mp (r.2.2 x)
      linarith
  have : between b h e := by
    euclid_apply (between_points b h e BE)
    rcases ‹between b h e ∨ between h b e ∨ between b e h› with x | x | x
    · exact x
    · euclid_finish
    · euclid_apply (between_if b e h)
      have := segment_gte_zero (e─h)
      linarith
  -- `DB`, `FB` are similar: they are about the same diagonal [Prop. 6.26]
  have : formParallelogram b k h f AB LH BE KM := by euclid_finish
  have hf := proposition_26 b c d e k f h AB DE BE CD KM LH ⟨by euclid_finish,
    this, by euclid_finish, by euclid_finish, by euclid_finish, ‹_›, ‹_›, ‹_›,
    ‹_›⟩
  euclid_apply (line_from_points d b) as DB
  euclid_apply (parallel_meets c LH AB CD)
  euclid_apply (intersection_lines LH CD) as p
  euclid_apply (parallel_meets e KM BE DE)
  euclid_apply (intersection_lines KM DE) as m
  euclid_assert between d p c
  euclid_assert f.sameSide d AB
  euclid_assert f.sameSide b DE
  euclid_assert m.sameSide d AB
  euclid_assert k.sameSide b DE
  euclid_apply (between_points m f k KM)
  have : between m f k := by
    rcases ‹between m f k ∨ between f m k ∨ between m k f› with x | x | x
    · exact x
    · have : f.sameSide k DE := by euclid_finish
      exact absurd this (pasch_3 f m k DE ⟨x, ‹m.onLine DE›⟩)
    · have : m.sameSide f AB := by euclid_finish
      exact absurd this (pasch_3 m k f AB ⟨x, ‹k.onLine AB›⟩)
  euclid_assert between d m e
  euclid_assert between l p f
  euclid_assert between p f h
  euclid_apply (Elements.Book1.proposition_30 DE LH AB)
  euclid_apply (Elements.Book1.proposition_30 CD KM BE)
  -- the complement `CF` is equal to `FE` [Prop. 1.43]
  euclid_apply (Elements.Book1.proposition_43 d c b e p h k m f DE AB CD BE DB LH KM)
  -- `CH`, `KE` are `CF`, `FB` and `FB`, `FE`; `AF` is `CG` and `CF`; `DB` is `DF`, `FE`,
  -- `CF`, `FB`
  euclid_apply (sum_parallelograms_area p h c b f k LH AB CD BE)
  euclid_apply (sum_parallelograms_area l f a k p c LH AB AG KM)
  euclid_apply (sum_parallelograms_area d e c b m k DE AB CD BE)
  euclid_apply (sum_parallelograms_area d c m k p f CD KM DE AB)
  euclid_apply (sum_parallelograms_area m k e b f h KM BE DE AB)
  -- `CG` is equal to `CH`, `AC` being equal to `CB` [Prop. 6.1]; `AD` to `DB`
  euclid_apply (proposition_27_equal a b c l p h LH AB AG CD BE)
  euclid_apply (proposition_27_equal a b c g d e DE AB AG CD BE)
  -- so `AF` is the gnomon, less than `DB` by `DF`, and `AD` is greater than `AF`
  have : 0 < ▱ d:m:p:f := Area.parallelogram_pos d m p f DE LH CD KM (by euclid_finish)
  area_linarith

end Elements.Book6
