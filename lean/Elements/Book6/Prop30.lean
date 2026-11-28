import SystemE
import Elements.Book1.Prop10
import Elements.Book1.Prop14
import Elements.Book1.Prop46
import Elements.Book6.Prop14
import Elements.Book6.Prop29

namespace Elements.Book6

open Elements.Book5 Magnitude

set_option maxHeartbeats 4000000 in
/--
To cut a given finite straight line `ab` in extreme and mean ratio (Def. 6.2), at `e`,
`ae` the greater piece. Euclid applies to `CA`, a side of the square on `AB`, a
parallelogram equal to the square, overshooting by a square [Props. 1.46, 6.29], and
argues with Prop. 6.14.
-/
theorem proposition_30 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB → ∃ e : Point, extremeMeanRatio a b e ∧ |(e─b)| < |(a─e)| :=
by
  euclid_intros
  -- the square `BC` (`abhc`) on `AB` [Prop. 1.46]
  euclid_apply (Elements.Book1.proposition_46 a b AB) as (c, h, CH, CA, BH)
  euclid_apply (line_from_points a h) as AH
  -- the parallelogram `CD` (`cpox`) applied to `CA`, equal to `BC`, overshooting by `AD`
  -- (`qopa`) similar to `BC` [Prop. 6.29]; the figure on the half `MA`, away from `b`
  euclid_apply (Elements.Book1.proposition_10 c a CA) as m
  euclid_apply (extend_point AB b a) as y
  obtain ⟨g, h', AH', HG, GM, hq, hy, hs⟩ := proposition_18_side m a c a b h y CA CA AB BH
    CH (by euclid_finish)
  euclid_apply (equal_angles a c m h' h' CA AH')
  euclid_apply (Elements.Book1.proposition_14 c a b h' CA AB AH')
  obtain ⟨p, o, x, q, NO, AX, MO, hp, hx, hq', ho, hs', harea⟩ :=
    proposition_29 c a m g h' b a c h c a b h CA AH' HG GM AB AH BH CA CH CA AB BH CH
    ⟨by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish,
      by euclid_finish, ‹_›, ‹_›, by euclid_finish, by euclid_finish,
      ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩
  -- `AD` is on `AB` and below it, `CD` reaches the side `CH` of the square
  euclid_apply (Elements.Book1.proposition_30 AX AB MO)
  euclid_apply (parallel_line_unique c AB AX CH)
  euclid_apply (parallelogram_area c h a b CH AB CA BH)
  euclid_assert q.sameSide b CA
  euclid_assert x.sameSide c AB
  euclid_assert o.opposingSides c AB
  have : between x q o := between_of_opposite x q o AB NO (by euclid_finish)
  have hd : 0 < ▱ q:o:a:p := Area.parallelogram_pos q o a p NO CA AB MO (by euclid_finish)
  -- `E` is between `A` and `B`: else `CD` would not be less than the square
  have hqb : between a q b := by
    by_cases q = b
    · exfalso
      subst ‹q = b›
      euclid_assert x = h
      subst ‹x = h›
      euclid_apply (sum_parallelograms_area x o c p q a NO CA CH MO)
      area_linarith
    · euclid_apply (between_points a q b AB)
      rcases ‹between a q b ∨ between q a b ∨ between a b q› with e | e | e
      · exact e
      · euclid_finish
      · exfalso
        euclid_apply (Elements.Book1.proposition_30 NO BH CA)
        have hxq : x.sameSide q BH := by euclid_finish
        have hca : c.sameSide a BH := by euclid_finish
        have := pasch_3 a b q BH ⟨e, by euclid_finish⟩
        have t₁ : ¬(c.sameSide x BH) := fun hcx => this (same_side_trans c a q BH
          ⟨hca, same_side_trans x c q BH ⟨same_side_symm c x BH hcx, hxq⟩⟩)
        have t₂ : ¬(c.onLine BH) := by euclid_finish
        have t₃ : ¬(x.onLine BH) := by euclid_finish
        have : between c h x :=
          between_of_opposite c h x BH CH ⟨by euclid_finish, by euclid_finish,
            by euclid_finish, by euclid_finish, t₂, t₃, t₁⟩
        euclid_apply (sum_parallelograms_area x o c p q a NO CA CH MO)
        euclid_apply (sum_parallelograms_area c x a q h b CH AB CA NO)
        euclid_apply (parallelogram_area x q c a NO CA CH AB)
        have := Area.parallelogram_pos h x b q CH AB BH NO (by euclid_finish)
        area_linarith
  -- `BC` is equal to `CD`; take `CE` from both: `BF` is equal to `AD`
  euclid_apply (Elements.Book1.proposition_30 NO BH CA)
  have t1 : ¬(c.onLine NO) := by euclid_finish
  have t2 : ¬(h.onLine NO) := by euclid_finish
  have t3 : c.sameSide a NO := by euclid_finish
  have t4 : h.sameSide b NO := by euclid_finish
  have := pasch_3 a q b NO ⟨hqb, by euclid_finish⟩
  have t5 : ¬(c.sameSide h NO) := by euclid_finish
  have : between c x h := between_of_opposite c x h NO CH ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, by euclid_finish, t1, t2, t5⟩
  euclid_apply (sum_parallelograms_area x o c p q a NO CA CH MO)
  euclid_apply (sum_parallelograms_area c h a b x q CH AB CA BH)
  euclid_apply (parallelogram_area x q c a NO CA CH AB)
  euclid_apply (parallelogram_area q o a p NO CA AB MO)
  euclid_apply (parallelogram_area x h q b CH AB NO BH)
  have he : ▱ p:o:a:q = ▱ h:b:x:q := by area_linarith
  -- and equiangular: their sides about the equal angles are reciprocally proportional,
  -- `AE : EB :: FE : ED` [Prop. 6.14]
  euclid_apply (Elements.Book1.proposition_15 a b x o q AB NO)
  have t6 : o.opposingSides x AB := by euclid_finish
  have t7 : ∠ a:q:o = ∠ x:q:b := by euclid_finish
  have t8 : formParallelogram p o a q MO AB CA NO := by euclid_finish
  have t9 : formParallelogram h b x q BH NO CH AB := by euclid_finish
  have h₁ := proposition_14 p q h a b o x MO AB CA NO BH NO CH ⟨t8, t9, hqb, t6, t7, he⟩
  -- `FE` is equal to `AB`, and `ED` to `AE`: `BA : AE :: AE : EB`
  euclid_apply (Elements.Book1.proposition_34' c x a q CH AB CA NO)
  have hao : |(a─q)| = |(q─o)| := by
    obtain ⟨hhc, hca, haq, hqo, r⟩ := ‹(h─c) ∶ (c─a) ∷ (a─q) ∶ (q─o)›
    have := (r.eq 1 1).mp (by
      rw [one_mult, one_mult]
      exact mag_congr (by simp only [size_segment]; euclid_finish))
    rw [one_mult, one_mult] at this
    exact mag_inj.mp this
  have h₂ : (a─b) ∶ (a─q) ∷ (a─q) ∶ (q─b) :=
    (h₁.congr rfl rfl (by simp only [size_segment]; euclid_finish) hao.symm).symm
  -- `AB` is greater than `AE`, so `AE` than `EB` [Prop. 5.14]
  refine ⟨q, ⟨hqb, h₂⟩, ?_⟩
  obtain ⟨hab, haq, haq', hqb', r⟩ := h₂
  have := (Elements.Book5.proposition_14 r).1 (mag_lt.mpr (by
    have := between_if a q b hqb
    have : 0 < |(q─b)| := size_segment_pos.mpr (by euclid_finish)
    show |(a─q)| < |(a─b)|
    linarith))
  exact mag_lt.mp this

end Elements.Book6
