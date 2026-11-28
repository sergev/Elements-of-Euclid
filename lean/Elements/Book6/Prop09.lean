import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop31
import Elements.Book6.Prop02

namespace Elements.Book6

open Elements.Book5 Magnitude

/--
To cut off a prescribed part from a given straight line `ab`: the `m`-th part `af`,
`m • af = ab`. Euclid prescribes a third; here any part, his `DE`, `EC` equal to `AD` laid
off `m - 1` times by induction (`multiple_on_line'`).
-/
theorem proposition_9 (m : ℕ+) : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ (f : Point) (hf : 0 < size (a─f)) (hb : 0 < size (a─b)),
  f.onLine AB ∧ (between a f b ∨ f = b) ∧ m • mag (a─f) hf = mag (a─b) hb :=
by
  euclid_intros
  have hab : 0 < size (a─b) := size_segment_pos.mpr ‹_›
  induction m using PNat.recOn with
  | one => exact ⟨b, hab, hab, ‹_›, Or.inr rfl, rfl⟩
  | succ k _ =>
  -- let `AC` be drawn from `a` at a random angle with `AB`, and `d` a random point on it
  euclid_apply (Elements.Book1.proposition_1 a b AB) as d
  euclid_apply (line_from_points a d) as AC
  have had : 0 < size (a─d) := size_segment_pos.mpr (by euclid_finish)
  -- `DE`, `EC`, … equal to `AD`: `AC` is `AD` taken `m` times [Prop. 1.3]
  obtain ⟨c, hac, hcAC, hdc, hlen⟩ := multiple_on_line' (k + 1) ‹a.onLine AC›
    ‹d.onLine AC› had
  have hadc : between a d c := by
    rcases hdc with h | h
    · exact h
    · subst h
      have h₁ := mult_inj_left (hlen.symm.trans (one_mult _).symm)
      have := k.pos
      exact absurd (congrArg PNat.val h₁) (by rw [PNat.add_coe, PNat.one_coe]; omega)
  -- so `DC` is `AD` taken `m - 1` times
  have hdc' : 0 < size (d─c) := size_segment_pos.mpr (by euclid_finish)
  have hDC : mag (d─c) hdc' = k • mag (a─d) had := by
    have e₁ : mag (d─c) hdc' + mag (a─d) had = mag (a─c) hac :=
      mag_add (by rw [size_segment, size_segment, size_segment, add_comm]; euclid_finish)
    rw [hlen, mult_succ] at e₁
    exact add_right_cancel e₁
  -- join `BC`, and draw `DF` through `d` parallel to it [Prop. 1.31]
  euclid_apply (line_from_points b c) as BC
  euclid_apply (Elements.Book1.proposition_31 d b c BC) as DF
  euclid_apply (parallel_meets b DF BC AB)
  euclid_apply (intersection_lines DF AB) as f
  -- `CD : DA :: BF : FA` [Prop. 6.2]
  obtain ⟨hcd, hda, hbf, hfa, h⟩ := proposition_2 a c b d f AC BC AB DF
    ⟨by euclid_finish, ‹_›, by euclid_finish, ‹_›, ‹_›, by euclid_finish⟩
  -- `CD` is `DA` taken `m - 1` times, so `BF` is `FA` taken as many [Def. 5.5]
  have hBF := (h.eq 1 k).mp (by
    rw [one_mult, mag_congr (hq := hdc') (size_segment_symm c d), hDC,
      mag_congr (hq := had) (size_segment_symm d a)])
  rw [one_mult] at hBF
  -- so `BA` is `AF` taken `m` times
  have haf : 0 < size (a─f) := by rw [size_segment_symm]; exact hfa
  refine ⟨f, haf, hab, ‹_›, Or.inl (by euclid_finish), ?_⟩
  rw [mult_succ, mag_congr (hq := hfa) (size_segment_symm a f), ← hBF, add_comm]
  apply mag_add
  rw [size_segment, size_segment, size_segment, segment_symmetric b f]
  euclid_finish

end Elements.Book6
