import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop03
import Elements.Book1.Prop31
import Elements.Book1.Prop38
import Elements.Book6.Definitions

/-
Multiples in the figure. Prop. 6.1 lays off "any number" of straight lines equal to a
base, and Prop. 6.9 a part of a line: equal segments laid off `m` times. That is
induction on `m`, with each step a System E construction.
-/

namespace Elements.Book6

open Elements.Book5 Magnitude

/--
One more copy: on the line `L` beyond `g` (which is `c`, or beyond `c` from `b`), a point
`e` with `ge` equal to `bc` [Prop. 1.3]; the triangle on `ge` with vertex `a` is equal to
that on `bc` [Prop. 1.38], so `△abe` is `△abg` and `△abc` together.
-/
theorem multiple_step : ∀ (a b c g : Point) (L : Line),
  b.onLine L ∧ c.onLine L ∧ g.onLine L ∧ ¬(a.onLine L) ∧ b ≠ c ∧
  (between b c g ∨ g = c) →
  ∃ e : Point, e.onLine L ∧ between b c e ∧ between b g e ∧
  |(b─e)| = |(b─g)| + |(b─c)| ∧
  Triangle.area △a:b:e = Triangle.area △a:b:g + Triangle.area △a:b:c :=
by
  euclid_intros
  have : b ≠ g := by
    rcases ‹between b c g ∨ g = c› with h | h
    · euclid_finish
    · subst h
      euclid_finish
  euclid_apply (extend_point_longer L b g (b─c)) as x
  euclid_apply (Elements.Book1.proposition_3 g x b c L L) as e
  euclid_assert between b g e
  have hce : between b c e := by
    rcases ‹between b c g ∨ g = c› with h | h
    · euclid_finish
    · subst h
      euclid_finish
  euclid_apply (Elements.Book1.proposition_31 a b c L) as AD
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points a e) as AE
  euclid_apply (Elements.Book1.proposition_38 a b c a g e AD L AB AC AG AE)
  euclid_apply (sum_areas_if b e g a L)
  use e
  euclid_finish

/--
`m` copies of `bc` laid off along `L` from `b`, by induction on `m`, each copy by
`multiple_step`: a point `g` with `bg` the `m`-th multiple of `bc`, and the triangle
`abg` the `m`-th multiple of `abc`, since the triangles on the copies are equal to it. The
points between are those of the steps.
-/
theorem multiple_on_line (m : ℕ+) {a b c : Point} {L : Line} (hb : b.onLine L)
    (hc : c.onLine L) (ha : ¬ a.onLine L) (hbc : 0 < size (b─c))
    (habc : 0 < size (△a:b:c)) :
    ∃ (g : Point) (hg : 0 < size (b─g)) (habg : 0 < size (△a:b:g)),
      g.onLine L ∧ (between b c g ∨ g = c) ∧
      mag (b─g) hg = m • mag (b─c) hbc ∧ mag (△a:b:g) habg = m • mag (△a:b:c) habc := by
  induction m using PNat.recOn with
  | one => exact ⟨c, hbc, habc, hc, Or.inr rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨g, hg, habg, hgL, hcg, hlen, harea⟩ := ih
    have hbc' : b ≠ c := size_segment_pos.mp hbc
    obtain ⟨e, heL, hce, hge, hbe, habe⟩ :=
      multiple_step a b c g L ⟨hb, hc, hgL, ha, hbc', hcg⟩
    have hbe' : b ≠ e := by euclid_finish
    refine ⟨e, size_segment_pos.mpr hbe', size_triangle_pos' ⟨hb, heL, hbe'⟩ ha, heL,
      Or.inl hce, ?_, ?_⟩
    · rw [mult_succ, ← hlen, mag_add (r := (b─e)) hbe.symm]
    · rw [mult_succ, ← harea, mag_add (r := △a:b:e) habe.symm]

/-- `m` copies of `bc` laid off along `L` from `b`: `bg` is the `m`-th multiple of
`bc`. -/
theorem multiple_on_line' (m : ℕ+) {b c : Point} {L : Line} (hb : b.onLine L)
    (hc : c.onLine L) (hbc : 0 < size (b─c)) :
    ∃ (g : Point) (hg : 0 < size (b─g)), g.onLine L ∧ (between b c g ∨ g = c) ∧
      mag (b─g) hg = m • mag (b─c) hbc := by
  have hbc' : b ≠ c := size_segment_pos.mp hbc
  -- a point off `L` [Prop. 1.1]
  obtain ⟨a, ha⟩ := Elements.Book1.proposition_1 b c L ⟨hb, hc, hbc'⟩
  have ha' : ¬ a.onLine L := by euclid_finish
  obtain ⟨g, hg, _, hgL, hcg, hlen, _⟩ :=
    multiple_on_line m hb hc ha' hbc (size_triangle_pos' ⟨hb, hc, hbc'⟩ ha')
  exact ⟨g, hg, hgL, hcg, hlen⟩

end Elements.Book6
