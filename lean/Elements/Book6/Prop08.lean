import SystemE
import Elements.Book1.Prop17
import Elements.Book4.Lemmas
import Elements.Book6.Prop04

namespace Elements.Book6

open Elements.Book5

/-- The perpendicular `AD` from the right angle falls between `b` and `c`: the angles at
`b` and `c` are less than right angles [Prop. 1.17]. -/
theorem proposition_8_between : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ ∠ b:a:c = ∟ ∧ d.onLine BC ∧ ∠ a:d:b = ∟ ∧
  ∠ a:d:c = ∟ → between b d c :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_17 c b a BC AB CA)
  euclid_apply (Elements.Book1.proposition_17 b c a BC CA AB)
  have : d ≠ b := by
    intro h
    subst h
    euclid_finish
  have : d ≠ c := by
    intro h
    subst h
    euclid_finish
  euclid_apply (Elements.Book4.foot_on_ray c b a d BC)
  euclid_apply (Elements.Book4.foot_on_ray b c a d BC)
  euclid_apply (between_points b d c BC)
  rcases ‹between b d c ∨ between d b c ∨ between b c d› with h | h | h
  · exact h
  · euclid_finish
  · euclid_finish

/--
If in the right-angled triangle `abc`, with the right angle at `a`, `AD` is drawn
perpendicular to the base `BC`, the triangles `dba`, `dac` about the perpendicular are
similar to the whole and to one another.
-/
theorem proposition_8 : ∀ (a b c d : Point) (AB BC CA AD : Line),
  formTriangle a b c AB BC CA ∧ ∠ b:a:c = ∟ ∧ distinctPointsOnLine a d AD ∧
  d.onLine BC ∧ ∠ a:d:b = ∟ ∧ ∠ a:d:c = ∟ →
  similarTriangles a b c d b a ∧ similarTriangles a b c d a c ∧
  similarTriangles d b a d a c :=
by
  euclid_intros
  euclid_apply (proposition_8_between a b c d AB BC CA)
  euclid_apply (equal_angles b a a c d AB BC)
  euclid_apply (equal_angles c a a b d CA BC)
  euclid_apply (triangle_angles a b c AB BC CA)
  euclid_apply (triangle_angles d b a BC AB AD)
  euclid_apply (triangle_angles d a c AD CA BC)
  -- the angle `BAC` is equal to `ADB`, being right, and that at `b` is common: the
  -- remaining `ACB` is equal to `BAD` [Prop. 1.32]; `ABC` is equiangular to `DBA`, and
  -- has the sides about the equal angles proportional [Prop. 6.4]: they are similar
  -- [Def. 6.1]. So for `ABC` and `DAC`, and for `DBA` and `DAC`
  exact ⟨proposition_4 a b c d b a AB BC CA BC AB AD (by euclid_finish),
    proposition_4 a b c d a c AB BC CA AD CA BC (by euclid_finish),
    proposition_4 d b a d a c BC AB AD AD CA BC (by euclid_finish)⟩

/-- Corollary: the perpendicular `ad` is in mean proportion to the pieces `bd`, `dc` of
the base. -/
theorem proposition_8_corollary : ∀ (a b c d : Point) (AB BC CA AD : Line),
  formTriangle a b c AB BC CA ∧ ∠ b:a:c = ∟ ∧ distinctPointsOnLine a d AD ∧
  d.onLine BC ∧ ∠ a:d:b = ∟ ∧ ∠ a:d:c = ∟ → (b─d) ∶ (d─a) ∷ (d─a) ∶ (d─c) :=
by
  euclid_intros
  obtain ⟨-, -, -, -, -, h⟩ := proposition_8 a b c d AB BC CA AD (by euclid_finish)
  -- `AD : DB :: CD : DA` in the similar triangles `DBA`, `DAC`, and inversely
  -- [Prop. 5.7 corollary]
  exact h.inv.congr (by size_perm) (by size_perm) rfl (by size_perm)

end Elements.Book6
