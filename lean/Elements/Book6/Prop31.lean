import SystemE
import Elements.Book1.Prop17
import Elements.Book4.Lemmas
import Elements.Book5.Prop24
import Elements.Book6.Prop08
import Elements.Book6.Prop19

namespace Elements.Book6

open Elements.Book5 Magnitude

/--
In the right-angled triangle `abc`, with the right angle at `a`, the figure on the side
`bc` subtending the right angle is equal to the similar, and similarly described, figures
on the sides `ba`, `ac` about it, together. The figures are triangles `pbc`, `qba`, `rac`.
-/
theorem proposition_31 : ∀ (a b c p q r : Point)
    (AB BC CA PB PC QB QA RA RC : Line),
  formTriangle a b c AB BC CA ∧ ∠ b:a:c = ∟ ∧ formTriangle p b c PB BC PC ∧
  formTriangle q b a QB AB QA ∧ formTriangle r a c RA CA RC ∧
  similarTriangles p b c q b a ∧ similarTriangles p b c r a c →
  Triangle.area △p:b:c = Triangle.area △q:b:a + Triangle.area △r:a:c :=
by
  euclid_intros
  -- let the perpendicular `AD` be drawn [Prop. 1.12]
  euclid_apply (Elements.Book1.proposition_17 c b a BC AB CA)
  euclid_apply (Elements.Book1.proposition_17 b c a BC CA AB)
  euclid_apply (Elements.Book4.foot_between b c a BC) as d
  euclid_apply (line_from_points a d) as AD
  -- `ABD`, `ADC` are similar to `ABC` [Prop. 6.8]: `CB : BA :: AB : BD`, and
  -- `BC : CA :: AC : CD`
  obtain ⟨⟨-, h₁, -, -⟩, ⟨-, -, h₂, -⟩, -⟩ := proposition_8 a b c d AB BC CA AD
    (by euclid_finish)
  have h₁ : (b─c) ∶ (b─a) ∷ (b─a) ∶ (b─d) :=
    h₁.inv.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  have h₂ : (b─c) ∶ (a─c) ∷ (a─c) ∶ (d─c) :=
    h₂.congr rfl (by size_perm) rfl (by size_perm)
  -- so `CB : BD` as the figure on `CB` to that on `BA`, and `BC : CD` as the figure on
  -- `BC` to that on `CA` [Prop. 6.19 corollary]
  have h₃ := proposition_19_corollary p b c q b a b d PB BC PC QB AB QA
    ⟨by euclid_finish, by euclid_finish, ⟨by euclid_finish, ‹_›, ‹_›, ‹_›⟩, h₁⟩
  have h₄ := proposition_19_corollary p b c r a c d c PB BC PC RA CA RC
    ⟨by euclid_finish, by euclid_finish, ⟨by euclid_finish, ‹_›, ‹_›, ‹_›⟩, h₂⟩
  -- so `BC : BD, DC` as the figure on `BC` to those on `BA`, `AC` [Prop. 5.24]
  obtain ⟨hbd, hbc, hq, hp, h₃⟩ := h₃.inv
  obtain ⟨hdc, hbc', hr, hp', h₄⟩ := h₄.inv
  -- Model: the fourth proportional that 5.24 assumes is an area, and the figure gives
  -- none; the positive reals have one.
  have h₅ := Elements.Book5.proposition_24 h₃ h₄ (Positive.fourth _ _ _)
  -- `BD`, `DC` together are `BC`
  have e₁ : mag (b─d) hbd + mag (d─c) hdc = mag (b─c) hbc :=
    mag_add (between_if b d c ‹_›)
  rw [e₁] at h₅
  -- and `BC : BC :: P : P` [Def. 5.5]; so the figures on `BA`, `AC` together have to the
  -- figure on `BC` the same ratio as it has, and are equal to it [Props. 5.11, 5.9]
  have h₆ : Proportion (mag (b─c) hbc) (mag (b─c) hbc) (mag (△p:b:c) hp)
      (mag (△p:b:c) hp) := Proportion.of_imp
    (fun _ _ h => mult_lt_mult_left _ (lt_of_mult_lt_mult_left h))
    (fun _ _ h => by rw [mult_inj_left h])
    (fun _ _ h => mult_lt_mult_left _ (lt_of_mult_lt_mult_left h))
  have h₇ := Elements.Book5.proposition_9 (Elements.Book5.proposition_11 h₅.symm h₆)
  have := Kind.of_inj.mp ((Kind.of_add hq hr).trans h₇)
  exact this.symm

end Elements.Book6
