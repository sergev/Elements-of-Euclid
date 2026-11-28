import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop14
import Elements.Book6.Prop01

namespace Elements.Book6

open Elements.Book5

/--
The figure of Prop. 6.15: triangles `abc`, `ade` with the angles at `a` equal, and `ca`,
`ad` straight-on; then `ea`, `ab` are straight-on [Prop. 1.14]. Join `BD`:
`CA : AD :: CAB : BAD` and `EA : AB :: EAD : BAD` [Prop. 6.1].
-/
theorem proposition_15_ratios : ∀ (a b c d e : Point) (AB CD AE : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a e AE ∧ c.onLine CD ∧
  a.onLine CD ∧ d.onLine CD ∧ between c a d ∧ b.opposingSides e CD ∧
  ∠ b:a:c = ∠ d:a:e →
  (c─a) ∶ (a─d) ∷ △a:b:c ∶ △a:b:d ∧ (e─a) ∶ (a─b) ∷ △a:d:e ∶ △a:b:d :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_13 e a d c AE CD)
  euclid_apply (Elements.Book1.proposition_14 c a b e CD AB AE)
  subst ‹AB = AE›
  have h₁ := proposition_1 b c a d CD (by euclid_finish)
  have h₂ := proposition_1 d e a b AB (by euclid_finish)
  exact ⟨h₁.congr rfl rfl (by size_perm) (by size_perm),
    h₂.congr rfl rfl (by size_perm) (by size_perm)⟩

/--
In equal triangles `abc`, `ade` with one angle equal to one angle, `bac` to `dae`, the
sides about the equal angles are reciprocally proportional: `ca : ad :: ea : ab`. The
triangles are laid down as Euclid lays them, `ca` straight-on to `ad`.
-/
theorem proposition_15 : ∀ (a b c d e : Point) (AB CD AE : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a e AE ∧ c.onLine CD ∧
  a.onLine CD ∧ d.onLine CD ∧ between c a d ∧ b.opposingSides e CD ∧
  ∠ b:a:c = ∠ d:a:e ∧ Triangle.area △a:b:c = Triangle.area △a:d:e →
  (c─a) ∶ (a─d) ∷ (e─a) ∶ (a─b) :=
by
  euclid_intros
  obtain ⟨h₁, h₂⟩ := proposition_15_ratios a b c d e AB CD AE (by euclid_finish)
  -- `ABC` is equal to `ADE`, so `CAB : BAD :: EAD : BAD` [Prop. 5.7]; so
  -- `CA : AD :: EA : AB` [Props. 6.1, 5.11]
  have h₃ := Proportional.of_eq h₁.2.2.1 h₁.2.2.2.1 (q := △a:d:e) ‹_›
  exact (h₁.trans h₃).trans h₂.symm

/--
Triangles `abc`, `ade` with one angle equal to one angle, `bac` to `dae`, and the sides
about the equal angles reciprocally proportional, `ca : ad :: ea : ab`, are equal.
-/
theorem proposition_15' : ∀ (a b c d e : Point) (AB CD AE : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine a e AE ∧ c.onLine CD ∧
  a.onLine CD ∧ d.onLine CD ∧ between c a d ∧ b.opposingSides e CD ∧
  ∠ b:a:c = ∠ d:a:e ∧ (c─a) ∶ (a─d) ∷ (e─a) ∶ (a─b) →
  Triangle.area △a:b:c = Triangle.area △a:d:e :=
by
  euclid_intros
  obtain ⟨h₁, h₂⟩ := proposition_15_ratios a b c d e AB CD AE (by euclid_finish)
  -- `CAB : BAD :: CA : AD :: EA : AB :: EAD : BAD` [Props. 6.1, 5.11], so `ABC` is
  -- equal to `ADE` [Prop. 5.9]
  exact ((h₁.symm.trans ‹(c─a) ∶ (a─d) ∷ (e─a) ∶ (a─b)›).trans h₂).eq_left rfl

end Elements.Book6
