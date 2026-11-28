import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop14
import Elements.Book1.Prop15
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

/-- Prop. 6.15 with the triangles laid down as Euclid lays them, `ca` straight-on to
`ad`. -/
theorem proposition_15_placed : ∀ (a b c d e : Point) (AB CD AE : Line),
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

/-- Prop. 6.15, the converse, with the triangles laid down as Euclid lays them. -/
theorem proposition_15_placed' : ∀ (a b c d e : Point) (AB CD AE : Line),
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

/--
Let the triangle `def` be laid down as `ad'f'`, `ad'` straight-on to `ca` and `af'` to
`ba` [Prop. 1.3]: the angle `d'af'` is equal to `bac` [Prop. 1.15], so to `edf`, and the
triangles `ad'f'`, `def` are equal [Prop. 1.4].
-/
theorem proposition_15_place : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧ ∠ b:a:c = ∠ e:d:f →
  ∃ (d' f' : Point) (AF : Line), distinctPointsOnLine a f' AF ∧ d'.onLine CA ∧
  between c a d' ∧ b.opposingSides f' CA ∧ ∠ b:a:c = ∠ d':a:f' ∧
  |(a─d')| = |(d─e)| ∧ |(a─f')| = |(d─f)| ∧
  Triangle.area △a:d':f' = Triangle.area △d:e:f :=
by
  euclid_intros
  euclid_apply (lay_beyond c a d e CA) as d'
  euclid_apply (lay_beyond b a d f AB) as f'
  euclid_apply (Elements.Book1.proposition_15 c d' b f' a CA AB)
  euclid_apply (line_from_points d' f') as DF'
  euclid_apply (Elements.Book1.proposition_4 a d' f' d e f CA DF' AB DE EF FD)
  use d', f', AB
  euclid_finish

/--
In equal triangles `abc`, `def` with one angle equal to one angle, `bac` to `edf`, the
sides about the equal angles are reciprocally proportional: `ca : de :: fd : ab`.
-/
theorem proposition_15 : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧ ∠ b:a:c = ∠ e:d:f ∧
  Triangle.area △a:b:c = Triangle.area △d:e:f → (c─a) ∶ (d─e) ∷ (f─d) ∶ (a─b) :=
by
  euclid_intros
  -- let `CA` be laid down straight-on to `AD`; then `EA` is straight-on to `AB`
  euclid_apply (proposition_15_place a b c d e f AB BC CA DE EF FD) as (d', f', AF)
  have h := proposition_15_placed a b c d' f' AB CA AF (by euclid_finish)
  exact h.congr rfl ‹|(a─d')| = |(d─e)|› (by rw [size_segment, size_segment,
    segment_symmetric f' a, segment_symmetric f d]; exact ‹|(a─f')| = |(d─f)|›) rfl

/--
Triangles `abc`, `def` with one angle equal to one angle, `bac` to `edf`, and the sides
about the equal angles reciprocally proportional, `ca : de :: fd : ab`, are equal.
-/
theorem proposition_15' : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧ ∠ b:a:c = ∠ e:d:f ∧
  (c─a) ∶ (d─e) ∷ (f─d) ∶ (a─b) → Triangle.area △a:b:c = Triangle.area △d:e:f :=
by
  euclid_intros
  euclid_apply (proposition_15_place a b c d e f AB BC CA DE EF FD) as (d', f', AF)
  have h : (c─a) ∶ (a─d') ∷ (f'─a) ∶ (a─b) :=
    ‹(c─a) ∶ (d─e) ∷ (f─d) ∶ (a─b)›.congr rfl ‹|(a─d')| = |(d─e)|›.symm
      (by rw [size_segment, size_segment, segment_symmetric f' a,
        segment_symmetric f d]; exact ‹|(a─f')| = |(d─f)|›.symm) rfl
  have := proposition_15_placed' a b c d' f' AB CA AF (by euclid_finish)
  linarith

end Elements.Book6
