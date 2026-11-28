import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop04
import Elements.Book1.Prop15
import Elements.Book1.Prop17
import Elements.Book1.Prop23
import Elements.Book1.Prop27
import Elements.Book1.Prop34
import Elements.Book6.Prop02

namespace Elements.Book6

open Elements.Book5

/--
Prop. 1.28 with the corresponding angles `abc`, `gcx` on the line `BC`: `AB` is parallel
to `CG`. Produce `GC` to `y`: `bcy` is equal to `gcx` [Prop. 1.15], and alternate to `abc`
[Prop. 1.27].
-/
theorem parallel_of_corresponding : ∀ (a b c g x : Point) (AB BC CG : Line),
  distinctPointsOnLine a b AB ∧ b.onLine BC ∧ c.onLine BC ∧ x.onLine BC ∧
  distinctPointsOnLine c g CG ∧ between b c x ∧ a.sameSide g BC ∧
  ∠ a:b:c = ∠ g:c:x → ¬(AB.intersectsLine CG) :=
by
  euclid_intros
  euclid_apply (extend_point CG g c) as y
  euclid_apply (Elements.Book1.proposition_15 b x g y c BC CG)
  euclid_apply (Elements.Book1.proposition_27 a y b c AB CG BC)
  euclid_finish

/--
Prop. 6.4 with the triangles placed as Euclid places them: `xgc` beside `abc`, the base
`cx` straight-on to `bc`, with the angles at `b`, `c` equal to those at `c`, `x`.
-/
theorem proposition_4_placed : ∀ (a b c g x : Point) (AB BC CA CG XG : Line),
  formTriangle a b c AB BC CA ∧ distinctPointsOnLine c g CG ∧
  distinctPointsOnLine x g XG ∧ x.onLine BC ∧ between b c x ∧ a.sameSide g BC ∧
  ∠ a:b:c = ∠ g:c:x ∧ ∠ a:c:b = ∠ g:x:c →
  (a─b) ∶ (b─c) ∷ (g─c) ∶ (c─x) ∧ (b─c) ∶ (c─a) ∷ (c─x) ∶ (x─g) :=
by
  euclid_intros
  -- `ABC`, `ACB` are less than two right angles [Prop. 1.17], so `BA`, `XG` produced
  -- meet [Post. 5], at `f`
  euclid_apply (Elements.Book1.proposition_17 a b c AB BC CA)
  euclid_apply (equal_angles b a a c x AB BC)
  euclid_apply (equal_angles x c b g g BC XG)
  euclid_apply (lines_intersect a b x g AB BC XG) as f
  -- `BF` is parallel to `CG`, and `AC` to `FX` [Prop. 1.28]
  euclid_apply (parallel_of_corresponding a b c g x AB BC CG)
  euclid_apply (parallel_of_corresponding g x c a b XG BC CA)
  euclid_assert between b a f
  euclid_assert between x g f
  -- `FACG` is a parallelogram: `FA` is equal to `GC`, and `AC` to `FG` [Prop. 1.34]
  euclid_apply (Elements.Book1.proposition_34' a f c g AB CG CA XG)
  -- `AC` is parallel to the side `FX` of the triangle `FBX`: `BA : AF :: BC : CX`
  -- [Prop. 6.2], and `AF` is `CG`: `BA : CG :: BC : CX`; alternately,
  -- `AB : BC :: GC : CX` [Prop. 5.16]
  have h₁ := proposition_2 b f x a c AB XG BC CA
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›, by euclid_finish⟩
  have h₁ : (a─b) ∶ (b─c) ∷ (g─c) ∶ (c─x) :=
    (h₁.inv.congr (by size_perm) (by rw [size_segment, size_segment]; euclid_finish)
      (by size_perm) (by size_perm)).alt
  -- `CG` is parallel to the side `BF` of the triangle `XBF`: `BC : CX :: FG : GX`
  -- [Prop. 6.2], and `FG` is `AC`: `BC : CX :: AC : GX`; alternately,
  -- `BC : CA :: CX : XG` [Prop. 5.16]
  have h₂ := proposition_2 x b f c g BC AB XG CG
    ⟨by euclid_finish, by euclid_finish, ‹_›, ‹_›, ‹_›, by euclid_finish⟩
  have h₂ : (b─c) ∶ (c─a) ∷ (c─x) ∶ (x─g) :=
    (h₂.congr rfl rfl (by rw [size_segment, size_segment]; euclid_finish)
      (by size_perm)).alt
  exact ⟨h₁, h₂⟩

/--
The triangle `def` placed beside `abc`: on `BC` produced, `cx` equal to `ef` [Prop. 1.3],
and `cg` equal to `ed` making with it an angle equal to `def` [Prop. 1.23], on `a`'s side.
The triangle `gcx` is equal to `def` in all respects [Prop. 1.4].
-/
theorem proposition_4_place : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD →
  ∃ (g x : Point) (CG XG : Line), distinctPointsOnLine c g CG ∧
  distinctPointsOnLine x g XG ∧ x.onLine BC ∧ between b c x ∧ a.sameSide g BC ∧
  |(c─x)| = |(e─f)| ∧ |(c─g)| = |(e─d)| ∧ |(x─g)| = |(f─d)| ∧
  ∠ g:c:x = ∠ d:e:f ∧ ∠ g:x:c = ∠ d:f:e ∧ ∠ c:g:x = ∠ e:d:f :=
by
  euclid_intros
  euclid_apply (extend_point_longer BC b c (e─f)) as y
  euclid_apply (Elements.Book1.proposition_3 c y e f BC EF) as x
  euclid_apply (Elements.Book1.proposition_23_side c x e d f a BC DE EF) as p
  euclid_apply (line_from_points c p) as CG
  euclid_apply (extend_point_longer CG c p (e─d)) as q
  euclid_apply (Elements.Book1.proposition_3 c q e d CG DE) as g
  euclid_apply (equal_angles c p g x x CG BC)
  euclid_apply (line_from_points x g) as XG
  euclid_apply (Elements.Book1.proposition_4 c g x e d f CG XG BC DE FD EF)
  use g, x, CG, XG
  euclid_finish

/--
In equiangular triangles `abc`, `def` the sides about the equal angles are proportional,
and those subtending equal angles correspond: the triangles are similar.
-/
theorem proposition_4 : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧
  equiangularTriangles a b c d e f → similarTriangles a b c d e f :=
by
  euclid_intros
  -- let `BC` be placed straight-on to `CE`
  euclid_apply (proposition_4_place a b c d e f AB BC CA DE EF FD) as (g, x, CG, XG)
  have ⟨h₁, h₂⟩ := proposition_4_placed a b c g x AB BC CA CG XG
    (by euclid_finish)
  -- via equality, `BA : AC :: CG : GX` [Prop. 5.22]
  have h₃ := (h₁.exAequali h₂).inv
  have e₁ : size (g─c) = size (d─e) := by
    rw [size_segment, size_segment]; euclid_finish
  have e₂ : size (c─x) = size (e─f) := ‹_›
  have e₃ : size (x─g) = size (f─d) := ‹_›
  refine ⟨⟨‹_›, ‹_›, ‹_›⟩, h₁.congr rfl rfl e₁ e₂, h₂.congr rfl rfl e₂ e₃,
    h₃.congr (by size_perm) (by size_perm) e₃ e₁⟩

end Elements.Book6
