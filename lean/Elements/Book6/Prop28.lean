import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop27
import Elements.Book1.Prop30
import Elements.Book1.Prop43
import Elements.Book4.Lemmas
import Elements.Book1.Prop29
import Elements.Book6.Prop25
import Elements.Book6.Prop27

namespace Elements.Book6

open Elements.Book5 Magnitude

/-- Straight lines `EH`, `FG` making with `EF` interior angles equal to two right angles
are parallel: produce `HE` to `h'`; the angles `h'EF`, `EFG` are alternate and equal
[Props. 1.13, 1.27]. -/
theorem parallel_of_interior : ∀ (e f g h : Point) (EF FG HE : Line),
  distinctPointsOnLine e f EF ∧ distinctPointsOnLine f g FG ∧
  distinctPointsOnLine h e HE ∧ h.sameSide g EF ∧ ∠ h:e:f + ∠ e:f:g = ∟ + ∟ →
  ¬(HE.intersectsLine FG) :=
by
  euclid_intros
  euclid_apply (extend_point HE h e) as h'
  euclid_apply (Elements.Book1.proposition_13 f e h' h EF HE)
  euclid_apply (Elements.Book1.proposition_27 h' g e f HE FG EF)
  euclid_finish

/-- A quadrilateral `efgh` equiangular to a parallelogram `abcd` is a parallelogram: its
adjacent angles make two right angles [Props. 1.29, 1.28]. -/
theorem parallelogram_of_equiangular : ∀ (a b c d e f g h : Point)
    (AB CD AD BC EF FG GH HE : Line),
  formParallelogram a b d c AB CD AD BC ∧ quadrilateral e f g h EF FG GH HE ∧
  equiangularQuadrilaterals a b c d e f g h → formParallelogram e f h g EF GH HE FG :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_29_interior d c a b AD BC AB)
  euclid_apply (Elements.Book1.proposition_29_interior a d b c AB CD BC)
  euclid_apply (parallel_of_interior e f g h EF FG HE)
  euclid_apply (parallel_of_interior f g h e FG GH EF)
  euclid_finish

/-- A straight line `GM` making with `GE` the angle that `GF` makes, on `f`'s side, is
`GF`: otherwise one angle would be part of the other. -/
theorem same_ray : ∀ (e g f m : Point) (GE GF GM : Line),
  distinctPointsOnLine g e GE ∧ distinctPointsOnLine g f GF ∧
  distinctPointsOnLine g m GM ∧ ¬(f.onLine GE) ∧ m.sameSide f GE ∧ ∠ e:g:m = ∠ e:g:f →
  GM = GF :=
by
  euclid_intros
  by_contra
  have : ¬(m.onLine GF) := by
    intro h
    euclid_finish
  by_cases m.sameSide e GF
  · euclid_apply (sum_angles_onlyif g e f m GE GF)
    euclid_finish
  · euclid_apply (triple_incidence_2 GE GF GM g e f m)
    euclid_apply (sum_angles_onlyif g e m f GE GM)
    euclid_finish

/--
The excess of the parallelogram `gfeb` (vertices `g`, `e`, `b`, `f` in order) over a
lesser figure `C` (the triangles `d₁d₂d₄`, `d₄d₂d₃`) is a parallelogram `xfyb`: apply to
`GE`, in the angle `EGF`, a parallelogram `geyx` equal to `C` [Prop. 1.45]; it is less
than `gfeb`, so `x` is between `g` and `f`.
-/
theorem excess : ∀ (g e b f d₁ d₂ d₃ d₄ : Point) (GF EB GE BF D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ : Line),
  formParallelogram g f e b GF EB GE BF ∧ formTriangle d₁ d₂ d₄ D₁₂ D₂₄ D₄₁ ∧
  formTriangle d₄ d₂ d₃ D₂₄ D₂₃ D₃₄ ∧
  Triangle.area △d₁:d₂:d₄ + Triangle.area △d₄:d₂:d₃ < ▱ g:f:e:b →
  ∃ (x y : Point) (XY : Line), between g x f ∧ between e y b ∧
  formParallelogram x f y b GF EB XY BF ∧
  ▱ x:f:y:b + (Triangle.area △d₁:d₂:d₄ + Triangle.area △d₄:d₂:d₃) = ▱ g:f:e:b :=
by
  euclid_intros
  euclid_apply (extend_point GF f g) as z
  have := angle_pos_of_not_on_line g e f GE (by euclid_finish)
  euclid_apply (Elements.Book4.angle_lt_flat e g f GF)
  euclid_apply (proposition_25_apply g e z d₁ d₂ d₃ d₄ e g f GE D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ GE GF)
    as (y, x, LL, CM, XY)
  euclid_apply (same_ray e g f x GE GF CM)
  euclid_apply (parallel_line_unique e GF LL EB)
  euclid_apply (parallelogram_area g f e b GF EB GE BF)
  euclid_apply (parallelogram_area g x e y GF EB GE XY)
  have : between g x f := by
    by_cases x = f
    · exfalso
      subst ‹x = f›
      euclid_assert y = b
      subst ‹y = b›
      euclid_apply (parallelogram_area g x e y GF EB GE BF)
      area_linarith
    · euclid_apply (between_points g x f GF)
      rcases ‹between g x f ∨ between x g f ∨ between g f x› with h | h | h
      · exact h
      · euclid_finish
      · exfalso
        euclid_apply (Elements.Book1.proposition_30 XY BF GE)
        euclid_assert between e b y
        euclid_apply (sum_parallelograms_area g x e y f b GF EB GE XY)
        have := Area.parallelogram_pos f x b y GF EB BF XY (by euclid_finish)
        area_linarith
  euclid_apply (Elements.Book1.proposition_30 XY BF GE)
  euclid_assert between e y b
  euclid_apply (sum_parallelograms_area g f e b x y GF EB GE BF)
  refine ⟨x, y, XY, ‹_›, ‹_›, by euclid_finish, ?_⟩
  area_linarith

/--
The gnomon of Prop. 6.28: `e` halves `ab`; `gfeb` is a parallelogram on `eb` and `hgae`
on `ae`; `gpoq` is a parallelogram about the diagonal `gb`. Through `q`, `OQ` meets `AH`,
`BF` at `t`, `s`, and `PQ` meets `AB` at `r`. The complement `PS` is equal to `OR`
[Prop. 1.43]; add `QB`: `PB` is equal to `OB`, which is equal to `TE` [Prop. 6.1]; add
`OR`: `TR` is equal to the gnomon, `gfeb` less `gpoq`.
-/
theorem gnomon : ∀ (a b e f g h o p q : Point) (AB GF GE BF AH OQ PQ GB : Line),
  between a e b ∧ |(a─e)| = |(e─b)| ∧ formParallelogram g f e b GF AB GE BF ∧
  formParallelogram h g a e GF AB AH GE ∧ distinctPointsOnLine g b GB ∧ q.onLine GB ∧
  between g q b ∧ formParallelogram g p o q GF OQ GE PQ ∧ between g o e ∧ between g p f →
  ∃ (r s t : Point), formParallelogram t q a r OQ AB AH PQ ∧
  formParallelogram q s r b OQ AB PQ BF ∧ between a r b ∧
  ▱ t:q:a:r + ▱ g:p:o:q = ▱ g:f:e:b :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_30 OQ AB GF)
  euclid_apply (Elements.Book1.proposition_30 PQ BF GE)
  euclid_apply (Elements.Book1.proposition_30 PQ AH GE)
  euclid_assert q.sameSide b GE
  euclid_assert q.sameSide b GF
  euclid_apply (parallel_meets b OQ AB BF)
  euclid_apply (intersection_lines OQ BF) as s
  euclid_assert between o q s
  euclid_assert between f s b
  euclid_apply (parallel_meets e PQ GE AB)
  euclid_apply (intersection_lines PQ AB) as r
  euclid_assert between e r b
  euclid_apply (parallel_meets a OQ AB AH)
  euclid_apply (intersection_lines OQ AH) as t
  euclid_assert t.sameSide a GE
  euclid_assert between t o q
  -- the complement `PS` is equal to `OR` [Prop. 1.43]
  euclid_apply (Elements.Book1.proposition_43 g e b f o s r p q GF AB GE BF GB OQ PQ)
  -- `OB` is equal to `TE`, `AE` being equal to `EB` [Prop. 6.1]
  euclid_apply (proposition_27_equal a b e t o s OQ AB AH GE BF)
  euclid_apply (sum_parallelograms_area t q a r o e OQ AB AH PQ)
  euclid_apply (sum_parallelograms_area o s e b q r OQ AB GE BF)
  euclid_apply (sum_parallelograms_area g e f b o s GE BF GF AB)
  euclid_apply (sum_parallelograms_area g f o s p q GF OQ GE BF)
  refine ⟨r, s, t, by euclid_finish, by euclid_finish, by euclid_finish, ?_⟩
  area_linarith

/--
The parallelogram `GQ` of Prop. 6.28: `KM` (`pqrs`) is similar to `GB` (`ebfg`) and less
than it, so `GE` exceeds `SP`, and `GF` exceeds `SR` [Props. 6.20 corollary, 5.14]. Make
`GO` equal to `SP`, and `GX` to `SR` [Prop. 1.3], and complete the parallelogram `gxoy`:
it is equal and similar to `KM`, so similar to `GB`, and about the same diagonal
[Props. 6.21, 6.26].
-/
theorem parallelogram_gq : ∀ (e b f g p q r s : Point) (AB GF GE BF PQ QR RS SP : Line),
  formParallelogram g f e b GF AB GE BF ∧ formParallelogram p q s r PQ RS SP QR ∧
  quadrilateral e b f g AB BF GF GE ∧ quadrilateral p q r s PQ QR RS SP ∧
  similarQuadrilaterals e b f g p q r s ∧ |(p─q)| < |(e─b)| →
  ∃ (o x y : Point) (OQ XY GB : Line), between g o e ∧ between g x f ∧
  formParallelogram g x o y GF OQ GE XY ∧ distinctPointsOnLine g b GB ∧ y.onLine GB ∧
  between g y b ∧ ▱ g:x:o:y = Triangle.area △s:p:q + Triangle.area △s:q:r :=
by
  euclid_intros
  -- `GE` exceeds `SP`, and `GF` exceeds `SR` [Prop. 5.14]
  have h₁ : |(s─p)| < |(g─e)| :=
    ‹(g─e) ∶ (e─b) ∷ (s─p) ∶ (p─q)›.lt_first ‹|(p─q)| < |(e─b)|›
  have h₂ : |(r─s)| < |(f─g)| := ‹(f─g) ∶ (g─e) ∷ (r─s) ∶ (s─p)›.lt_first h₁
  euclid_apply (Elements.Book1.proposition_3 g e s p GE SP) as o
  euclid_apply (Elements.Book1.proposition_3 g f s r GF RS) as x
  euclid_apply (Elements.Book1.proposition_31 o g f GF) as OQ
  euclid_apply (Elements.Book1.proposition_31 x g e GE) as XY
  euclid_apply (parallel_meets o XY GE OQ)
  euclid_apply (intersection_lines OQ XY) as y
  euclid_apply (Elements.Book1.proposition_30 OQ AB GF)
  euclid_apply (Elements.Book1.proposition_30 XY BF GE)
  euclid_apply (line_from_points g b) as GB
  euclid_apply (line_from_points p r) as PR
  euclid_apply (line_from_points x o) as XO
  -- the sides of `GQ` and `KM` are equal, and their angles [Props. 1.29, 1.34]
  euclid_apply (Elements.Book1.proposition_34 g x o y GF OQ GE XY XO)
  euclid_apply (Elements.Book1.proposition_34 s p r q SP QR RS PQ PR)
  euclid_apply (Elements.Book1.proposition_34' g f e b GF AB GE BF)
  euclid_apply (equal_angles g x f o o GF GE)
  euclid_apply (Elements.Book1.proposition_29_exterior y b g o e OQ AB GE)
  euclid_apply (equal_angles e o g b b GE AB)
  euclid_apply (Elements.Book1.proposition_29_exterior y b g x f XY BF GF)
  euclid_apply (equal_angles f x g b b GF BF)
  euclid_apply (parallelogram_area g x o y GF OQ GE XY)
  euclid_apply (parallelogram_area p q s r PQ RS SP QR)
  euclid_apply (Elements.Book1.proposition_4 g o x s p r GE XO GF SP PR RS)
  have hrs : 0 < size (r─s) := size_segment_pos.mpr (by euclid_finish)
  have hsp : 0 < size (s─p) := size_segment_pos.mpr (by euclid_finish)
  have hpq : 0 < size (p─q) := size_segment_pos.mpr (by euclid_finish)
  have hqr : 0 < size (q─r) := size_segment_pos.mpr (by euclid_finish)
  have s₂ : similarQuadrilaterals s p q r g o y x := ⟨by euclid_finish,
    (Proportional.refl hrs hsp).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish),
    (Proportional.refl hsp hpq).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish),
    (Proportional.refl hpq hqr).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish),
    (Proportional.refl hqr hrs).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish)⟩
  have s₀ : similarQuadrilaterals e b f g p q r s :=
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩
  have s₁ := similarQuadrilaterals_rot (similarQuadrilaterals_rot
    (similarQuadrilaterals_rot s₀))
  have s₃ := proposition_21' g e b f s p q r g o y x ⟨s₁, similarQuadrilaterals_symm s₂⟩
  -- so `GQ` and `GB` are about the same diagonal [Prop. 6.26]
  have := proposition_26 g e b f o y x GE BF GF AB OQ XY ⟨by euclid_finish,
    by euclid_finish, ‹_›, ‹_›, s₃⟩
  refine ⟨o, x, y, OQ, XY, GB, ‹_›, ‹_›, by euclid_finish, by euclid_finish,
    by euclid_finish, this, ?_⟩
  area_linarith

/--
To apply to a given straight line `ab` a parallelogram `tqar` (on `ar`) equal to a given
figure `C` (the triangles `c₁c₂c₄`, `c₄c₂c₃`), falling short by a parallelogram `rbsq`
similar to a given parallelogram `D`, `d₁d₂d₃d₄`. The condition: `C` is not greater
than the parallelogram `ebfg` on the half `eb`, similar to `D`.
-/
theorem proposition_28 : ∀ (a b e f g c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ : Point)
    (AB BF GF GE C₁₂ C₂₄ C₄₁ C₂₃ C₃₄ D₁₂ D₂₃ D₃₄ D₄₁ : Line),
  formTriangle c₁ c₂ c₄ C₁₂ C₂₄ C₄₁ ∧ formTriangle c₄ c₂ c₃ C₂₄ C₂₃ C₃₄ ∧
  c₁.opposingSides c₃ C₂₄ ∧ formParallelogram d₁ d₂ d₄ d₃ D₁₂ D₃₄ D₄₁ D₂₃ ∧
  quadrilateral d₁ d₂ d₃ d₄ D₁₂ D₂₃ D₃₄ D₄₁ ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧
  a.onLine AB ∧ quadrilateral e b f g AB BF GF GE ∧
  similarQuadrilaterals d₁ d₂ d₃ d₄ e b f g ∧
  Triangle.area △c₁:c₂:c₄ + Triangle.area △c₄:c₂:c₃ ≤
    Triangle.area △e:b:f + Triangle.area △e:f:g →
  ∃ (r q s t : Point) (TQ AT RQ : Line), between a r b ∧
  formParallelogram t q a r TQ AB AT RQ ∧ formParallelogram q s r b TQ AB RQ BF ∧
  similarQuadrilaterals d₁ d₂ d₃ d₄ r b s q ∧
  ▱ t:q:a:r = Triangle.area △c₁:c₂:c₄ + Triangle.area △c₄:c₂:c₃ :=
by
  euclid_intros
  -- `EBFG` is a parallelogram, being equiangular to `D`; complete `AG`
  euclid_apply (parallelogram_of_equiangular d₁ d₂ d₃ d₄ e b f g D₁₂ D₃₄ D₄₁ D₂₃ AB BF GF
    GE)
  euclid_apply (parallelogram_area g f e b GF AB GE BF)
  euclid_apply (Elements.Book1.proposition_31 a e g GE) as AH
  euclid_apply (parallel_meets g AH GE GF)
  euclid_apply (intersection_lines AH GF) as h
  euclid_apply (proposition_27_equal a b e h g f GF AB AH GE BF)
  rcases lt_or_eq_of_le ‹Triangle.area △c₁:c₂:c₄ + Triangle.area △c₄:c₂:c₃ ≤
    Triangle.area △e:b:f + Triangle.area △e:f:g› with hlt | heq
  swap
  · -- if `AG` is equal to `C`, it is applied, falling short by `GB`, similar to `D`
    refine ⟨e, g, f, h, GF, AH, GE, ‹_›, by euclid_finish, by euclid_finish,
      ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩, ?_⟩
    area_linarith
  -- if not, `GB` is greater than `C`: let `KM` be similar to `D` and equal to the excess
  -- [Prop. 6.25]
  euclid_apply (excess g e b f c₁ c₂ c₃ c₄ GF AB GE BF C₁₂ C₂₄ C₄₁ C₂₃ C₃₄ (by
    constructor <;> euclid_finish)) as (x, y, XY)
  euclid_apply (line_from_points x b) as XB
  obtain ⟨p, q, r, s, PQ, QR, RS, SP, hq, s₂, hs⟩ := proposition_25' d₁ d₂ d₃ d₄ f x y b
    D₁₂ D₂₃ D₃₄ D₄₁ GF XB BF XY AB (by euclid_finish)
  euclid_apply (parallelogram_of_equiangular d₁ d₂ d₃ d₄ p q r s D₁₂ D₃₄ D₄₁ D₂₃ PQ QR RS
    SP)
  euclid_apply (parallelogram_area p q s r PQ RS SP QR)
  -- `KM` is similar to `GB` [Prop. 6.21], and less: `KL` is less than `GE` [Prop. 6.20
  -- corollary, 5.14]
  have s₀ : similarQuadrilaterals d₁ d₂ d₃ d₄ e b f g :=
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩
  have s₂ : similarQuadrilaterals d₁ d₂ d₃ d₄ p q r s :=
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩
  have s₃ := proposition_21' e b f g d₁ d₂ d₃ d₄ p q r s
    ⟨similarQuadrilaterals_symm s₀, similarQuadrilaterals_symm s₂⟩
  obtain ⟨-, -, -, -, q₁⟩ := proposition_20_corollary e b f g p q r s AB BF GF GE PQ QR RS
    SP ⟨by euclid_finish, by euclid_finish, s₃⟩
  have hC : 0 < Triangle.area △c₁:c₂:c₄ := size_triangle_pos (L := C₁₂) (by euclid_finish)
    (by euclid_finish)
  have hC' : 0 < Triangle.area △c₄:c₂:c₃ := size_triangle_pos (L := C₂₄)
    (by euclid_finish) (by euclid_finish)
  have hpq : |(p─q)| < |(e─b)| := q₁.lt (by
    rw [size_quadrilateral, size_quadrilateral]
    area_linarith)
  -- `GQ`, equal and similar to `KM`, about the diagonal `GB`
  obtain ⟨o, x', y', OQ, XY', GB, ho, hx', hgq, hGB, hy', hgy, hgqa⟩ :=
    parallelogram_gq e b f g p q r s AB GF GE BF PQ QR RS SP ⟨by euclid_finish,
      by euclid_finish, by euclid_finish, by euclid_finish, s₃, hpq⟩
  -- the gnomon is equal to `C`, and so is `TR` [Props. 1.43, 6.1]
  obtain ⟨r₀, s₀', t, ht, hs', hr₀, harea⟩ := gnomon a b e f g h o x' y' AB GF GE BF AH OQ
    XY' GB ⟨‹_›, ‹_›, by euclid_finish, by euclid_finish, hGB, hy', hgy, hgq, ho, hx'⟩
  -- and the deficit `QB` is similar to `GB` [Prop. 6.24], so to `D` [Prop. 6.21]
  have h₂₄ := proposition_24 g e b f o y' x' s₀' r₀ GE BF GF AB OQ XY' (by euclid_finish)
  have s₄ := similarQuadrilaterals_rot (similarQuadrilaterals_rot
    (similarQuadrilaterals_rot s₀))
  have s₅ := proposition_21' d₄ d₁ d₂ d₃ g e b f y' r₀ b s₀'
    ⟨s₄, similarQuadrilaterals_symm h₂₄.2.1⟩
  refine ⟨r₀, y', s₀', t, OQ, AH, XY', hr₀, ht, hs', similarQuadrilaterals_rot s₅, ?_⟩
  area_linarith

end Elements.Book6
