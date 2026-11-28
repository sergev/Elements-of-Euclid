import SystemE
import Elements.Book6.Prop28

namespace Elements.Book6

open Elements.Book5 Magnitude

/--
The sum of the parallelogram `ebfl` (vertices `e`, `b`, `l`, `f` in order) and a figure
`C` (the triangles `d₁d₂d₄`, `d₄d₂d₃`) is a parallelogram `ewfz`: apply to `BL`, outward,
in the angle `LBW` beside the angle `EBL`, a parallelogram `bwlz` equal to `C`
[Prop. 1.45]; it continues `ebfl`.
-/
theorem sum_parallelogram : ∀ (e b f l d₁ d₂ d₃ d₄ : Point)
    (AB FL EF BL D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ : Line),
  formParallelogram e b f l AB FL EF BL ∧ formTriangle d₁ d₂ d₄ D₁₂ D₂₄ D₄₁ ∧
  formTriangle d₄ d₂ d₃ D₂₄ D₂₃ D₃₄ →
  ∃ (w z : Point) (WZ : Line), between e b w ∧ between f l z ∧
  formParallelogram e w f z AB FL EF WZ ∧
  ▱ e:w:f:z = ▱ e:b:f:l + (Triangle.area △d₁:d₂:d₄ + Triangle.area △d₄:d₂:d₃) :=
by
  euclid_intros
  euclid_apply (extend_point AB e b) as w₀
  have := angle_pos_of_not_on_line b l w₀ BL (by euclid_finish)
  euclid_apply (Elements.Book4.angle_lt_flat l b w₀ AB)
  euclid_apply (proposition_25_apply b l e d₁ d₂ d₃ d₄ l b w₀ BL D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ BL
    AB) as (z, w, LL, CM, WZ)
  euclid_apply (same_ray l b w₀ w BL AB CM)
  euclid_apply (parallel_line_unique l AB LL FL)
  euclid_apply (Elements.Book1.proposition_30 EF WZ BL)
  euclid_assert between e b w
  euclid_assert between f l z
  euclid_apply (sum_parallelograms_area e w f z b l AB FL EF WZ)
  euclid_apply (parallelogram_area l z b w FL AB BL WZ)
  euclid_apply (parallelogram_area b w l z AB FL BL WZ)
  refine ⟨w, z, WZ, ‹_›, ‹_›, by euclid_finish, ?_⟩
  area_linarith

/-- On the ray from `f` through `l`, a point `m` with `fm` greater than `fl` is beyond
`l`. -/
theorem beyond_of_longer : ∀ (f l m : Point) (L : Line),
  f.onLine L ∧ l.onLine L ∧ m.onLine L ∧ f ≠ l ∧ m ≠ f ∧ ¬(between m f l) ∧
  |(f─l)| < |(f─m)| → between f l m :=
by
  euclid_intros
  have : l ≠ m := by
    intro h
    subst h
    linarith
  euclid_apply (between_points f l m L)
  rcases ‹between f l m ∨ between l f m ∨ between f m l› with h | h | h
  · exact h
  · exact absurd (by euclid_finish) ‹¬(between m f l)›
  · euclid_apply (between_if f m l)
    have := segment_gte_zero (m─l)
    linarith

set_option maxHeartbeats 1000000 in
/--
The parallelogram `MN` of Prop. 6.29: `GH` (`pqrs`) is similar to `EL` (`ebfl`) and
greater, so `KH` exceeds `FL`, and `KG` exceeds `FE` [Props. 6.20 corollary, 5.14].
Produce `FL`, `FE`, make `FM` equal to `KH` and `FN` to `KG` [Prop. 1.3], and complete
`fmon`: it is equal and similar to `GH`, so similar to `EL`, and about the same diagonal
[Props. 6.21, 6.26].
-/
theorem parallelogram_mn : ∀ (e b l f p q r s : Point) (AB FL EF BL PQ QR RS SP : Line),
  formParallelogram e b f l AB FL EF BL ∧ formParallelogram p q s r PQ RS SP QR ∧
  quadrilateral e b l f AB BL FL EF ∧ quadrilateral p q r s PQ QR RS SP ∧
  similarQuadrilaterals e b l f p q r s ∧ |(e─b)| < |(p─q)| →
  ∃ (m n o : Point) (MO NO FO : Line), between f l m ∧ between f e n ∧
  formParallelogram f m n o FL NO EF MO ∧ distinctPointsOnLine f o FO ∧ b.onLine FO ∧
  between f b o ∧ ▱ f:m:n:o = Triangle.area △s:p:q + Triangle.area △s:q:r :=
by
  euclid_intros
  -- `KG` exceeds `FE`, and `KH` exceeds `FL` [Prop. 5.14]
  have h₁ : |(f─e)| < |(s─p)| :=
    ‹(f─e) ∶ (e─b) ∷ (s─p) ∶ (p─q)›.symm.lt_first ‹|(e─b)| < |(p─q)|›
  have h₂ : |(l─f)| < |(r─s)| := ‹(l─f) ∶ (f─e) ∷ (r─s) ∶ (s─p)›.symm.lt_first h₁
  euclid_apply (lay_on_ray f l s r FL) as m
  euclid_apply (lay_on_ray f e s p EF) as n
  have : between f l m := beyond_of_longer f l m FL ⟨by euclid_finish, by euclid_finish,
    by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish, by
      have := segment_symmetric l f; have := segment_symmetric r s; linarith⟩
  have : between f e n := beyond_of_longer f e n EF ⟨by euclid_finish, by euclid_finish,
    by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish, by linarith⟩
  euclid_apply (Elements.Book1.proposition_31 m f e EF) as MO
  euclid_apply (Elements.Book1.proposition_31 n f l FL) as NO
  euclid_apply (parallel_meets n MO EF NO)
  euclid_apply (intersection_lines MO NO) as o
  euclid_apply (Elements.Book1.proposition_30 MO BL EF)
  euclid_apply (Elements.Book1.proposition_30 NO AB FL)
  euclid_apply (line_from_points f o) as FO
  euclid_apply (line_from_points p r) as PR
  euclid_apply (line_from_points m n) as MN
  -- the sides of `MN` and `GH` are equal, and their angles [Props. 1.29, 1.34]
  euclid_apply (Elements.Book1.proposition_34 f m n o FL NO EF MO MN)
  euclid_apply (Elements.Book1.proposition_34 s p r q SP QR RS PQ PR)
  euclid_apply (Elements.Book1.proposition_34' e b f l AB FL EF BL)
  euclid_apply (equal_angles f m l n e FL EF)
  euclid_apply (Elements.Book1.proposition_29_exterior b o f e n AB NO EF)
  euclid_apply (equal_angles n e f o o EF NO)
  euclid_apply (Elements.Book1.proposition_29_exterior b o f l m BL MO FL)
  euclid_apply (equal_angles m l f o o FL MO)
  euclid_apply (parallelogram_area f m n o FL NO EF MO)
  euclid_apply (parallelogram_area p q s r PQ RS SP QR)
  euclid_apply (Elements.Book1.proposition_4 f n m s p r EF MN FL SP PR RS)
  have hrs : 0 < size (r─s) := size_segment_pos.mpr (by euclid_finish)
  have hsp : 0 < size (s─p) := size_segment_pos.mpr (by euclid_finish)
  have hpq : 0 < size (p─q) := size_segment_pos.mpr (by euclid_finish)
  have hqr : 0 < size (q─r) := size_segment_pos.mpr (by euclid_finish)
  have s₂ : similarQuadrilaterals s p q r f n o m := ⟨by euclid_finish,
    (Proportional.refl hrs hsp).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish),
    (Proportional.refl hsp hpq).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish),
    (Proportional.refl hpq hqr).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish),
    (Proportional.refl hqr hrs).congr rfl rfl (by simp only [size_segment]; euclid_finish)
      (by simp only [size_segment]; euclid_finish)⟩
  have s₀ : similarQuadrilaterals e b l f p q r s :=
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩
  have s₁ := similarQuadrilaterals_rot (similarQuadrilaterals_rot
    (similarQuadrilaterals_rot s₀))
  have s₃ := proposition_21' f n o m s p q r f e b l
    ⟨similarQuadrilaterals_symm s₂, s₁⟩
  -- so `EL`, `MN` are about the same diagonal [Prop. 6.26]
  have := proposition_26 f n o m e b l EF MO FL NO AB BL ⟨by euclid_finish,
    by euclid_finish, ‹_›, ‹_›, s₃⟩
  refine ⟨m, n, o, MO, NO, FO, ‹_›, ‹_›, by euclid_finish, by euclid_finish,
    by euclid_finish, this, ?_⟩
  area_linarith

/--
The gnomon of Prop. 6.29: `e` halves `ab`; `ebfl` is about the diagonal `fo` of
`fmon`. Through `b`, `AB` meets `MO` at `p`, and `BL` meets `NO` at `q`; `AX` is parallel
to `EF`. `AN` is equal to `NB` [Prop. 6.1], that is, to the complement `LP` [Prop. 1.43];
add `EO`: `AO` is equal to the gnomon, `fmon` less `ebfl`.
-/
theorem gnomon_29 : ∀ (a b e f l m n o : Point) (AB FL EF BL MO NO FO : Line),
  between a e b ∧ |(a─e)| = |(e─b)| ∧ formParallelogram e b f l AB FL EF BL ∧
  between f l m ∧ between f e n ∧ formParallelogram f m n o FL NO EF MO ∧
  distinctPointsOnLine f o FO ∧ b.onLine FO ∧ between f b o →
  ∃ (p q x : Point) (AX : Line), between a b p ∧ formParallelogram x o a p NO AB AX MO ∧
  formParallelogram q o b p NO AB BL MO ∧ p.onLine MO ∧ q.onLine BL ∧
  ▱ x:o:a:p + ▱ e:b:f:l = ▱ f:m:n:o :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_30 MO BL EF)
  euclid_apply (Elements.Book1.proposition_30 NO AB FL)
  euclid_apply (parallel_meets e MO EF AB)
  euclid_apply (intersection_lines MO AB) as p
  euclid_assert between e b p
  euclid_assert between m p o
  euclid_apply (parallel_meets l NO FL BL)
  euclid_apply (intersection_lines NO BL) as q
  euclid_assert between l b q
  euclid_assert between n q o
  euclid_apply (Elements.Book1.proposition_31 a e f EF) as AX
  euclid_apply (parallel_meets a NO AB AX)
  euclid_apply (intersection_lines NO AX) as x
  euclid_apply (Elements.Book1.proposition_30 AX MO EF)
  euclid_assert between x n o
  -- the complement `NB` is equal to `LP` [Prop. 1.43], and `AN` to `NB` [Prop. 6.1]
  euclid_apply (Elements.Book1.proposition_43 f n o m e p q l b FL NO EF MO FO AB BL)
  euclid_apply (proposition_27_equal a b e x n q NO AB AX EF BL)
  euclid_apply (sum_parallelograms_area f n m o e p EF MO FL NO)
  euclid_apply (sum_parallelograms_area f m e p l b FL AB EF MO)
  euclid_apply (sum_parallelograms_area e p n o b q AB NO EF MO)
  euclid_apply (sum_parallelograms_area x o a p n e NO AB AX MO)
  euclid_apply (parallelogram_area e p n o AB NO EF MO)
  euclid_apply (parallelogram_area n q e b NO AB EF BL)
  euclid_apply (parallelogram_area e b f l AB FL EF BL)
  refine ⟨p, q, x, AX, by euclid_finish, by euclid_finish, by euclid_finish, ‹_›, ‹_›, ?_⟩
  area_linarith

/--
To apply to a given straight line `ab` a parallelogram `xoap` (on `ap`) equal to a given
figure `C` (the triangles `c₁c₂c₄`, `c₄c₂c₃`), overshooting by a parallelogram `qopb`
similar to a given parallelogram `D`, `d₁d₂d₃d₄`. The applied parallelogram lies on the
side of `AB` away from the parallelogram `eblf` on the half.
-/
theorem proposition_29 : ∀ (a b e f l c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ : Point)
    (AB BL FL EF C₁₂ C₂₄ C₄₁ C₂₃ C₃₄ D₁₂ D₂₃ D₃₄ D₄₁ : Line),
  formTriangle c₁ c₂ c₄ C₁₂ C₂₄ C₄₁ ∧ formTriangle c₄ c₂ c₃ C₂₄ C₂₃ C₃₄ ∧
  c₁.opposingSides c₃ C₂₄ ∧ formParallelogram d₁ d₂ d₄ d₃ D₁₂ D₃₄ D₄₁ D₂₃ ∧
  quadrilateral d₁ d₂ d₃ d₄ D₁₂ D₂₃ D₃₄ D₄₁ ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧
  a.onLine AB ∧ quadrilateral e b l f AB BL FL EF ∧
  similarQuadrilaterals d₁ d₂ d₃ d₄ e b l f →
  ∃ (p o x q : Point) (NO AX MO : Line), between a b p ∧
  formParallelogram x o a p NO AB AX MO ∧ formParallelogram q o b p NO AB BL MO ∧
  o.opposingSides l AB ∧ similarQuadrilaterals d₁ d₂ d₃ d₄ q o p b ∧
  ▱ x:o:a:p = Triangle.area △c₁:c₂:c₄ + Triangle.area △c₄:c₂:c₃ :=
by
  euclid_intros
  -- `EL` on `EB` is a parallelogram, being equiangular to `D`
  euclid_apply (parallelogram_of_equiangular d₁ d₂ d₃ d₄ e b l f D₁₂ D₃₄ D₄₁ D₂₃ AB BL FL
    EF)
  -- `GH` similar to `D` and equal to the sum of `EL` and `C` [Prop. 6.25]
  euclid_apply (sum_parallelogram e b f l c₁ c₂ c₃ c₄ AB FL EF BL C₁₂ C₂₄ C₄₁ C₂₃ C₃₄)
    as (w, z, WZ)
  euclid_apply (line_from_points w f) as WF
  obtain ⟨p, q, r, s, PQ, QR, RS, SP, hq, s₂, hs⟩ := proposition_25' d₁ d₂ d₃ d₄ e w z f
    D₁₂ D₂₃ D₃₄ D₄₁ AB WF EF WZ FL (by euclid_finish)
  euclid_apply (parallelogram_of_equiangular d₁ d₂ d₃ d₄ p q r s D₁₂ D₃₄ D₄₁ D₂₃ PQ QR RS
    SP)
  euclid_apply (parallelogram_area p q s r PQ RS SP QR)
  euclid_apply (parallelogram_area e b f l AB FL EF BL)
  euclid_apply (parallelogram_area e w f z AB FL EF WZ)
  -- `GH` is similar to `EL` [Prop. 6.21], and greater: `KH` exceeds `FL`
  -- [Prop. 6.20 corollary, 5.14]
  have s₀ : similarQuadrilaterals d₁ d₂ d₃ d₄ e b l f :=
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩
  have s₂ : similarQuadrilaterals d₁ d₂ d₃ d₄ p q r s :=
    ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩
  have s₃ := proposition_21' e b l f d₁ d₂ d₃ d₄ p q r s
    ⟨similarQuadrilaterals_symm s₀, similarQuadrilaterals_symm s₂⟩
  obtain ⟨-, -, -, -, q₁⟩ := proposition_20_corollary p q r s e b l f PQ QR RS SP AB BL FL
    EF ⟨by euclid_finish, by euclid_finish, similarQuadrilaterals_symm s₃⟩
  have hC : 0 < Triangle.area △c₁:c₂:c₄ := size_triangle_pos (L := C₁₂) (by euclid_finish)
    (by euclid_finish)
  have hC' : 0 < Triangle.area △c₄:c₂:c₃ := size_triangle_pos (L := C₂₄)
    (by euclid_finish) (by euclid_finish)
  have hpq : |(e─b)| < |(p─q)| := q₁.lt (by
    rw [size_quadrilateral, size_quadrilateral]
    area_linarith)
  -- `MN`, equal and similar to `GH`, about the same diagonal as `EL`
  obtain ⟨m, n, o, MO, NO, FO, hm, hn, hmn, hFO, hb, hfo, hmna⟩ :=
    parallelogram_mn e b l f p q r s AB FL EF BL PQ QR RS SP ⟨by euclid_finish,
      by euclid_finish, by euclid_finish, by euclid_finish, s₃, hpq⟩
  have : ¬(AB.intersectsLine NO) := by
    have := Elements.Book1.proposition_30 NO AB FL (by euclid_finish)
    euclid_finish
  have hol : o.opposingSides l AB := by euclid_finish
  -- the gnomon is equal to `C`, and so is `AO` [Props. 1.43, 6.1]
  obtain ⟨p', q', x, AX, hp', hx, hq', hpMO, hqBL, harea⟩ := gnomon_29 a b e f l m n o AB
    FL EF BL MO NO FO ⟨‹_›, ‹_›, by euclid_finish, hm, hn, hmn, hFO, hb, hfo⟩
  -- and the excess `QP` is similar to `EL` [Prop. 6.24], so to `D` [Prop. 6.21]
  have h₂₄ := proposition_24 f n o m e b l p' q' EF MO FL NO AB BL (by euclid_finish)
  have s₄ := similarQuadrilaterals_rot (similarQuadrilaterals_rot
    (similarQuadrilaterals_rot s₀))
  have s₅ := proposition_21' d₄ d₁ d₂ d₃ f e b l b q' o p'
    ⟨s₄, similarQuadrilaterals_symm h₂₄.2.2⟩
  refine ⟨p', o, x, q', NO, AX, MO, hp', hx, hq', hol, similarQuadrilaterals_rot s₅, ?_⟩
  area_linarith

end Elements.Book6
