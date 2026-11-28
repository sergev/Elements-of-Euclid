import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop05
import Elements.Book1.Prop06
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book1.Prop36
import Elements.Book1.Prop43
import Elements.Book1.Prop46
import Elements.Book2.Lemmas

namespace Elements.Book2

open Elements.Book1

/--
The closing sums of Prop. 2.8: Euclid's equalities of the pieces, and how they make up
`AK` and the whole square, give the statement. Kept apart so saturation sees only areas.
-/
theorem proposition_8_sums : ∀ (a b c d e f g h k l m n o p q r : Point),
  -- CK = KD, GR = RN [1.36]; RN = CK [1.43]
  ▱ c:b:g:k = ▱ b:d:k:n ∧
  ▱ g:k:q:r = ▱ k:n:r:p ∧
  ▱ n:k:p:r = ▱ b:c:k:g ∧
  -- AG = MQ, QL = RF [1.36]; QL = MQ [1.43]
  ▱ g:c:m:a = ▱ q:g:o:m ∧
  ▱ q:r:h:l = ▱ r:p:l:f ∧
  ▱ r:q:l:h = ▱ g:m:q:o ∧
  -- AK, OH, AEFD as rectangles
  ▱ m:k:a:b = |(m─k)| * |(m─a)| ∧
  ▱ e:h:o:q = |(e─h)| * |(e─o)| ∧
  ▱ e:f:a:d = |(e─f)| * |(e─a)| ∧
  -- how the pieces make up AK and the whole
  ▱ m:g:a:c + ▱ b:c:k:g = ▱ m:k:a:b ∧
  ▱ e:h:a:c + ▱ h:f:c:d = ▱ e:f:a:d ∧
  ▱ h:l:c:b + ▱ l:f:b:d = ▱ h:f:c:d ∧
  ▱ e:h:o:q + ▱ o:a:q:c = ▱ e:h:a:c ∧
  ▱ g:m:q:o + ▱ m:g:a:c = ▱ o:a:q:c ∧
  ▱ r:q:l:h + ▱ q:c:r:b = ▱ h:l:c:b ∧
  ▱ q:g:r:k + ▱ b:c:k:g = ▱ q:c:r:b ∧
  ▱ l:r:f:p + ▱ r:b:p:d = ▱ l:f:b:d ∧
  ▱ n:k:p:r + ▱ k:b:n:d = ▱ r:b:p:d ∧
  -- the two diagonals of each piece [parallelogram_area]
  ▱ b:c:k:g = ▱ c:b:g:k ∧
  ▱ k:b:n:d = ▱ b:d:k:n ∧
  ▱ q:g:r:k = ▱ g:k:q:r ∧
  ▱ n:k:p:r = ▱ k:n:r:p ∧
  ▱ m:g:a:c = ▱ g:c:m:a ∧
  ▱ g:m:q:o = ▱ q:g:o:m ∧
  ▱ r:q:l:h = ▱ q:r:h:l ∧
  ▱ l:r:f:p = ▱ r:p:l:f ∧
  -- lengths
  |(m─k)| = |(a─b)| ∧ |(m─a)| = |(k─b)| ∧ |(b─k)| = |(b─d)| ∧ |(b─d)| = |(c─b)| ∧
  |(e─h)| = |(o─q)| ∧ |(o─q)| = |(a─c)| ∧ |(o─e)| = |(o─q)| ∧
  |(e─f)| = |(a─d)| ∧ |(a─e)| = |(a─d)| ∧ |(a─b)| + |(b─d)| = |(a─d)| →
  4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| = (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) :=
by
  euclid_intros
  euclid_assert |(m─a)| = |(b─c)|
  euclid_assert |(e─h)| = |(a─c)| ∧ |(e─o)| = |(a─c)|
  euclid_assert |(e─f)| = |(a─b)| + |(b─c)| ∧ |(e─a)| = |(a─b)| + |(b─c)|
  euclid_assert ▱ m:k:a:b = |(a─b)| * |(b─c)|
  euclid_assert ▱ e:h:o:q = |(a─c)| * |(a─c)|
  euclid_assert ▱ e:f:a:d = (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|)
  -- the four squares are equal, and so are the four rectangles
  euclid_assert ▱ c:b:g:k = ▱ b:d:k:n
  euclid_assert ▱ c:b:g:k = ▱ g:k:q:r
  euclid_assert ▱ c:b:g:k = ▱ k:n:r:p
  euclid_assert ▱ g:c:m:a = ▱ q:g:o:m
  euclid_assert ▱ g:c:m:a = ▱ q:r:h:l
  euclid_assert ▱ g:c:m:a = ▱ r:p:l:f
  -- AK is AG and CK; the eight are four AK; with OH they are the whole
  euclid_assert ▱ m:k:a:b = ▱ g:c:m:a + ▱ c:b:g:k
  euclid_assert ▱ e:f:a:d = 4 * ▱ m:k:a:b + ▱ e:h:o:q
  euclid_finish


set_option maxHeartbeats 1000000 in
theorem proposition_8 : ∀ (a b c : Point),
  between a c b →
  4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| = (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (extend_point_longer AB a b (c─b)) as x
  euclid_apply (line_from_points c b) as CB
  obtain ⟨d, hbd, hd⟩ := proposition_3 b x c b AB CB (by euclid_finish)
  obtain ⟨e, f, EF, AE, DF, hsq, hef, hae, hsq'⟩ := proposition_46 a d AB (by euclid_finish)
  euclid_apply (line_from_points d e) as DE
  euclid_apply (proposition_31 c a e AE) as CH
  euclid_apply (proposition_31 b a e AE) as BL
  euclid_apply (intersection_lines BL DE) as k
  euclid_apply (intersection_lines CH DE) as q
  euclid_apply (intersection_lines CH EF) as h
  euclid_apply (intersection_lines BL EF) as l
  euclid_apply (proposition_31 k a d AB) as MN
  euclid_apply (intersection_lines MN AE) as m
  euclid_apply (intersection_lines MN CH) as g
  euclid_apply (intersection_lines MN DF) as n
  euclid_apply (proposition_31 q a d AB) as OP
  euclid_apply (intersection_lines OP AE) as o
  euclid_apply (intersection_lines OP BL) as r
  euclid_apply (intersection_lines OP DF) as p
  -- Missed by Euclid.
  euclid_apply (proposition_30 CH DF AE)
  euclid_apply (proposition_30 BL DF AE)
  euclid_apply (proposition_30 CH BL AE)
  euclid_apply (proposition_30 MN EF AB)
  euclid_apply (proposition_30 OP EF AB)
  euclid_assert k ≠ q
  euclid_assert ¬(k.onLine AB)
  euclid_assert ¬(q.onLine AB)
  euclid_assert ¬(q.onLine MN)
  euclid_apply (proposition_30 MN OP AB)
  -- Missed by Euclid: where the points fall, read off his figure.
  euclid_apply (parallel_between c b d q k d CH BL DF DE)
  euclid_apply (parallel_between a c d e q d AE CH DF DE)
  euclid_apply (parallel_between d k q a m o AB MN OP AE)
  euclid_apply (parallel_between k q e m o e MN OP EF AE)
  euclid_apply (parallel_between d k q c g q AB MN OP CH)
  euclid_apply (parallel_between k q e g q h MN OP EF CH)
  euclid_apply (parallel_between d k q b k r AB MN OP BL)
  euclid_apply (parallel_between k q e k r l MN OP EF BL)
  euclid_apply (parallel_between d k q d n p AB MN OP DF)
  euclid_apply (parallel_between k q e n p f MN OP EF DF)
  euclid_apply (parallel_between a c b e h l AE CH BL EF)
  euclid_apply (parallel_between c b d h l f CH BL DF EF)
  euclid_apply (parallel_between a c b m g k AE CH BL MN)
  euclid_apply (parallel_between c b d g k n CH BL DF MN)
  euclid_apply (parallel_between a c b o q r AE CH BL OP)
  euclid_apply (parallel_between c b d q r p CH BL DF OP)
  -- the sides of the figures
  euclid_apply (proposition_34' g k c b MN AB CH BL)
  euclid_apply (proposition_34' k n b d MN AB BL DF)
  euclid_apply (proposition_34' q r g k OP MN CH BL)
  euclid_apply (proposition_34' r p k n OP MN BL DF)
  euclid_apply (proposition_34' m g a c MN AB AE CH)
  euclid_apply (proposition_34' o q m g OP MN AE CH)
  euclid_apply (proposition_34' o q a c OP AB AE CH)
  euclid_apply (proposition_34' m k a b MN AB AE BL)
  -- Missed by Euclid: BK = BD, GQ = GK, OE = OQ.
  euclid_apply (proposition_5' a e d AE DE AB)
  euclid_apply (proposition_29_exterior b a d k e BL AE DE)
  have i₁ := Elements.Book1.proposition_6 b k d BL DE AB (by euclid_finish)
  euclid_assert c.sameSide a DE
  euclid_assert g.sameSide c DE
  have : g.sameSide a DE := same_side_trans c g a DE ⟨same_side_symm g c DE ‹_›, ‹c.sameSide a DE›⟩
  have : between k q e :=
    between_trans_in' d q e k ⟨(between_symm e q d ‹between e q d›).1, (between_symm q k d ‹between q k d›).1⟩
  euclid_apply (proposition_29_exterior g a k q e CH AE DE)
  euclid_apply (proposition_29_exterior g a q k d MN AB DE)
  euclid_apply (Elements.Book1.proposition_6 g q k CH DE MN)
  euclid_apply (proposition_29_exterior o a e q d OP AB DE)
  euclid_apply (equal_angles e o a q d AE DE)
  euclid_apply (equal_angles d q e a a DE AB)
  have i₂ := Elements.Book1.proposition_6 o e q AE DE OP (by euclid_finish)
  -- the four squares CK, KD, GR, RN are equal
  have s₁ : ▱ c:b:g:k = ▱ b:d:k:n := by
    have := proposition_36' g c b k k b d n MN AB CH BL BL DF (by euclid_finish)
    euclid_finish
  have s₂ : ▱ g:k:q:r = ▱ k:n:r:p := by
    have := proposition_36' q g k r r k n p OP MN CH BL BL DF (by euclid_finish)
    euclid_finish
  have s₃ : ▱ n:k:p:r = ▱ b:c:k:g := by
    have := proposition_43 d p q c n g r b k AB OP DF CH DE MN BL (by euclid_finish)
    euclid_finish
  -- the four rectangles AG, MQ, QL, RF are equal
  have r₁ : ▱ g:c:m:a = ▱ q:g:o:m := by
    have := proposition_36' m g c a o q g m AE CH MN AB OP MN (by euclid_finish)
    euclid_finish
  have r₂ : ▱ q:r:h:l = ▱ r:p:l:f := by
    have := proposition_36' h q r l l r p f EF OP CH BL BL DF (by euclid_finish)
    euclid_finish
  have r₃ : ▱ r:q:l:h = ▱ g:m:q:o := by
    have := proposition_43 k l e m r o h g q MN EF BL AE DE OP CH (by euclid_finish)
    euclid_finish
  -- AK, OH and the whole AEFD are rectangles
  euclid_apply (proposition_29_exterior q d e o a OP AB AE)
  have a₁ := (rectangle_area m k a b MN AB AE BL (by euclid_finish)).1
  have a₂ := (rectangle_area e h o q EF OP AE CH (by euclid_finish)).1
  have a₃ := (rectangle_area e f a d EF AB AE DF (by euclid_finish)).1
  -- AK is AG and CK; the whole is cut into nine
  have u₁ : ▱ m:g:a:c + ▱ b:c:k:g = ▱ m:k:a:b := by
    have := sum_parallelograms_area m k a b g c MN AB AE BL (by euclid_finish)
    euclid_finish
  have u₂ : ▱ e:h:a:c + ▱ h:f:c:d = ▱ e:f:a:d := by
    have := sum_parallelograms_area e f a d h c EF AB AE DF (by euclid_finish)
    euclid_finish
  have u₃ : ▱ h:l:c:b + ▱ l:f:b:d = ▱ h:f:c:d := by
    have := sum_parallelograms_area h f c d l b EF AB CH DF (by euclid_finish)
    euclid_finish
  have u₄ : ▱ e:h:o:q + ▱ o:a:q:c = ▱ e:h:a:c := by
    have := sum_parallelograms_area e a h c o q AE CH EF AB (by euclid_finish)
    euclid_finish
  have u₅ : ▱ g:m:q:o + ▱ m:g:a:c = ▱ o:a:q:c := by
    have := sum_parallelograms_area o a q c m g AE CH OP AB (by euclid_finish)
    euclid_finish
  have u₆ : ▱ r:q:l:h + ▱ q:c:r:b = ▱ h:l:c:b := by
    have := sum_parallelograms_area h c l b q r CH BL EF AB (by euclid_finish)
    euclid_finish
  have u₇ : ▱ q:g:r:k + ▱ b:c:k:g = ▱ q:c:r:b := by
    have := sum_parallelograms_area q c r b g k CH BL OP AB (by euclid_finish)
    euclid_finish
  have u₈ : ▱ l:r:f:p + ▱ r:b:p:d = ▱ l:f:b:d := by
    have := sum_parallelograms_area l b f d r p BL DF EF AB (by euclid_finish)
    euclid_finish
  have u₉ : ▱ n:k:p:r + ▱ k:b:n:d = ▱ r:b:p:d := by
    have := sum_parallelograms_area r b p d k n BL DF OP AB (by euclid_finish)
    euclid_finish
  -- the two diagonals of each piece
  have v₁ : ▱ b:c:k:g = ▱ c:b:g:k := by
    have := parallelogram_area g k c b MN AB CH BL (by euclid_finish)
    euclid_finish
  have v₂ : ▱ k:b:n:d = ▱ b:d:k:n := by
    have := parallelogram_area k n b d MN AB BL DF (by euclid_finish)
    euclid_finish
  have v₃ : ▱ q:g:r:k = ▱ g:k:q:r := by
    have := parallelogram_area q r g k OP MN CH BL (by euclid_finish)
    euclid_finish
  have v₄ : ▱ n:k:p:r = ▱ k:n:r:p := by
    have := parallelogram_area r p k n OP MN BL DF (by euclid_finish)
    euclid_finish
  have v₅ : ▱ m:g:a:c = ▱ g:c:m:a := by
    have := parallelogram_area m g a c MN AB AE CH (by euclid_finish)
    euclid_finish
  have v₆ : ▱ g:m:q:o = ▱ q:g:o:m := by
    have := parallelogram_area o q m g OP MN AE CH (by euclid_finish)
    euclid_finish
  have v₇ : ▱ r:q:l:h = ▱ q:r:h:l := by
    have := parallelogram_area h l q r EF OP CH BL (by euclid_finish)
    euclid_finish
  have v₈ : ▱ l:r:f:p = ▱ r:p:l:f := by
    have := parallelogram_area l f r p EF OP BL DF (by euclid_finish)
    euclid_finish
  -- the sides
  obtain ⟨p₁, p₁', -⟩ := proposition_34' m k a b MN AB AE BL (by euclid_finish)
  obtain ⟨p₂, -⟩ := proposition_34' e h o q EF OP AE CH (by euclid_finish)
  obtain ⟨p₃, -⟩ := proposition_34' o q a c OP AB AE CH (by euclid_finish)
  have t₁ := between_if a b d (by euclid_finish)
  exact proposition_8_sums a b c d e f g h k l m n o p q r
    ⟨s₁, s₂, s₃, r₁, r₂, r₃, a₁, a₂, a₃, u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, u₉,
     v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈,
     p₁, p₁', i₁, hd, p₂, p₃, i₂, hef, hae, t₁⟩

end Elements.Book2
