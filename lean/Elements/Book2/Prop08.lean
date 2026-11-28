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
  Triangle.area △ g:c:k + Triangle.area △ k:c:b = Triangle.area △ k:b:n + Triangle.area △ n:b:d ∧
  Triangle.area △ q:g:r + Triangle.area △ r:g:k = Triangle.area △ r:k:p + Triangle.area △ p:k:n ∧
  Triangle.area △ n:p:r + Triangle.area △ n:r:k = Triangle.area △ b:k:g + Triangle.area △ b:g:c ∧
  -- AG = MQ, QL = RF [1.36]; QL = MQ [1.43]
  Triangle.area △ m:g:a + Triangle.area △ a:g:c = Triangle.area △ o:q:m + Triangle.area △ m:q:g ∧
  Triangle.area △ h:q:l + Triangle.area △ l:q:r = Triangle.area △ l:r:f + Triangle.area △ f:r:p ∧
  Triangle.area △ r:l:h + Triangle.area △ r:h:q = Triangle.area △ g:q:o + Triangle.area △ g:o:m ∧
  -- AK, OH, AEFD as rectangles
  ▱ m:k:a:b = |(m─k)| * |(m─a)| ∧
  ▱ e:h:o:q = |(e─h)| * |(e─o)| ∧
  ▱ e:f:a:d = |(e─f)| * |(e─a)| ∧
  -- how the pieces make up AK and the whole
  Triangle.area △ m:a:c + Triangle.area △ m:c:g + Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ m:a:b + Triangle.area △ m:b:k ∧
  Triangle.area △ e:a:c + Triangle.area △ e:c:h + Triangle.area △ h:c:d + Triangle.area △ h:d:f = Triangle.area △ e:a:d + Triangle.area △ e:d:f ∧
  Triangle.area △ h:c:b + Triangle.area △ h:b:l + Triangle.area △ l:b:d + Triangle.area △ l:d:f = Triangle.area △ h:c:d + Triangle.area △ h:d:f ∧
  Triangle.area △ e:h:q + Triangle.area △ e:q:o + Triangle.area △ o:q:c + Triangle.area △ o:c:a = Triangle.area △ e:h:c + Triangle.area △ e:c:a ∧
  Triangle.area △ o:q:g + Triangle.area △ o:g:m + Triangle.area △ m:g:c + Triangle.area △ m:c:a = Triangle.area △ o:q:c + Triangle.area △ o:c:a ∧
  Triangle.area △ h:l:r + Triangle.area △ h:r:q + Triangle.area △ q:r:b + Triangle.area △ q:b:c = Triangle.area △ h:l:b + Triangle.area △ h:b:c ∧
  Triangle.area △ q:r:k + Triangle.area △ q:k:g + Triangle.area △ g:k:b + Triangle.area △ g:b:c = Triangle.area △ q:r:b + Triangle.area △ q:b:c ∧
  Triangle.area △ l:f:p + Triangle.area △ l:p:r + Triangle.area △ r:p:d + Triangle.area △ r:d:b = Triangle.area △ l:f:d + Triangle.area △ l:d:b ∧
  Triangle.area △ r:p:n + Triangle.area △ r:n:k + Triangle.area △ k:n:d + Triangle.area △ k:d:b = Triangle.area △ r:p:d + Triangle.area △ r:d:b ∧
  -- the two diagonals of each piece [parallelogram_area]
  Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:g:c + Triangle.area △ k:c:b ∧
  Triangle.area △ k:b:d + Triangle.area △ k:d:n = Triangle.area △ n:k:b + Triangle.area △ n:b:d ∧
  Triangle.area △ q:g:k + Triangle.area △ q:k:r = Triangle.area △ r:q:g + Triangle.area △ r:g:k ∧
  Triangle.area △ r:k:n + Triangle.area △ r:n:p = Triangle.area △ p:r:k + Triangle.area △ p:k:n ∧
  Triangle.area △ m:a:c + Triangle.area △ m:c:g = Triangle.area △ g:m:a + Triangle.area △ g:a:c ∧
  Triangle.area △ o:m:g + Triangle.area △ o:g:q = Triangle.area △ q:o:m + Triangle.area △ q:m:g ∧
  Triangle.area △ h:q:r + Triangle.area △ h:r:l = Triangle.area △ l:h:q + Triangle.area △ l:q:r ∧
  Triangle.area △ l:r:p + Triangle.area △ l:p:f = Triangle.area △ f:l:r + Triangle.area △ f:r:p ∧
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
  euclid_assert Triangle.area △ g:c:k + Triangle.area △ k:c:b = Triangle.area △ k:b:n + Triangle.area △ n:b:d
  euclid_assert Triangle.area △ g:c:k + Triangle.area △ k:c:b = Triangle.area △ q:g:r + Triangle.area △ r:g:k
  euclid_assert Triangle.area △ g:c:k + Triangle.area △ k:c:b = Triangle.area △ r:k:p + Triangle.area △ p:k:n
  euclid_assert Triangle.area △ m:g:a + Triangle.area △ a:g:c = Triangle.area △ o:q:m + Triangle.area △ m:q:g
  euclid_assert Triangle.area △ m:g:a + Triangle.area △ a:g:c = Triangle.area △ h:q:l + Triangle.area △ l:q:r
  euclid_assert Triangle.area △ m:g:a + Triangle.area △ a:g:c = Triangle.area △ l:r:f + Triangle.area △ f:r:p
  -- AK is AG and CK; the eight are four AK; with OH they are the whole
  euclid_assert ▱ m:k:a:b =
    (Triangle.area △ m:g:a + Triangle.area △ a:g:c) + (Triangle.area △ g:c:k + Triangle.area △ k:c:b)
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
  have s₁ := proposition_36' g c b k k b d n MN AB CH BL BL DF (by euclid_finish)
  have s₂ := proposition_36' q g k r r k n p OP MN CH BL BL DF (by euclid_finish)
  have s₃ := proposition_43 d p q c n g r b k AB OP DF CH DE MN BL (by euclid_finish)
  -- the four rectangles AG, MQ, QL, RF are equal
  have r₁ := proposition_36' m g c a o q g m AE CH MN AB OP MN (by euclid_finish)
  have r₂ := proposition_36' h q r l l r p f EF OP CH BL BL DF (by euclid_finish)
  have r₃ := proposition_43 k l e m r o h g q MN EF BL AE DE OP CH (by euclid_finish)
  -- AK, OH and the whole AEFD are rectangles
  euclid_apply (proposition_29_exterior q d e o a OP AB AE)
  have a₁ := (rectangle_area m k a b MN AB AE BL (by euclid_finish)).1
  have a₂ := (rectangle_area e h o q EF OP AE CH (by euclid_finish)).1
  have a₃ := (rectangle_area e f a d EF AB AE DF (by euclid_finish)).1
  -- AK is AG and CK; the whole is cut into nine
  have u₁ := sum_parallelograms_area m k a b g c MN AB AE BL (by euclid_finish)
  have u₂ := sum_parallelograms_area e f a d h c EF AB AE DF (by euclid_finish)
  have u₃ := sum_parallelograms_area h f c d l b EF AB CH DF (by euclid_finish)
  have u₄ := sum_parallelograms_area e a h c o q AE CH EF AB (by euclid_finish)
  have u₅ := sum_parallelograms_area o a q c m g AE CH OP AB (by euclid_finish)
  have u₆ := sum_parallelograms_area h c l b q r CH BL EF AB (by euclid_finish)
  have u₇ := sum_parallelograms_area q c r b g k CH BL OP AB (by euclid_finish)
  have u₈ := sum_parallelograms_area l b f d r p BL DF EF AB (by euclid_finish)
  have u₉ := sum_parallelograms_area r b p d k n BL DF OP AB (by euclid_finish)
  -- the two diagonals of each piece
  have v₁ := parallelogram_area g k c b MN AB CH BL (by euclid_finish)
  have v₂ := parallelogram_area k n b d MN AB BL DF (by euclid_finish)
  have v₃ := parallelogram_area q r g k OP MN CH BL (by euclid_finish)
  have v₄ := parallelogram_area r p k n OP MN BL DF (by euclid_finish)
  have v₅ := parallelogram_area m g a c MN AB AE CH (by euclid_finish)
  have v₆ := parallelogram_area o q m g OP MN AE CH (by euclid_finish)
  have v₇ := parallelogram_area h l q r EF OP CH BL (by euclid_finish)
  have v₈ := parallelogram_area l f r p EF OP BL DF (by euclid_finish)
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
