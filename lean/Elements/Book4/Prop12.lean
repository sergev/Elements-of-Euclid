import SystemE
import Elements.Book1.Prop08
import Elements.Book1.Prop26
import Elements.Book1.Prop47
import Elements.Book3.Lemmas
import Elements.Book3.Prop18
import Elements.Book3.Prop27
import Elements.Book3.Prop28
import Elements.Book4.Lemmas
import Elements.Book4.Prop11

namespace Elements.Book4

/--
At a vertex `K` of the tangents at `B`, `C`: `BK = KC` [Props. 3.18, 1.47], and `FK`, from
the center, cuts the angles `BFC`, `BKC` in half [Prop. 1.8].
-/
theorem proposition_12_vertex : ∀ (b c f k : Point) (TB TC : Line) (α : Circle),
  f.isCentre α ∧ TB.touchesCircleAt α b ∧ TC.touchesCircleAt α c ∧ k.onLine TB ∧
  k.onLine TC ∧ b ≠ c ∧ k ≠ b ∧ k ≠ c →
  |(b─k)| = |(k─c)| ∧ ∠ b:f:k = ∠ k:f:c ∧ ∠ b:k:f = ∠ f:k:c :=
by
  euclid_intros
  euclid_apply (Elements.Book3.proposition_18 b k f TB α)
  euclid_apply (Elements.Book3.proposition_18 c k f TC α)
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f c) as FC
  euclid_apply (line_from_points f k) as FK
  euclid_apply (not_on_line_of_right_angle k b f FB)
  euclid_apply (not_on_line_of_right_angle k c f FC)
  -- the square on FK is equal to the squares on FB, BK, and on FC, CK [Prop. 1.47]
  euclid_apply (Elements.Book1.proposition_47 b f k FB FK TB)
  euclid_apply (Elements.Book1.proposition_47 c f k FC FK TC)
  euclid_apply (point_on_circle_onlyif f b c α)
  euclid_apply (Elements.Book3.length_eq_of_square_eq b k c k)
  -- FB = FC, FK common, BK = CK [Prop. 1.8]
  euclid_apply (Elements.Book1.proposition_8 f b k f c k FB TB FK FC TC FK)
  euclid_apply (Elements.Book1.proposition_8 k b f k c f TB FB FK TC FC FK)
  euclid_finish

/-- The angle `HKL` of the tangents at `B`, `C` is double `FKC` [Prop. 1.8]. -/
theorem proposition_12_double : ∀ (b c f h k l : Point) (HK KL : Line) (α : Circle),
  f.isCentre α ∧ HK.touchesCircleAt α b ∧ KL.touchesCircleAt α c ∧ h.onLine HK ∧
  k.onLine HK ∧ k.onLine KL ∧ l.onLine KL ∧ between h b k ∧ between k c l ∧ b ≠ c ∧
  ∠ b:k:f = ∠ f:k:c → ∠ h:k:l = ∠ f:k:c + ∠ f:k:c :=
by
  euclid_intros
  euclid_apply (centre_same_side_of_touches b c f HK α)
  euclid_apply (centre_same_side_of_touches c b f KL α)
  euclid_apply (sum_angles_onlyif k b c f HK KL)
  euclid_apply (equal_angles k b h c l HK KL)
  euclid_finish

/--
On the side `KL`, touching at `C`: the angles `BFC`, `CFD` being equal, so are their
halves `KFC`, `LFC`; `FC` is common and the angles at `C` right, so `KC = CL` and `FKC =
FLC` [Prop. 1.26].
-/
theorem proposition_12_side : ∀ (b c d f k l : Point) (KL FC : Line) (α : Circle),
  f.isCentre α ∧ KL.touchesCircleAt α c ∧ distinctPointsOnLine f c FC ∧ k.onLine KL ∧
  l.onLine KL ∧ between k c l ∧ ∠ b:f:c = ∠ c:f:d ∧ ∠ b:f:k = ∠ k:f:c ∧
  ∠ c:f:l = ∠ l:f:d ∧ ∠ b:f:c = ∠ b:f:k + ∠ k:f:c ∧ ∠ c:f:d = ∠ c:f:l + ∠ l:f:d →
  |(k─c)| = |(c─l)| ∧ ∠ f:k:c = ∠ f:l:c :=
by
  euclid_intros
  euclid_apply (Elements.Book3.proposition_18 c k f KL α)
  euclid_apply (Elements.Book3.proposition_18 c l f KL α)
  euclid_apply (line_from_points f k) as FK
  euclid_apply (line_from_points f l) as FL
  euclid_apply (Elements.Book1.proposition_26 k f c l f c FK FC KL FL FC KL)
  euclid_finish

/--
`HK`, touching at `B`, has the vertex `M` of the tangents at `D`, `E` on the center's
side: `HK` meets `LM` at `P`, across `DF` from `M`, so `D` is between `P` and `M`.
-/
theorem proposition_12_convex : ∀ (b d e f m : Point) (TB TD BD DE DF BF : Line)
    (α : Circle),
  f.isCentre α ∧ b.onCircle α ∧ d.onCircle α ∧ e.onCircle α ∧ TB.touchesCircleAt α b ∧
  TD.touchesCircleAt α d ∧ m.onLine TD ∧ distinctPointsOnLine b d BD ∧
  distinctPointsOnLine d e DE ∧ distinctPointsOnLine d f DF ∧
  distinctPointsOnLine b f BF ∧
  f.sameSide b DE ∧ f.sameSide e BD ∧ m.sameSide e DF → m.sameSide f TB :=
by
  euclid_intros
  euclid_apply (tangents_meet b d f TB TD BD BF DF α) as p
  euclid_apply (triple_incidence_1 BD DF DE d b f e)
  euclid_apply (centre_same_side_of_touches b d f TB α)
  euclid_finish

/--
Euclid's argument: the tangents `GH`, `HK`, `KL`, `LM`, `MG` at `A`, `B`, `C`, `D`, `E`,
the angles `AFB`, `BFC`, `CFD`, `DFE`, `EFA` at the center being equal, make an
equilateral and equiangular pentagon `GHKLM`.
-/
theorem proposition_12_metric : ∀ (a b c d e f g h k l m : Point)
    (GH HK KL LM MG : Line) (α : Circle),
  f.isCentre α ∧ GH.touchesCircleAt α a ∧ HK.touchesCircleAt α b ∧
  KL.touchesCircleAt α c ∧ LM.touchesCircleAt α d ∧ MG.touchesCircleAt α e ∧
  g.onLine GH ∧ h.onLine GH ∧ h.onLine HK ∧ k.onLine HK ∧ k.onLine KL ∧ l.onLine KL ∧
  l.onLine LM ∧ m.onLine LM ∧ m.onLine MG ∧ g.onLine MG ∧
  between g a h ∧ between h b k ∧ between k c l ∧ between l d m ∧ between m e g ∧
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a ∧
  ∠ a:f:b = ∠ b:f:c ∧ ∠ b:f:c = ∠ c:f:d ∧ ∠ c:f:d = ∠ d:f:e ∧ ∠ d:f:e = ∠ e:f:a ∧
  ∠ a:f:b = ∠ a:f:h + ∠ h:f:b ∧ ∠ b:f:c = ∠ b:f:k + ∠ k:f:c ∧
  ∠ c:f:d = ∠ c:f:l + ∠ l:f:d ∧ ∠ d:f:e = ∠ d:f:m + ∠ m:f:e ∧
  ∠ e:f:a = ∠ e:f:g + ∠ g:f:a →
  equilateralPentagon g h k l m ∧ equiangularPentagon g h k l m :=
by
  euclid_intros
  -- at each vertex, the tangents are equal and FH, FK, FL, FM, FG cut the angles in
  -- half [Props. 3.18, 1.47, 1.8]
  euclid_apply (proposition_12_vertex a b f h GH HK α)
  euclid_apply (proposition_12_vertex b c f k HK KL α)
  euclid_apply (proposition_12_vertex c d f l KL LM α)
  euclid_apply (proposition_12_vertex d e f m LM MG α)
  euclid_apply (proposition_12_vertex e a f g MG GH α)
  -- KFC = LFC, FC common, the angles at C right: KC = CL, FKC = FLC [Prop. 1.26]; and so
  -- on each side
  euclid_apply (line_from_points f a) as FA
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f c) as FC
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points f e) as FE
  euclid_apply (proposition_12_side e a b f g h GH FA α)
  euclid_apply (proposition_12_side a b c f h k HK FB α)
  euclid_apply (proposition_12_side b c d f k l KL FC α)
  euclid_apply (proposition_12_side c d e f l m LM FD α)
  euclid_apply (proposition_12_side d e a f m g MG FE α)
  -- KL is double KC, and HK double BK: HK = KL; and so the other sides
  euclid_apply (between_if g a h)
  euclid_apply (between_if h b k)
  euclid_apply (between_if k c l)
  euclid_apply (between_if l d m)
  euclid_apply (between_if m e g)
  -- HKL is double FKC, and KLM double FLC: they are equal; and so the other angles
  euclid_apply (proposition_12_double a b f g h k GH HK α)
  euclid_apply (proposition_12_double b c f h k l HK KL α)
  euclid_apply (proposition_12_double c d f k l m KL LM α)
  euclid_apply (proposition_12_double d e f l m g LM MG α)
  euclid_apply (proposition_12_double e a f m g h MG GH α)
  euclid_assert ∠ f:h:a = ∠ f:h:b
  euclid_assert ∠ f:k:b = ∠ f:k:c
  euclid_assert ∠ f:l:c = ∠ f:l:d
  euclid_assert ∠ f:m:d = ∠ f:m:e
  euclid_assert ∠ f:g:e = ∠ f:g:a
  have : |(l─m)| = |(m─g)| := by linarith
  euclid_finish

/-- The tangents make a convex pentagon `GHKLM`: the vertices next to each side are on the
circle's side of it, and so, by `proposition_12_convex`, is the vertex opposite. -/
theorem proposition_12_pentagon : ∀ (a b c d e f g h k l m : Point)
    (GH HK KL LM MG : Line) (α : Circle),
  f.isCentre α ∧ GH.touchesCircleAt α a ∧ HK.touchesCircleAt α b ∧
  KL.touchesCircleAt α c ∧ LM.touchesCircleAt α d ∧ MG.touchesCircleAt α e ∧
  g.onLine GH ∧ h.onLine GH ∧ h.onLine HK ∧ k.onLine HK ∧ k.onLine KL ∧ l.onLine KL ∧
  l.onLine LM ∧ m.onLine LM ∧ m.onLine MG ∧ g.onLine MG ∧
  between g a h ∧ between h b k ∧ between k c l ∧ between l d m ∧ between m e g ∧
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a ∧
  l.sameSide f GH ∧ m.sameSide f HK ∧ g.sameSide f KL ∧ h.sameSide f LM ∧
  k.sameSide f MG →
  pentagon g h k l m GH HK KL LM MG :=
by
  euclid_intros
  euclid_apply (centre_same_side_of_touches a b f GH α)
  euclid_apply (centre_same_side_of_touches a e f GH α)
  euclid_apply (centre_same_side_of_touches b a f HK α)
  euclid_apply (centre_same_side_of_touches b c f HK α)
  euclid_apply (centre_same_side_of_touches c b f KL α)
  euclid_apply (centre_same_side_of_touches c d f KL α)
  euclid_apply (centre_same_side_of_touches d c f LM α)
  euclid_apply (centre_same_side_of_touches d e f LM α)
  euclid_apply (centre_same_side_of_touches e d f MG α)
  euclid_apply (centre_same_side_of_touches e a f MG α)
  euclid_finish

/-- To circumscribe an equilateral and equiangular pentagon `GHKLM` about a given circle
`α`, with center `f`; its sides touch the circle at `A`, `B`, `C`, `D`, `E`. -/
theorem proposition_12 : ∀ (f : Point) (α : Circle),
  f.isCentre α →
  ∃ (g h k l m a b c d e : Point) (GH HK KL LM MG : Line),
  pentagon g h k l m GH HK KL LM MG ∧
  circumscribedPentagon g h k l m GH HK KL LM MG a b c d e α ∧
  equilateralPentagon g h k l m ∧ equiangularPentagon g h k l m :=
by
  euclid_intros
  -- A, B, C, D, E the vertices of a pentagon inscribed in the circle [Prop. 4.11]
  euclid_apply (proposition_11' f α) as (a, b, c, d, e, AB, BC, CD, DE, EA, AC, AD, BD,
    BE, CE)
  -- GH, HK, KL, LM, MG touching the circle at A, B, C, D, E. Missed by Euclid: they
  -- meet (Post. 5).
  euclid_apply (exists_tangent a f α) as GH
  euclid_apply (exists_tangent b f α) as HK
  euclid_apply (exists_tangent c f α) as KL
  euclid_apply (exists_tangent d f α) as LM
  euclid_apply (exists_tangent e f α) as MG
  euclid_apply (line_from_points f a) as FA
  euclid_apply (line_from_points f b) as FB
  euclid_apply (line_from_points f c) as FC
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points f e) as FE
  euclid_apply (tangents_meet a b f GH HK AB FA FB α) as h
  euclid_apply (tangents_meet b c f HK KL BC FB FC α) as k
  euclid_apply (tangents_meet c d f KL LM CD FC FD α) as l
  euclid_apply (tangents_meet d e f LM MG DE FD FE α) as m
  euclid_apply (tangents_meet e a f MG GH EA FE FA α) as g
  euclid_assert between g a h
  euclid_assert between h b k
  euclid_assert between k c l
  euclid_assert between l d m
  euclid_assert between m e g
  -- the angles AFB, BFC, CFD, DFE, EFA are halved by FH, FK, FL, FM, FG
  euclid_apply (sum_angles_onlyif f a b h FA FB)
  euclid_apply (sum_angles_onlyif f b c k FB FC)
  euclid_apply (sum_angles_onlyif f c d l FC FD)
  euclid_apply (sum_angles_onlyif f d e m FD FE)
  euclid_apply (sum_angles_onlyif f e a g FE FA)
  -- the circumferences AB, BC, CD, DE, EA are equal [Prop. 3.28], and so are the angles
  -- AFB, BFC, CFD, DFE, EFA on them [Prop. 3.27]
  euclid_apply (point_on_circle_onlyif f a b α)
  euclid_apply (point_on_circle_onlyif f a c α)
  euclid_apply (point_on_circle_onlyif f a d α)
  euclid_apply (point_on_circle_onlyif f a e α)
  euclid_apply (Elements.Book3.proposition_28 a b b c f f AB BC α α)
  euclid_apply (Elements.Book3.proposition_28 b c c d f f BC CD α α)
  euclid_apply (Elements.Book3.proposition_28 c d d e f f CD DE α α)
  euclid_apply (Elements.Book3.proposition_28 d e e a f f DE EA α α)
  euclid_apply (Elements.Book3.proposition_27' a b b c f f AB BC α α)
  euclid_apply (Elements.Book3.proposition_27' b c c d f f BC CD α α)
  euclid_apply (Elements.Book3.proposition_27' c d d e f f CD DE α α)
  euclid_apply (Elements.Book3.proposition_27' d e e a f f DE EA α α)
  euclid_apply (proposition_12_metric a b c d e f g h k l m GH HK KL LM MG α)
  -- Missed by Euclid: GHKLM is convex. The vertices next to a side are on the circle's
  -- side of it, and so is the vertex opposite.
  euclid_apply (proposition_12_convex b d e f m HK LM BD DE FD FB α)
  euclid_apply (proposition_12_convex a c d f l GH KL AC CD FC FA α)
  euclid_apply (proposition_12_convex c e a f g KL MG CE EA FE FC α)
  euclid_apply (proposition_12_convex d a b f h LM GH AD AB FA FD α)
  euclid_apply (proposition_12_convex e b c f k MG HK BE BC FB FE α)
  euclid_apply (proposition_12_pentagon a b c d e f g h k l m GH HK KL LM MG α)
  use g, h, k, l, m, a, b, c, d, e, GH, HK, KL, LM, MG

end Elements.Book4
