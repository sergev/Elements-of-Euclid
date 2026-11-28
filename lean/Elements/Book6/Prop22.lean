import SystemE
import Elements.Book6.Prop12
import Elements.Book6.Prop18
import Elements.Book6.Prop20
import Elements.Book6.Prop21

namespace Elements.Book6

open Elements.Book5

/--
If four straight lines are proportional, `ab : cd :: ef : gh`, similar and similarly
described figures on them are proportional. As in Euclid's figure, the figures on `ab`,
`cd` are the similar triangles `kab`, `lcd`, and those on `ef`, `gh` the similar
quadrilaterals `efpm`, `ghqn`.
-/
theorem proposition_22 :
  ∀ (a b c d e f g h k l m n p q : Point)
    (KA AB BK LC CD DL EF FP PM ME GH HQ QN NG : Line),
  formTriangle k a b KA AB BK ∧ formTriangle l c d LC CD DL ∧
  similarTriangles k a b l c d ∧
  quadrilateral e f p m EF FP PM ME ∧ quadrilateral g h q n GH HQ QN NG ∧
  similarQuadrilaterals e f p m g h q n ∧ (a─b) ∶ (c─d) ∷ (e─f) ∶ (g─h) →
  △k:a:b ∶ △l:c:d ∷ □m:e:f:p ∶ □n:g:h:q :=
by
  euclid_intros
  -- `KAB : LCD` is the squared ratio of `AB : CD`, and `MF : NH` of `EF : GH`
  -- [Props. 6.19, 6.20 corollary]; with third proportionals `O`, `P`, via equality
  -- `AB : O :: EF : P` [Prop. 5.22], and so the figures are proportional
  have q₁ := proposition_19 k a b l c d KA AB BK LC CD DL (by euclid_finish)
  obtain ⟨-, -, -, -, q₂⟩ := proposition_20_corollary e f p m g h q n EF FP PM ME GH HQ QN
    NG (by euclid_finish)
  exact q₁.same q₂ ‹_›

/--
If similar and similarly described figures on four straight lines are proportional,
`kab : lcd :: efpm : ghqn`, the lines are proportional: `ab : cd :: ef : gh`.
-/
theorem proposition_22' :
  ∀ (a b c d e f g h k l m n p q : Point)
    (KA AB BK LC CD DL EF FP PM ME GH HQ QN NG : Line),
  formTriangle k a b KA AB BK ∧ formTriangle l c d LC CD DL ∧
  similarTriangles k a b l c d ∧
  quadrilateral e f p m EF FP PM ME ∧ quadrilateral g h q n GH HQ QN NG ∧
  similarQuadrilaterals e f p m g h q n ∧ △k:a:b ∶ △l:c:d ∷ □m:e:f:p ∶ □n:g:h:q →
  (a─b) ∶ (c─d) ∷ (e─f) ∶ (g─h) :=
by
  euclid_intros
  -- let `AB : CD :: EF : XY` [Prop. 6.12], and on `XY` the figure `XYST` similar, and
  -- similarly laid down, to `EFPM` [Prop. 6.18], so to `GHQN` [Prop. 6.21]
  obtain ⟨x, y, h₁⟩ := proposition_12 a b c d e f (by euclid_finish)
  have hxy : x ≠ y := size_segment_pos.mp h₁.2.2.2.1
  euclid_apply (line_from_points x y) as XY
  obtain ⟨t, s, YS, ST, TX, hq, hs⟩ := proposition_18 x y e f p m XY EF FP PM ME
    (by euclid_finish)
  have s₁ := similarQuadrilaterals_symm hs
  have s₂ := proposition_21' x y s t e f p m g h q n
    ⟨s₁, similarQuadrilaterals_symm ⟨by euclid_finish, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩
  -- so `KAB : LCD :: MF : SX` (as shown), and `MF : NH :: MF : SX` [Prop. 5.11]: `NH` is
  -- equal to `SX` [Prop. 5.9]
  have q₁ := proposition_19 k a b l c d KA AB BK LC CD DL (by euclid_finish)
  obtain ⟨-, -, -, -, q₂⟩ := proposition_20_corollary e f p m x y s t EF FP PM ME XY YS ST
    TX (by euclid_finish)
  have h₂ := q₁.same q₂ h₁
  have h₃ := (‹△k:a:b ∶ △l:c:d ∷ □m:e:f:p ∶ □n:g:h:q›.symm.trans h₂).eq_right rfl
  -- equal similar figures have their corresponding sides equal (Euclid takes it for
  -- granted): `GH` is `XY`, the figures being in the squared ratio of `XY : GH`
  -- [Prop. 6.20 corollary, Prop. 5.14]
  obtain ⟨-, -, -, -, q₃⟩ := proposition_20_corollary x y s t g h q n XY YS ST TX GH HQ QN
    NG (by euclid_finish)
  have h₄ := q₃.eq h₃.symm
  exact h₁.congr rfl rfl rfl h₄

end Elements.Book6
