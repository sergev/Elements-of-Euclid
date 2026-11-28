import SystemE
import Elements.Book1.Prop01
import Elements.Book4.Lemmas
import Elements.Book6.Prop04

namespace Elements.Book6

open Elements.Book5

/--
To describe on a given straight line `ab` a triangle `abg` similar, and similarly laid
down, to a given triangle `cde`: the angles at `a`, `b` equal to those at `c`, `d`
[Prop. 1.23], the remaining angle at `g` to that at `e` [Prop. 1.32], and the sides
proportional [Prop. 6.4].
-/
theorem proposition_18_triangle : ∀ (a b c d e : Point) (AB CD DE EC : Line),
  distinctPointsOnLine a b AB ∧ formTriangle c d e CD DE EC →
  ∃ (g : Point) (BG GA : Line), formTriangle a b g AB BG GA ∧
  similarTriangles c d e a b g :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_1 a b AB) as y
  euclid_apply (triangle_on e c d a b y EC CD DE AB) as g
  euclid_apply (line_from_points b g) as BG
  euclid_apply (line_from_points g a) as GA
  refine ⟨g, BG, GA, by euclid_finish, ?_⟩
  exact proposition_4 c d e a b g CD DE EC AB BG GA (by euclid_finish)

/--
To describe on a given straight line `ab` a quadrilateral `abhg` similar, and similarly
laid down, to a given quadrilateral `cdef`, as in Euclid's figure. Join `DF`; on `AB` the
triangle `GAB` equiangular to `FCD`, and on `BG` the triangle `GBH` equiangular to `FDE`
[Props. 1.23, 1.32]. The whole angles at `b`, `g` are equal to those at `d`, `f`, and the
sides are proportional [Props. 6.4, 5.22].
-/
theorem proposition_18 : ∀ (a b c d e f : Point) (AB CD DE EF FC : Line),
  distinctPointsOnLine a b AB ∧ quadrilateral c d e f CD DE EF FC →
  ∃ (g h : Point) (BH HG GA : Line), quadrilateral a b h g AB BH HG GA ∧
  similarQuadrilaterals c d e f a b h g :=
by
  euclid_intros
  euclid_apply (line_from_points d f) as DF
  -- on `AB`, the angles `GAB`, `ABG` equal to the angle at `c` and `CDF` [Prop. 1.23]
  euclid_apply (Elements.Book1.proposition_1 a b AB) as y
  euclid_apply (triangle_on f c d a b y FC CD DF AB) as g
  euclid_apply (line_from_points b g) as BG
  euclid_apply (line_from_points g a) as GA
  -- on `BG`, away from `a`, the angles `BGH`, `GBH` equal to `DFE`, `FDE`
  euclid_apply (extend_point AB a b) as y'
  euclid_apply (triangle_on e f d g b y' EF DF DE BG) as h
  euclid_apply (line_from_points b h) as BH
  euclid_apply (line_from_points h g) as HG
  -- the angles `CDE`, `EFC` are made of `CDF`, `FDE` and `EFD`, `DFC`, and are less than
  -- two right angles; so are `ABH`, `HGA`, of the angles equal to them
  euclid_apply (sum_angles_onlyif d c e f CD DE)
  euclid_apply (sum_angles_onlyif f e c d EF FC)
  euclid_apply (Elements.Book4.angle_lt_flat c d e DE)
  euclid_apply (Elements.Book4.angle_lt_flat e f c FC)
  euclid_apply (inside_of_sum a g b h AB BG BH)
  euclid_apply (inside_of_sum a b g h GA BG HG)
  -- `FCD` is equiangular to `GAB`, and `FDE` to `GBH`: their sides are proportional
  -- [Prop. 6.4]
  obtain ⟨-, h₁, h₂, h₃⟩ := proposition_4 f c d g a b FC CD DF GA AB BG
    (by euclid_finish)
  obtain ⟨-, h₄, h₅, h₆⟩ := proposition_4 f d e g b h DF DE EF BG BH HG
    (by euclid_finish)
  -- via equality, `CD : DE :: AB : BH` and `EF : FC :: HG : GA` [Prop. 5.22]
  have h₇ := h₂.exAequali (h₄.congr (by size_perm) rfl (by size_perm) rfl)
  have h₈ := h₆.exAequali (h₃.congr (by size_perm) rfl (by size_perm) rfl)
  exact ⟨g, h, BH, HG, GA, by euclid_finish, by euclid_finish, h₁, h₇, h₅, h₈⟩

end Elements.Book6
