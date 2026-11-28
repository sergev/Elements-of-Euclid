import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop31
import Elements.Book6.Prop02

namespace Elements.Book6

open Elements.Book5

/--
To find a fourth straight line `xy` proportional to three given straight lines `a₁a₂`,
`b₁b₂`, `c₁c₂`: `a₁a₂ : b₁b₂ :: c₁c₂ : xy`. Props. 5.18 and 5.24 assume a fourth
proportional; for lines, this is it.
-/
theorem proposition_12 : ∀ (a₁ a₂ b₁ b₂ c₁ c₂ : Point),
  a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ c₁ ≠ c₂ → ∃ x y : Point, (a₁─a₂) ∶ (b₁─b₂) ∷ (c₁─c₂) ∶ (x─y) :=
by
  euclid_intros
  -- let `DE`, `DF` be set out at a random angle; `dg` equal to `A`, `ge` to `B`, and
  -- `dh` to `C` [Prop. 1.3]
  euclid_apply (line_from_points a₁ a₂) as DE
  euclid_apply (lay_beyond a₁ a₂ b₁ b₂ DE) as e
  euclid_apply (Elements.Book1.proposition_1 a₁ a₂ DE) as z
  euclid_apply (line_from_points a₁ z) as DF
  euclid_apply (lay_on_ray a₁ z c₁ c₂ DF) as h
  -- join `GH`, and draw `EF` through `e` parallel to it [Prop. 1.31]
  euclid_apply (line_from_points a₂ h) as GH
  euclid_apply (Elements.Book1.proposition_31 e a₂ h GH) as EF
  euclid_apply (parallel_meets h EF GH DF)
  euclid_apply (intersection_lines EF DF) as f
  -- `GH` is parallel to the side `EF` of the triangle `DEF`: `DG : GE :: DH : HF`
  -- [Prop. 6.2], that is, `A : B :: C : HF`
  have h₁ := proposition_2 a₁ e f a₂ h DE EF DF GH
    ⟨by euclid_finish, ‹_›, by euclid_finish, ‹_›, ‹_›, by euclid_finish⟩
  have e₁ : size (e─a₂) = size (b₁─b₂) := by
    rw [size_segment, size_segment, segment_symmetric e a₂]; euclid_finish
  have e₂ : size (h─a₁) = size (c₁─c₂) := by
    rw [size_segment, size_segment, segment_symmetric h a₁]; euclid_finish
  exact ⟨h, f, h₁.inv.congr (by size_perm) e₁ e₂ (by size_perm)⟩

end Elements.Book6
