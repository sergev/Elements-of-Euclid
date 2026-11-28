import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop31
import Elements.Book5.Prop18
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

/--
Prop. 5.18 for straight lines, composition: if `be : ea :: dg : ga`, with `e`, `g` on
`ba`, `da`, then `ba : ae :: da : ag`. The fourth proportional that 5.18 assumes is
found by Prop. 6.12.
-/
theorem componendo : ∀ (a b d e g : Point),
  between b e a ∧ between d g a ∧ (b─e) ∶ (e─a) ∷ (d─g) ∶ (g─a) →
  (b─a) ∶ (a─e) ∷ (d─a) ∶ (a─g) :=
by
  euclid_intros
  obtain ⟨hbe, hea, hdg, hga, h⟩ := ‹(b─e) ∶ (e─a) ∷ (d─g) ∶ (g─a)›
  have hba : 0 < size (b─a) := size_segment_pos.mpr (by euclid_finish)
  have hda : 0 < size (d─a) := size_segment_pos.mpr (by euclid_finish)
  have e₁ : mag (b─e) hbe + mag (e─a) hea = mag (b─a) hba :=
    mag_add (between_if b e a ‹_›)
  have e₂ : mag (d─g) hdg + mag (g─a) hga = mag (d─a) hda :=
    mag_add (between_if d g a ‹_›)
  -- a fourth proportional to `BA`, `EA`, `DA` [Prop. 6.12]
  obtain ⟨x, y, hx, hy, hz, hxy, hf⟩ := proposition_12 b a e a d a (by euclid_finish)
  have h₁ := Elements.Book5.proposition_18 h (by
    rw [e₁, e₂]
    exact ⟨mag (x─y) hxy, by rwa [mag_congr (hp := hx) (hq := hba) rfl] at hf⟩)
  rw [e₁, e₂] at h₁
  exact Proportional.congr ⟨hba, hea, hda, hga, h₁⟩ rfl (by size_perm) rfl (by size_perm)

end Elements.Book6
