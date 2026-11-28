import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop31
import Elements.Book6.Prop02

namespace Elements.Book6

open Elements.Book5

/--
To find a third straight line `ef` proportional to two given straight lines `ab`, `cd`:
`ab : cd :: cd : ef`.
-/
theorem proposition_11 : ∀ (a b c d : Point),
  a ≠ b ∧ c ≠ d → ∃ e f : Point, (a─b) ∶ (c─d) ∷ (c─d) ∶ (e─f) :=
by
  euclid_intros
  -- let `ab` be laid down on a line `AD`, and `ag` equal to `cd` on a line `AE` at a
  -- random angle with it; `bh` equal to `ag` beyond `b` [Prop. 1.3]
  euclid_apply (line_from_points a b) as AD
  euclid_apply (Elements.Book1.proposition_1 a b AD) as x
  euclid_apply (line_from_points a x) as AE
  euclid_apply (lay_on_ray a x c d AE) as g
  euclid_apply (lay_beyond a b c d AD) as h
  -- join `BG`, and draw `HK` through `h` parallel to it [Prop. 1.31], meeting `AE` at `k`
  euclid_apply (line_from_points b g) as BG
  euclid_apply (Elements.Book1.proposition_31 h b g BG) as HK
  euclid_apply (parallel_meets g HK BG AE)
  euclid_apply (intersection_lines HK AE) as k
  -- `BG` is parallel to the side `HK` of the triangle `AHK`: `AB : BH :: AG : GK`
  -- [Prop. 6.2], and `BH` is equal to `AG`: `AB : AG :: AG : GK`
  have h₁ := proposition_2 a h k b g AD HK AE BG
    ⟨by euclid_finish, ‹_›, by euclid_finish, ‹_›, ‹_›, by euclid_finish⟩
  have e₁ : size (h─b) = size (c─d) := by
    rw [size_segment, size_segment, segment_symmetric h b]; euclid_finish
  have e₂ : size (g─a) = size (c─d) := by
    rw [size_segment, size_segment, segment_symmetric g a]; euclid_finish
  exact ⟨g, k, h₁.inv.congr (by size_perm) e₁ e₂ (by size_perm)⟩

end Elements.Book6
