import SystemE
import Elements.Book1.Prop37
import Elements.Book1.Prop39
import Elements.Book5.Prop07
import Elements.Book5.Prop09
import Elements.Book6.Prop01

namespace Elements.Book6

open Elements.Book5

/--
The triangles `bde`, `cde` on the base `de`, with `d` on `ab` and `e` on `ac`, are to
`ade` as `bd` to `da` and `ce` to `ea` [Prop. 6.1].
-/
theorem proposition_2_ratios : ∀ (a b c d e : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ between a d b ∧ between a e c →
  (b─d) ∶ (d─a) ∷ △b:d:e ∶ △a:d:e ∧ (c─e) ∶ (e─a) ∷ △c:d:e ∶ △a:d:e :=
by
  euclid_intros
  have h₁ := proposition_1 e b d a AB ⟨‹_›, by euclid_finish, ‹_›, by euclid_finish,
    by euclid_finish⟩
  have h₂ := proposition_1 d c e a CA ⟨‹_›, by euclid_finish, ‹_›, by euclid_finish,
    by euclid_finish⟩
  exact ⟨h₁.congr rfl rfl (by triangle_perm) (by triangle_perm),
    h₂.congr rfl rfl (by triangle_perm) (by triangle_perm)⟩

/--
A straight line `DE` parallel to the side `BC` of the triangle `abc` cuts the sides
proportionally: `bd : da :: ce : ea`.
-/
theorem proposition_2 : ∀ (a b c d e : Point) (AB BC CA DE : Line),
  formTriangle a b c AB BC CA ∧ between a d b ∧ between a e c ∧ d.onLine DE ∧
  e.onLine DE ∧ ¬(DE.intersectsLine BC) → (b─d) ∶ (d─a) ∷ (c─e) ∶ (e─a) :=
by
  euclid_intros
  -- join `BE`, `CD`: triangles `BDE`, `CDE` are equal, on the same base `DE` and between
  -- the same parallels [Prop. 1.37]
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c d) as CD
  euclid_apply (Elements.Book1.proposition_37' b d e c AB DE BE CD CA BC)
  obtain ⟨h₁, h₂⟩ := proposition_2_ratios a b c d e AB BC CA ⟨by euclid_finish, ‹_›, ‹_›⟩
  obtain ⟨hbd, hda, hbde, hade, h₁⟩ := h₁
  obtain ⟨hce, hea, hcde, hade', h₂⟩ := h₂
  -- `BDE` and `CDE` have the same ratio to `ADE` [Prop. 5.7]
  have h₃ := (proposition_7 (mag (△a:d:e) hade)
    (mag_congr (hp := hbde) (hq := hcde) ‹_›)).1
  -- `BD : DA :: BDE : ADE` and `CE : EA :: CDE : ADE` [Prop. 6.1]; so
  -- `BD : DA :: CE : EA` [Prop. 5.11]
  exact ⟨hbd, hda, hce, hea, proposition_11 (proposition_11 h₁ h₃) h₂.symm⟩

/--
If the sides `ab`, `ac` of the triangle `abc` are cut proportionally at `d` and `e`,
`bd : da :: ce : ea`, the straight line `DE` is parallel to the remaining side `BC`.
-/
theorem proposition_2' : ∀ (a b c d e : Point) (AB BC CA DE : Line),
  formTriangle a b c AB BC CA ∧ between a d b ∧ between a e c ∧ d.onLine DE ∧
  e.onLine DE ∧ (b─d) ∶ (d─a) ∷ (c─e) ∶ (e─a) → ¬(DE.intersectsLine BC) :=
by
  euclid_intros
  obtain ⟨h₁, h₂⟩ := proposition_2_ratios a b c d e AB BC CA ⟨by euclid_finish, ‹_›, ‹_›⟩
  obtain ⟨hbd, hda, hbde, hade, h₁⟩ := h₁
  obtain ⟨hce, hea, hcde, hade', h₂⟩ := h₂
  -- `BDE : ADE :: CDE : ADE` [Props. 6.1, 5.11]
  have h₃ := proposition_11 (proposition_11 h₁.symm
    (‹(b─d) ∶ (d─a) ∷ (c─e) ∶ (e─a)›.elim hbd hda hce hea)) h₂
  -- so `BDE` is equal to `CDE` [Prop. 5.9]
  have h₄ : Triangle.area △b:d:e = Triangle.area △c:d:e :=
    mag_inj.mp (proposition_9 h₃)
  -- and they are on the same base `DE`: so between the same parallels [Prop. 1.39]
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c d) as CD
  euclid_apply (Elements.Book1.proposition_39 b d e c AB DE BE CD CA BC)
  euclid_finish

end Elements.Book6
