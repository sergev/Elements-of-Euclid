import SystemE
import Elements.Book1.Prop03
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book1.Prop38
import Elements.Book5.Prop11
import Elements.Book5.Prop15
import Elements.Book6.Lemmas

namespace Elements.Book6

open Elements.Book5 Magnitude

/-- `h` beyond `b` from `c`, and `l` beyond `d`, are on either side of `c`. -/
theorem proposition_1_between : ∀ (b c d h l : Point) (L : Line),
  b.onLine L ∧ c.onLine L ∧ d.onLine L ∧ h.onLine L ∧ l.onLine L ∧ between b c d ∧
  (between c b h ∨ h = b) ∧ (between c d l ∨ l = d) → between h c l :=
by
  euclid_intros
  rcases ‹between c b h ∨ h = b› with h₁ | h₁ <;>
  rcases ‹between c d l ∨ l = d› with h₂ | h₂
  · euclid_finish
  · subst h₂
    euclid_finish
  · subst h₁
    euclid_finish
  · subst h₁ h₂
    euclid_finish

/-- Triangles with vertex `a` on equal bases `hc`, `cl` are equal [Prop. 1.38]. -/
theorem proposition_1_eq : ∀ (a c h l : Point) (L : Line),
  h.onLine L ∧ c.onLine L ∧ l.onLine L ∧ ¬(a.onLine L) ∧ between h c l ∧
  |(c─h)| = |(c─l)| → Triangle.area △a:c:h = Triangle.area △a:c:l :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_31 a h c L) as AD
  euclid_apply (line_from_points a h) as AH
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points a l) as AL
  euclid_apply (Elements.Book1.proposition_38 a h c a c l AD L AH AC AC AL)
  euclid_finish

/--
If base `hc` is less than `cl`, triangle `ahc` is less than `acl`: cut off `cx` equal to
`ch` [Prop. 1.3]; `acx` is equal to `ach` [Prop. 1.38], and a part of `acl`.
-/
theorem proposition_1_lt : ∀ (a c h l : Point) (L : Line),
  h.onLine L ∧ c.onLine L ∧ l.onLine L ∧ ¬(a.onLine L) ∧ between h c l ∧
  |(c─h)| < |(c─l)| → Triangle.area △a:c:h < Triangle.area △a:c:l :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_3 c l c h L L) as x
  euclid_apply (proposition_1_eq a c h x L)
  euclid_apply (sum_areas_if c l x a L)
  have : 0 < Triangle.area △a:x:l :=
    size_triangle_pos' ⟨by euclid_finish, ‹l.onLine L›, by euclid_finish⟩ ‹¬(a.onLine L)›
  euclid_finish

/--
Triangles `abc`, `acd` of the same height, with the vertex `a` and the bases `bc`, `cd`
on a line, are to one another as their bases.
-/
theorem proposition_1 : ∀ (a b c d : Point) (BD : Line),
  b.onLine BD ∧ c.onLine BD ∧ d.onLine BD ∧ between b c d ∧ ¬(a.onLine BD) →
  (b─c) ∶ (c─d) ∷ △a:b:c ∶ △a:c:d :=
by
  euclid_intros
  have hbc : 0 < size (b─c) := size_segment_pos.mpr (by euclid_finish)
  have hcd : 0 < size (c─d) := size_segment_pos.mpr (by euclid_finish)
  have hcb : 0 < size (c─b) := size_segment_pos.mpr (by euclid_finish)
  have habc : 0 < size (△a:b:c) := size_triangle_pos' ⟨‹_›, ‹_›, by euclid_finish⟩ ‹_›
  have hacb : 0 < size (△a:c:b) := size_triangle_pos' ⟨‹_›, ‹_›, by euclid_finish⟩ ‹_›
  have hacd : 0 < size (△a:c:d) := size_triangle_pos' ⟨‹_›, ‹_›, by euclid_finish⟩ ‹_›
  refine ⟨hbc, hcd, habc, hacd, ?_⟩
  -- produce `BD` both ways, and make `BG`, `GH`, … equal to `BC`, any number, and `DK`,
  -- `KL`, … equal to `CD`; join `AG`, `AH`, `AK`, `AL`. Triangles `AHG`, `AGB`, `ABC`
  -- are equal [Prop. 1.38]: as many times as `HC` is `BC`, so many times is `AHC` the
  -- triangle `ABC`, and so for `LC`, `CD` and `ALC`, `ACD`
  have copies : ∀ m n : ℕ+, ∃ (h l : Point) (hh : 0 < size (c─h)) (hl : 0 < size (c─l))
      (hah : 0 < size (△a:c:h)) (hal : 0 < size (△a:c:l)), between h c l ∧
      mag (c─h) hh = m • mag (b─c) hbc ∧ mag (△a:c:h) hah = m • mag (△a:b:c) habc ∧
      mag (c─l) hl = n • mag (c─d) hcd ∧ mag (△a:c:l) hal = n • mag (△a:c:d) hacd ∧
      h.onLine BD ∧ l.onLine BD := by
    intro m n
    obtain ⟨h, hh, hah, hBD, hbh, h₁, h₂⟩ := multiple_on_line m ‹c.onLine BD›
      ‹b.onLine BD› ‹_› hcb hacb
    obtain ⟨l, hl, hal, lBD, hdl, h₃, h₄⟩ := multiple_on_line n ‹c.onLine BD›
      ‹d.onLine BD› ‹_› hcd hacd
    refine ⟨h, l, hh, hl, hah, hal, ?_, ?_, ?_, h₃, h₄, hBD, lBD⟩
    · exact proposition_1_between b c d h l BD ⟨‹_›, ‹_›, ‹_›, hBD, lBD, ‹_›,
        by rcases hbh with h' | h' <;> [left; right] <;> euclid_finish,
        by rcases hdl with h' | h' <;> [left; right] <;> euclid_finish⟩
    · rw [h₁, mag_congr (size_segment_symm c b)]
    · rw [h₂, mag_congr (size_triangle_swap a c b)]
  -- if base `HC` is equal to `CL`, triangle `AHC` is equal to `ACL` [Prop. 1.38]; if it
  -- exceeds, it exceeds, and if less, less. So `BC : CD :: ABC : ACD` [Def. 5.5]
  apply Proportion.of_imp <;> intro m n hmn <;>
    obtain ⟨h, l, hh, hl, hah, hal, hhcl, h₁, h₂, h₃, h₄, hBD, lBD⟩ := copies m n <;>
    rw [← h₁, ← h₃] at hmn <;> rw [← h₂, ← h₄]
  · rw [mag_lt] at hmn ⊢
    exact proposition_1_lt a c l h BD ⟨lBD, ‹_›, hBD, ‹_›, by euclid_finish, hmn⟩
  · rw [mag_inj] at hmn ⊢
    exact proposition_1_eq a c h l BD ⟨hBD, ‹_›, lBD, ‹_›, hhcl, hmn⟩
  · rw [mag_lt] at hmn ⊢
    exact proposition_1_lt a c h l BD ⟨hBD, ‹_›, lBD, ‹_›, hhcl, hmn⟩

/-- A parallelogram `ebca` is double the triangle `abc` of its diagonal [Prop. 1.34]. -/
theorem proposition_1_double : ∀ (a b c e : Point) (EA BC EB AC : Line),
  formParallelogram e a b c EA BC EB AC →
  Triangle.area △e:b:c + Triangle.area △e:c:a =
    Triangle.area △a:b:c + Triangle.area △a:b:c :=
by
  euclid_intros
  euclid_apply (line_from_points a b) as AB
  euclid_apply (Elements.Book1.proposition_34 e a b c EA BC EB AC AB)
  euclid_apply (parallelogram_area e a b c EA BC EB AC)
  euclid_finish

/--
Parallelograms `ebca`, `facd` of the same height, between the parallels `EF` and `BD`,
with the bases `bc`, `cd` on `BD`, are to one another as their bases.
-/
theorem proposition_1' : ∀ (a b c d e f : Point) (EF BD EB AC FD : Line),
  formParallelogram e a b c EF BD EB AC ∧ formParallelogram a f c d EF BD AC FD ∧
  between b c d → (b─c) ∶ (c─d) ∷ □e:b:c:a ∶ □f:a:c:d :=
by
  euclid_intros
  -- `EC` is double `ABC`, and `FC` double `ACD` [Prop. 1.34]
  have h₂ := proposition_1_double a b c e EF BD EB AC (by euclid_finish)
  have h₃ := proposition_1_double a d c f EF BD FD AC (by euclid_finish)
  obtain ⟨hbc, hcd, habc, hacd, h₁⟩ :=
    proposition_1 a b c d BD ⟨‹_›, ‹_›, ‹_›, ‹_›, by euclid_finish⟩
  have s₂ : size (□e:b:c:a) = size (△a:b:c) + size (△a:b:c) := h₂
  have s₃ : size (□f:a:c:d) = size (△a:c:d) + size (△a:c:d) := by
    rw [size_quadrilateral, size_triangle, area_symm_2 f a c, area_symm_2 f c d,
      area_symm_2 a c d]
    linarith
  have hEC : 0 < size (□e:b:c:a) := s₂ ▸ add_pos habc habc
  have hFC : 0 < size (□f:a:c:d) := s₃ ▸ add_pos hacd hacd
  refine ⟨hbc, hcd, hEC, hFC, ?_⟩
  -- parts have the same ratio as equal multiples [Prop. 5.15]: `ABC : ACD :: EC : FC`
  have h₄ := proposition_15 (mag (△a:b:c) habc) (mag (△a:c:d) hacd) 2
  rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult, mult_succ, one_mult,
    mag_add (hr := hEC) s₂.symm, mag_add (hr := hFC) s₃.symm] at h₄
  -- so `BC : CD :: EC : FC` [Prop. 5.11]
  exact proposition_11 h₁ h₄

end Elements.Book6
