import SystemE
import Elements.Book6.Prop11
import Elements.Book6.Prop15

namespace Elements.Book6

open Elements.Book5

/--
Similar triangles `abc`, `def` are to one another in the squared ratio of corresponding
sides: `abc : def` is the squared ratio of `bc : ef` (Def. 5.9).
-/
theorem proposition_19 : ∀ (a b c d e f : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧
  similarTriangles a b c d e f → SquaredRatio' (△a:b:c) (△d:e:f) (b─c) (e─f) :=
by
  euclid_intros
  -- a third proportional `BG` to `BC`, `EF` [Prop. 6.11], laid off on `BC` [Prop. 1.3]
  obtain ⟨x, y, h₁⟩ := proposition_11 b c e f (by euclid_finish)
  have hxy : x ≠ y := size_segment_pos.mp h₁.2.2.2.1
  euclid_apply (lay_on_ray b c x y BC) as g
  have h₁ : (b─c) ∶ (e─f) ∷ (e─f) ∶ (b─g) :=
    h₁.congr rfl rfl rfl ‹|(b─g)| = |(x─y)|›.symm
  euclid_apply (line_from_points a g) as AG
  euclid_apply (equal_angles b c g a a BC AB)
  -- `AB : BC :: DE : EF`, alternately `AB : DE :: BC : EF` [Prop. 5.16], that is,
  -- `EF : BG`; so the sides of `ABG`, `DEF` about the equal angles at `b`, `e` are
  -- reciprocally proportional, and they are equal [Prop. 6.15]
  have h₂ := (‹(a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f)›.alt.trans h₁).alt
  have h₃ := proposition_15' b g a e f d BC AG AB EF FD DE
    ⟨by euclid_finish, by euclid_finish, by euclid_finish, h₂⟩
  -- `BC` has to `BG` the squared ratio of `BC : EF` [Def. 5.9], and
  -- `BC : BG :: ABC : ABG` [Prop. 6.1], and `ABG` is equal to `DEF`
  have e₁ : size (△a:b:g) = size (△d:e:f) :=
    calc size (△a:b:g) = size (△b:g:a) := by size_perm
      _ = size (△e:f:d) := h₃
      _ = size (△d:e:f) := by size_perm
  have h₄ := (proposition_1_ray a b c g BC (by euclid_finish)).symm.congr rfl e₁ rfl rfl
  obtain ⟨hbc, hef, hef', hbg, h₁⟩ := h₁
  obtain ⟨habc, hdef, hbc', hbg', h₄⟩ := h₄
  exact ⟨habc, hdef, hbc, hef, mag (b─g) hbg, h₁, h₄⟩

/--
Corollary: if three straight lines are proportional, `bc : ef :: ef : xy`, then as the
first is to the third, so is the triangle on the first to the similar, and similarly
described, triangle on the second.
-/
theorem proposition_19_corollary : ∀ (a b c d e f x y : Point) (AB BC CA DE EF FD : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d e f DE EF FD ∧
  similarTriangles a b c d e f ∧ (b─c) ∶ (e─f) ∷ (e─f) ∶ (x─y) →
  (b─c) ∶ (x─y) ∷ △a:b:c ∶ △d:e:f :=
by
  euclid_intros
  obtain ⟨habc, hdef, hbc, hef, z, h₁, h₂⟩ :=
    proposition_19 a b c d e f AB BC CA DE EF FD (by euclid_finish)
  obtain ⟨hbc', hef', hef'', hxy, h₃⟩ := ‹(b─c) ∶ (e─f) ∷ (e─f) ∶ (x─y)›
  -- `BC : EF :: EF : z` and `BC : EF :: EF : XY`, so `z` is `XY` [Props. 5.11, 5.9]
  have := Elements.Book5.proposition_9' (Elements.Book5.proposition_11 h₁.symm h₃)
  subst this
  exact ⟨hbc, hxy, habc, hdef, h₂.symm⟩

end Elements.Book6
