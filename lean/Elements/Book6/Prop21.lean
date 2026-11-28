import SystemE
import Elements.Book6.Lemmas

namespace Elements.Book6

open Elements.Book5

/--
Triangles `abc`, `ghk` similar to the same triangle `def` are similar to one another:
each is equiangular to it, with the sides about the equal angles proportional [Def. 6.1,
Prop. 5.11].
-/
theorem proposition_21 : ∀ (a b c d e f g h k : Point),
  similarTriangles a b c d e f ∧ similarTriangles g h k d e f →
  similarTriangles a b c g h k :=
by
  euclid_intros
  exact ⟨by euclid_finish, ‹(a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f)›.trans
      ‹(g─h) ∶ (h─k) ∷ (d─e) ∶ (e─f)›.symm,
    ‹(b─c) ∶ (c─a) ∷ (e─f) ∶ (f─d)›.trans ‹(h─k) ∶ (k─g) ∷ (e─f) ∶ (f─d)›.symm,
    ‹(c─a) ∶ (a─b) ∷ (f─d) ∶ (d─e)›.trans ‹(k─g) ∶ (g─h) ∷ (f─d) ∶ (d─e)›.symm⟩

/-- Prop. 6.21 for quadrilaterals `abcd`, `pqrs` similar to `efgh`. -/
theorem proposition_21' : ∀ (a b c d e f g h p q r s : Point),
  similarQuadrilaterals a b c d e f g h ∧ similarQuadrilaterals p q r s e f g h →
  similarQuadrilaterals a b c d p q r s :=
by
  euclid_intros
  exact ⟨by euclid_finish,
    ‹(d─a) ∶ (a─b) ∷ (h─e) ∶ (e─f)›.trans ‹(s─p) ∶ (p─q) ∷ (h─e) ∶ (e─f)›.symm,
    ‹(a─b) ∶ (b─c) ∷ (e─f) ∶ (f─g)›.trans ‹(p─q) ∶ (q─r) ∷ (e─f) ∶ (f─g)›.symm,
    ‹(b─c) ∶ (c─d) ∷ (f─g) ∶ (g─h)›.trans ‹(q─r) ∶ (r─s) ∷ (f─g) ∶ (g─h)›.symm,
    ‹(c─d) ∶ (d─a) ∷ (g─h) ∶ (h─e)›.trans ‹(r─s) ∶ (s─p) ∷ (g─h) ∶ (h─e)›.symm⟩

/-- Prop. 6.21 for pentagons `abcde`, `pqrst` similar to `fghkl`. -/
theorem proposition_21'' : ∀ (a b c d e f g h k l p q r s t : Point),
  similarPentagons a b c d e f g h k l ∧ similarPentagons p q r s t f g h k l →
  similarPentagons a b c d e p q r s t :=
by
  euclid_intros
  exact ⟨by euclid_finish,
    ‹(e─a) ∶ (a─b) ∷ (l─f) ∶ (f─g)›.trans ‹(t─p) ∶ (p─q) ∷ (l─f) ∶ (f─g)›.symm,
    ‹(a─b) ∶ (b─c) ∷ (f─g) ∶ (g─h)›.trans ‹(p─q) ∶ (q─r) ∷ (f─g) ∶ (g─h)›.symm,
    ‹(b─c) ∶ (c─d) ∷ (g─h) ∶ (h─k)›.trans ‹(q─r) ∶ (r─s) ∷ (g─h) ∶ (h─k)›.symm,
    ‹(c─d) ∶ (d─e) ∷ (h─k) ∶ (k─l)›.trans ‹(r─s) ∶ (s─t) ∷ (h─k) ∶ (k─l)›.symm,
    ‹(d─e) ∶ (e─a) ∷ (k─l) ∶ (l─f)›.trans ‹(s─t) ∶ (t─p) ∷ (k─l) ∶ (l─f)›.symm⟩

/-- Similarity of quadrilaterals reads the same either way (Def. 6.1). -/
theorem similarQuadrilaterals_symm {a b c d e f g h : Point}
    (s : similarQuadrilaterals a b c d e f g h) : similarQuadrilaterals e f g h a b c d :=
  let ⟨⟨h₁, h₂, h₃, h₄⟩, r₁, r₂, r₃, r₄⟩ := s
  ⟨⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm⟩, r₁.symm, r₂.symm, r₃.symm, r₄.symm⟩

end Elements.Book6
