import Elements.Book10.Prop113

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- If an area is contained by an apotome `l`, with terms `x > y`, and a binomial `m`,
with terms `x'`, `y'` commensurable with those of the apotome and in the same ratio, the
square root `z` of the area is rational. -/
theorem proposition_114 {l m x y x' y' z : Length} (_h : BinomialTerms ρ x y)
    (hl : l + y = x)
    (h' : BinomialTerms ρ x' y') (hm : m = x' + y') (hx : Commensurable x x')
    (_hy : Commensurable y y') (hp : Proportion x y x' y') (hz : sq z = rect l m) :
    Rational ρ z := by
  -- let the square on the rational `ρ` be applied to `m`, making `k` as breadth: an
  -- apotome whose terms `x''`, `y''` are commensurable with those of `m`, in the same
  -- ratio [Prop. 10.112]
  obtain ⟨k, hk⟩ := Area.apply m (sq ρ)
  subst hm
  obtain ⟨x'', y'', hk', -, hx', -, hp', -⟩ := proposition_112 (Rational.self ρ) h' hk
  -- so as `x` is to `y`, so `x''` to `y''` [Prop. 5.11]; alternately [Prop. 5.16], and
  -- the remainder `l` is to `k` as `x` to `x''` [Prop. 5.19]
  have h₁ := Elements.Book5.proposition_16 (Elements.Book5.proposition_11 hp hp')
  have h₂ : Proportion l k x x'' := by
    rw [← hl, ← hk', add_comm l y, add_comm k y''] at h₁ ⊢
    exact Elements.Book5.proposition_19 h₁
  -- `x` is commensurable with `x''` [Prop. 10.12], so `l` with `k` [Prop. 10.11], and the
  -- rectangles contained by `m` and them [Props. 6.1, 10.11]; that with `k` is the square
  -- on `ρ`, rational: so the square on `z`, and `z` [Def. 10.3]
  have hxx := proposition_12 Length.divisible hx hx'.symm
  have hlk := (proposition_11 h₂.symm Length.divisible Length.divisible).1 hxx
  have h₃ := (rect_commensurable_iff (x' + y')).mpr hlk
  rw [hk, ← rect_comm, ← hz] at h₃
  exact Rational.of_sq ((Rational.self ρ).sq_rational.of_comm h₃)

/-- 10.114, corollary: a rational area can be contained by irrational lines: the apotome
and the binomial of the same terms [Props. 10.29, 10.36, 10.73, 10.114, 2.14]. -/
theorem proposition_114_corollary :
    ∃ l m, ¬ Rational ρ l ∧ ¬ Rational ρ m ∧ RationalArea ρ (rect l m) := by
  obtain ⟨x, y, ⟨hx, hy, hxy, hyx⟩, -⟩ := proposition_29 (ρ := ρ)
  obtain ⟨l, hl⟩ := Magnitude.remainder y x hyx
  rw [add_comm] at hl
  obtain ⟨z, hz⟩ := Area.side (rect l (x + y))
  have hzr := proposition_114 ⟨hx, hy, hxy, hyx⟩ hl ⟨hx, hy, hxy, hyx⟩ rfl
    (.refl x) (.refl y)
    (Proportion.refl x y) hz
  exact ⟨l, x + y, proposition_73 hx hy hxy hl, proposition_36 hx hy hxy,
    hz ▸ hzr.sq_rational⟩

end Elements.Book10
