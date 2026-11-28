import Elements.Book10.Prop005

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude Number

variable {M : Type*} [Magnitude M]

/-- If `a` is `c` taken `m` times, then as `a` is to `c` taken `n` times, so `m` is to
`n`: 10.6's construction. -/
theorem proportion_parts (m n : ℕ+) (c : M) :
    Proportion (m • c) (n • c) (m : Number) (n : Number) :=
  -- as `c` is to `a`, so the unit to `m` [Def. 7.20]; inversely [Prop. 5.7 corr.]; as `c`
  -- to `f`, so the unit to `n` [Def. 7.20]; via equality [Prop. 5.22]
  Elements.Book5.proposition_22'
    (Elements.Book5.proposition_7_corollary (proportion_unit m c)) (proportion_unit n c)

/--
If two magnitudes have to one another the ratio which a number has to a number, they are
commensurable. Euclid divides `a` into as many equal parts as there are units in `m`: for
lines, Prop. 6.9 (`Length.part`); for magnitudes of any kind, a hypothesis.
-/
theorem proposition_6 {a b : M} {m n : ℕ+} (h : Proportion a b (m : Number) (n : Number))
    (hpart : ∃ c, a = m • c) : Commensurable a b := by
  -- let `a` be divided into `m` equal parts, `c` one of them, and `f` be `c` taken `n`
  -- times
  obtain ⟨c, rfl⟩ := hpart
  -- via equality, as `a` is to `f`, so `m` to `n` [Prop. 5.22]
  have h₁ := proportion_parts m n c
  -- so as `a` is to `b`, so to `f` [Prop. 5.11]: `b` is equal to `f` [Prop. 5.9]
  have hb : b = n • c :=
    Elements.Book5.proposition_9' (Elements.Book5.proposition_11 h h₁.symm)
  -- `c` measures `a` and `b`
  exact ⟨c, ⟨m, rfl⟩, ⟨n, hb⟩⟩

/--
10.6, corollary: given numbers `m`, `n` and a line `a`, to find a line `f` with `a` to `f`
as `m` to `n`; and with the mean proportional `b` of `a` and `f`, the square on `a` is to
the square on `b` as `m` to `n`.
-/
theorem proposition_6_corollary (m n : ℕ+) (a : Length) :
    ∃ f b : Length, Proportion (m : Number) (n : Number) a f ∧
      Proportion (m : Number) (n : Number) (sq a) (sq b) := by
  -- as in 10.6: `a` divided into `m` parts [Prop. 6.9], `f` the `n` of them
  obtain ⟨c, hc⟩ := Length.part a m
  have h₁ : Proportion a (n • c) (m : Number) (n : Number) := hc ▸ proportion_parts m n c
  -- the mean proportional `b` of `a` and `f` [Prop. 6.13]
  obtain ⟨b, hb⟩ := Length.mean a (n • c)
  -- as `a` is to `f`, so the square on `a` to the square on `b` [Prop. 6.19 corr.]
  obtain ⟨e, he₁, he₂⟩ := squaredRatio_sq a b
  have he : e = n • c :=
    Elements.Book5.proposition_9' (Elements.Book5.proposition_11 he₁.symm hb)
  subst he
  exact ⟨n • c, b, h₁.symm, Elements.Book5.proposition_11 h₁.symm he₂.symm⟩

end Elements.Book10
