import Elements.Book7

/-
The notions of Book 8, over Book 7's numbers and proportion (Def. 7.20). Book 8 has no
definitions of its own: these are the phrases of its enunciations.
-/

namespace Elements.Book8

open Elements.Book7

/-- `a 0`, …, `a n` are continuously proportional in the ratio of `r` to `s`: each is to
the next as `r` is to `s` (Def. 7.20). -/
def ContinuedIn {n : ℕ} (a : Fin (n + 1) → ℕ) (r s : ℕ) : Prop :=
  ∀ i : Fin n, a i.castSucc ∶ a i.succ ∷ r ∶ s

/-- Any multitude of numbers `a 0`, …, `a n` are continuously proportional: each is to the
next as the first is to the second. One number alone is (vacuously) so. The unit may be
among them, as in 8.9 and in Book 9 (9.8–9.13: continuously proportional from a unit,
`a 0 = 1`). -/
def Continued {n : ℕ} (a : Fin (n + 1) → ℕ) : Prop := ContinuedIn a (a 0) (a 1)

/-- `b` has the same ratios as `a`, each of each: `b i` is to `b (i + 1)` as `a i` is to
`a (i + 1)`. -/
def SameRatios {n : ℕ} (b a : Fin (n + 1) → ℕ) : Prop :=
  ∀ i : Fin n, b i.castSucc ∶ b i.succ ∷ a i.castSucc ∶ a i.succ

/-- `a 0`, …, `a n` are the least of those numbers having the same ratio as them, as
7.20–7.22 have it for two (`Least`): no numbers as many, in the same ratios, are each less
than each. For two numbers it is `Least (a 0) (a 1)`. -/
def LeastSeq {n : ℕ} (a : Fin (n + 1) → ℕ) : Prop :=
  ∀ b : Fin (n + 1) → ℕ, (∀ i, 0 < b i) → SameRatios b a → ¬ ∀ i, b i < a i

/-- `n` numbers fall between `a` and `b` in continued proportion: `a`, `c 1`, …, `c n`,
`b` are continuously proportional. So 8.8–8.10 read as Euclid has them: "as many numbers
as fall between …, so many fall between …", the same `n`. -/
def FallBetween (n a b : ℕ) : Prop :=
  ∃ c : Fin (n + 2) → ℕ, (∀ i, 0 < c i) ∧ Continued c ∧ c 0 = a ∧ c (Fin.last _) = b

/--
Def. 5.9, for numbers: `c` has to `d` the squared ratio of `a` to `b` when `c`, `x`, `d`
are proportional in that ratio, `c ∶ x ∷ a ∶ b` and `x ∶ d ∷ a ∶ b`: the first has to the
third the squared ratio of that it has to the second. Euclid carries Book 5's definition
over to numbers without comment (8.11, 8.18), with proportion of numbers (Def. 7.20). Book
5's `SquaredRatio` takes the third proportional to `a`, `b`, which numbers need not have,
so here the middle term is between `c` and `d`.
-/
def SquaredRatio (c d a b : ℕ) : Prop :=
  ∃ x, 0 < x ∧ c ∶ x ∷ a ∶ b ∧ x ∶ d ∷ a ∶ b

/-- Def. 5.10, for numbers: `c` has to `d` the cubed ratio of `a` to `b` when `c`, `x`,
`y`, `d` are continuously proportional in that ratio. As with `SquaredRatio`, Euclid uses
it for numbers without comment (8.12, 8.19). -/
def CubedRatio (c d a b : ℕ) : Prop :=
  ∃ x y, 0 < x ∧ 0 < y ∧ c ∶ x ∷ a ∶ b ∧ x ∶ y ∷ a ∶ b ∧ y ∶ d ∷ a ∶ b

/--
The ratio of `c` to `d` is compounded of the ratios of `a` to `b` and `e` to `f`, as
Euclid builds it in 8.5: numbers `g`, `h`, `k` continuously proportional in those ratios,
`g ∶ h ∷ a ∶ b` and `h ∶ k ∷ e ∶ f`, and `c ∶ d ∷ g ∶ k`. Euclid takes `g`, `h`, `k` the
least such (8.4); any others give the same ratio of the outermost, so the definition does
not ask for the least. It is Book 6's `CompoundRatio` (Def. 6.5) for numbers.
-/
def CompoundRatio (c d a b e f : ℕ) : Prop :=
  ∃ g h k, 0 < g ∧ 0 < h ∧ 0 < k ∧ g ∶ h ∷ a ∶ b ∧ h ∶ k ∷ e ∶ f ∧ c ∶ d ∷ g ∶ k

end Elements.Book8
