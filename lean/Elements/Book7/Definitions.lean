import Mathlib.Data.Nat.Notation

/-
The definitions of Book 7, over Lean's numbers `ℕ`.
-/

namespace Elements.Book7

/-! Defs. 7.1, 7.2: the unit is `1`; a number is a multitude of units, `1 < a`.

Def. 7.15: `a * b` is `a` added to itself as many times as there are units in `b`,
"`b` multiplies `a`". It is Lean's own `*`: `a * (b + 1) = a * b + a` (`Nat.mul_succ`)
holds by definition. Def. 7.5: "`a` measures `b` according to the units in `c`" is
`b = a * c`, and "`a` measures `b`" is `a ∣ b`, which is `∃ c, b = a * c`. -/

/-- Def. 7.3: `a` is a part of `b`, the `n`th part: `a` measures `b` according to the
units in `n`. The unit is a part too: `1` is the `n`th part of `n`. -/
def PartOf (a b n : ℕ) : Prop := 1 < n ∧ b = a * n

/--
Def. 7.4: `a` is parts of `b`, `m` of its `n`th parts: `a` is some `e` taken `m` times,
and `b` is `e` taken `n` times, with `1 < m < n`. "The same parts" are the same `m` and
`n`. Euclid takes the parts as he finds them (7.6, 7.10), not in least terms, so `m`, `n`
need not be prime to one another; `e` may be the unit (7.4).
-/
def PartsOf (a b m n : ℕ) : Prop := 1 < m ∧ m < n ∧ ∃ e, a = e * m ∧ b = e * n

/--
Def. 7.20, `a ∶ b ∷ c ∶ d`: numbers are proportional when the first is the same multiple,
or the same part, or the same parts, of the second that the third is of the fourth.
- The same multiple includes once: equals to equals (`n = 1`).
- Euclid's parts are of a greater number, so the definition says nothing of a greater
  first that is not a multiple, as `3 ∶ 2 ∷ 6 ∶ 4`. His proofs need it (7.13 alternates
  `2 ∶ 3 ∷ 4 ∶ 6`), and they read it the other way round: the second is the same parts of
  the first that the fourth is of the third. That is the last case.
-/
def Proportion (a b c d : ℕ) : Prop :=
  (∃ n, 0 < n ∧ a = b * n ∧ c = d * n) ∨
  (∃ n, PartOf a b n ∧ PartOf c d n) ∨
  (∃ m n, PartsOf a b m n ∧ PartsOf c d m n) ∨
  (∃ m n, PartsOf b a m n ∧ PartsOf d c m n)

@[inherit_doc] scoped notation:50 a:51 " ∶ " b:51 " ∷ " c:51 " ∶ " d:51 =>
  Proportion a b c d

/-- Any multitude of numbers `a 0`, …, `a n`, all of them added (7.12). -/
def sum : {n : ℕ} → (Fin (n + 1) → ℕ) → ℕ
  | 0, a => a 0
  | n + 1, a => sum (fun i : Fin (n + 1) => a i.castSucc) + a (Fin.last (n + 1))

/-- `a`, `b` are the least of those numbers having the same ratio as them (7.20): there
are no numbers less than `a` and `b` in the same ratio. -/
def Least (a b : ℕ) : Prop := ∀ c d, 0 < c → 0 < d → c ∶ d ∷ a ∶ b → ¬ (c < a ∧ d < b)

/--
`h`, `k`, `l` have the same ratio as `a`, `b`, `c` (7.33): they are the same multiple,
part, or parts of `a`, `b`, `c`, each of each, as `proportion_iff` puts Def. 7.20 for
two; so, alternately, `h ∶ k ∷ a ∶ b` and `k ∶ l ∷ b ∶ c`.
-/
def SameRatio₃ (h k l a b c : ℕ) : Prop :=
  ∃ m n x y z, 0 < m ∧ 0 < n ∧
    h = x * m ∧ a = x * n ∧ k = y * m ∧ b = y * n ∧ l = z * m ∧ c = z * n

/-- `a`, `b`, `c` are the least of those numbers having the same ratio as them (7.33). -/
def Least₃ (a b c : ℕ) : Prop :=
  ∀ h k l, 0 < h → 0 < k → 0 < l → SameRatio₃ h k l a b c → ¬ (h < a ∧ k < b ∧ l < c)

/-- `c` is the least number that `a` and `b` measure (7.34). -/
def LeastMeasured (c a b : ℕ) : Prop :=
  0 < c ∧ a ∣ c ∧ b ∣ c ∧ ∀ d, 0 < d → a ∣ d → b ∣ d → c ≤ d

/-- `d` is the least number that `a`, `b` and `c` measure (7.36). -/
def LeastMeasured₃ (d a b c : ℕ) : Prop :=
  0 < d ∧ a ∣ d ∧ b ∣ d ∧ c ∣ d ∧ ∀ e, 0 < e → a ∣ e → b ∣ e → c ∣ e → d ≤ e

/-- Def. 7.11: a prime number is measured by a unit alone (and by itself). -/
def PrimeNumber (p : ℕ) : Prop := 1 < p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Def. 7.12: numbers prime to one another are measured by a unit alone as a common
measure. -/
def PrimeTo (a b : ℕ) : Prop := ∀ d, d ∣ a → d ∣ b → d = 1

/-- Def. 7.12, three numbers: prime to one another when a unit alone measures all
three. -/
def PrimeTo₃ (a b c : ℕ) : Prop := ∀ d, d ∣ a → d ∣ b → d ∣ c → d = 1

/-- The greatest common measure `g` of `a` and `b` (7.2): it measures both, and no
greater number measures both. -/
def GreatestCommonMeasure (g a b : ℕ) : Prop :=
  g ∣ a ∧ g ∣ b ∧ ∀ e, e ∣ a → e ∣ b → e ≤ g

/-- The greatest common measure `g` of `a`, `b` and `c` (7.3). -/
def GreatestCommonMeasure₃ (g a b c : ℕ) : Prop :=
  g ∣ a ∧ g ∣ b ∧ g ∣ c ∧ ∀ e, e ∣ a → e ∣ b → e ∣ c → e ≤ g

/-- Def. 7.13: a composite number is measured by some number, other than itself. -/
def CompositeNumber (a : ℕ) : Prop := ∃ d, 1 < d ∧ d < a ∧ d ∣ a

/-- Def. 7.14: numbers composite to one another are measured by some number as a common
measure. -/
def CompositeTo (a b : ℕ) : Prop := ∃ d, 1 < d ∧ d ∣ a ∧ d ∣ b

/-- Def. 7.16: a plane number is made by two numbers multiplying one another, its
sides. -/
def PlaneNumber (a : ℕ) : Prop := ∃ p q, 1 < p ∧ 1 < q ∧ a = p * q

/-- Def. 7.17: a solid number is made by three numbers multiplying one another. -/
def SolidNumber (a : ℕ) : Prop := ∃ p q r, 1 < p ∧ 1 < q ∧ 1 < r ∧ a = p * q * r

/-- Def. 7.18: a square number is an equal times an equal. -/
def SquareNumber (a : ℕ) : Prop := ∃ p, 1 < p ∧ a = p * p

/-- Def. 7.19: a cube number is an equal times an equal times an equal. -/
def CubeNumber (a : ℕ) : Prop := ∃ p, 1 < p ∧ a = p * p * p

/-- Def. 7.21: similar plane numbers have proportional sides, `p ∶ q ∷ r ∶ s`. -/
def SimilarPlane (a b : ℕ) : Prop :=
  ∃ p q r s, 1 < p ∧ 1 < q ∧ 1 < r ∧ 1 < s ∧ a = p * q ∧ b = r * s ∧ p ∶ q ∷ r ∶ s

/-- Def. 7.21: similar solid numbers have proportional sides. -/
def SimilarSolid (a b : ℕ) : Prop :=
  ∃ p q r s t u, 1 < p ∧ 1 < q ∧ 1 < r ∧ 1 < s ∧ 1 < t ∧ 1 < u ∧
    a = p * q * r ∧ b = s * t * u ∧ p ∶ q ∷ s ∶ t ∧ q ∶ r ∷ t ∶ u

/-- Def. 7.22: a perfect number is equal to (the sum of) its own parts, the unit among
them. -/
def Perfect (a : ℕ) : Prop :=
  1 < a ∧ ((List.range a).filter (· ∣ a)).sum = a

end Elements.Book7
