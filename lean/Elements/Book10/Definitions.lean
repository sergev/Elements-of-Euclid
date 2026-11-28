import Elements.Book5.Plane
import Elements.Book7.Definitions

/-
Defs. 10.1–10.4, and the medial line of Prop. 10.21: commensurable, commensurable in
square, rational and irrational, relative to an assigned line `ρ`. Also numbers as a kind
of magnitude, for "the ratio which a number has to a number" (10.5–10.9), and the square
and the rectangle as areas.
-/

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {M : Type*} [Magnitude M]

/-- `c` measures `a`: `a` is `c` taken some number of times, `a = n • c`, `n ≥ 1`. -/
def Measures (c a : M) : Prop := ∃ n : ℕ+, a = n • c

/--
Def. 10.1: magnitudes are commensurable when the same measure measures both, and
incommensurable (`¬ Commensurable a b`) when no magnitude is a common measure of them.
-/
def Commensurable (a b : M) : Prop := ∃ c, Measures c a ∧ Measures c b

/-! Numbers as a kind of magnitude. -/

/--
A number, a multitude of units, as a magnitude of its own kind (10.5–10.9: "the ratio
which a number has to a number" is Book 5's `Proportion` between magnitudes and numbers).
It is `ℕ+` in a wrapper, `(m : Number)`, so that `n • a` is Book 5's multiple, not
Mathlib's product. Here the unit is a number too: Euclid takes it so in 10.5 (`C` is to
`A` as the unit to `D`).
-/
structure Number where
  /-- The number `n : ℕ+` as a magnitude. -/
  ofPNat ::
  /-- The number as an element of `ℕ+`. -/
  toPNat : ℕ+

namespace Number

attribute [coe] ofPNat

instance : Coe ℕ+ Number := ⟨ofPNat⟩

theorem toPNat_injective : Function.Injective toPNat := fun a b h => by
  cases a; cases b; cases h; rfl

instance : Add Number := ⟨fun a b => ofPNat (a.toPNat + b.toPNat)⟩

instance : AddCommSemigroup Number where
  add_assoc a b c := congrArg ofPNat (add_assoc a.toPNat b.toPNat c.toPNat)
  add_comm a b := congrArg ofPNat (add_comm a.toPNat b.toPNat)

instance : LinearOrder Number := LinearOrder.lift' toPNat toPNat_injective

/-- Def. 7.15: a number multiplying a number. -/
instance : Mul Number := ⟨fun a b => ofPNat (a.toPNat * b.toPNat)⟩

/-- The number of `n` units. -/
def of (n : ℕ) (h : 0 < n) : Number := ofPNat ⟨n, h⟩

/-- The units in a number. -/
def val (n : Number) : ℕ := n.toPNat

/-- The unit. -/
def unit : Number := ofPNat 1

@[simp] theorem val_coe (n : ℕ+) : val n = n := rfl

theorem val_add (a b : Number) : val (a + b) = val a + val b := PNat.add_coe _ _

theorem val_mul (a b : Number) : val (a * b) = val a * val b := PNat.mul_coe _ _

theorem val_pos (a : Number) : 0 < val a := PNat.pos _

theorem val_lt {a b : Number} : val a < val b ↔ a < b := PNat.coe_lt_coe _ _

theorem val_le {a b : Number} : val a ≤ val b ↔ a ≤ b := PNat.coe_le_coe _ _

theorem ext {a b : Number} (h : val a = val b) : a = b := toPNat_injective (PNat.eq h)

theorem val_inj {a b : Number} : val a = val b ↔ a = b := ⟨ext, congrArg val⟩

@[simp] theorem val_of (n : ℕ) (h : 0 < n) : val (of n h) = n := rfl

@[simp] theorem of_val (a : Number) : of (val a) (val_pos a) = a := rfl

theorem iter_val (a : Number) (n : ℕ) : val ((· + a)^[n] a) = (n + 1) * val a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', val_add, ih, Nat.succ_mul (n + 1)]

/-- Numbers are a kind of magnitude: they can be added and compared, the lesser taken
from the greater, and a multiple of one exceeds the other. -/
instance : Magnitude Number where
  lt_add a b := val_lt.mp (by rw [val_add]; have := val_pos b; omega)
  remainder a b h := ⟨of (val b - val a) (by have := val_lt.mpr h; omega), ext (by
    rw [val_add, val_of]; have := val_lt.mpr h; omega)⟩
  ratio a b := ⟨val b, val_lt.mp (by
    rw [iter_val]; have := val_pos a; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_mul_of_pos_right _ this))⟩

/-- A multiple of a number: `m • n` has `m * n` units (Def. 7.15). -/
theorem mult_val (m : ℕ+) (n : Number) : val (m • n) = m * val n := by
  show val ((· + n)^[m.natPred] n) = _
  rw [iter_val, PNat.natPred_add_one]

/-- `m` times the unit is the number `m`. -/
theorem mult_unit (m : ℕ+) : m • unit = m := ext (by rw [mult_val]; exact Nat.mul_one _)

end Number

/-! Lines and areas: positive reals (`Elements/Book5/Plane.lean`). -/

/-- The square on the line `a`, an area: the product of its length with itself. -/
def sq (a : Length) : Area := ⟨a.1 * a.1, mul_pos a.2 a.2⟩

/-- The rectangle contained by the lines `a` and `b`, an area: the product of the
lengths, as in Book 2. -/
def rect (a b : Length) : Area := ⟨a.1 * b.1, mul_pos a.2 b.2⟩

/--
Def. 10.2: lines are commensurable in square when the squares on them are commensurable
(measured by the same area), and incommensurable in square when not.
-/
def CommensurableInSquare (a b : Length) : Prop := Commensurable (sq a) (sq b)

/-- Lines commensurable in square only: in square, but not in length. -/
def InSquareOnly (a b : Length) : Prop :=
  CommensurableInSquare a b ∧ ¬ Commensurable a b

/--
Def. 10.3: given an assigned line `ρ`, a line is rational when it is commensurable with
`ρ`, in length and in square, or in square only; else irrational (`¬ Rational ρ x`).
Commensurable in length implies in square (10.9's corollary), so the second case covers
the first; the definition keeps Euclid's two.
-/
def Rational (ρ x : Length) : Prop := Commensurable x ρ ∨ CommensurableInSquare x ρ

/--
Def. 10.4: the square on `ρ` is rational, and so are areas commensurable with it; the
others are irrational (`¬ RationalArea ρ A`), and so are their square roots, the lines on
which squares equal to them are described.
-/
def RationalArea (ρ : Length) (A : Area) : Prop := Commensurable A (sq ρ)

/--
A medial area (10.21): the rectangle contained by rational lines commensurable in square
only. 10.21 proves it irrational.
-/
def MedialArea (ρ : Length) (A : Area) : Prop :=
  ∃ x y, Rational ρ x ∧ Rational ρ y ∧ InSquareOnly x y ∧ A = rect x y

/-- A medial line (10.21): the square root of a medial area, a line whose square is
medial. 10.21 proves it irrational. -/
def Medial (ρ x : Length) : Prop := MedialArea ρ (sq x)

end Elements.Book10
