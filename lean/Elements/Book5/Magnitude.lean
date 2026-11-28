import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic

/-
Magnitudes of one kind, their multiples, and Defs. 5.4, 5.5, 5.7.
-/

namespace Elements.Book5

/--
A kind of magnitude: lines, or areas, or angles. Magnitudes of one kind can be added and
compared (Def. 5.3), and the lesser can be taken away from the greater. None is zero: a
magnitude is less than its sum with another. Def. 5.4: magnitudes have a ratio to one
another when a multiple of each exceeds the other; those of one kind always do
(Archimedes). `(· + a)^[n] a` is `a` added to itself `n` times, `a` taken `n + 1` times.
-/
class Magnitude (M : Type*) extends AddCommSemigroup M, LinearOrder M where
  /-- A magnitude is less than its sum with another. -/
  lt_add : ∀ a b : M, a < a + b
  /-- The lesser taken away from the greater leaves a remainder. -/
  remainder : ∀ a b : M, a < b → ∃ c, a + c = b
  /-- Def. 5.4: some multiple of `a` exceeds `b`. -/
  ratio : ∀ a b : M, ∃ n : ℕ, b < (· + a)^[n] a

namespace Magnitude

variable {M : Type*} [Magnitude M]

/-- `n • a`, a multiple of `a`: `a` taken `n` times, `n ≥ 1` (Def. 5.2). -/
instance : SMul ℕ+ M := ⟨fun n a => (· + a)^[n.natPred] a⟩

theorem one_mult (a : M) : (1 : ℕ+) • a = a := rfl

/-- `a` taken `n + 1` times is `a` taken `n` times, and `a`. -/
theorem mult_succ (n : ℕ+) (a : M) : (n + 1) • a = n • a + a := by
  show (· + a)^[(n + 1).natPred] a = (· + a)^[n.natPred] a + a
  have : (n + 1).natPred = n.natPred + 1 := by
    rw [← Nat.natPred_succPNat (n.natPred + 1)]
    congr 1
    apply PNat.eq
    simp [PNat.natPred_add_one]
  rw [this, Function.iterate_succ_apply']

/-- Def. 5.4: a multiple of `a` exceeds `b`. -/
theorem archimedes (a b : M) : ∃ n : ℕ+, b < n • a := by
  obtain ⟨n, h⟩ := ratio a b
  refine ⟨n.succPNat, ?_⟩
  show b < (· + a)^[n.succPNat.natPred] a
  rwa [Nat.natPred_succPNat]

theorem lt_add' (a b : M) : b < a + b := add_comm b a ▸ lt_add b a

/-! The common notions for addition and order, which Euclid takes for granted. -/

theorem add_lt_add_right' {a b : M} (c : M) (h : a < b) : a + c < b + c := by
  obtain ⟨d, rfl⟩ := remainder a b h
  rw [add_right_comm]
  exact lt_add _ _

instance : AddRightStrictMono M := ⟨fun c _ _ h => add_lt_add_right' c h⟩

instance : AddLeftStrictMono M := ⟨fun c a b (h : a < b) => by
  show c + a < c + b
  rw [add_comm c a, add_comm c b]
  exact add_lt_add_right' c h⟩

instance : AddRightMono M := ⟨fun c a b (h : a ≤ b) => by
  show a + c ≤ b + c
  rcases h.lt_or_eq with h | rfl
  · exact (add_lt_add_right' c h).le
  · rfl⟩

instance : AddLeftMono M := ⟨fun c a b (h : a ≤ b) => by
  show c + a ≤ c + b
  rw [add_comm c a, add_comm c b]
  exact add_le_add_left h c⟩

theorem lt_of_add_lt_add_right' {a b c : M} (h : a + c < b + c) : a < b := by
  rcases lt_trichotomy a b with h' | rfl | h'
  · exact h'
  · exact absurd h (lt_irrefl _)
  · exact absurd (add_lt_add_right' c h') (lt_asymm h)

instance : AddRightReflectLT M := ⟨fun c _ _ h => lt_of_add_lt_add_right' (c := c) h⟩

instance : AddLeftReflectLT M := ⟨fun c a b (h : c + a < c + b) => by
  rw [add_comm c a, add_comm c b] at h
  exact lt_of_add_lt_add_right' h⟩

theorem add_right_cancel' {a b c : M} (h : a + c = b + c) : a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (ne_of_lt (add_lt_add_right' c h'))
  · exact h'
  · exact absurd h (ne_of_gt (add_lt_add_right' c h'))

instance : IsCancelAdd M where
  add_left_cancel c a b h := add_right_cancel' (by rwa [add_comm a c, add_comm b c])
  add_right_cancel _ _ _ h := add_right_cancel' h

/-! Multiples, as Euclid takes them for granted. -/

/-- Equal multiples of unequal magnitudes are unequal. -/
theorem mult_lt_mult (n : ℕ+) {a b : M} (h : a < b) : n • a < n • b := by
  induction n using PNat.recOn with
  | one => exact h
  | succ n ih => rw [mult_succ, mult_succ]; exact add_lt_add ih h

theorem mult_le_mult (n : ℕ+) {a b : M} (h : a ≤ b) : n • a ≤ n • b := by
  rcases h.lt_or_eq with h | rfl
  · exact (mult_lt_mult n h).le
  · rfl

/-- Equal multiples are of equal magnitudes. -/
theorem mult_inj (n : ℕ+) {a b : M} (h : n • a = n • b) : a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (ne_of_lt (mult_lt_mult n h'))
  · exact h'
  · exact absurd h (ne_of_gt (mult_lt_mult n h'))

/-- The greater multiple of a magnitude is greater. -/
theorem mult_lt_mult_left {m n : ℕ+} (a : M) (h : m < n) : m • a < n • a := by
  induction n using PNat.recOn with
  | one => exact absurd h (by simp)
  | succ n ih =>
    rw [mult_succ]
    rcases (PNat.lt_add_one_iff.mp h).lt_or_eq with h | rfl
    · exact lt_trans (ih h) (lt_add _ _)
    · exact lt_add _ _

theorem mult_le_mult_left {m n : ℕ+} (a : M) (h : m ≤ n) : m • a ≤ n • a := by
  rcases h.lt_or_eq with h | rfl
  · exact (mult_lt_mult_left a h).le
  · rfl

/-- The multiple which is greater is taken more times. -/
theorem lt_of_mult_lt_mult_left {m n : ℕ+} {a : M} (h : m • a < n • a) : m < n :=
  lt_of_not_ge fun h' => not_lt_of_ge (mult_le_mult_left a h') h

/-- A magnitude is equal multiples of itself only. -/
theorem mult_inj_left {m n : ℕ+} {a : M} (h : m • a = n • a) : m = n := by
  rcases lt_trichotomy m n with h' | h' | h'
  · exact absurd h (ne_of_lt (mult_lt_mult_left a h'))
  · exact h'
  · exact absurd h (ne_of_gt (mult_lt_mult_left a h'))

/-! Any number of magnitudes: `a 0`, `a 1`, …, `a n`, a function on `Fin (n + 1)`. -/

/-- All the magnitudes `a 0`, …, `a n`, added together. -/
def sum : {n : ℕ} → (Fin (n + 1) → M) → M
  | 0, a => a 0
  | n + 1, a => sum (fun i : Fin (n + 1) => a i.castSucc) + a (Fin.last (n + 1))

theorem sum_lt_sum {n : ℕ} {a b : Fin (n + 1) → M} (h : ∀ i, a i < b i) :
    sum a < sum b := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact add_lt_add (ih fun i => h _) (h _)

theorem sum_eq_sum {n : ℕ} {a b : Fin (n + 1) → M} (h : ∀ i, a i = b i) :
    sum a = sum b := by
  rw [funext h]

/-- `n + 1` magnitudes equal to `c` make `c` taken `n + 1` times. -/
theorem sum_const (n : ℕ) (c : M) : sum (fun _ : Fin (n + 1) => c) = n.succPNat • c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show sum (fun _ : Fin (n + 1) => c) + c = _
    rw [ih, ← mult_succ]
    rfl

end Magnitude

open Magnitude

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
Def. 5.5: `a` has the same ratio to `b` as `c` to `d` (`a : b :: c : d`) when equal
multiples `m • a`, `m • c` of the first and the third both exceed, are both equal to, or
are both less than, equal multiples `n • b`, `n • d` of the second and the fourth. `a`
and `b` are of one kind, `c` and `d` may be of another. Def. 5.6: such magnitudes are
proportional.
-/
structure Proportion (a b : M) (c d : N) : Prop where
  gt : ∀ m n : ℕ+, n • b < m • a ↔ n • d < m • c
  eq : ∀ m n : ℕ+, m • a = n • b ↔ m • c = n • d
  lt : ∀ m n : ℕ+, m • a < n • b ↔ m • c < n • d

/--
Def. 5.7: `a` has a greater ratio to `b` than `c` to `d` when, for some equal multiples,
the multiple of the first exceeds that of the second, and the multiple of the third does
not exceed that of the fourth.
-/
def GreaterRatio (a b : M) (c d : N) : Prop :=
  ∃ m n : ℕ+, n • b < m • a ∧ ¬ n • d < m • c

/--
Def. 5.9: when three magnitudes `a`, `b`, `e` are proportional, `a : b :: b : e`, the
first has to the third the squared ratio of that it has to the second. `SquaredRatio c d
a b`: `c : d` is the squared ratio of `a : b`, the same ratio as `a : e` for such an `e`.
Book 5 does not use it; Book 6 is its first user (Props. 6.19, 6.20, 6.22).
-/
def SquaredRatio (c d : N) (a b : M) : Prop :=
  ∃ e : M, Proportion a b b e ∧ Proportion c d a e

namespace Proportion

variable {a b : M} {c d : N}

/--
Def. 5.5 in one direction: if the multiples of the first and the third exceed together,
are equal together and are less together, then also conversely, since of two magnitudes
one exceeds, or they are equal, or the other exceeds.
-/
theorem of_imp
    (gt : ∀ m n : ℕ+, n • b < m • a → n • d < m • c)
    (eq : ∀ m n : ℕ+, m • a = n • b → m • c = n • d)
    (lt : ∀ m n : ℕ+, m • a < n • b → m • c < n • d) : Proportion a b c d where
  gt m n := ⟨gt m n, fun h => by
    rcases lt_trichotomy (n • b) (m • a) with h' | h' | h'
    · exact h'
    · exact absurd (eq m n h'.symm) (ne_of_gt h)
    · exact absurd (lt m n h') (lt_asymm h)⟩
  eq m n := ⟨eq m n, fun h => by
    rcases lt_trichotomy (m • a) (n • b) with h' | h' | h'
    · exact absurd h (ne_of_lt (lt m n h'))
    · exact h'
    · exact absurd h (ne_of_gt (gt m n h'))⟩
  lt m n := ⟨lt m n, fun h => by
    rcases lt_trichotomy (m • a) (n • b) with h' | h' | h'
    · exact h'
    · exact absurd (eq m n h') (ne_of_lt h)
    · exact absurd (gt m n h') (lt_asymm h)⟩

/-- Def. 5.5 reads the same from either pair. -/
theorem symm (h : Proportion a b c d) : Proportion c d a b where
  gt m n := (h.gt m n).symm
  eq m n := (h.eq m n).symm
  lt m n := (h.lt m n).symm

theorem refl (a b : M) : Proportion a b a b :=
  ⟨fun _ _ => .rfl, fun _ _ => .rfl, fun _ _ => .rfl⟩

/-- The same ratio is not a greater one (Defs. 5.5, 5.7). -/
theorem not_greaterRatio (h : Proportion a b c d) : ¬ GreaterRatio a b c d := by
  rintro ⟨m, n, h₁, h₂⟩
  exact h₂ ((h.gt m n).mp h₁)

end Proportion

end Elements.Book5
