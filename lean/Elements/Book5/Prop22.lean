import Elements.Book5.Prop04
import Elements.Book5.Prop20

namespace Elements.Book5

variable {M N : Type*} [Magnitude M] [Magnitude N]

/--
Euclid's case, three magnitudes: if `A : B :: D : E` and `B : C :: E : F`, then via
equality `A : C :: D : F`.
-/
theorem proposition_22' {a b c : M} {d e f : N}
    (h₁ : Proportion a b d e) (h₂ : Proportion b c e f) : Proportion a c d f := by
  -- let `G`, `H` be equal multiples `m` of `A`, `D`, `K`, `L` others of `B`, `E`, and
  -- `M`, `N` others `n` of `C`, `F`
  have key : ∀ m n : ℕ+,
      (n • c < m • a → n • f < m • d) ∧ (m • a = n • c → m • d = n • f) ∧
        (m • a < n • c → m • d < n • f) := by
    intro m n
    -- `G : K :: H : L`, and `K : M :: L : N` [Prop. 5.4]; so via equality, if `G` exceeds
    -- `M`, `H` exceeds `N`; if equal, equal; if less, less [Prop. 5.20]
    exact proposition_20 (proposition_4 h₁ m 1) (proposition_4 h₂ 1 n)
  -- so `A : C :: D : F` [Def. 5.5]
  exact Proportion.of_imp (fun m n => (key m n).1) (fun m n => (key m n).2.1)
    (fun m n => (key m n).2.2)

/--
If there are any number of magnitudes `a 0`, …, `a (n + 1)`, and as many others
`b 0`, …, `b (n + 1)`, in the same ratio taken two by two, `a i : a (i + 1) ::
b i : b (i + 1)`, then they are in the same ratio via equality: the first to the last.
-/
theorem proposition_22 {n : ℕ} {a : Fin (n + 2) → M} {b : Fin (n + 2) → N}
    (h : ∀ i : Fin (n + 1),
      Proportion (a i.castSucc) (a i.succ) (b i.castSucc) (b i.succ)) :
    Proportion (a 0) (a (Fin.last _)) (b 0) (b (Fin.last _)) := by
  induction n with
  | zero => exact h 0
  | succ n ih =>
    -- all but the last, via equality, and then the last [Prop. 5.22, three magnitudes]
    have h₁ := ih (a := fun i => a i.castSucc) (b := fun i => b i.castSucc)
      fun i => h i.castSucc
    exact proposition_22' h₁ (h (Fin.last _))
