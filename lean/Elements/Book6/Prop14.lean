import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop14
import Elements.Book6.Prop01

namespace Elements.Book6

open Elements.Book5

/--
The figure of Prop. 6.14: parallelograms `adbf`, `becg` with the angles at `b` equal, and
`db`, `be` straight-on; then `fb`, `bg` are straight-on [Prop. 1.14]. Complete the
parallelogram `fbeh`: `AB : FE :: DB : BE` and `BC : FE :: GB : BF` [Prop. 6.1].
-/
theorem proposition_14_ratios : ∀ (a b c d e f g : Point) (AF DE AD FB CE BG CG : Line),
  formParallelogram a f d b AF DE AD FB ∧ formParallelogram c e g b CE BG CG DE ∧
  between d b e ∧ f.opposingSides g DE ∧ ∠ d:b:f = ∠ g:b:e →
  ∃ h : Point, (d─b) ∶ (b─e) ∷ □a:d:b:f ∶ □h:f:b:e ∧
  (g─b) ∶ (b─f) ∷ □c:g:b:e ∶ □h:f:b:e :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_13 g b e d BG DE)
  euclid_apply (Elements.Book1.proposition_14 d b f g DE FB BG)
  subst ‹FB = BG›
  euclid_apply (parallel_meets e AF DE CE)
  euclid_apply (intersection_lines AF CE) as h
  have h₁ := proposition_1' f d b e a h AF DE AD FB CE (by euclid_finish)
  have h₂ := proposition_1' e g b f c h CE FB CG DE AF (by euclid_finish)
  refine ⟨h, h₁, h₂.congr rfl rfl rfl ?_⟩
  rw [size_quadrilateral, size_quadrilateral, area_symm_2 h e b, area_symm_2 h b f,
    add_comm]

/--
In equal and equiangular parallelograms `adbf`, `becg`, the sides about the equal angles
at `b` are reciprocally proportional: `db : be :: gb : bf`. The parallelograms are laid
down as Euclid lays them, `db` straight-on to `be`.
-/
theorem proposition_14 : ∀ (a b c d e f g : Point) (AF DE AD FB CE BG CG : Line),
  formParallelogram a f d b AF DE AD FB ∧ formParallelogram c e g b CE BG CG DE ∧
  between d b e ∧ f.opposingSides g DE ∧ ∠ d:b:f = ∠ g:b:e ∧
  ▱ a:f:d:b = ▱ c:e:g:b → (d─b) ∶ (b─e) ∷ (g─b) ∶ (b─f) :=
by
  euclid_intros
  obtain ⟨h, h₁, h₂⟩ :=
    proposition_14_ratios a b c d e f g AF DE AD FB CE BG CG (by euclid_finish)
  -- `AB` is equal to `BC`, so `AB : FE :: BC : FE` [Prop. 5.7]; so `DB : BE :: GB : BF`
  -- [Props. 6.1, 5.11]
  have h₃ := Proportional.of_eq h₁.2.2.1 h₁.2.2.2.1 (q := □c:g:b:e) (by
    rw [size_quadrilateral, size_quadrilateral, area_symm_2 a b f, area_symm_2 c b e]
    linarith)
  exact (h₁.trans h₃).trans h₂.symm

/--
Equiangular parallelograms `adbf`, `becg` in which the sides about the equal angles are
reciprocally proportional, `db : be :: gb : bf`, are equal.
-/
theorem proposition_14' : ∀ (a b c d e f g : Point) (AF DE AD FB CE BG CG : Line),
  formParallelogram a f d b AF DE AD FB ∧ formParallelogram c e g b CE BG CG DE ∧
  between d b e ∧ f.opposingSides g DE ∧ ∠ d:b:f = ∠ g:b:e ∧
  (d─b) ∶ (b─e) ∷ (g─b) ∶ (b─f) → ▱ a:f:d:b = ▱ c:e:g:b :=
by
  euclid_intros
  obtain ⟨h, h₁, h₂⟩ :=
    proposition_14_ratios a b c d e f g AF DE AD FB CE BG CG (by euclid_finish)
  -- `AB : FE :: DB : BE :: GB : BF :: BC : FE` [Props. 6.1, 5.11], so `AB` is equal to
  -- `BC` [Prop. 5.9]
  have h₃ := (h₁.symm.trans ‹(d─b) ∶ (b─e) ∷ (g─b) ∶ (b─f)›).trans h₂
  have := h₃.eq_left rfl
  rw [size_quadrilateral, size_quadrilateral, area_symm_2 a b f,
    area_symm_2 c b e] at this
  linarith

end Elements.Book6
