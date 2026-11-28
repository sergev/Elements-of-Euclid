import Elements.Book10.Prop002

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {M : Type*} [Magnitude M]

/-- `g` is the greatest common measure of `a` and `b`: it measures both, and no greater
magnitude measures both. -/
def GreatestCommonMeasure (g a b : M) : Prop :=
  Measures g a ∧ Measures g b ∧ ∀ e, Measures e a → Measures e b → e ≤ g

open Classical in
/--
The process of 10.3, the pair `(x, y)` at each stage: the lesser `y` is taken from the
greater `x` as often as it can be, and the pair becomes `y` and the remainder; when `y`
measures `x`, the process stops, and the pair stays.
-/
noncomputable def process (a b : M) : ℕ → M × M
  | 0 => (a, b)
  | n + 1 =>
    let p := process a b n
    if h : p.2 < p.1 ∧ ¬ Measures p.2 p.1 then
      (p.2, Classical.choose (exists_leaves h.1 h.2))
    else p

/-- The process of 10.3 has not stopped at stage `n`. -/
def Going (a b : M) (n : ℕ) : Prop :=
  (process a b n).2 < (process a b n).1 ∧ ¬ Measures (process a b n).2 (process a b n).1

theorem process_succ {a b : M} {n : ℕ} (h : Going a b n) :
    (process a b (n + 1)).1 = (process a b n).2 ∧
      Leaves (process a b n).1 (process a b n).2 (process a b (n + 1)).2 := by
  have e : process a b (n + 1) =
      (((process a b n).2, Classical.choose (exists_leaves h.1 h.2)) : M × M) := by
    simp only [process]
    exact dite_eq_left_of_eq_true (eq_true h)
  rw [e]
  exact ⟨rfl, Classical.choose_spec (exists_leaves h.1 h.2)⟩

/--
The greatest common measure of `a` and `b`, with the corollary's property: whatever
measures `a` and `b` measures it.
-/
theorem exists_greatestCommonMeasure {a b : M} (h : Commensurable a b) :
    ∃ g, GreatestCommonMeasure g a b ∧
      ∀ e, Measures e a → Measures e b → Measures e g := by
  classical
  -- of `a` and `b`, let `b` be the lesser
  wlog hab : b < a generalizing a b
  · rcases (not_lt.mp hab).lt_or_eq with hlt | rfl
    · obtain ⟨g, ⟨h₁, h₂, h₃⟩, h₄⟩ := this h.symm hlt
      exact ⟨g, ⟨h₂, h₁, fun e he₁ he₂ => h₃ e he₂ he₁⟩, fun e he₁ he₂ => h₄ e he₂ he₁⟩
    · -- `a` measures itself: it is the greatest common measure
      exact ⟨a, ⟨.refl a, .refl a, fun e he _ => he.le⟩, fun e he _ => he⟩
  -- continually taking the lesser from the greater, the remainder will sometime measure
  -- the magnitude before it, since `a` and `b` are not incommensurable [Prop. 10.2]
  have hstop : ∃ n, ¬ Going a b n := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hr : NeverMeasures (fun n => (process a b n).1) := by
      intro n
      have h₁ := process_succ (hall n)
      have h₂ := process_succ (hall (n + 1))
      show Leaves (process a b n).1 (process a b (n + 1)).1 (process a b (n + 2)).1
      rw [h₂.1, h₁.1]
      exact h₁.2
    have h₂ := proposition_2 hr
    rw [show (process a b 1).1 = b from (process_succ (hall 0)).1] at h₂
    exact h₂ h
  let N := Nat.find hstop
  have hgo : ∀ k < N, Going a b k := fun k hk => not_not.mp (Nat.find_min hstop hk)
  -- at each stage before the last, the lesser is less
  have hlt : ∀ k ≤ N, (process a b k).2 < (process a b k).1 := by
    intro k hk
    induction k with
    | zero => exact hab
    | succ k ih =>
      obtain ⟨h₁, ⟨_, _, hc⟩⟩ := process_succ (hgo k (by omega))
      rw [h₁]
      exact hc
  -- at stage `N` the lesser measures the greater
  have hN : Measures (process a b N).2 (process a b N).1 := by
    by_contra hn
    exact Nat.find_spec hstop ⟨hlt N le_rfl, hn⟩
  set g := (process a b N).2
  -- `g` measures both magnitudes at every stage, back to `a` and `b`
  have hg : ∀ d k, k + d = N →
      Measures g (process a b k).1 ∧ Measures g (process a b k).2 := by
    intro d
    induction d with
    | zero => intro k hk; subst hk; exact ⟨hN, .refl _⟩
    | succ d ih =>
      intro k hk
      obtain ⟨h₁, ⟨m, hm, -⟩⟩ := process_succ (hgo k (by omega))
      obtain ⟨ih₁, ih₂⟩ := ih (k + 1) (by omega)
      rw [h₁] at ih₁
      refine ⟨?_, ih₁⟩
      rw [hm]
      exact (ih₁.mult m).add ih₂
  -- whatever measures `a` and `b` measures both at every stage, and so `g`
  have he : ∀ e, Measures e a → Measures e b → ∀ k ≤ N,
      Measures e (process a b k).1 ∧ Measures e (process a b k).2 := by
    intro e ha hb k hk
    induction k with
    | zero => exact ⟨ha, hb⟩
    | succ k ih =>
      obtain ⟨h₁, ⟨m, hm, -⟩⟩ := process_succ (hgo k (by omega))
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      rw [h₁]
      exact ⟨ih₂, (hm ▸ ih₁).sub (ih₂.mult m)⟩
  have hg₀ := hg N 0 (by omega)
  refine ⟨g, ⟨hg₀.1, hg₀.2, fun e ha hb => (he e ha hb N le_rfl).2.le⟩,
    fun e ha hb => (he e ha hb N le_rfl).2⟩

/-- To find the greatest common measure of two given commensurable magnitudes. -/
theorem proposition_3 {a b : M} (h : Commensurable a b) :
    ∃ g, GreatestCommonMeasure g a b :=
  (exists_greatestCommonMeasure h).imp fun _ h => h.1

/-- 10.3, corollary: if a magnitude measures two magnitudes, it measures their greatest
common measure. -/
theorem proposition_3_corollary {a b g e : M} (hg : GreatestCommonMeasure g a b)
    (ha : Measures e a) (hb : Measures e b) : Measures e g := by
  obtain ⟨g', hg', h'⟩ := exists_greatestCommonMeasure ⟨g, hg.1, hg.2.1⟩
  -- the greatest common measure is one only
  have : g = g' := le_antisymm (hg'.2.2 g hg.1 hg.2.1) (hg.2.2 g' hg'.1 hg'.2.1)
  exact this ▸ h' e ha hb

end Elements.Book10
