import Elements.Book8.Prop01

namespace Elements.Book8

open Elements.Book7

/--
The numbers Euclid finds in 8.2, in the ratio of `a` to `b`, `n + 1` of them: from `n`
of them, `a` multiplying each makes the first `n`, and `b` multiplying the last makes the
last (`A` multiplying `C`, `D`, `E` makes `F`, `G`, `H`, and `B` multiplying `E` makes
`K`). The count starts from the unit, alone: one step makes `a`, `b`.
-/
def powers (a b : ℕ) : (n : ℕ) → Fin (n + 1) → ℕ
  | 0 => fun _ => 1
  | n + 1 => fun i => Fin.lastCases (powers a b n (Fin.last n) * b)
      (fun j => powers a b n j * a) i

theorem powers_castSucc (a b n : ℕ) (i : Fin (n + 1)) :
    powers a b (n + 1) i.castSucc = powers a b n i * a := by
  simp only [powers, Fin.lastCases_castSucc]

theorem powers_last (a b n : ℕ) :
    powers a b (n + 1) (Fin.last (n + 1)) = powers a b n (Fin.last n) * b := by
  simp only [powers, Fin.lastCases_last]

theorem powers_zero (a b n : ℕ) : powers a b (n + 1) 0 = powers a b n 0 * a :=
  powers_castSucc a b n 0

theorem powers_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) (i : Fin (n + 1)) :
    0 < powers a b n i := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [powers_last]; exact Nat.mul_pos (ih _) hb
    | cast i => rw [powers_castSucc]; exact Nat.mul_pos (ih _) ha

/-- The numbers are continuously proportional in the ratio of `a` to `b`: each is to the
next as `a` to `b`, by 7.17 (`a` multiplying both) or 7.18 (`a`, `b` multiplying the
last). -/
theorem powers_continuedIn {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ContinuedIn (powers a b n) a b := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    intro i
    induction i using Fin.lastCases with
    | last =>
      -- `a`, `b` multiplying the last make the last two: as `a` is to `b`, so are they
      -- [Prop. 7.18]
      rw [Fin.succ_last, powers_last]
      erw [powers_castSucc]
      exact (Elements.Book7.proposition_18 ha hb (powers_pos ha hb n _)).symm
    | cast i =>
      -- `a` multiplying two of them makes two in the same ratio [Prop. 7.17], which is
      -- that of `a` to `b`
      rw [Fin.succ_castSucc, powers_castSucc, powers_castSucc]
      exact proportion_trans (Nat.mul_pos (powers_pos ha hb n _) ha)
        (Nat.mul_pos (powers_pos ha hb n _) ha) (powers_pos ha hb n _)
        (powers_pos ha hb n _)
        (Elements.Book7.proposition_17 ha (powers_pos ha hb n _)
          (powers_pos ha hb n _)).symm (ih i)

/--
If `a`, `b` are prime to one another, so are the outermost of the numbers. Euclid cites
7.27, for squares and cubes; for any multitude it is 7.24 and 7.26, once for each step:
the first is prime to `b`, `a` to the last, and the first to the last.
-/
theorem powers_primeTo {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : PrimeTo a b) (n : ℕ) :
    PrimeTo (powers a b n 0) (powers a b n (Fin.last n)) := by
  have hp := powers_pos ha hb
  suffices PrimeTo (powers a b n 0) (powers a b n (Fin.last n)) ∧
      PrimeTo (powers a b n 0) b ∧ PrimeTo a (powers a b n (Fin.last n)) from this.1
  induction n with
  | zero =>
    have h1 : ∀ c, PrimeTo 1 c := fun c d hd _ => Nat.dvd_one.mp hd
    exact ⟨h1 1, h1 b, (h1 a).symm⟩
  | succ n ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    rw [powers_zero, powers_last]
    refine ⟨Elements.Book7.proposition_26 ha (hp n 0) hb (hp n _) h h₂ h₃ h₁,
      (Elements.Book7.proposition_24 ha (hp n 0) hb h h₂).symm,
      Elements.Book7.proposition_24 hb (hp n _) ha h.symm h₃.symm⟩

/--
To find the least numbers, as many as may be prescribed, continuously proportional in a
given ratio, of `a` to `b` in least numbers: `powers a b n`, `n + 1` of them. Euclid finds
three and four; the construction is the same for any multitude, one step at a time.
-/
theorem proposition_2 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : Least a b) (n : ℕ) :
    (∀ i, 0 < powers a b n i) ∧ ContinuedIn (powers a b n) a b ∧
      LeastSeq (powers a b n) := by
  -- `a`, `b` are the least, so prime to one another [Prop. 7.22]; so are the outermost
  -- [Prop. 7.27], and the numbers are the least [Prop. 8.1]
  have hp := Elements.Book7.proposition_22 ha hb h
  exact ⟨powers_pos ha hb n, powers_continuedIn ha hb n,
    proposition_1 (powers_pos ha hb n) (powers_primeTo ha hb hp n)⟩

/-- Any least numbers `c` continuously proportional are Euclid's numbers, in the least
numbers of the ratio of the first to the second [Props. 7.33, 8.2]. -/
theorem eq_powers {n : ℕ} {c : Fin (n + 1) → ℕ} (hc : ∀ i, 0 < c i) (hcon : Continued c)
    (hl : LeastSeq c) :
    ∃ a b, 0 < a ∧ 0 < b ∧ Least a b ∧ c = powers a b n := by
  obtain ⟨a, b, ha, hb, hab, hlab⟩ := Elements.Book7.proposition_33' (hc 0) (hc 1)
  obtain ⟨hp, hcin, hlp⟩ := proposition_2 ha hb hlab n
  have hcab : ContinuedIn c a b :=
    fun i => proportion_trans (hc _) (hc _) (hc 0) (hc 1) (hcon i) hab.symm
  exact ⟨a, b, ha, hb, hlab, LeastSeq.eq hp hc hlp hl (hcin.sameRatios ha hb hc hcab)⟩

/--
So it is clear that if three continuously proportional numbers are the least of those
having the same ratio as them, the outermost of them are squares, and, if four, cubes:
of the least numbers in their ratio. They may be squares of the unit (`1`, `2`, `4`).
-/
theorem proposition_2_corollary :
    (∀ c : Fin 3 → ℕ, (∀ i, 0 < c i) → Continued c → LeastSeq c →
      ∃ p q, c 0 = p * p ∧ c 2 = q * q) ∧
    (∀ c : Fin 4 → ℕ, (∀ i, 0 < c i) → Continued c → LeastSeq c →
      ∃ p q, c 0 = p * p * p ∧ c 3 = q * q * q) := by
  constructor
  · intro c hc hcon hl
    obtain ⟨a, b, -, -, -, rfl⟩ := eq_powers hc hcon hl
    exact ⟨a, b, by show 1 * a * a = _; rw [Nat.one_mul],
      by show 1 * b * b = _; rw [Nat.one_mul]⟩
  · intro c hc hcon hl
    obtain ⟨a, b, -, -, -, rfl⟩ := eq_powers hc hcon hl
    exact ⟨a, b, by show 1 * a * a * a = _; rw [Nat.one_mul],
      by show 1 * b * b * b = _; rw [Nat.one_mul]⟩

end Elements.Book8
