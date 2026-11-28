import Elements.Book10.Prop025

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- A medial area does not exceed a medial area by a rational area. -/
theorem proposition_26 {A B C : Area} (hA : MedialArea ρ A) (hB : MedialArea ρ B)
    (h : B + C = A) : ¬ RationalArea ρ C := by
  intro hC
  -- let the rational line `ρ` be laid down, and `A` applied to it, making `e` as breadth,
  -- and `B` cut off, making `g` [Prop. 1.44]; the remainder `k` makes `C`
  obtain ⟨e, he⟩ := Area.apply ρ A
  obtain ⟨g, hg⟩ := Area.apply ρ B
  have hge : g < e := rect_lt_rect.mp (by rw [he, hg, ← h]; exact lt_add _ _)
  obtain ⟨k, hk⟩ := remainder g e hge
  have hkC : rect ρ k = C := by
    apply add_left_cancel (a := B)
    rw [h, ← hg, ← rect_add, hk, he]
  -- `e` and `g` are rational, and incommensurable in length with `ρ` [Prop. 10.22]
  obtain ⟨her, -⟩ := proposition_22' hA (Rational.self ρ) he
  obtain ⟨hgr, hgρ⟩ := proposition_22' hB (Rational.self ρ) hg
  -- `C` is rational, applied to `ρ`: `k` is rational, and commensurable with `ρ` [Prop.
  -- 10.20]
  obtain ⟨hkr, hkρ⟩ := proposition_20 (Rational.self ρ) hC hkC
  -- so `g` is incommensurable in length with `k` [Prop. 10.13]
  have h₁ : ¬ Commensurable g k :=
    fun hc => proposition_13 Length.divisible hkρ.symm (fun h' => hgρ h'.symm) hc.symm
  -- as `g` is to `k`, so the square on `g` to the rectangle: they are incommensurable
  -- [Props. 10.21 lemma, 10.11]
  have h₂ := (proposition_11 (proposition_21_lemma g k).1 Length.divisible
    Area.divisible).2 h₁
  -- the squares on `g` and `k` are commensurable with the square on `g`, both rational
  -- [Prop. 10.15]; twice the rectangle with the rectangle [Prop. 10.6]
  have h₃ := (proposition_15.1 (hgr.sq_rational.comm hkr.sq_rational)).1
  have h₄ : Commensurable ((2 : ℕ+) • rect g k) (rect g k) := by
    rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult]
    exact double_commensurable _
  -- so the squares are incommensurable with twice the rectangle [Prop. 10.13]
  have h₅ := proposition_13 Area.divisible h₃.symm h₂
  have h₆ := proposition_13 Area.divisible h₄.symm (fun h' => h₅ h'.symm)
  -- and so the squares with twice the rectangle, the square on `e` [Prop. 2.4], with the
  -- squares [Prop. 10.16]
  have h₇ := (proposition_16.1 (fun h' => h₆ h'.symm)).1
  rw [← sq_add, hk] at h₇
  -- the squares are rational: so the square on `e` is irrational, and `e` [Def. 10.4];
  -- but it is rational, which is impossible
  have h₈ := (hgr.sq_rational.of_comm h₃).not_of_not_comm (fun h' => h₇ h'.symm)
  exact h₈ her.sq_rational

end Elements.Book10
