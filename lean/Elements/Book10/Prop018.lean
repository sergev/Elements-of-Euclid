import Elements.Book10.Prop017

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

/--
If a rectangle equal to the fourth part of the square on the lesser `a` of two unequal
lines, falling short by a square, is applied to the greater `l`, cutting it into `x` and
`y`, then `x` and `y` are incommensurable in length exactly when the square on `l` exceeds
the square on `a` by the square on a line incommensurable in length with `l`. The same
construction as 10.17.
-/
theorem proposition_18 {a l h x y : Length} (hal : a < l) (hh : h + h = a)
    (hxy : x + y = l) (hr : rect x y = sq h) : ¬ Commensurable x y ↔ ExceedsIncomm l a :=
      by
  wlog hyx : y < x generalizing x y
  · rcases (not_lt.mp hyx).lt_or_eq with hlt | rfl
    · rw [show Commensurable x y ↔ Commensurable y x from ⟨.symm, .symm⟩]
      exact this (add_comm x y ▸ hxy) (rect_comm x y ▸ hr) hlt
    · exfalso
      have : sq l = sq a := by
        rw [← hxy, ← hh, sq_double, sq_double, ← hr, sq_eq_rect]
      exact absurd (sq_inj this) (ne_of_gt hal)
  -- by the same construction, the square on `l` exceeds the square on `a` by the square
  -- on `t + t`
  obtain ⟨t, hl, hsq⟩ := proposition_17_construction hh hxy hr hyx
  have hyy := double_commensurable y
  constructor
  · intro hc
    -- `l` is incommensurable with `y` [Prop. 10.16], `y + y` commensurable with `y`
    -- [Prop. 10.6]: so `l` is incommensurable with `y + y` [Prop. 10.13], and with the
    -- remainder `t + t` [Prop. 10.16]
    have h₁ : ¬ Commensurable l y := hxy ▸ (proposition_16.1 hc).2
    have h₂ : ¬ Commensurable (y + y) l :=
      proposition_13 Length.divisible hyy.symm (fun h => h₁ h.symm)
    rw [← hl] at h₂
    have h₃ := (proposition_16.1 (proposition_16.2 fun h => h₂ h.symm)).2
    rw [hl] at h₃
    exact ⟨t + t, hsq, fun h => h₃ h.symm⟩
  · rintro ⟨z, hz, hzl⟩
    -- `z` is `t + t`: `l` is incommensurable with `t + t`, and so with the remainder
    -- `y + y` [Prop. 10.16], and with `y` [Prop. 10.13]; so, via separation, `x` with `y`
    -- [Prop. 10.16]
    have hzt : z = t + t := sq_inj (add_left_cancel (hz.trans hsq.symm))
    subst hzt
    rw [← hl, add_comm (y + y)] at hzl
    have h₁ := (proposition_16.1 (proposition_16.2 fun h => hzl h.symm)).2
    rw [add_comm, hl] at h₁
    have h₂ : ¬ Commensurable y l := proposition_13 Length.divisible hyy (fun h => h₁
      h.symm)
    rw [← hxy, add_comm] at h₂
    exact fun h => (proposition_16.2 fun h' => h₂ h'.symm) h.symm

end Elements.Book10
