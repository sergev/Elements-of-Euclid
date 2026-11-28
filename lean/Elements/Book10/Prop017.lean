import Elements.Book10.Prop016

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

/-- A magnitude and its double are commensurable [Prop. 10.6]: they are as `2` to the
unit. -/
theorem double_commensurable {M : Type*} [Magnitude M] (a : M) :
    Commensurable (a + a) a := by
  have h := proportion_parts 2 1 a
  rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult] at h
  exact proposition_6 h ⟨a, by rw [mult_succ, one_mult]⟩

/--
To apply to the greater `l` of two unequal lines a rectangle equal to the fourth part of
the square on the lesser `a`, that is, the square on its half `h`, falling short by a
square [Prop. 6.28]: it cuts `l` into `x` and `y`, contained by the rectangle [Prop. 10.16
lemma]. For 10.17, 10.18 and their users.
-/
theorem exists_application {a l : Length} (hal : a < l) :
    ∃ h x y : Length, h + h = a ∧ x + y = l ∧ rect x y = sq h := by
  obtain ⟨h, hh⟩ := Length.part a 2
  obtain ⟨e, he⟩ := Length.part l 2
  rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult] at hh he
  have hlt : h < e := by
    by_contra hge
    exact absurd (hh ▸ he ▸ add_le_add (not_lt.mp hge) (not_lt.mp hge)) (not_le.mpr hal)
  obtain ⟨x, y, hxy, hr⟩ := Area.apply_short he.symm (sq_lt_sq.mpr hlt).le
  exact ⟨h, x, y, hh.symm, hxy, hr⟩

/--
The construction of 10.17 and 10.18. `l` is cut in half at `e` [Prop. 1.10], and
unequally into `x` and `y`, the lesser `y`; `e + t = x`. Laying off `t` again from the
half, `y` is left, and `l` is `y + y` and `t + t`, the line `D F`. And the square on `l`
exceeds the square on `a` by the square on `D F`.
-/
theorem proposition_17_construction {a l h x y : Length} (hh : h + h = a) (hxy : x + y =
    l)
    (hr : rect x y = sq h) (hyx : y < x) :
    ∃ t, (y + y) + (t + t) = l ∧ sq a + sq (t + t) = sq l := by
  -- let `l` be cut in half at `e` [Prop. 1.10]
  obtain ⟨e, he⟩ := Length.part l 2
  rw [show (2 : ℕ+) = 1 + 1 from rfl, mult_succ, one_mult] at he
  -- `x` is greater than the half: `e + t = x`; and `y + t = e`
  have hex : e < x := by
    by_contra hxe
    have : x + y < e + e := add_lt_add_of_le_of_lt (not_lt.mp hxe) (lt_of_lt_of_le hyx
      (not_lt.mp hxe))
    exact absurd (hxy.trans he) (ne_of_lt this)
  obtain ⟨t, ht⟩ := remainder e x hex
  have hyt : y + t = e := by
    apply add_right_cancel (b := e)
    rw [add_assoc, add_comm t e, ht, add_comm, hxy, he]
  refine ⟨t, ?_, ?_⟩
  · rw [he, ← hyt]
    ac_rfl
  · -- the rectangle contained by `x` and `y`, with the square on `t`, is the square on
    -- `e` [Prop. 2.5], and so the quadruples [Prop. 5.1]: the square on `a` is four times
    -- the rectangle, the square on `t + t` four times the square on `t`, and the square
    -- on `l` four times the square on `e`
    have h25 := rect_add_sq ht hyt
    rw [← hh, sq_double, sq_double, he, sq_double, ← hr, ← h25,
      Elements.Book5.proposition_1']

/--
If a rectangle equal to the fourth part of the square on the lesser `a` of two unequal
lines, falling short by a square, is applied to the greater `l`, cutting it into `x` and
`y`, then `x` and `y` are commensurable in length exactly when the square on `l` exceeds
the square on `a` by the square on a line commensurable in length with `l`.
-/
theorem proposition_17 {a l h x y : Length} (hal : a < l) (hh : h + h = a)
    (hxy : x + y = l) (hr : rect x y = sq h) : Commensurable x y ↔ ExceedsComm l a := by
  wlog hyx : y < x generalizing x y
  · rcases (not_lt.mp hyx).lt_or_eq with hlt | rfl
    · rw [show Commensurable x y ↔ Commensurable y x from ⟨.symm, .symm⟩]
      exact this (add_comm x y ▸ hxy) (rect_comm x y ▸ hr) hlt
    · -- equal pieces would make `a` equal to `l`
      exfalso
      have : sq l = sq a := by
        rw [← hxy, ← hh, sq_double, sq_double, ← hr, sq_eq_rect]
      exact absurd (sq_inj this) (ne_of_gt hal)
  obtain ⟨t, hl, hsq⟩ := proposition_17_construction hh hxy hr hyx
  have hyy := double_commensurable y
  constructor
  · intro hc
    -- `l` is commensurable with `y` [Prop. 10.15], and `y + y` with `y` [Prop. 10.6]; so
    -- `l` with `y + y` [Prop. 10.12], and with the remainder `t + t` [Prop. 10.15]
    have h₁ : Commensurable l y := hxy ▸ (proposition_15.1 hc).2
    have h₂ := proposition_12 Length.divisible h₁ hyy
    rw [← hl] at h₂
    have h₃ := (proposition_15.1 (proposition_15.2 h₂)).2
    rw [hl] at h₃
    exact ⟨t + t, hsq, h₃.symm⟩
  · rintro ⟨z, hz, hzl⟩
    -- the square on `l` exceeds the square on `a` by the square on `t + t`, so `z` is
    -- `t + t`: `l` is commensurable with `t + t`, and so with the remainder `y + y`
    -- [Prop. 10.15], and with `y` [Prop. 10.12]; so, via separation, `x` with `y`
    -- [Prop. 10.15]
    have hzt : z = t + t := sq_inj (add_left_cancel (hz.trans hsq.symm))
    subst hzt
    rw [← hl, add_comm (y + y)] at hzl
    have h₁ := (proposition_15.1 (proposition_15.2 hzl.symm)).2
    rw [add_comm, hl] at h₁
    have h₂ := proposition_12 Length.divisible h₁ hyy.symm
    rw [← hxy, add_comm] at h₂
    exact (proposition_15.2 h₂).symm

end Elements.Book10
