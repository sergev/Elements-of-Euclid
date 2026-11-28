import Elements.Book10.Prop080

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {ρ : Length}

/-- If two medial areas `S`, `A`, incommensurable, `A` the less, leave the same remainder
as two others `S'`, `A'` so, the first are the others: applied to a rational line, each
pair makes rational breadths commensurable in square only, and the remainders are the same
apotome; only one line can be attached to it [Prop. 10.79]. The argument of 10.81 and
10.84, the mirror of `medial_add_medial_eq`. -/
theorem medial_sub_medial_eq {S S' A A' : Area} (hS : MedialArea ρ S)
    (hS' : MedialArea ρ S') (hA : MedialArea ρ A) (hA' : MedialArea ρ A')
    (hi : ¬ Commensurable S A) (hi' : ¬ Commensurable S' A') (hlt : A < S)
      (hlt' : A' < S')
    (h : S + A' = S' + A) : S = S' := by
  obtain ⟨a, ha⟩ := Area.apply ρ S
  obtain ⟨b, hb⟩ := Area.apply ρ A
  obtain ⟨a', ha'⟩ := Area.apply ρ S'
  obtain ⟨b', hb'⟩ := Area.apply ρ A'
  obtain ⟨har, hbr, hab⟩ := medial_breadths hS hA hi ha hb
  obtain ⟨har', hbr', hab'⟩ := medial_breadths hS' hA' hi' ha' hb'
  have hba : b < a := rect_lt_rect.mp (by rw [ha, hb]; exact hlt)
  have hba' : b' < a' := rect_lt_rect.mp (by rw [ha', hb']; exact hlt')
  have he : a + b' = a' + b := rect_inj (by rw [rect_add, rect_add, ha, hb, ha', hb', h])
  -- the remainders are the same
  obtain ⟨c, hc⟩ := remainder b a hba
  obtain ⟨c', hc'⟩ := remainder b' a' hba'
  have hcc : c' = c := add_right_cancel (b := b + b') (calc
    c' + (b + b') = (b' + c') + b := by ac_rfl
    _ = a + b' := by rw [hc', he]
    _ = (b + c) + b' := by rw [hc]
    _ = c + (b + b') := by ac_rfl)
  subst hcc
  obtain ⟨rfl, -⟩ := proposition_79 ⟨har, hbr, hab, hba⟩ ⟨har', hbr', hab', hba'⟩
    ((add_comm c' b).trans hc) ((add_comm c' b').trans hc')
  exact ha.symm.trans ha'

/-- Only one medial line, commensurable in square only with the whole and containing a
medial area with it, can be attached to a second apotome of a medial. -/
theorem proposition_81 {l x y x' y' : Length} (h : SecondBimedialTerms ρ x y)
    (h' : SecondBimedialTerms ρ x' y') (hl : l + y = x) (hl' : l + y' = x') :
    x = x' ∧ y = y' := by
  obtain ⟨hx, -, hxy, hr, hyx⟩ := h
  obtain ⟨hx', -, hxy', hr', hyx'⟩ := h'
  -- the squares and twice the rectangles, medial and incommensurable, applied to a
  -- rational line, leave the same apotome as breadth [Props. 2.7, 10.22, 10.73, 10.79]
  have h₂ := medial_sub_medial_eq (proposition_23_corollary hx (proposition_15.1 hxy.1).1)
    (proposition_23_corollary hx' (proposition_15.1 hxy'.1).1) hr.twice hr'.twice
    hxy.squares_twice_rect hxy'.squares_twice_rect (twice_rect_lt_squares hyx)
    (twice_rect_lt_squares hyx') (squares_sub_eq hl hl')
  exact eq_of_squares_eq_sub hl hl' h₂

end Elements.Book10
