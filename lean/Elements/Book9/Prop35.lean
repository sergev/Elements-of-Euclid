import Elements.Book9.Prop34

namespace Elements.Book9

open Elements.Book7 Elements.Book8

/--
If any multitude of numbers `a 0`, …, `a (n + 1)` are continuously proportional, and the
first is taken from the second and the last, then as the excess of the second is to the
first, so the excess of the last is to all those before it. The numbers begin from the
least, so the excesses are numbers.
-/
theorem proposition_35 {n : ℕ} {a : Fin (n + 2) → ℕ} (ha : ∀ i, 0 < a i)
    (hcon : Continued a) (hlt : a 0 < a 1) :
    a 1 - a 0 ∶ a 0 ∷
      a (Fin.last (n + 1)) - a 0 ∶ sum (fun i : Fin (n + 1) => a i.castSucc) := by
  -- each is less than the next [Prop. 5.13]
  have hinc : ∀ i : Fin (n + 1), a i.castSucc < a i.succ := fun i =>
    lt_of_proportion (ha 1) (ha 0) (ha _) (hcon i).symm.inv hlt
  -- by separation, as the excess of each over the one before is to that one, so the
  -- excess of the second is to the first [Props. 7.11, 7.13]
  have hsep : ∀ i : Fin (n + 1),
      a i.succ - a i.castSucc ∶ a i.castSucc ∷ a 1 - a 0 ∶ a 0 := fun i => by
    have halt := Elements.Book7.proposition_13 (ha _) (ha _) (ha 1) (ha 0) (hcon i).inv
    have h11 := Elements.Book7.proposition_11 (hinc i).le hlt.le halt
    have hd : 0 < a i.succ - a i.castSucc := by have := hinc i; omega
    have h := proportion_trans hd (by omega) (ha _) (ha 1) h11 halt
    exact Elements.Book7.proposition_13 hd (by omega) (ha _) (ha 0) h
  -- as one of the leading is to one of the following, so are all the leading to all the
  -- following [Prop. 7.12]
  have h0 : a (Fin.succ 0) - a (Fin.castSucc 0) = a 1 - a 0 := by
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero]
  have h12 := Elements.Book7.proposition_12
    (a := fun i : Fin (n + 1) => a i.succ - a i.castSucc)
    (b := fun i : Fin (n + 1) => a i.castSucc) (fun i => by have := hinc i; omega)
    (fun i => ha _) fun i => by
      show _ ∶ _ ∷ a (Fin.succ 0) - a (Fin.castSucc 0) ∶ a (Fin.castSucc 0)
      rw [h0, Fin.castSucc_zero]
      exact hsep i
  rw [h0, Fin.castSucc_zero] at h12
  -- and all the excesses are the excess of the last
  have := sum_excess fun i => (hinc i).le
  rwa [show sum (fun i : Fin (n + 1) => a i.succ - a i.castSucc) =
    a (Fin.last (n + 1)) - a 0 by omega] at h12

end Elements.Book9
