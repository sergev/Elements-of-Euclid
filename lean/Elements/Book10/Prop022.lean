import Elements.Book10.Prop021

namespace Elements.Book10

open Elements.Book5

variable {ρ : Length}

/-- The square on a medial line `a`, applied to a rational line `r`, makes as breadth a
rational line `d`, incommensurable in length with `r`. -/
theorem proposition_22 {a r d : Length} (ha : Medial ρ a) (hr : Rational ρ r)
    (h : rect r d = sq a) : Rational ρ d ∧ ¬ Commensurable d r := by
  -- the square on `a` is the rectangle contained by rational lines `f`, `g` commensurable
  -- in square only [Prop. 10.21]
  obtain ⟨f, g, hf, hg, hfg, hsq⟩ := ha
  -- equal rectangles: as `r` is to `g`, so `f` to `d` [Prop. 6.14]; and so the squares
  -- [Prop. 6.22]
  have h₁ : Proportion r g f d :=
    proportion_of_rect_eq (h.trans (hsq.trans (rect_comm f g)))
  have h₂ := proportion_sq.mp h₁
  -- the squares on `r` and `g` are commensurable, both rational: so the squares on `f`
  -- and `d` [Prop. 10.11]; the square on `f` is rational, so the square on `d`, and `d`
  -- is rational [Def. 10.4]
  have h₃ := (proposition_11 h₂ Area.divisible Area.divisible).1 (hr.inSquare_of hg)
  have hd : Rational ρ d := Rational.of_sq (hf.sq_rational.of_comm h₃.symm)
  -- `f` is incommensurable in length with `g`, and as `f` is to `g`, so the square on
  -- `f` to the rectangle [Prop. 10.21 lemma]: they are incommensurable [Prop. 10.11]
  have h₄ := (proposition_11 (proposition_21_lemma f g).1 Length.divisible
    Area.divisible).2 hfg.2
  -- the square on `d` is commensurable with the square on `f`, and the rectangle
  -- contained by `d`, `r` equal to that contained by `f`, `g`: so the square on `d` is
  -- incommensurable with the rectangle contained by `d`, `r` [Prop. 10.13]
  have h₅ := proposition_13 Area.divisible h₃ h₄
  rw [← hsq, ← h, rect_comm] at h₅
  -- as the square on `d` is to that rectangle, so `d` to `r` [Prop. 10.21 lemma]: `d` is
  -- incommensurable in length with `r` [Prop. 10.11]
  exact ⟨hd, fun hdr => h₅ ((proposition_11 (proposition_21_lemma d r).1 Length.divisible
    Area.divisible).1 hdr)⟩

/-- 10.22 for a medial area: applied to a rational line, it makes as breadth a rational
line incommensurable in length with it (its side is medial [Prop. 2.14]). -/
theorem proposition_22' {A : Area} {r d : Length} (hA : MedialArea ρ A) (hr : Rational ρ
    r)
    (h : rect r d = A) : Rational ρ d ∧ ¬ Commensurable d r := by
  obtain ⟨a, rfl⟩ := Area.side A
  exact proposition_22 hA hr h

end Elements.Book10
