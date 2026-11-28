import Elements.Book10.Prop010

namespace Elements.Book10

open Elements.Book5 Number

/-- Prop. 8.4 for two ratios, of `D` to `E` and `F` to `G`: numbers `H`, `K`, `L`
continuously proportional in them. -/
theorem continued_two (D E F G : ℕ+) : ∃ H K L : ℕ+,
    Proportion (D : Number) (E : Number) (H : Number) (K : Number) ∧
      Proportion (F : Number) (G : Number) (K : Number) (L : Number) := by
  -- the ratios in least numbers [Prop. 7.33]
  obtain ⟨d, e, hd, he, hde, hl₁, -⟩ := Elements.Book7.exists_least D.pos E.pos
  obtain ⟨f, g, hf, hg, hfg, hl₂, -⟩ := Elements.Book7.exists_least F.pos G.pos
  obtain ⟨s, hs, hrat, -⟩ := Elements.Book8.proposition_4 (n := 2)
    (p := fun i => if i = 0 then d else f) (q := fun i => if i = 0 then e else g)
    (fun i => by split_ifs <;> assumption)
    (fun i => by split_ifs <;> assumption)
    (fun i => by split_ifs <;> assumption)
  have h₀ := hrat 0
  have h₁ := hrat 1
  simp at h₀ h₁
  refine ⟨⟨s 0, hs 0⟩, ⟨s 1, hs 1⟩, ⟨s 2, hs 2⟩, number_proportion_iff.mpr ?_,
    number_proportion_iff.mpr ?_⟩
  · exact Elements.Book7.proportion_trans D.pos E.pos hd he hde.symm h₀.symm
  · exact Elements.Book7.proportion_trans F.pos G.pos hf hg hfg.symm h₁.symm

variable {M : Type*} [Magnitude M]

/-- Magnitudes commensurable with the same magnitude are commensurable with one another.
Through 10.6, the magnitudes divided into equal parts. -/
theorem proposition_12 (hM : Divisible M) {a b c : M} (ha : Commensurable a c)
    (hb : Commensurable b c) : Commensurable a b := by
  -- `a` has to `c` the ratio of a number `D` to a number `E`, and `c` to `b` that of `F`
  -- to `G` [Prop. 10.5]
  obtain ⟨D, E, h₁⟩ := proposition_5 ha
  obtain ⟨F, G, h₂⟩ := proposition_5 hb.symm
  -- numbers `H`, `K`, `L` continuously proportional in these ratios [Prop. 8.4]
  obtain ⟨H, K, L, hHK, hKL⟩ := continued_two D E F G
  -- as `a` is to `c`, so `H` to `K`, and as `c` to `b`, so `K` to `L` [Prop. 5.11]
  have h₃ := Elements.Book5.proposition_11 h₁ hHK
  have h₄ := Elements.Book5.proposition_11 h₂ hKL
  -- via equality, as `a` is to `b`, so `H` to `L` [Prop. 5.22]: they are commensurable
  -- [Prop. 10.6]
  exact proposition_6 (Elements.Book5.proposition_22' h₃ h₄) (hM a H)

end Elements.Book10
