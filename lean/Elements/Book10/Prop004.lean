import Elements.Book10.Prop003

namespace Elements.Book10

open Elements.Book5 Elements.Book5.Magnitude

variable {M : Type*} [Magnitude M]

/-- `g` is the greatest common measure of `a`, `b` and `c`. -/
def GreatestCommonMeasure₃ (g a b c : M) : Prop :=
  Measures g a ∧ Measures g b ∧ Measures g c ∧
    ∀ e, Measures e a → Measures e b → Measures e c → e ≤ g

/-- The greatest common measure of three commensurable magnitudes, with the corollary's
property: whatever measures the three measures it. -/
theorem exists_greatestCommonMeasure₃ {a b c : M}
    (h : ∃ f, Measures f a ∧ Measures f b ∧ Measures f c) :
    ∃ g, GreatestCommonMeasure₃ g a b c ∧
      ∀ e, Measures e a → Measures e b → Measures e c → Measures e g := by
  obtain ⟨f, hfa, hfb, hfc⟩ := h
  -- let the greatest common measure `d` of `a` and `b` be taken [Prop. 10.3]
  obtain ⟨d, hd⟩ := proposition_3 ⟨f, hfa, hfb⟩
  -- whatever measures `a` and `b` measures `d` [Prop. 10.3 corr.]
  have hd' : ∀ e, Measures e a → Measures e b → Measures e d :=
    fun e => proposition_3_corollary hd
  by_cases hdc : Measures d c
  · -- `d` measures `c`: it is the greatest common measure, for no magnitude greater than
    -- `d` measures `a` and `b`
    exact ⟨d, ⟨hd.1, hd.2.1, hdc, fun e ha hb _ => hd.2.2 e ha hb⟩,
      fun e ha hb _ => hd' e ha hb⟩
  · -- `c` and `d` are commensurable: `f`, measuring `a`, `b`, `c`, measures `d`
    -- [Prop. 10.3 corr.]; let their greatest common measure `e` be taken [Prop. 10.3]
    obtain ⟨g, hg⟩ := proposition_3 ⟨f, hfc, hd' f hfa hfb⟩
    -- whatever measures `a`, `b`, `c` measures `d` and `c`, and so `g` [Prop. 10.3 corr.]
    have hg' : ∀ e, Measures e a → Measures e b → Measures e c → Measures e g :=
      fun e ha hb hc => proposition_3_corollary hg hc (hd' e ha hb)
    -- `g` measures `d`, which measures `a` and `b`; and it measures `c`
    exact ⟨g, ⟨hg.2.1.trans hd.1, hg.2.1.trans hd.2.1, hg.1,
      fun e ha hb hc => (hg' e ha hb hc).le⟩, hg'⟩

/-- To find the greatest common measure of three given commensurable magnitudes. -/
theorem proposition_4 {a b c : M} (h : ∃ f, Measures f a ∧ Measures f b ∧ Measures f c) :
    ∃ g, GreatestCommonMeasure₃ g a b c :=
  (exists_greatestCommonMeasure₃ h).imp fun _ h => h.1

/-- 10.4, corollary: if a magnitude measures three magnitudes, it measures their greatest
common measure. Euclid adds that the same holds for more magnitudes. -/
theorem proposition_4_corollary {a b c g e : M} (hg : GreatestCommonMeasure₃ g a b c)
    (ha : Measures e a) (hb : Measures e b) (hc : Measures e c) : Measures e g := by
  obtain ⟨g', hg', h'⟩ := exists_greatestCommonMeasure₃ ⟨g, hg.1, hg.2.1, hg.2.2.1⟩
  have : g = g' := le_antisymm (hg'.2.2.2 g hg.1 hg.2.1 hg.2.2.1)
    (hg.2.2.2 g' hg'.1 hg'.2.1 hg'.2.2.1)
  exact this ▸ h' e ha hb hc

end Elements.Book10
