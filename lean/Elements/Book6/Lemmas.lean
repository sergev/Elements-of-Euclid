import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop03
import Elements.Book1.Prop17
import Elements.Book1.Prop23
import Elements.Book1.Prop31
import Elements.Book1.Prop32
import Elements.Book1.Prop38
import Elements.Book5.Prop07
import Elements.Book5.Prop09
import Elements.Book5.Prop11
import Elements.Book5.Prop16
import Elements.Book5.Prop22
import Elements.Book6.Definitions

/-
Book 5's propositions for figures; constructions Book 6 repeats; and multiples in the
figure. Prop. 6.1 lays off "any number" of straight lines equal to a base, and Prop. 6.9
a part of a line: equal segments laid off `m` times. That is induction on `m`, with each
step a System E construction.
-/

namespace Elements.Book6

open Elements.Book5 Magnitude

/-! Book 5's ways of forming a proportion, for figures. -/

namespace Proportional

variable {X Y Z W X' Y' Z' W' : Type} {K L : Type} [Magnitude K] [Kind K] [Magnitude L]
  [Kind L] [Figure X K] [Figure Y K] [Figure Z L] [Figure W L]

/-- Def. 5.5 reads the same from either pair. -/
theorem symm {p : X} {q : Y} {r : Z} {s : W} (h : p ∶ q ∷ r ∶ s) : r ∶ s ∷ p ∶ q :=
  let ⟨hp, hq, hr, hs, h⟩ := h; ⟨hr, hs, hp, hq, h.symm⟩

/-- Inversely, `q ∶ p ∷ s ∶ r` [Prop. 5.7 corollary]. -/
theorem inv {p : X} {q : Y} {r : Z} {s : W} (h : p ∶ q ∷ r ∶ s) : q ∶ p ∷ s ∶ r :=
  let ⟨hp, hq, hr, hs, h⟩ := h; ⟨hq, hp, hs, hr, proposition_7_corollary h⟩

/-- Ratios the same as the same ratio are the same [Prop. 5.11]. -/
theorem trans {M : Type} [Magnitude M] [Kind M] {U V : Type} [Figure U M] [Figure V M]
    {p : X} {q : Y} {r : Z} {s : W} {u : U} {v : V} (h₁ : p ∶ q ∷ r ∶ s)
    (h₂ : r ∶ s ∷ u ∶ v) : p ∶ q ∷ u ∶ v :=
  let ⟨hp, hq, hr, hs, h₁⟩ := h₁
  ⟨hp, hq, h₂.2.2.1, h₂.2.2.2.1, proposition_11 h₁ (h₂.elim hr hs _ _)⟩

/-- Alternately, `p ∶ r ∷ q ∶ s`, the four of one kind [Prop. 5.16]. -/
theorem alt [Figure Z K] [Figure W K] {p : X} {q : Y} {r : Z} {s : W}
    (h : p ∶ q ∷ r ∶ s) : p ∶ r ∷ q ∶ s :=
  let ⟨hp, hq, hr, hs, h⟩ := h; ⟨hp, hr, hq, hs, proposition_16 h⟩

/-- Via equality (ex aequali): from `p ∶ q ∷ u ∶ v` and `q ∶ r ∷ v ∶ w`, `p ∶ r ∷ u ∶ w`
[Prop. 5.22]. -/
theorem exAequali {Q R U V T : Type} [Figure Q K] [Figure R K] [Figure U L]
    [Figure V L] [Figure T L] {p : X} {q : Q} {r : R} {u : U} {v : V} {w : T}
    (h₁ : p ∶ q ∷ u ∶ v) (h₂ : q ∶ r ∷ v ∶ w) : p ∶ r ∷ u ∶ w :=
  let ⟨hp, _, hu, _, h₁⟩ := h₁
  let ⟨_, hr, _, hw, h₂⟩ := h₂
  ⟨hp, hr, hu, hw, proposition_22' h₁ h₂⟩

/-- Magnitudes with the same ratio to equal magnitudes are equal [Prop. 5.9]. -/
theorem eq_left {A B C D : Type} [Figure A K] [Figure B K] [Figure C K] [Figure D K]
    {p : A} {q : B} {r : C} {r' : D} (h : p ∶ r ∷ q ∶ r') (hr : size r = size r') :
    size p = size q :=
  let ⟨hp, hr₀, hq, hr', h⟩ := h
  mag_inj.mp (proposition_9 (by rwa [mag_congr (hp := hr') (hq := hr₀) hr.symm] at h))

/-- Magnitudes to which equal magnitudes have the same ratio are equal [Prop. 5.9]. -/
theorem eq_right {A B C D : Type} [Figure A K] [Figure B K] [Figure C K] [Figure D K]
    {p : A} {q : B} {r : C} {r' : D} (h : r ∶ p ∷ r' ∶ q) (hr : size r = size r') :
    size p = size q :=
  let ⟨hr₀, hp, hr', hq, h⟩ := h
  mag_inj.mp (proposition_9' (by rwa [mag_congr (hp := hr') (hq := hr₀) hr.symm] at h))

end Proportional

/-- The angles of a triangle are equal to two right angles [Prop. 1.32]. -/
theorem triangle_angles : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA → ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point BC b c) as d
  euclid_apply (Elements.Book1.proposition_32 a b c d AB BC CA)
  euclid_finish

/--
On the straight line `ef`, on `y`'s side, a triangle `gef` with the angles at `e`, `f`
equal to those at `b`, `c` of the triangle `abc` [Prop. 1.23]; `EG`, `FG` meet since
those angles are less than two right angles [Prop. 1.17, Post. 5], and the remaining
angle at `g` is equal to that at `a` [Prop. 1.32].
-/
theorem triangle_on : ∀ (a b c e f y : Point) (AB BC CA EF : Line),
  formTriangle a b c AB BC CA ∧ distinctPointsOnLine e f EF ∧ ¬(y.onLine EF) →
  ∃ g : Point, g.sameSide y EF ∧ ∠ g:e:f = ∠ a:b:c ∧ ∠ g:f:e = ∠ a:c:b ∧
  ∠ e:g:f = ∠ b:a:c :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_23_side e f b a c y EF AB BC) as p
  euclid_apply (Elements.Book1.proposition_23_side f e c a b y EF CA BC) as q
  euclid_apply (Elements.Book1.proposition_17 a b c AB BC CA)
  euclid_apply (line_from_points e p) as EP
  euclid_apply (line_from_points f q) as FQ
  euclid_apply (lines_intersect p e f q EP EF FQ) as g
  euclid_apply (equal_angles e p g f f EP EF)
  euclid_apply (equal_angles f q g e e FQ EF)
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_apply (triangle_angles a b c AB BC CA)
  euclid_apply (triangle_angles g e f EG EF FG)
  use g
  euclid_finish

/--
A straight line `BP` making with `BA` a lesser angle than `BC` does, on `c`'s side, cuts
`ac` (the crossbar): `p` is inside the angle `abc`, or the angle `abp` would be `abc`
or exceed it.
-/
theorem crossbar : ∀ (a b c p : Point) (AB BC CA BP : Line),
  formTriangle a b c AB BC CA ∧ distinctPointsOnLine b p BP ∧ p.sameSide c AB ∧
  ∠ a:b:p < ∠ a:b:c → ∃ g : Point, g.onLine BP ∧ between a g c :=
by
  euclid_intros
  have : ¬(c.onLine BP) := by
    intro h
    euclid_apply (equal_angles b p c a a BP AB)
    euclid_finish
  have : p.sameSide a BC := by
    by_contra h
    by_cases p.onLine BC
    · euclid_finish
    · euclid_apply (triple_incidence_2 AB BC BP b a c p)
      euclid_apply (sum_angles_onlyif b a p c AB BP)
      euclid_finish
  euclid_apply (triple_incidence_1 AB BP BC b a p c)
  euclid_apply (intersection_lines_opposing a c BP CA)
  euclid_apply (intersection_lines BP CA) as g
  use g
  euclid_finish

/--
One more copy: on the line `L` beyond `g` (which is `c`, or beyond `c` from `b`), a point
`e` with `ge` equal to `bc` [Prop. 1.3]; the triangle on `ge` with vertex `a` is equal to
that on `bc` [Prop. 1.38], so `△abe` is `△abg` and `△abc` together.
-/
theorem multiple_step : ∀ (a b c g : Point) (L : Line),
  b.onLine L ∧ c.onLine L ∧ g.onLine L ∧ ¬(a.onLine L) ∧ b ≠ c ∧
  (between b c g ∨ g = c) →
  ∃ e : Point, e.onLine L ∧ between b c e ∧ between b g e ∧
  |(b─e)| = |(b─g)| + |(b─c)| ∧
  Triangle.area △a:b:e = Triangle.area △a:b:g + Triangle.area △a:b:c :=
by
  euclid_intros
  have : b ≠ g := by
    rcases ‹between b c g ∨ g = c› with h | h
    · euclid_finish
    · subst h
      euclid_finish
  euclid_apply (extend_point_longer L b g (b─c)) as x
  euclid_apply (Elements.Book1.proposition_3 g x b c L L) as e
  euclid_assert between b g e
  have hce : between b c e := by
    rcases ‹between b c g ∨ g = c› with h | h
    · euclid_finish
    · subst h
      euclid_finish
  euclid_apply (Elements.Book1.proposition_31 a b c L) as AD
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points a e) as AE
  euclid_apply (Elements.Book1.proposition_38 a b c a g e AD L AB AC AG AE)
  euclid_apply (sum_areas_if b e g a L)
  use e
  euclid_finish

/--
`m` copies of `bc` laid off along `L` from `b`, by induction on `m`, each copy by
`multiple_step`: a point `g` with `bg` the `m`-th multiple of `bc`, and the triangle
`abg` the `m`-th multiple of `abc`, since the triangles on the copies are equal to it. The
points between are those of the steps.
-/
theorem multiple_on_line (m : ℕ+) {a b c : Point} {L : Line} (hb : b.onLine L)
    (hc : c.onLine L) (ha : ¬ a.onLine L) (hbc : 0 < size (b─c))
    (habc : 0 < size (△a:b:c)) :
    ∃ (g : Point) (hg : 0 < size (b─g)) (habg : 0 < size (△a:b:g)),
      g.onLine L ∧ (between b c g ∨ g = c) ∧
      mag (b─g) hg = m • mag (b─c) hbc ∧ mag (△a:b:g) habg = m • mag (△a:b:c) habc := by
  induction m using PNat.recOn with
  | one => exact ⟨c, hbc, habc, hc, Or.inr rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨g, hg, habg, hgL, hcg, hlen, harea⟩ := ih
    have hbc' : b ≠ c := size_segment_pos.mp hbc
    obtain ⟨e, heL, hce, hge, hbe, habe⟩ :=
      multiple_step a b c g L ⟨hb, hc, hgL, ha, hbc', hcg⟩
    have hbe' : b ≠ e := by euclid_finish
    refine ⟨e, size_segment_pos.mpr hbe', size_triangle_pos' ⟨hb, heL, hbe'⟩ ha, heL,
      Or.inl hce, ?_, ?_⟩
    · rw [mult_succ, ← hlen, mag_add (r := (b─e)) hbe.symm]
    · rw [mult_succ, ← harea, mag_add (r := △a:b:e) habe.symm]

/-- `m` copies of `bc` laid off along `L` from `b`: `bg` is the `m`-th multiple of
`bc`. -/
theorem multiple_on_line' (m : ℕ+) {b c : Point} {L : Line} (hb : b.onLine L)
    (hc : c.onLine L) (hbc : 0 < size (b─c)) :
    ∃ (g : Point) (hg : 0 < size (b─g)), g.onLine L ∧ (between b c g ∨ g = c) ∧
      mag (b─g) hg = m • mag (b─c) hbc := by
  have hbc' : b ≠ c := size_segment_pos.mp hbc
  -- a point off `L` [Prop. 1.1]
  obtain ⟨a, ha⟩ := Elements.Book1.proposition_1 b c L ⟨hb, hc, hbc'⟩
  have ha' : ¬ a.onLine L := by euclid_finish
  obtain ⟨g, hg, _, hgL, hcg, hlen, _⟩ :=
    multiple_on_line m hb hc ha' hbc (size_triangle_pos' ⟨hb, hc, hbc'⟩ ha')
  exact ⟨g, hg, hgL, hcg, hlen⟩

end Elements.Book6
