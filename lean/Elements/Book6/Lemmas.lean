import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop03
import Elements.Book1.Prop13
import Elements.Book1.Prop17
import Elements.Book1.Prop23
import Elements.Book1.Prop31
import Elements.Book1.Prop32
import Elements.Book1.Prop38
import Elements.Book5.Prop07
import Elements.Book5.Prop09
import Elements.Book5.Prop11
import Elements.Book5.Prop14
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

/-- A ratio is the same as itself (Def. 5.5). -/
theorem refl {p : X} {q : Y} (hp : 0 < size p) (hq : 0 < size q) : p ∶ q ∷ p ∶ q :=
  ⟨hp, hq, hp, hq, Proportion.refl _ _⟩

/-- Inversely, `q ∶ p ∷ s ∶ r` [Prop. 5.7 corollary]. -/
theorem inv {p : X} {q : Y} {r : Z} {s : W} (h : p ∶ q ∷ r ∶ s) : q ∶ p ∷ s ∶ r :=
  let ⟨hp, hq, hr, hs, h⟩ := h; ⟨hq, hp, hs, hr, Elements.Book5.proposition_7_corollary h⟩

/-- Ratios the same as the same ratio are the same [Prop. 5.11]. -/
theorem trans {M : Type} [Magnitude M] [Kind M] {U V : Type} [Figure U M] [Figure V M]
    {p : X} {q : Y} {r : Z} {s : W} {u : U} {v : V} (h₁ : p ∶ q ∷ r ∶ s)
    (h₂ : r ∶ s ∷ u ∶ v) : p ∶ q ∷ u ∶ v :=
  let ⟨hp, hq, hr, hs, h₁⟩ := h₁
  ⟨hp, hq, h₂.2.2.1, h₂.2.2.2.1, Elements.Book5.proposition_11 h₁ (h₂.elim hr hs _ _)⟩

/-- Alternately, `p ∶ r ∷ q ∶ s`, the four of one kind [Prop. 5.16]. -/
theorem alt [Figure Z K] [Figure W K] {p : X} {q : Y} {r : Z} {s : W}
    (h : p ∶ q ∷ r ∶ s) : p ∶ r ∷ q ∶ s :=
  let ⟨hp, hq, hr, hs, h⟩ := h; ⟨hp, hr, hq, hs, Elements.Book5.proposition_16 h⟩

/-- Via equality (ex aequali): from `p ∶ q ∷ u ∶ v` and `q ∶ r ∷ v ∶ w`, `p ∶ r ∷ u ∶ w`
[Prop. 5.22]. -/
theorem exAequali {Q R U V T : Type} [Figure Q K] [Figure R K] [Figure U L]
    [Figure V L] [Figure T L] {p : X} {q : Q} {r : R} {u : U} {v : V} {w : T}
    (h₁ : p ∶ q ∷ u ∶ v) (h₂ : q ∶ r ∷ v ∶ w) : p ∶ r ∷ u ∶ w :=
  let ⟨hp, _, hu, _, h₁⟩ := h₁
  let ⟨_, hr, _, hw, h₂⟩ := h₂
  ⟨hp, hr, hu, hw, Elements.Book5.proposition_22' h₁ h₂⟩

/-- Magnitudes with the same ratio to equal magnitudes are equal [Prop. 5.9]. -/
theorem eq_left {A B C D : Type} [Figure A K] [Figure B K] [Figure C K] [Figure D K]
    {p : A} {q : B} {r : C} {r' : D} (h : p ∶ r ∷ q ∶ r') (hr : size r = size r') :
    size p = size q :=
  let ⟨hp, hr₀, hq, hr', h⟩ := h
  mag_inj.mp (Elements.Book5.proposition_9
    (by rwa [mag_congr (hp := hr') (hq := hr₀) hr.symm] at h))

/-- Magnitudes to which equal magnitudes have the same ratio are equal [Prop. 5.9]. -/
theorem eq_right {A B C D : Type} [Figure A K] [Figure B K] [Figure C K] [Figure D K]
    {p : A} {q : B} {r : C} {r' : D} (h : r ∶ p ∷ r' ∶ q) (hr : size r = size r') :
    size p = size q :=
  let ⟨hr₀, hp, hr', hq, h⟩ := h
  mag_inj.mp (Elements.Book5.proposition_9'
    (by rwa [mag_congr (hp := hr') (hq := hr₀) hr.symm] at h))

/-- Equal magnitudes have the same ratio to the same [Prop. 5.7]. -/
theorem of_eq {A B C : Type} [Figure A K] [Figure B K] [Figure C K] {p : A} {q : B}
    {r : C} (hp : 0 < size p) (hr : 0 < size r) (h : size p = size q) : p ∶ r ∷ q ∶ r :=
  ⟨hp, hr, h ▸ hp, hr,
    (Elements.Book5.proposition_7 (mag r hr) (mag_congr (hq := h ▸ hp) h)).1⟩

/-- Of four proportionals of one kind, if the second exceeds the fourth, the first exceeds
the third [Prop. 5.14]. -/
theorem lt_first {A B C D : Type} [Figure A K] [Figure B K] [Figure C K] [Figure D K]
    {p : A} {q : B} {r : C} {s : D} (h : p ∶ q ∷ r ∶ s) (hs : size s < size q) :
    size r < size p := by
  obtain ⟨hp, hq, hr, hs₀, h⟩ := h
  have h₁ := Elements.Book5.proposition_14 h
  rcases lt_trichotomy (mag r hr) (mag p hp) with e | e | e
  · exact mag_lt.mp e
  · exact absurd (h₁.2.1 e.symm) (ne_of_gt (mag_lt.mpr hs))
  · exact absurd (h₁.2.2 e) (lt_asymm (mag_lt.mpr hs))

end Proportional

/-- Two magnitudes `x`, `y`, as Prop. 5.12 takes them. -/
def two {M : Type} (x y : M) : Fin 2 → M := fun i => match i with | 0 => x | 1 => y

/-- Three magnitudes `x`, `y`, `z`, as Prop. 5.12 takes them. -/
def three {M : Type} (x y z : M) : Fin 3 → M :=
  fun i => match i with | 0 => x | 1 => y | 2 => z

theorem sum_two {M : Type} [Magnitude M] (x y : M) :
    Magnitude.sum (two x y) = x + y := rfl

theorem sum_three {M : Type} [Magnitude M] (x y z : M) :
    Magnitude.sum (three x y z) = x + y + z := rfl

/-! The squared ratio (Def. 5.9) of figures. -/

namespace SquaredRatio'

variable {X Y Z W : Type} {K L : Type} [Magnitude K] [Kind K] [Magnitude L] [Kind L]
  [Figure X K] [Figure Y K] [Figure Z L] [Figure W L]

/--
Ratios squared of the same ratio are the same: if `p : q` is the squared ratio of `r : s`,
and `p' : q'` of `r' : s'`, with `r : s :: r' : s'`, then `p : q :: p' : q'`. Of the third
proportionals `z`, `z'`, `s : z :: s' : z'` [Prop. 5.11], so `r : z :: r' : z'`
[Prop. 5.22].
-/
theorem same {X' Y' Z' W' : Type} {K' L' : Type} [Magnitude K'] [Kind K'] [Magnitude L']
    [Kind L'] [Figure X' K'] [Figure Y' K'] [Figure Z' L'] [Figure W' L']
    {p : X} {q : Y} {r : Z} {s : W} {p' : X'} {q' : Y'} {r' : Z'} {s' : W'}
    (h : SquaredRatio' p q r s) (h' : SquaredRatio' p' q' r' s') (hr : r ∶ s ∷ r' ∶ s') :
    p ∶ q ∷ p' ∶ q' := by
  obtain ⟨hp, hq, hr₀, hs, z, h₁, h₂⟩ := h
  obtain ⟨hp', hq', hr₀', hs', z', h₁', h₂'⟩ := h'
  have hr := hr.elim hr₀ hs hr₀' hs'
  have h₃ := Elements.Book5.proposition_11 (Elements.Book5.proposition_11 h₁.symm hr) h₁'
  have h₄ := Elements.Book5.proposition_22' hr h₃
  exact ⟨hp, hq, hp', hq',
    Elements.Book5.proposition_11 (Elements.Book5.proposition_11 h₂ h₄) h₂'.symm⟩

/-- If `p : q` is the squared ratio of `r : s`, and `r : s :: s : t`, then
`r : t :: p : q` [Def. 5.9, Props. 5.11, 5.9]. -/
theorem third {T : Type} [Figure T L] {p : X} {q : Y} {r : Z} {s : W} {t : T}
    (h : SquaredRatio' p q r s) (ht : r ∶ s ∷ s ∶ t) : r ∶ t ∷ p ∶ q := by
  obtain ⟨hp, hq, hr, hs, z, h₁, h₂⟩ := h
  obtain ⟨hr', hs', hs'', htt, h₃⟩ := ht
  have := Elements.Book5.proposition_9' (Elements.Book5.proposition_11 h₁.symm h₃)
  subst this
  exact ⟨hr, htt, hp, hq, h₂.symm⟩

/-- A ratio the same as a squared ratio of `r : s` is one too [Prop. 5.11]. -/
theorem congr {X' Y' : Type} [Figure X' K] [Figure Y' K] {p : X} {q : Y} {p' : X'}
    {q' : Y'} {r : Z} {s : W} (h : SquaredRatio' p q r s) (hp : p ∶ q ∷ p' ∶ q') :
    SquaredRatio' p' q' r s := by
  obtain ⟨hp₀, hq, hr, hs, z, h₁, h₂⟩ := h
  obtain ⟨hp₁, hq₁, hp', hq', hp⟩ := hp
  exact ⟨hp', hq', hr, hs, z, h₁, Elements.Book5.proposition_11 hp.symm h₂⟩

/--
Equal figures in the squared ratio of `r : s` have `r` equal to `s`: `r : s :: s : z`
with `z` equal to `r` [Def. 5.5], and if `r` exceeded `s`, `s` would exceed `r`
[Prop. 5.14].
-/
theorem eq {p : X} {q : Y} {r : Z} {s : W} (h : SquaredRatio' p q r s)
    (hpq : size p = size q) : size r = size s := by
  obtain ⟨hp, hq, hr, hs, z, h₁, h₂⟩ := h
  have : mag r hr = z := by
    have := (h₂.eq 1 1).mp (by rw [one_mult, one_mult]; exact mag_congr hpq)
    rwa [one_mult, one_mult] at this
  subst this
  have h₃ := Elements.Book5.proposition_14 h₁
  rcases lt_trichotomy (mag r hr) (mag s hs) with e | e | e
  · exact absurd (h₃.2.2 e) (lt_asymm e)
  · exact mag_inj.mp e
  · exact absurd (h₃.1 e) (lt_asymm e)

/-- In the squared ratio of `r : s`, if `p` exceeds `q`, then `r` exceeds `s`: of the
third proportional `z`, `r` exceeds `z` [Def. 5.5], and `r : s :: s : z` [Prop. 5.14]. -/
theorem lt {p : X} {q : Y} {r : Z} {s : W} (h : SquaredRatio' p q r s)
    (hpq : size q < size p) : size s < size r := by
  obtain ⟨hp, hq, hr, hs, z, h₁, h₂⟩ := h
  have hz : z < mag r hr := by
    have := (h₂.gt 1 1).mp (by rw [one_mult, one_mult]; exact mag_lt.mpr hpq)
    rwa [one_mult, one_mult] at this
  have h₃ := Elements.Book5.proposition_14 h₁
  rcases lt_trichotomy (mag s hs) (mag r hr) with e | e | e
  · exact mag_lt.mp e
  · have h₄ : mag s hs = z := h₃.2.1 e.symm
    rw [← h₄, e] at hz
    exact absurd hz (lt_irrefl _)
  · exact absurd (lt_trans (lt_trans hz e) (h₃.2.2 e)) (lt_irrefl _)

end SquaredRatio'

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
A straight line `BP` making with `BA` a lesser angle than `BC` does, on `c`'s side, is
inside the angle `abc`: `p` is on `a`'s side of `BC`, or the angle `abp` would be `abc`
or exceed it.
-/
theorem inside_of_lt : ∀ (a b c p : Point) (AB BC BP : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine b p BP ∧ ¬(c.onLine AB) ∧ p.sameSide c AB ∧ ∠ a:b:p < ∠ a:b:c →
  ¬(c.onLine BP) ∧ p.sameSide a BC :=
by
  euclid_intros
  have : ¬(c.onLine BP) := by
    intro h
    euclid_apply (equal_angles b p c a a BP AB)
    euclid_finish
  refine ⟨this, ?_⟩
  by_contra h
  by_cases p.onLine BC
  · euclid_finish
  · euclid_apply (triple_incidence_2 AB BC BP b a c p)
    euclid_apply (sum_angles_onlyif b a p c AB BP)
    euclid_finish

/-- The straight line `BP` of `inside_of_lt` cuts `ac` (the crossbar). -/
theorem crossbar : ∀ (a b c p : Point) (AB BC CA BP : Line),
  formTriangle a b c AB BC CA ∧ distinctPointsOnLine b p BP ∧ p.sameSide c AB ∧
  ∠ a:b:p < ∠ a:b:c → ∃ g : Point, g.onLine BP ∧ between a g c :=
by
  euclid_intros
  euclid_apply (inside_of_lt a b c p AB BC BP)
  euclid_apply (triple_incidence_1 AB BP BC b a p c)
  euclid_apply (intersection_lines_opposing a c BP CA)
  euclid_apply (intersection_lines BP CA) as g
  use g
  euclid_finish

/--
Angles `agb`, `bgh` on either side of `GB`, together less than two right angles, make
the angle `agh`: `b` is inside it. Produce `ag` to `a'`: `bgh` is less than `bga'`
[Prop. 1.13], so `h` is inside the angle `bga'`.
-/
theorem inside_of_sum : ∀ (a b g h : Point) (GA GB GH : Line),
  distinctPointsOnLine g a GA ∧ distinctPointsOnLine g b GB ∧
  distinctPointsOnLine g h GH ∧ a.opposingSides h GB ∧ ∠ a:g:b + ∠ b:g:h < ∟ + ∟ →
  b.sameSide h GA ∧ b.sameSide a GH ∧ ∠ a:g:h = ∠ a:g:b + ∠ b:g:h :=
by
  euclid_intros
  euclid_apply (extend_point GA a g) as a'
  euclid_apply (Elements.Book1.proposition_13 b g a' a GB GA)
  euclid_apply (inside_of_lt b g a' h GB GA GH)
  euclid_apply (triple_incidence_1 GB GH GA g b h a')
  have : b.sameSide h GA ∧ b.sameSide a GH := by
    constructor
    · euclid_finish
    · by_contra
      euclid_finish
  euclid_apply (sum_angles_onlyif g a h b GA GH)
  euclid_finish

/-- A line `N` meeting `M` at `p` meets every parallel `L` to `M` (Post. 5): otherwise
`M` and `N` would be two parallels to `L` through `p`. -/
theorem parallel_meets : ∀ (p : Point) (L M N : Line),
  ¬(L.intersectsLine M) ∧ p.onLine M ∧ p.onLine N ∧ M ≠ N → L.intersectsLine N :=
by
  euclid_intros
  by_contra
  euclid_apply (parallel_line_unique p L M N)
  euclid_finish

/-- On the line `DG` beyond `g`, `ge` equal to a given straight line `c₀c₁`
[Prop. 1.3]. -/
theorem lay_beyond : ∀ (d g c₀ c₁ : Point) (L : Line),
  distinctPointsOnLine d g L ∧ c₀ ≠ c₁ →
  ∃ e : Point, e.onLine L ∧ between d g e ∧ |(g─e)| = |(c₀─c₁)| :=
by
  euclid_intros
  euclid_apply (line_from_points c₀ c₁) as C
  euclid_apply (extend_point_longer L d g (c₀─c₁)) as y
  euclid_apply (Elements.Book1.proposition_3 g y c₀ c₁ L C) as e
  use e
  euclid_finish

/-- On the ray from `d` through `x`, `dg` equal to a given straight line `c₀c₁`
[Prop. 1.3]. -/
theorem lay_on_ray : ∀ (d x c₀ c₁ : Point) (L : Line),
  distinctPointsOnLine d x L ∧ c₀ ≠ c₁ →
  ∃ g : Point, g.onLine L ∧ g ≠ d ∧ ¬(between g d x) ∧ |(d─g)| = |(c₀─c₁)| :=
by
  euclid_intros
  euclid_apply (lay_beyond d x c₀ c₁ L) as y
  euclid_apply (line_from_points c₀ c₁) as C
  euclid_assert |(d─y)| > |(c₀─c₁)|
  euclid_apply (Elements.Book1.proposition_3 d y c₀ c₁ L C) as g
  use g
  euclid_finish

/-- A straight line `M` through `x` and `o`, on opposite sides of `L`, meets `L` between
them. -/
theorem between_of_opposite : ∀ (x q o : Point) (L M : Line),
  q.onLine L ∧ x.onLine M ∧ q.onLine M ∧ o.onLine M ∧ x.opposingSides o L →
  between x q o :=
by
  euclid_intros
  have : x ≠ q := by
    intro h
    subst h
    exact ‹¬(x.onLine L)› ‹_›
  have : o ≠ q := by
    intro h
    subst h
    exact ‹¬(o.onLine L)› ‹_›
  have : x ≠ o := by
    intro h
    subst h
    euclid_finish
  euclid_apply (between_points x q o M)
  rcases ‹between x q o ∨ between q x o ∨ between x o q› with h | h | h
  · exact h
  · exact absurd (pasch_2 q x o L ⟨h, ‹_›, ‹_›⟩) ‹¬(x.sameSide o L)›
  · exact absurd (pasch_2 q o x L ⟨by euclid_finish, ‹_›, ‹_›⟩)
      (fun h' => ‹¬(x.sameSide o L)› (by euclid_finish))

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
