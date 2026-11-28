import SystemE
import Elements.Book5.Plane

/-
Book 6's definitions with ratios: lines and figures as magnitudes, their proportion, and
Def. 6.1, Def. 6.2, the squared and the compounded ratio in the figure.
-/

section
open Lean Elab Tactic Meta

/-- `linarith`, with the area of each triangle in the goal and the hypotheses the same in
any order of its vertices (`area_symm_1`, `area_symm_2`). -/
elab "area_linarith" : tactic => withMainContext do
  let tris ← IO.mkRef (#[] : Array (Expr × Expr × Expr))
  let visit (e : Expr) : MetaM Unit := do
    Meta.forEachExpr (← instantiateMVars e) fun s => do
      if s.isAppOfArity ``Triangle.ofPoints 3 then
        let t := (s.getAppArgs[0]!, s.getAppArgs[1]!, s.getAppArgs[2]!)
        unless (← tris.get).contains t do tris.modify (·.push t)
  visit (← getMainTarget)
  for d in ← getLCtx do
    if !d.isImplementationDetail then visit d.type
  let mut g ← getMainGoal
  for (a, b, c) in ← tris.get do
    for (x, y, z) in [(a, b, c), (b, c, a), (c, a, b), (a, c, b), (c, b, a), (b, a, c)] do
      for n in [``area_symm_1, ``area_symm_2] do
        let p ← mkAppM n #[x, y, z]
        let (_, g') ← (← g.assert `h (← inferType p) p).intro1P
        g := g'
  replaceMainGoal [g]
  evalTactic (← `(tactic| linarith))

end

namespace Elements.Book6

open Elements.Book5

/-- A kind of magnitude in the plane, `Length` or `Area`: a positive real is one. -/
class Kind (K : Type) [Magnitude K] where
  of : (x : ℝ) → 0 < x → K
  of_inj {x y : ℝ} {hx : 0 < x} {hy : 0 < y} : of x hx = of y hy ↔ x = y
  of_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    of x hx + of y hy = of (x + y) (by positivity)
  of_lt {x y : ℝ} {hx : 0 < x} {hy : 0 < y} : of x hx < of y hy ↔ x < y

noncomputable instance : Kind Length where
  of x h := ⟨x, h⟩
  of_inj := Subtype.mk_eq_mk
  of_add _ _ := Subtype.ext (Positive.coe_add _ _)
  of_lt := Iff.rfl

noncomputable instance : Kind Area where
  of x h := ⟨x, h⟩
  of_inj := Subtype.mk_eq_mk
  of_add _ _ := Subtype.ext (Positive.coe_add _ _)
  of_lt := Iff.rfl

/--
A figure of System E that is a magnitude of kind `K`: a straight line `(a─b)` a length,
a triangle `△a:b:c`, quadrilateral `□a:b:c:d` or pentagon `⬠a:b:c:d:e` an area. `size`
is System E's measure of it, a real; when it is positive, the figure is a magnitude.
-/
class Figure (X : Type) (K : outParam Type) [Magnitude K] [Kind K] where
  size : X → ℝ

export Figure (size)

instance : Figure Segment Length := ⟨Segment.length⟩
instance : Figure Triangle Area := ⟨Triangle.area⟩
instance : Figure Quadrilateral Area := ⟨Quadrilateral.area⟩
instance : Figure Pentagon Area := ⟨Pentagon.area⟩

variable {X Y Z W U V : Type} {K L : Type} [Magnitude K] [Kind K] [Magnitude L] [Kind L]
  [Figure X K] [Figure Y K] [Figure Z L] [Figure W L] [Figure U K] [Figure V K]

/-- The figure `p` as a magnitude, when it is not degenerate. -/
noncomputable def mag (p : X) (h : 0 < size p) : K := Kind.of (size p) h

/--
`p ∶ q ∷ r ∶ s`, "as `p` is to `q`, so is `r` to `s`": four figures, none degenerate, and
proportional (Def. 5.5). `p`, `q` are of one kind, `r`, `s` of one kind, the same or
another. The positivity of each is part of the statement, so that the proportion of
lines `(a─b) ∶ (c─d) ∷ …` says that their ends are distinct.
-/
def Proportional (p : X) (q : Y) (r : Z) (s : W) : Prop :=
  ∃ (hp : 0 < size p) (hq : 0 < size q) (hr : 0 < size r) (hs : 0 < size s),
    Proportion (mag p hp) (mag q hq) (mag r hr) (mag s hs)

@[inherit_doc] notation:50 p:51 " ∶ " q:51 " ∷ " r:51 " ∶ " s:51 => Proportional p q r s

/-- `p ∶ q` is greater than `r ∶ s` (Def. 5.7), the four figures not degenerate. -/
def GreaterRatio' (p : X) (q : Y) (r : Z) (s : W) : Prop :=
  ∃ (hp : 0 < size p) (hq : 0 < size q) (hr : 0 < size r) (hs : 0 < size s),
    GreaterRatio (mag p hp) (mag q hq) (mag r hr) (mag s hs)

/-- `p ∶ q` is the squared ratio of `r ∶ s` (Def. 5.9). -/
def SquaredRatio' (p : X) (q : Y) (r : Z) (s : W) : Prop :=
  ∃ (hp : 0 < size p) (hq : 0 < size q) (hr : 0 < size r) (hs : 0 < size s),
    SquaredRatio (mag p hp) (mag q hq) (mag r hr) (mag s hs)

/--
The compounded ratio, used by Prop. 6.23 and not defined in Book 5. Euclid takes a
magnitude `k`, makes `k : l` the same as the first ratio and `l : m` as the second
(Prop. 6.12), and says that `k : m` is compounded of `k : l` and `l : m`.
`CompoundRatio a b c d e f`: `a : b` is compounded of `c : d` and `e : f`, being the same
as such a `k : m`, with `k`, `l`, `m` of the kind of `c`, `d`.
-/
def CompoundRatio {M N P : Type} [Magnitude M] [Magnitude N] [Magnitude P]
    (a b : N) (c d : M) (e f : P) : Prop :=
  ∃ k l m : M, Proportion c d k l ∧ Proportion e f l m ∧ Proportion a b k m

/-- `p ∶ q` is compounded of `r ∶ s` and `u ∶ v`, the six figures not degenerate. -/
def CompoundRatio' (p : X) (q : Y) (r : Z) (s : W) (u : U) (v : V) : Prop :=
  ∃ (hp : 0 < size p) (hq : 0 < size q) (hr : 0 < size r) (hs : 0 < size s)
    (hu : 0 < size u) (hv : 0 < size v),
    CompoundRatio (mag p hp) (mag q hq) (mag r hr) (mag s hs) (mag u hu) (mag v hv)

/-! Bridge lemmas: figures as magnitudes. -/

/-- Figures of equal size are equal magnitudes. -/
theorem mag_congr {p : X} {q : Y} {hp : 0 < size p} {hq : 0 < size q}
    (h : size p = size q) : mag p hp = mag q hq :=
  Kind.of_inj.mpr h

theorem mag_inj {p : X} {q : Y} {hp : 0 < size p} {hq : 0 < size q} :
    mag p hp = mag q hq ↔ size p = size q :=
  Kind.of_inj

/-- Two figures together make a third when their sizes add up. -/
theorem mag_add {p : X} {q : Y} {r : U} {hp : 0 < size p} {hq : 0 < size q}
    {hr : 0 < size r} (h : size p + size q = size r) :
    mag p hp + mag q hq = mag r hr := by
  unfold mag
  rw [Kind.of_add]
  exact Kind.of_inj.mpr h

theorem mag_lt {p : X} {q : Y} {hp : 0 < size p} {hq : 0 < size q} :
    mag p hp < mag q hq ↔ size p < size q :=
  Kind.of_lt

theorem size_segment (a b : Point) : size (a─b) = |(a─b)| := rfl
theorem size_triangle (a b c : Point) : size (△a:b:c) = Triangle.area △a:b:c := rfl
theorem size_quadrilateral (a b c d : Point) :
    size (□a:b:c:d) = Triangle.area △a:b:c + Triangle.area △a:c:d := rfl
theorem size_pentagon (a b c d e : Point) : size (⬠a:b:c:d:e) =
    Triangle.area △a:b:c + Triangle.area △a:c:d + Triangle.area △a:d:e := rfl

/-- A straight line is a magnitude when its ends are distinct. -/
theorem size_segment_pos {a b : Point} : 0 < size (a─b) ↔ a ≠ b :=
  ⟨fun h h' => (ne_of_gt h) (zero_segment_onlyif a b h'),
   fun h => lt_of_le_of_ne (segment_gte_zero _) fun h' => h (zero_segment_if a b h'.symm)⟩

/-- A triangle is a magnitude when its vertex is off its base. -/
theorem size_triangle_pos {a b c : Point} {L : Line} (h : distinctPointsOnLine a b L)
    (hc : ¬ c.onLine L) : 0 < size (△a:b:c) :=
  lt_of_le_of_ne (area_gte_zero _) fun h' => hc (degenerated_area_if a b c L ⟨h, h'.symm⟩)

/-- `(a─b)` is `(b─a)`. -/
theorem size_segment_symm (a b : Point) : size (a─b) = size (b─a) :=
  segment_symmetric a b

/-- A triangle doesn't depend on the order of its vertices. -/
theorem size_triangle_rot (a b c : Point) : size (△a:b:c) = size (△b:c:a) :=
  (area_symm_1 b c a).symm

theorem size_triangle_swap (a b c : Point) : size (△a:b:c) = size (△a:c:b) :=
  area_symm_2 a b c

/-- A triangle is a magnitude when its vertex is off its base: the vertex first. -/
theorem size_triangle_pos' {a b c : Point} {L : Line} (h : distinctPointsOnLine b c L)
    (ha : ¬ a.onLine L) : 0 < size (△a:b:c) := by
  rw [size_triangle_rot]
  exact size_triangle_pos h ha

/-- `size p = size q` for the same straight line with its ends either way, or the same
triangle with its vertices in any order. -/
macro "size_perm" : tactic => `(tactic| first
  | rfl
  | exact size_segment_symm _ _
  | exact size_triangle_rot _ _ _
  | exact (size_triangle_rot _ _ _).symm
  | exact size_triangle_swap _ _ _
  | exact (size_triangle_swap _ _ _).trans (size_triangle_rot _ _ _)
  | exact (size_triangle_rot _ _ _).trans (size_triangle_swap _ _ _))

namespace Proportional

theorem intro {p : X} {q : Y} {r : Z} {s : W} (hp : 0 < size p) (hq : 0 < size q)
    (hr : 0 < size r) (hs : 0 < size s)
    (h : Proportion (mag p hp) (mag q hq) (mag r hr) (mag s hs)) : p ∶ q ∷ r ∶ s :=
  ⟨hp, hq, hr, hs, h⟩

/-- The proportion of the magnitudes, whichever proofs of positivity are given. -/
theorem elim {p : X} {q : Y} {r : Z} {s : W} (h : p ∶ q ∷ r ∶ s) (hp : 0 < size p)
    (hq : 0 < size q) (hr : 0 < size r) (hs : 0 < size s) :
    Proportion (mag p hp) (mag q hq) (mag r hr) (mag s hs) :=
  let ⟨_, _, _, _, h⟩ := h; h

/-- Figures of equal sizes are proportional alike. -/
theorem congr {p p' : X} {q q' : Y} {r r' : Z} {s s' : W} (h : p ∶ q ∷ r ∶ s)
    (hp : size p = size p') (hq : size q = size q') (hr : size r = size r')
    (hs : size s = size s') : p' ∶ q' ∷ r' ∶ s' := by
  obtain ⟨hp₀, hq₀, hr₀, hs₀, h⟩ := h
  refine ⟨hp ▸ hp₀, hq ▸ hq₀, hr ▸ hr₀, hs ▸ hs₀, ?_⟩
  rwa [mag_congr hp.symm, mag_congr hq.symm, mag_congr hr.symm, mag_congr hs.symm]

end Proportional

/-! Def. 6.1: similar figures. -/

/--
Def. 6.1 for triangles: `abc` and `def` are similar, with the vertices in corresponding
order: equal angles, and the sides about the equal angles proportional.
-/
@[simp]
abbrev similarTriangles (a b c d e f : Point) : Prop :=
  equiangularTriangles a b c d e f ∧
  (a─b) ∶ (b─c) ∷ (d─e) ∶ (e─f) ∧ (b─c) ∶ (c─a) ∷ (e─f) ∶ (f─d) ∧
  (c─a) ∶ (a─b) ∷ (f─d) ∶ (d─e)

/-- Def. 6.1 for quadrilaterals `abcd` and `efgh`, similarly laid down. -/
@[simp]
abbrev similarQuadrilaterals (a b c d e f g h : Point) : Prop :=
  equiangularQuadrilaterals a b c d e f g h ∧
  (d─a) ∶ (a─b) ∷ (h─e) ∶ (e─f) ∧ (a─b) ∶ (b─c) ∷ (e─f) ∶ (f─g) ∧
  (b─c) ∶ (c─d) ∷ (f─g) ∶ (g─h) ∧ (c─d) ∶ (d─a) ∷ (g─h) ∶ (h─e)

/-- Def. 6.1 for pentagons `abcde` and `fghkl`, similarly laid down. -/
@[simp]
abbrev similarPentagons (a b c d e f g h k l : Point) : Prop :=
  equiangularPentagons a b c d e f g h k l ∧
  (e─a) ∶ (a─b) ∷ (l─f) ∶ (f─g) ∧ (a─b) ∶ (b─c) ∷ (f─g) ∶ (g─h) ∧
  (b─c) ∶ (c─d) ∷ (g─h) ∶ (h─k) ∧ (c─d) ∶ (d─e) ∷ (h─k) ∶ (k─l) ∧
  (d─e) ∶ (e─a) ∷ (k─l) ∶ (l─f)

/-- Def. 6.2: `ab` is cut at `c` in extreme and mean ratio, `ac` the greater segment: as
the whole is to the greater segment, so the greater is to the lesser. -/
@[simp]
abbrev extremeMeanRatio (a b c : Point) : Prop :=
  between a c b ∧ (a─b) ∶ (a─c) ∷ (a─c) ∶ (c─b)

end Elements.Book6
