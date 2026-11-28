import SystemE.Theory

/-!
Book 3's definitions, over System E's relations. In System E, `L.intersectsCircle α`
and `α.intersectsCircle β` mean that they *cut*, at two points.
-/

namespace Line

/--
Def. 3.2: `L` touches `α` at `a`: it meets the circle there and, being produced,
does not cut it. Every other point of `L` is then outside `α` (`outside_of_touches`).
-/
@[simp]
abbrev touchesCircleAt (L : Line) (α : Circle) (a : Point) : Prop :=
  a.onLine L ∧ a.onCircle α ∧ ¬(L.intersectsCircle α)

end Line

namespace Circle

/-- Def. 3.3: `α` and `β` touch at `a`: they meet there and do not cut. -/
@[simp]
abbrev touchesCircleAt (α β : Circle) (a : Point) : Prop :=
  α ≠ β ∧ a.onCircle α ∧ a.onCircle β ∧ ¬(α.intersectsCircle β)

/-- `α` touches `β` internally at `a`: `α` is within `β`, its inside inside `β`'s. -/
@[simp]
abbrev touchesInternallyAt (α β : Circle) (a : Point) : Prop :=
  α.touchesCircleAt β a ∧ ∀ x : Point, x.insideCircle α → x.insideCircle β

/-- `α` and `β` touch externally at `a`: each is outside the other, no point inside both. -/
@[simp]
abbrev touchesExternallyAt (α β : Circle) (a : Point) : Prop :=
  α.touchesCircleAt β a ∧ ∀ x : Point, x.insideCircle α → ¬(x.insideCircle β)

end Circle

/--
Def. 3.1: equal circles have equal radii; `c₁`, `c₂` are the centers of `α`, `β`,
and `p₁`, `p₂` points on them.
-/
@[simp]
abbrev equalCircles (α β : Circle) (c₁ p₁ c₂ p₂ : Point) : Prop :=
  c₁.isCentre α ∧ p₁.onCircle α ∧ c₂.isCentre β ∧ p₂.onCircle β ∧ |(c₁─p₁)| = |(c₂─p₂)|

/-- A line touching a circle at `a` has no other point on it. -/
theorem not_on_circle_of_touches : ∀ (a b : Point) (L : Line) (α : Circle),
    L.touchesCircleAt α a ∧ b.onLine L ∧ b ≠ a → ¬(b.onCircle α) := by
  intro a b L α ⟨⟨haL, haα, hL⟩, hbL, hba⟩ hbα
  obtain ⟨m, hmL, hm⟩ := exists_point_between_points_on_line L a b ⟨haL, hbL, hba.symm⟩
  have hin := circle_points_between a b m α
    ⟨fun h => h.2 haα, fun h => h.2 hbα, hm⟩
  exact hL (intersection_circle_line_2 m α L ⟨hin, hmL⟩)

/-- A line touching a circle at `a` is outside it elsewhere. -/
theorem outside_of_touches : ∀ (a b : Point) (L : Line) (α : Circle),
    L.touchesCircleAt α a ∧ b.onLine L ∧ b ≠ a → b.outsideCircle α := by
  intro a b L α ⟨⟨haL, haα, hL⟩, hbL, hba⟩
  exact ⟨fun h => hL (intersection_circle_line_2 b α L ⟨h, hbL⟩),
    not_on_circle_of_touches a b L α ⟨⟨haL, haα, hL⟩, hbL, hba⟩⟩

/-- A line meets a circle in at most two points. -/
theorem not_on_line_of_on_circle : ∀ (a b c : Point) (L : Line) (α : Circle),
    a.onLine L ∧ b.onLine L ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
    a ≠ b ∧ c ≠ a ∧ c ≠ b → ¬(c.onLine L) := by
  intro a b c L α ⟨haL, hbL, ha, hb, hc, hab, hca, hcb⟩ hcL
  obtain ⟨m, hmL, hm⟩ := exists_point_between_points_on_line L a b ⟨haL, hbL, hab⟩
  have hin := circle_points_between a b m α ⟨fun h => h.2 ha, fun h => h.2 hb, hm⟩
  have h1 := circle_line_intersections m a c L α ⟨hmL, haL, hcL, hin, ha, hc, hca.symm⟩
  have h2 := circle_line_intersections m b c L α ⟨hmL, hbL, hcL, hin, hb, hc, hcb.symm⟩
  exact between_not_trans a m b c ⟨hm, h1⟩ h2

theorem point_ne_of_centre : ∀ (a b : Point) (α : Circle),
    a.isCentre α ∧ ¬(b.isCentre α) → a ≠ b := fun _ _ _ ⟨h, hn⟩ e => hn (e ▸ h)

/--
Defs. 3.6 and 3.8: `c` is on the circumference of the segment of `α` cut off by the
chord `AB` on the side of `s`; the angle in the segment is then `∠ a:c:b`.
-/
@[simp]
abbrev Point.onSegment (c : Point) (α : Circle) (a b : Point) (AB : Line) (s : Point) : Prop :=
  distinctPointsOnLine a b AB ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧ c.sameSide s AB

/--
Def. 3.11: similar segments admit equal angles. The segment of `α` on the chord `AB` on
the side of `x`, and that of `β` on `CD` on the side of `y`, with `x`, `y` on them.
-/
@[simp]
abbrev similarSegments (α : Circle) (a b : Point) (AB : Line) (x : Point)
    (β : Circle) (c d : Point) (CD : Line) (y : Point) : Prop :=
  x.onSegment α a b AB x ∧ y.onSegment β c d CD y ∧ ∠ a:x:b = ∠ c:y:d
