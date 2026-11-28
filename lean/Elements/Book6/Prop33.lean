import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop23
import Elements.Book3.Axioms
import Elements.Book3.Prop20
import Elements.Book3.Prop26
import Elements.Book3.Prop27
import Elements.Book6.Lemmas

namespace Elements.Book6

open Elements.Book3

/-
Euclid lays off circumferences equal to `BC`, "any number whatsoever", one after another
round the circle, and the angles on them are equal [Prop. 3.27]: the angle and the
circumference together are equal multiples of `BGC` and `BC`. Past the whole circle they
are not angles of System E nor circumferences of Book 3, but they are reals: `Wound`
counts the semicircles they pass, a half-turn at a time, and what remains.
-/

/--
`x` within the angle `ugy` at the center: the angle `ugy` is made of `ugx`, `xgy`, and
the circumference `uy` of `ux`, `xy`. `x` is on `y`'s side of `GU`, and `GX` separates
`u` from `y`.
-/
theorem center_add : ∀ (g u x y : Point) (GU GX : Line) (α : Circle),
  g.isCentre α ∧ u.onCircle α ∧ x.onCircle α ∧ y.onCircle α ∧
  distinctPointsOnLine g u GU ∧ distinctPointsOnLine g x GX ∧ x.sameSide y GU ∧
  u.opposingSides y GX →
  ∠ u:g:y = ∠ u:g:x + ∠ x:g:y ∧ α.arc u y g = α.arc u x g + α.arc x y g :=
by
  euclid_intros
  euclid_apply (line_from_points u y) as UY
  euclid_apply (line_from_points g y) as GY
  euclid_apply (line_from_points u x) as UX
  euclid_apply (line_from_points x y) as XY
  -- `GX` cuts `UY` at `p`, inside the circle; `x` is beyond `p`
  euclid_apply (intersection_lines_opposing u y GX UY)
  euclid_apply (intersection_lines GX UY) as p
  euclid_apply (circle_points_between u y p α)
  euclid_apply (point_in_circle_onlyif g u p α)
  euclid_apply (point_on_circle_onlyif g u x α)
  euclid_assert p.sameSide x GU
  euclid_assert p ≠ g
  euclid_assert p ≠ x
  have : between g p x := by
    rcases between_points g p x GX (by euclid_finish) with _ | _ | _
    · assumption
    · exfalso; euclid_finish
    · exfalso
      euclid_apply (between_if g x p)
      euclid_finish
  euclid_apply (sum_angles_onlyif g u y x GU GY)
  euclid_apply (arc_add u y x g UY α)
  euclid_apply (arc_side u x y g UX α)
  euclid_apply (arc_side x y u g XY α)
  euclid_finish

/--
At the center `g` of `α`, on `GX`, on the side of `t`, an angle `xgy` equal to the angle
`bhc` at the center of an equal circle `β` [Prop. 1.23], with `y` on `α`: it stands on a
circumference equal to `bc` [Prop. 3.26].
-/
theorem lay_off : ∀ (b c g h x t : Point) (BC GX : Line) (α β : Circle),
  h.isCentre β ∧ b.onCircle β ∧ c.onCircle β ∧ distinctPointsOnLine b c BC ∧
  ¬(h.onLine BC) ∧ g.isCentre α ∧ x.onCircle α ∧ |(g─x)| = |(h─b)| ∧
  distinctPointsOnLine g x GX ∧ ¬(t.onLine GX) →
  ∃ y : Point, y.onCircle α ∧ y.sameSide t GX ∧ ∠ x:g:y = ∠ b:h:c ∧
  α.arc x y g = β.arc b c h :=
by
  euclid_intros
  euclid_apply (line_from_points h b) as HB
  euclid_apply (line_from_points h c) as HC
  euclid_apply (Elements.Book1.proposition_23_side g x h b c t GX HB HC) as k
  euclid_apply (line_from_points g k) as GK
  euclid_apply (extend_point GK k g) as w
  euclid_apply (intersection_circle_line_extending_points α GK g w) as y
  euclid_apply (equal_angles g x x k y GX GK)
  euclid_apply (line_from_points x y) as XY
  euclid_apply (proposition_26' x y b c g h XY BC α β)
  use y
  euclid_finish

/-- In equal circles, the greater angle at the center stands on the greater
circumference: Prop. 3.27's argument. -/
theorem arc_lt : ∀ (b c e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(g.onLine BC) ∧ ¬(h.onLine EF) ∧
  ∠ e:h:f < ∠ b:g:c → β.arc e f h < α.arc b c g :=
by
  euclid_intros
  euclid_apply (line_from_points g b) as GB
  -- `BGK` equal to `EHF`, on the side of `C`
  euclid_apply (lay_off e f g h b c EF GB α β) as k
  euclid_apply (line_from_points g k) as GK
  -- `GK` is within the angle `BGC`
  have : b.opposingSides c GK := by
    by_cases (c.onLine GK)
    · exfalso
      euclid_apply (equal_angles g b b k c GB GK)
      euclid_finish
    · by_cases (b.sameSide c GK)
      · exfalso
        euclid_apply (sum_angles_onlyif g b k c GB GK)
        euclid_finish
      · euclid_finish
  euclid_apply (center_add g b k c GB GK α)
  euclid_apply (line_from_points k c) as KC
  euclid_apply (arc_pos k c g KC α)
  euclid_finish

/-- A diameter `uv` cuts the circle in half [Def. 1.17]: each semicircle is half the
circumference. -/
theorem semicircle : ∀ (g u v t : Point) (L : Line) (α : Circle),
  g.isCentre α ∧ u.onCircle α ∧ v.onCircle α ∧ distinctPointsOnLine u v L ∧
  g.onLine L ∧ ¬(t.onLine L) → α.arc u v t + α.arc u v t = α.circumference :=
by
  euclid_intros
  -- `p`, `q` on the circle on either side of `uv`
  euclid_apply (line_from_points g t) as GT
  euclid_apply (extend_point GT t g) as w
  euclid_apply (intersection_circle_line_extending_points α GT g w) as p
  euclid_apply (intersection_circle_line_extending_points α GT g t) as q
  -- the angles in the semicircles at `p`, `q` are right [Prop. 3.31], so equal: their
  -- circumferences are equal [Prop. 3.26]
  euclid_apply (proposition_20'' p u v g L α)
  euclid_apply (proposition_20'' q u v g L α)
  euclid_apply (proposition_26 p u v q u v g g L L α α)
  euclid_apply (arc_whole u v p q L α)
  euclid_apply (arc_side u v t p L α)
  euclid_finish

/-- The semicircle `uv` on the side of `x` is made of the circumferences `ux`, `xv`. -/
theorem semicircle_add : ∀ (g u v x : Point) (L : Line) (α : Circle),
  g.isCentre α ∧ u.onCircle α ∧ v.onCircle α ∧ x.onCircle α ∧
  distinctPointsOnLine u v L ∧ g.onLine L ∧ ¬(x.onLine L) →
  α.arc u x g + α.arc x v g + (α.arc u x g + α.arc x v g) = α.circumference :=
by
  euclid_intros
  euclid_apply (exists_point_opposite L x) as s
  euclid_apply (semicircle g u v s L α)
  euclid_apply (circle_line_intersections g u v L α)
  euclid_apply (line_from_points u x) as UX
  euclid_apply (line_from_points x v) as XV
  euclid_apply (arc_add u v x s L α)
  euclid_apply (arc_side u x v g UX α)
  euclid_apply (arc_side x v u g XV α)
  euclid_finish

/--
`n` angles equal to `θ` and circumferences equal to `A`, laid round the circle `α`
(center `g`) one after another: they make `k` semicircles and two right angles `k` times,
and what remains. A diameter `uv` and `x` on the circle off it: the remainder is the angle
`ugx` and the circumference `ux`, or nothing.
-/
def Wound (α : Circle) (g : Point) (θ A : ℝ) (n : ℕ) : Prop :=
  ∃ (k : ℕ) (u v x : Point) (L : Line), u.onCircle α ∧ v.onCircle α ∧ x.onCircle α ∧
    distinctPointsOnLine u v L ∧ g.onLine L ∧ ¬(x.onLine L) ∧
    ((n * θ = k * (∟ + ∟) + ∠ u:g:x ∧
      n * A = k * (α.circumference / 2) + α.arc u x g) ∨
     (n * θ = k * (∟ + ∟) ∧ n * A = k * (α.circumference / 2)))

/-- No angle yet: the diameter through `b`. -/
theorem wound_zero : ∀ (b c g : Point) (BC : Line) (α : Circle),
  g.isCentre α ∧ b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c BC ∧
  ¬(g.onLine BC) → Wound α g (∠ b:g:c) (α.arc b c g) 0 :=
by
  euclid_intros
  euclid_apply (line_from_points g b) as GB
  euclid_apply (intersection_circle_line_extending_points α GB g b) as v
  refine ⟨0, b, v, c, GB, by euclid_finish, by euclid_finish, by euclid_finish,
    by euclid_finish, by euclid_finish, by euclid_finish, Or.inr ⟨by simp, by simp⟩⟩

/--
One more angle `xgy` equal to `bgc`, laid on from the last, `x`, away from `u`: it stays
within the semicircle, ends on the diameter at `v`, or passes it.
-/
theorem wound_succ (n : ℕ) : ∀ (b c g : Point) (BC : Line) (α : Circle),
  g.isCentre α ∧ b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c BC ∧
  ¬(g.onLine BC) ∧ Wound α g (∠ b:g:c) (α.arc b c g) n →
  Wound α g (∠ b:g:c) (α.arc b c g) (n + 1) :=
by
  euclid_intros
  obtain ⟨k, u, v, x, L, hu, hv, hx, hL, hgL, hxL, h⟩ :=
    ‹Wound α g (∠ b:g:c) (α.arc b c g) n›
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · euclid_apply (line_from_points g x) as M
    euclid_apply (circle_line_intersections g u v L α)
    euclid_apply (lay_off b c g g x v BC M α α) as y
    euclid_apply (Elements.Book1.proposition_13 x g u v M L)
    euclid_apply (semicircle_add g u v x L α)
    by_cases (y.onLine L)
    · -- `y` is `v`
      have : y = v := by
        by_contra
        euclid_apply (circle_line_intersections g u y L α)
        euclid_apply (circle_line_intersections g v y L α)
        euclid_finish
      subst this
      refine ⟨k + 1, y, u, x, L, by euclid_finish, by euclid_finish, by euclid_finish,
        by euclid_finish, by euclid_finish, by euclid_finish, Or.inr ⟨?_, ?_⟩⟩
      · push_cast; ring_nf; ring_nf at h₁ ⊢; linarith
      · push_cast; ring_nf; ring_nf at h₂ ⊢; linarith
    · by_cases (y.sameSide x L)
      · -- within the semicircle: `ugy` is made of `ugx`, `xgy`
        euclid_apply (center_add g u x y L M α)
        refine ⟨k, u, v, y, L, by euclid_finish, by euclid_finish, by euclid_finish,
          by euclid_finish, by euclid_finish, by euclid_finish, Or.inl ⟨?_, ?_⟩⟩
        · push_cast; ring_nf; ring_nf at h₁ ⊢; linarith
        · push_cast; ring_nf; ring_nf at h₂ ⊢; linarith
      · -- past `v`: `xgy` is made of `xgv`, `vgy`
        euclid_apply (center_add g x v y M L α)
        refine ⟨k + 1, v, u, y, L, by euclid_finish, by euclid_finish, by euclid_finish,
          by euclid_finish, by euclid_finish, by euclid_finish, Or.inl ⟨?_, ?_⟩⟩
        · push_cast; ring_nf; ring_nf at h₁ ⊢; linarith
        · push_cast; ring_nf; ring_nf at h₂ ⊢; linarith
  · -- from the diameter, on the side of `x`
    euclid_apply (lay_off b c g g u x BC L α α) as y
    refine ⟨k, u, v, y, L, by euclid_finish, by euclid_finish, by euclid_finish,
      by euclid_finish, by euclid_finish, by euclid_finish, Or.inl ⟨?_, ?_⟩⟩
    · push_cast; ring_nf; ring_nf at h₁ ⊢; linarith
    · push_cast; ring_nf; ring_nf at h₂ ⊢; linarith

/-- Any number of angles equal to `bgc` laid round. -/
theorem wound (n : ℕ) : ∀ (b c g : Point) (BC : Line) (α : Circle),
  g.isCentre α ∧ b.onCircle α ∧ c.onCircle α ∧ distinctPointsOnLine b c BC ∧
  ¬(g.onLine BC) → Wound α g (∠ b:g:c) (α.arc b c g) n :=
by
  induction n with
  | zero => exact wound_zero
  | succ n ih =>
    intro b c g BC α h
    exact wound_succ n b c g BC α ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
      ih b c g BC α h⟩

/-- What remains: nothing, or an angle `ugx` at the center and its circumference. -/
def Remainder (α : Circle) (g : Point) (ρ a : ℝ) : Prop :=
  (ρ = 0 ∧ a = 0) ∨ ∃ (u x : Point) (UX : Line), u.onCircle α ∧ x.onCircle α ∧
    distinctPointsOnLine u x UX ∧ ¬(g.onLine UX) ∧ ρ = ∠ u:g:x ∧ a = α.arc u x g

/-- The remainder is less than two right angles, and less than a semicircle. -/
theorem wound_remainder : ∀ (g : Point) (α : Circle) (θ A : ℝ) (n : ℕ),
  g.isCentre α ∧ Wound α g θ A n → ∃ (k : ℕ) (ρ a : ℝ),
  n * θ = k * (∟ + ∟) + ρ ∧ n * A = k * (α.circumference / 2) + a ∧
  0 ≤ ρ ∧ ρ < ∟ + ∟ ∧ 0 ≤ a ∧ a < α.circumference / 2 ∧ Remainder α g ρ a :=
by
  intro g α θ A n ⟨hg, k, u, v, x, L, hu, hv, hx, hL, hgL, hxL, h⟩
  euclid_apply (semicircle_add g u v x L α)
  euclid_apply (line_from_points u x) as UX
  euclid_apply (line_from_points x v) as XV
  euclid_apply (arc_pos u x g UX α)
  euclid_apply (arc_pos x v g XV α)
  euclid_apply (angle_range (Angle.ofPoints u g x))
  have : ∠ u:g:x ≠ 0 := by
    intro
    euclid_apply (degenerated_angle_onlyif g u x L)
    euclid_finish
  have : 0 < ∠ u:g:x := lt_of_le_of_ne (by linarith) (Ne.symm this)
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have : ∠ u:g:x ≠ ∟ + ∟ := by
      intro
      euclid_apply (flat_angle_if u g x)
      euclid_finish
    refine ⟨k, ∠ u:g:x, α.arc u x g, h₁, h₂, by euclid_finish,
      lt_of_le_of_ne (by euclid_finish) this, by linarith, by linarith,
      Or.inr ⟨u, x, UX, hu, hx, by euclid_finish, by euclid_finish, rfl, rfl⟩⟩
  · refine ⟨k, 0, 0, by linarith, by linarith, le_refl 0, by linarith, le_refl 0,
      by linarith, Or.inl ⟨rfl, rfl⟩⟩

/-- Remainders in equal circles: the greater angle has the greater circumference, and
equal angles equal circumferences [Props. 3.26, 3.27]. -/
theorem remainder_compare : ∀ (g h p q : Point) (α β : Circle) (ρ₁ a₁ ρ₂ a₂ : ℝ),
  g.isCentre α ∧ h.isCentre β ∧ p.onCircle α ∧ q.onCircle β ∧ |(g─p)| = |(h─q)| ∧
  Remainder α g ρ₁ a₁ ∧ Remainder β h ρ₂ a₂ →
  (ρ₁ < ρ₂ → a₁ < a₂) ∧ (ρ₁ = ρ₂ → a₁ = a₂) :=
by
  intro g h p q α β ρ₁ a₁ ρ₂ a₂ ⟨hg, hh, hp, hq, hpq, r₁, r₂⟩
  rcases r₁ with ⟨rfl, rfl⟩ | ⟨u, x, UX, hu, hx, hUX, hgUX, rfl, rfl⟩ <;>
    rcases r₂ with ⟨rfl, rfl⟩ | ⟨w, y, WY, hw, hy, hWY, hhWY, rfl, rfl⟩
  · exact ⟨fun h => absurd h (lt_irrefl 0), fun _ => rfl⟩
  · euclid_apply (arc_pos w y h WY β)
    have : ∠ w:h:y ≠ 0 := by
      intro
      euclid_apply (line_from_points h w) as HW
      euclid_apply (degenerated_angle_onlyif h w y HW)
      euclid_finish
    exact ⟨fun _ => ‹_›, fun h => absurd h.symm this⟩
  · euclid_apply (angle_range (Angle.ofPoints u g x))
    have : ∠ u:g:x ≠ 0 := by
      intro
      euclid_apply (line_from_points g u) as GU
      euclid_apply (degenerated_angle_onlyif g u x GU)
      euclid_finish
    exact ⟨fun h => absurd h (not_lt.mpr ‹_›), fun h => absurd h this⟩
  · euclid_apply (point_on_circle_onlyif g p u α)
    euclid_apply (point_on_circle_onlyif h q w β)
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · euclid_apply (arc_lt w y u x h g WY UX β α)
      euclid_finish
    · euclid_apply (proposition_26' u x w y g h UX WY α β)
      euclid_finish

/-- `k` semicircles and less, against `k'` and less: compared as the numbers `k`, `k'`,
and then as what remains. -/
theorem wound_lt {P ρ₁ ρ₂ : ℝ} {k₁ k₂ : ℕ} (hk : k₁ < k₂) (h₀ : 0 ≤ ρ₁) (h₁ : ρ₁ < P)
    (h₂ : 0 ≤ ρ₂) : k₁ * P + ρ₁ < k₂ * P + ρ₂ := by
  have : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast hk
  nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ P)]

theorem wound_compare {P S ρ₁ ρ₂ a₁ a₂ : ℝ} {k₁ k₂ : ℕ}
    (hρ₁ : 0 ≤ ρ₁ ∧ ρ₁ < P) (hρ₂ : 0 ≤ ρ₂ ∧ ρ₂ < P)
    (ha₁ : 0 ≤ a₁ ∧ a₁ < S) (ha₂ : 0 ≤ a₂ ∧ a₂ < S)
    (hlt : ρ₁ < ρ₂ → a₁ < a₂) (heq : ρ₁ = ρ₂ → a₁ = a₂) :
    (k₁ * P + ρ₁ < k₂ * P + ρ₂ → k₁ * S + a₁ < k₂ * S + a₂) ∧
    (k₁ * P + ρ₁ = k₂ * P + ρ₂ → k₁ * S + a₁ = k₂ * S + a₂) := by
  rcases lt_trichotomy k₁ k₂ with hk | rfl | hk
  · have := wound_lt hk hρ₁.1 hρ₁.2 hρ₂.1 (P := P)
    exact ⟨fun _ => wound_lt hk ha₁.1 ha₁.2 ha₂.1, fun h => absurd h (ne_of_lt this)⟩
  · exact ⟨fun h => by linarith [hlt (by linarith)],
      fun h => by linarith [heq (by linarith)]⟩
  · have := wound_lt hk hρ₂.1 hρ₂.2 hρ₁.1 (P := P)
    exact ⟨fun h => absurd h (not_lt.mpr (le_of_lt this)),
      fun h => absurd h.symm (ne_of_lt this)⟩

/-- In equal circles, `n` angles `θ₁` laid round and `m` angles `θ₂`: as the angles
together are greater or equal, so are their circumferences. -/
theorem wound_imp : ∀ (g h p q : Point) (α β : Circle) (θ₁ A₁ θ₂ A₂ : ℝ) (n m : ℕ),
  g.isCentre α ∧ h.isCentre β ∧ p.onCircle α ∧ q.onCircle β ∧ |(g─p)| = |(h─q)| ∧
  Wound α g θ₁ A₁ n ∧ Wound β h θ₂ A₂ m →
  (n * θ₁ < m * θ₂ → n * A₁ < m * A₂) ∧ (n * θ₁ = m * θ₂ → n * A₁ = m * A₂) :=
by
  intro g h p q α β θ₁ A₁ θ₂ A₂ n m ⟨hg, hh, hp, hq, hpq, w₁, w₂⟩
  obtain ⟨k₁, ρ₁, a₁, e₁, f₁, r₁, r₁', s₁, s₁', R₁⟩ := wound_remainder g α θ₁ A₁ n ⟨hg, w₁⟩
  obtain ⟨k₂, ρ₂, a₂, e₂, f₂, r₂, r₂', s₂, s₂', R₂⟩ := wound_remainder h β θ₂ A₂ m ⟨hh, w₂⟩
  obtain ⟨hlt, heq⟩ := remainder_compare g h p q α β ρ₁ a₁ ρ₂ a₂ ⟨hg, hh, hp, hq, hpq, R₁, R₂⟩
  -- the whole circles are equal
  have hC : α.circumference = β.circumference := circumference_eq g p h q α β
    ⟨hg, hp, hh, hq, hpq⟩
  rw [hC] at f₁ s₁'
  rw [e₁, e₂, f₁, f₂]
  exact wound_compare ⟨r₁, r₁'⟩ ⟨r₂, r₂'⟩ ⟨s₁, s₁'⟩ ⟨s₂, s₂'⟩ hlt heq

/-- Def. 5.5 for positive reals, in one direction (`Proportion.of_imp`). A fact of the
model: equal multiples of the angles and circumferences are their products by numbers
(`Positive.mult_val`), which `Wound` compares. -/
theorem proportion_of_val {a b c d : {x : ℝ // 0 < x}}
    (gt : ∀ m n : ℕ+, (n : ℝ) * b.val < m * a.val → (n : ℝ) * d.val < m * c.val)
    (eq : ∀ m n : ℕ+, (m : ℝ) * a.val = n * b.val → (m : ℝ) * c.val = n * d.val)
    (lt : ∀ m n : ℕ+, (m : ℝ) * a.val < n * b.val → (m : ℝ) * c.val < n * d.val) :
    Elements.Book5.Proportion a b c d :=
  Elements.Book5.Proportion.of_imp
    (fun m n h => by
      show (n • d).val < (m • c).val
      have h : (n • b).val < (m • a).val := h
      rw [Elements.Book5.Positive.mult_val, Elements.Book5.Positive.mult_val] at h ⊢
      exact gt m n h)
    (fun m n h => by
      have h := congrArg Subtype.val h
      rw [Elements.Book5.Positive.mult_val, Elements.Book5.Positive.mult_val] at h
      apply Subtype.ext
      rw [Elements.Book5.Positive.mult_val, Elements.Book5.Positive.mult_val]
      exact eq m n h)
    (fun m n h => by
      show (m • c).val < (n • d).val
      have h : (m • a).val < (n • b).val := h
      rw [Elements.Book5.Positive.mult_val, Elements.Book5.Positive.mult_val] at h ⊢
      exact lt m n h)

/--
In equal circles, the angles `bgc`, `ehf` at the centers have the same ratio as the
circumferences `bc`, `ef` on which they stand.
-/
theorem proposition_33 : ∀ (b c e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ b.onCircle α ∧ c.onCircle α ∧ e.onCircle β ∧
  f.onCircle β ∧ |(g─b)| = |(h─e)| ∧ distinctPointsOnLine b c BC ∧
  distinctPointsOnLine e f EF ∧ ¬(g.onLine BC) ∧ ¬(h.onLine EF) →
  ∡b:g:c ∶ ∡e:h:f ∷ ⌒α:b:c:g ∶ ⌒β:e:f:h :=
by
  euclid_intros
  euclid_apply (line_from_points g b) as GB
  euclid_apply (line_from_points h e) as HE
  euclid_apply (angle_range (Angle.ofPoints b g c))
  euclid_apply (angle_range (Angle.ofPoints e h f))
  have : ∠ b:g:c ≠ 0 := by
    intro
    euclid_apply (degenerated_angle_onlyif g b c GB)
    euclid_finish
  have : ∠ e:h:f ≠ 0 := by
    intro
    euclid_apply (degenerated_angle_onlyif h e f HE)
    euclid_finish
  euclid_apply (arc_pos b c g BC α)
  euclid_apply (arc_pos e f h EF β)
  have hθ₁ : 0 < size (∡b:g:c) := lt_of_le_of_ne ‹0 ≤ ∠ b:g:c› (Ne.symm ‹_›)
  have hθ₂ : 0 < size (∡e:h:f) := lt_of_le_of_ne ‹0 ≤ ∠ e:h:f› (Ne.symm ‹_›)
  have hA₁ : 0 < size (⌒α:b:c:g) := ‹_›
  have hA₂ : 0 < size (⌒β:e:f:h) := ‹_›
  -- take any equal multiples of the angle `bgc` and the circumference `bc`, laying
  -- circumferences equal to `bc` round the circle; likewise for `ehf`, `ef`
  have w₁ := fun n => wound n b c g BC α (by euclid_finish)
  have w₂ := fun n => wound n e f h EF β (by euclid_finish)
  -- as the angles together are greater, equal or less, so are the circumferences
  -- [Props. 3.26, 3.27]
  refine ⟨hθ₁, hθ₂, hA₁, hA₂, proportion_of_val (fun m n h' => ?_) (fun m n h' => ?_)
    (fun m n h' => ?_)⟩
  · exact (wound_imp h g e b β α _ _ _ _ n m ⟨‹_›, ‹_›, ‹_›, ‹_›,
      ‹|(g─b)| = |(h─e)|›.symm, w₂ n, w₁ m⟩).1 h'
  · exact (wound_imp g h b e α β _ _ _ _ m n ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, w₁ m, w₂ n⟩).2 h'
  · exact (wound_imp g h b e α β _ _ _ _ m n ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, w₁ m, w₂ n⟩).1 h'

/--
And the angles `bac`, `edf` at the circumferences, with the centers within them (the
circumferences less than semicircles, as in Euclid's figure): they are halves of those at
the centers [Prop. 3.20].
-/
theorem proposition_33' : ∀ (a b c d e f g h : Point) (BC EF : Line) (α β : Circle),
  g.isCentre α ∧ h.isCentre β ∧ a.onCircle α ∧ b.onCircle α ∧ c.onCircle α ∧
  d.onCircle β ∧ e.onCircle β ∧ f.onCircle β ∧ |(g─b)| = |(h─e)| ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧ g.sameSide a BC ∧
  h.sameSide d EF → ∡b:a:c ∶ ∡e:d:f ∷ ⌒α:b:c:a ∶ ⌒β:e:f:d :=
by
  euclid_intros
  have h₁ := proposition_33 b c e f g h BC EF α β (by euclid_finish)
  euclid_apply (proposition_20 a b c g BC α)
  euclid_apply (proposition_20 d e f h EF β)
  euclid_apply (arc_side b c a g BC α)
  euclid_apply (arc_side e f d h EF β)
  -- `bac` is half `bgc`, and `edf` half `ehf`: as `bac` is to `edf`, so `bgc` to `ehf`
  -- [Prop. 5.15]
  obtain ⟨hθ₁, hθ₂, -, -, -⟩ := id h₁
  have hx : 0 < size (∡b:a:c) := by
    rw [size_angle] at hθ₁ ⊢
    linarith
  have hy : 0 < size (∡e:d:f) := by
    rw [size_angle] at hθ₂ ⊢
    linarith
  have h₂ : ∡b:a:c ∶ ∡e:d:f ∷ ∡b:g:c ∶ ∡e:h:f := by
    refine ⟨hx, hy, hθ₁, hθ₂, proportion_of_val (fun m n h' => ?_) (fun m n h' => ?_)
      (fun m n h' => ?_)⟩ <;>
    · simp only [mag, Kind.of] at h' ⊢
      rw [size_angle, size_angle] at h' ⊢
      rw [‹∠ b:g:c = _›, ‹∠ e:h:f = _›]
      linarith
  exact (h₂.trans h₁).congr rfl rfl (by rw [size_arc, size_arc]; linarith)
    (by rw [size_arc, size_arc]; linarith)

end Elements.Book6
