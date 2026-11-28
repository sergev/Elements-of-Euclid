import SystemE
import Elements.Book1.Prop14
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book1.Prop33
import Elements.Book1.Prop34
import Elements.Book1.Prop44
import Elements.Book6.Prop01
import Elements.Book6.Prop13
import Elements.Book6.Prop18
import Elements.Book6.Prop19
import Elements.Book6.Prop21
import Elements.Book4.Lemmas

namespace Elements.Book6

open Elements.Book5 Magnitude

/--
Prop. 1.45 applied to a given straight line `lc`, as Prop. 6.25 uses it: a parallelogram
`l l₂ c m₂` on `lc`, away from `x`, with the angle at `c` equal to `e₁e₂e₃`, equal to the
quadrilateral of the triangles `d₁d₂d₄`, `d₄d₂d₃`. Book 1's proof, its first parallelogram
applied to `lc` [Prop. 1.44].
-/
theorem proposition_25_apply : ∀ (c l x d₁ d₂ d₃ d₄ e₁ e₂ e₃ : Point)
    (CL D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ E₁₂ E₂₃ : Line),
  distinctPointsOnLine c l CL ∧ ¬(x.onLine CL) ∧ formTriangle d₁ d₂ d₄ D₁₂ D₂₄ D₄₁ ∧
  formTriangle d₄ d₂ d₃ D₂₄ D₂₃ D₃₄ ∧ formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧
  ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (l₂ m₂ : Point) (LL CM LM : Line), m₂.opposingSides x CL ∧
  formParallelogram l l₂ c m₂ LL CM CL LM ∧ ∠ l:c:m₂ = ∠ e₁:e₂:e₃ ∧
  ▱ l:l₂:c:m₂ = Triangle.area △d₁:d₂:d₄ + Triangle.area △d₄:d₂:d₃ :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_44' l c d₁ d₂ d₄ e₁ e₂ e₃ x CL D₁₂ D₂₄ D₄₁ E₁₂
    E₂₃) as (m₁, l₁, CM, LL, ML)
  euclid_apply (Elements.Book1.proposition_44' l₁ m₁ d₄ d₂ d₃ e₁ e₂ e₃ c ML D₂₄ D₂₃ D₃₄
    E₁₂ E₂₃) as (m₂, l₂, HM, G, LM)
  euclid_assert ∠ m₁:c:l = ∠ l₁:m₁:m₂
  euclid_assert ∠ m₁:c:l + ∠ c:m₁:l₁ = ∠ l₁:m₁:m₂ + ∠ c:m₁:l₁
  euclid_apply (Elements.Book1.proposition_29_interior l l₁ c m₁ CL ML CM)
  euclid_assert ∠ c:m₁:l₁ + ∠ l₁:m₁:m₂ = ∟ + ∟
  euclid_apply (Elements.Book1.proposition_14 l₁ m₁ c m₂ ML CM HM)
  euclid_apply (Elements.Book1.proposition_29_alternate l m₂ l₁ m₁ LL HM ML)
  euclid_assert ∠ m₂:m₁:l₁ + ∠ m₁:l₁:l₂ = ∠ m₁:l₁:l + ∠ m₁:l₁:l₂
  euclid_apply (Elements.Book1.proposition_29_interior l₂ m₂ l₁ m₁ G HM ML)
  euclid_assert ∠ m₁:l₁:l + ∠ m₁:l₁:l₂ = ∟ + ∟
  euclid_apply (Elements.Book1.proposition_14 m₁ l₁ l l₂ ML LL G)
  euclid_apply (Elements.Book1.proposition_34' l l₁ c m₁ LL CM CL ML)
  euclid_apply (Elements.Book1.proposition_34' m₁ m₂ l₁ l₂ HM G ML LM)
  euclid_assert |(c─l)| = |(m₂─l₂)|
  euclid_apply (Elements.Book1.proposition_30 CL LM ML)
  euclid_assert |(l─l₂)| = |(c─m₂)|
  euclid_apply (Elements.Book1.proposition_33 l l₂ c m₂ LL CM CL LM)
  euclid_apply (sum_parallelograms_area l l₂ c m₂ l₁ m₁ LL CM CL LM)
  use l₂, m₂, LL, CM, LM
  euclid_finish

/--
To construct a figure similar to a given one, the triangle `abc`, and equal to another,
`D`, the quadrilateral of the triangles `d₁d₂d₄`, `d₄d₂d₃` (as Prop. 1.45 takes it).
-/
theorem proposition_25 : ∀ (a b c d₁ d₂ d₃ d₄ : Point)
    (AB BC CA D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ : Line),
  formTriangle a b c AB BC CA ∧ formTriangle d₁ d₂ d₄ D₁₂ D₂₄ D₄₁ ∧
  formTriangle d₄ d₂ d₃ D₂₄ D₂₃ D₃₄ ∧ d₁.opposingSides d₃ D₂₄ →
  ∃ (k x y : Point) (XY YK KX : Line), formTriangle x y k XY YK KX ∧
  similarTriangles a b c k x y ∧
  Triangle.area △k:x:y = Triangle.area △d₁:d₂:d₄ + Triangle.area △d₄:d₂:d₃ :=
by
  euclid_intros
  -- the parallelogram `BE` (`bmcl`) applied to `BC` equal to `ABC` [Prop. 1.44]
  have := angle_pos_of_not_on_line b c a BC (by euclid_finish)
  euclid_apply (Elements.Book4.angle_lt_flat a b c BC)
  euclid_apply (Elements.Book1.proposition_44' c b a b c a b c a BC AB BC CA AB BC)
    as (m, l, BM, CL, ML)
  -- and `CM` (`l l₂ c f`) applied to `CE` (`cl`) equal to `D`, in the angle `FCE` equal
  -- to `CBL` [Prop. 1.45]
  have := angle_pos_of_not_on_line b c m BC (by euclid_finish)
  euclid_apply (Elements.Book4.angle_lt_flat m b c BC)
  euclid_apply (proposition_25_apply c l b d₁ d₂ d₃ d₄ c b m CL D₁₂ D₂₄ D₄₁ D₂₃ D₃₄ BC BM)
    as (l₂, f, LL, CF, LM)
  -- `BC` is straight-on to `CF`, and `LE` to `EM` [Prop. 1.14]
  euclid_apply (Elements.Book1.proposition_29_interior m l b c BM CL BC)
  euclid_apply (Elements.Book1.proposition_14 l c b f CL BC CF)
  euclid_apply (parallel_line_unique l BC ML LL)
  euclid_assert between b c f
  -- `BC : CF :: BE : EF` [Prop. 6.1]
  have h₁ := proposition_1' l b c f m l₂ ML BC BM CL LM (by euclid_finish)
  euclid_apply (parallelogram_area l l₂ c f ML BC CL LM)
  -- `GH` the mean proportional to `BC`, `CF` [Prop. 6.13], and on it `KGH` similar and
  -- similarly laid down to `ABC` [Prop. 6.18]
  obtain ⟨x, y, h₂⟩ := proposition_13 b c c f (by euclid_finish)
  have hxy : x ≠ y := size_segment_pos.mp h₂.2.2.1
  euclid_apply (line_from_points x y) as XY
  obtain ⟨k, YK, KX, hk, s₁⟩ := proposition_18_triangle x y b c a XY BC CA AB
    (by euclid_finish)
  have s₂ := similarTriangles_rot b c a x y k BC CA AB XY YK KX ⟨by euclid_finish,
    by euclid_finish, s₁⟩
  have s₃ := similarTriangles_rot c a b y k x CA AB BC YK KX XY ⟨by euclid_finish,
    by euclid_finish, s₂⟩
  -- `BC : CF :: ABC : KGH` [Prop. 6.19 corollary], so `ABC : KGH :: BE : EF`
  -- [Prop. 5.11], and alternately `ABC : BE :: KGH : EF` [Prop. 5.16]
  have h₃ := proposition_19_corollary a b c k x y c f AB BC CA KX XY YK
    ⟨by euclid_finish, by euclid_finish, s₃, h₂⟩
  have h₄ := (h₃.symm.trans h₁).alt
  -- `ABC` is equal to `BE`, so `KGH` is equal to `EF` [Def. 5.5], which is equal to `D`
  obtain ⟨habc, hbe, hkxy, hef, h₄⟩ := h₄
  have e₁ : size (△a:b:c) = size (□m:b:c:l) := by
    rw [size_quadrilateral, size_triangle]
    have := area_symm_1 m b c
    have := area_symm_2 c b m
    have := area_symm_1 m c l
    have := area_symm_1 l m c
    linarith
  have e₂ := (h₄.eq 1 1).mp (by rw [one_mult, one_mult]; exact mag_congr e₁)
  rw [one_mult, one_mult] at e₂
  have e₂ : size (△k:x:y) = size (□l₂:l:c:f) := mag_inj.mp e₂
  refine ⟨k, x, y, XY, YK, KX, by euclid_finish, s₃, ?_⟩
  rw [size_triangle, size_quadrilateral] at e₂
  have := area_symm_2 l c f
  have := area_symm_2 l f l₂
  have := area_symm_1 l₂ l c
  linarith

end Elements.Book6
