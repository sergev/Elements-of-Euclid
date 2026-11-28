import SystemE
import Elements.Book1.Prop01
import Elements.Book1.Prop30
import Elements.Book1.Prop31
import Elements.Book1.Prop34
import Elements.Book6.Prop02

namespace Elements.Book6

open Elements.Book5

/--
To cut a given uncut straight line `ab` similarly to a given cut one `pq`, cut at `r`,
`s`: points `f`, `g` with `qs : sr :: bg : gf` and `sr : rp :: gf : fa`.
-/
theorem proposition_10 : ∀ (a b p r s q : Point) (AB PQ : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine p q PQ ∧ between p r s ∧
  between r s q →
  ∃ f g : Point, f.onLine AB ∧ g.onLine AB ∧ between a f g ∧ between f g b ∧
  (q─s) ∶ (s─r) ∷ (b─g) ∶ (g─f) ∧ (s─r) ∶ (r─p) ∷ (g─f) ∶ (f─a) :=
by
  euclid_intros
  -- let the cut line be laid down as `AC`, cut at `d`, `e`, at a random angle with `AB`
  euclid_apply (Elements.Book1.proposition_1 a b AB) as x
  euclid_apply (line_from_points a x) as AC
  euclid_apply (lay_on_ray a x p r AC) as d
  euclid_apply (lay_beyond a d r s AC) as e
  euclid_apply (lay_beyond d e s q AC) as c
  -- join `CB`; draw `DF`, `EG` through `d`, `e` parallel to `BC`, and `DHK` through `d`
  -- parallel to `AB` [Prop. 1.31]
  euclid_apply (line_from_points b c) as BC
  euclid_apply (Elements.Book1.proposition_31 d b c BC) as DF
  euclid_apply (Elements.Book1.proposition_31 e b c BC) as EG
  euclid_apply (Elements.Book1.proposition_31 d a b AB) as DK
  euclid_apply (parallel_meets b DF BC AB)
  euclid_apply (intersection_lines DF AB) as f
  euclid_apply (parallel_meets b EG BC AB)
  euclid_apply (intersection_lines EG AB) as g
  euclid_apply (parallel_meets g DK AB EG)
  euclid_apply (intersection_lines DK EG) as h
  euclid_apply (parallel_meets b DK AB BC)
  euclid_apply (intersection_lines DK BC) as k
  euclid_assert DF ≠ EG
  euclid_apply (Elements.Book1.proposition_30 DF EG BC)
  euclid_assert between a f g
  euclid_assert between f g b
  euclid_assert between d h k
  -- `FH`, `HB` are parallelograms: `DH` is equal to `FG`, and `HK` to `GB` [Prop. 1.34]
  euclid_apply (Elements.Book1.proposition_34' d h f g DK AB DF EG)
  euclid_apply (Elements.Book1.proposition_34' h k g b DK AB EG BC)
  -- `HE` is parallel to the side `KC` of the triangle `DKC`: `CE : ED :: KH : HD`
  -- [Prop. 6.2], that is, `BG : GF`
  have h₁ := proposition_2 d k c h e DK BC AC EG
    ⟨by euclid_finish, ‹_›, by euclid_finish, ‹_›, ‹_›, by euclid_finish⟩
  -- `FD` is parallel to the side `GE` of the triangle `AGE`: `ED : DA :: GF : FA`
  -- [Prop. 6.2]
  have h₂ := proposition_2 a g e f d AB EG AC DF
    ⟨by euclid_finish, ‹_›, by euclid_finish, ‹_›, ‹_›, by euclid_finish⟩
  have e₁ : size (c─e) = size (q─s) := by
    rw [size_segment, size_segment, segment_symmetric c e]; euclid_finish
  have e₂ : size (e─d) = size (s─r) := by
    rw [size_segment, size_segment, segment_symmetric e d]; euclid_finish
  have e₃ : size (d─a) = size (r─p) := by
    rw [size_segment, size_segment, segment_symmetric d a]; euclid_finish
  have e₄ : size (k─h) = size (b─g) := by
    rw [size_segment, size_segment, segment_symmetric k h]; euclid_finish
  have e₅ : size (h─d) = size (g─f) := by
    rw [size_segment, size_segment, segment_symmetric h d]; euclid_finish
  exact ⟨f, g, ‹_›, ‹_›, ‹_›, ‹_›, h₁.symm.congr e₁ e₂ e₄ e₅,
    h₂.symm.congr e₂ e₃ rfl rfl⟩

end Elements.Book6
