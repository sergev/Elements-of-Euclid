import SystemE
import Elements.Book1.Prop29
import Elements.Book1.Prop30
import Elements.Book6.Prop04
import Elements.Book6.Prop12
import Elements.Book6.Prop21

namespace Elements.Book6

open Elements.Book5

/--
Prop. 6.24 for the parallelogram `aefg` about the diagonal `ac` of the parallelogram
`abdc` at `a`: `EF` parallel to `BC`, `FG` to `CD`. It is similar to the whole.
-/
theorem proposition_24_one : ∀ (a b c d e f g : Point) (AB CD DA BC EF FG : Line),
  formParallelogram a b d c AB CD DA BC ∧ between a f c ∧ e.onLine AB ∧ e.onLine EF ∧
  f.onLine EF ∧ ¬(EF.intersectsLine BC) ∧ g.onLine DA ∧ g.onLine FG ∧ f.onLine FG ∧
  ¬(FG.intersectsLine CD) → similarQuadrilaterals a b c d a e f g :=
by
  euclid_intros
  euclid_apply (line_from_points a c) as AC
  euclid_assert between a e b
  euclid_assert between a g d
  euclid_apply (Elements.Book1.proposition_30 FG AB CD)
  euclid_apply (Elements.Book1.proposition_30 EF DA BC)
  euclid_assert e.sameSide a FG
  euclid_assert g.sameSide a EF
  -- `EF` is parallel to the side `BC` of the triangle `ABC`: `BE : EA :: CF : FA`, and
  -- `FG` to the side `CD` of `ACD`: `CF : FA :: DG : GA` [Prop. 6.2]
  have h₁ := proposition_2 a b c e f AB BC AC EF (by euclid_finish)
  have h₂ := proposition_2 a c d f g AC CD DA FG (by euclid_finish)
  -- so `BE : EA :: DG : GA`; composing, `BA : AE :: DA : AG` [Prop. 5.18], and
  -- alternately `BA : AD :: EA : AG` [Prop. 5.16]
  have h₃ := (componendo a b d e g ⟨by euclid_finish, by euclid_finish, h₁.trans h₂⟩).alt
  -- `AFG` is equal to `DCA`, and `AFE` to `BCA` [Prop. 1.29]; `ADC` is equiangular to
  -- `AGF`, and `ACB` to `AFE` [Prop. 1.32]
  euclid_apply (Elements.Book1.proposition_29_exterior g d a f c FG CD AC)
  euclid_apply (Elements.Book1.proposition_29_exterior e b a f c EF BC AC)
  euclid_apply (equal_angles c f a d d AC CD)
  euclid_apply (equal_angles c f a b b AC BC)
  euclid_apply (equal_angles a b e d g AB DA)
  euclid_apply (equal_angles a d g c f DA AC)
  euclid_apply (equal_angles a b e c f AB AC)
  euclid_apply (line_from_points a f) as AF
  euclid_apply (triangle_angles a d c DA CD AC)
  euclid_apply (triangle_angles a g f DA FG AC)
  euclid_apply (triangle_angles a c b AC BC AB)
  euclid_apply (triangle_angles a f e AC EF AB)
  euclid_apply (sum_angles_onlyif c b d a BC CD)
  euclid_apply (sum_angles_onlyif f e g a EF FG)
  -- `AD : DC :: AG : GF`, `DC : CA :: GF : FA`, `AC : CB :: AF : FE`,
  -- `CB : BA :: FE : EA` [Prop. 6.4]
  obtain ⟨-, h₄, h₅, -⟩ := proposition_4 a d c a g f DA CD AC DA FG AC (by euclid_finish)
  obtain ⟨-, h₆, h₇, -⟩ := proposition_4 a c b a f e AC BC AB AC EF AB (by euclid_finish)
  -- via equality, `DC : CB :: GF : FE` [Prop. 5.22]
  have h₈ := h₅.exAequali (h₆.congr (by size_perm) rfl (by size_perm) rfl)
  refine ⟨by euclid_finish, ?_, ?_, ?_, ?_⟩
  · exact h₃.inv.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  · exact h₇.inv.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  · exact h₈.inv.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  · exact h₄.inv.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)

/--
In any parallelogram `abdc` (vertices `a`, `b`, `c`, `d` in order) the parallelograms
about the diagonal `ac`, `aefg` and `fkch`, are similar to the whole, and to one another.
`EH` through `f` is parallel to `BC`, and `GK` to `AB`.
-/
theorem proposition_24 : ∀ (a b c d e f g h k : Point) (AB CD DA BC EH GK : Line),
  formParallelogram a b d c AB CD DA BC ∧ between a f c ∧ e.onLine AB ∧ h.onLine CD ∧
  e.onLine EH ∧ f.onLine EH ∧ h.onLine EH ∧ ¬(EH.intersectsLine BC) ∧ g.onLine DA ∧
  k.onLine BC ∧ g.onLine GK ∧ f.onLine GK ∧ k.onLine GK ∧ ¬(GK.intersectsLine AB) →
  similarQuadrilaterals a b c d a e f g ∧ similarQuadrilaterals a b c d f k c h ∧
  similarQuadrilaterals a e f g f k c h :=
by
  euclid_intros
  euclid_apply (Elements.Book1.proposition_30 EH DA BC)
  euclid_apply (Elements.Book1.proposition_30 GK CD AB)
  have s₁ := proposition_24_one a b c d e f g AB CD DA BC EH GK (by euclid_finish)
  -- so for the same reasons, `KH` is similar to `ABCD`
  have s₂ := proposition_24_one c d a b h f k CD AB BC DA EH GK (by euclid_finish)
  have s₂ := similarQuadrilaterals_rot (similarQuadrilaterals_rot s₂)
  -- so `EG`, `HK` are similar to one another [Prop. 6.21]
  exact ⟨s₁, s₂, proposition_21' a e f g a b c d f k c h
    ⟨similarQuadrilaterals_symm s₁, similarQuadrilaterals_symm s₂⟩⟩

end Elements.Book6
