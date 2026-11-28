import SystemE
import Elements.Book5.Prop12
import Elements.Book6.Prop06
import Elements.Book6.Prop19

namespace Elements.Book6

open Elements.Book5 Magnitude

/--
Similar pentagons `abcde`, `fghkl` (`ab` corresponding to `fg`) divide, by `BE`, `EC` and
`GL`, `LH`, into similar triangles: `abe` similar to `fgl` [Props. 6.6, 6.4]; the
remaining angles `ebc`, `lgh` are equal, and `eb : bc :: lg : gh` [Prop. 5.22], so `ebc`
is similar to `lgh`; and so `ecd` to `lhk`.
-/
theorem proposition_20_triangles :
  ∀ (a b c d e f g h k l : Point) (AB BC CD DE EA FG GH HK KL LF BE EC GL LH : Line),
  pentagon a b c d e AB BC CD DE EA ∧ pentagon f g h k l FG GH HK KL LF ∧
  similarPentagons a b c d e f g h k l ∧ distinctPointsOnLine b e BE ∧
  distinctPointsOnLine e c EC ∧ distinctPointsOnLine g l GL ∧
  distinctPointsOnLine l h LH →
  equiangularTriangles a b e f g l ∧ equiangularTriangles b e c g l h ∧
  equiangularTriangles c e d h l k :=
by
  euclid_intros
  -- `BAE` is equal to `GFL`, and `BA : AE :: GF : FL`: `ABE` is equiangular to `FGL`
  -- [Prop. 6.6]
  have h₁ := proposition_6 a b e f g l AB BE EA FG GL LF ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, ‹(e─a) ∶ (a─b) ∷ (l─f) ∶ (f─g)›.inv.congr
      (by size_perm) (by size_perm) (by size_perm) (by size_perm)⟩
  obtain ⟨-, h₂, -, -⟩ := proposition_4 a b e f g l AB BE EA FG GL LF (by euclid_finish)
  -- the whole angles `ABC`, `FGH` are equal, so the remaining `EBC`, `LGH`
  euclid_apply (sum_angles_onlyif b a c e AB BC)
  euclid_apply (sum_angles_onlyif g f h l FG GH)
  -- `EB : BA :: LG : GF` and `AB : BC :: FG : GH`: via equality, `EB : BC :: LG : GH`
  -- [Prop. 5.22], and `EBC` is equiangular to `LGH` [Prop. 6.6]
  have h₃ : (e─b) ∶ (a─b) ∷ (l─g) ∶ (f─g) :=
    h₂.inv.congr (by size_perm) rfl (by size_perm) rfl
  have h₃ := h₃.exAequali ‹(a─b) ∶ (b─c) ∷ (f─g) ∶ (g─h)›
  have h₄ := proposition_6 b e c g l h BE EC BC GL LH GH ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, h₃⟩
  obtain ⟨-, -, h₅, -⟩ := proposition_4 b e c g l h BE EC BC GL LH GH (by euclid_finish)
  -- so for `ECD`, `LHK`
  euclid_apply (sum_angles_onlyif c b d e BC CD)
  euclid_apply (sum_angles_onlyif h g k l GH HK)
  have h₆ : (e─c) ∶ (b─c) ∷ (l─h) ∶ (g─h) :=
    h₅.congr rfl (by size_perm) rfl (by size_perm)
  have h₆ := h₆.exAequali ‹(b─c) ∶ (c─d) ∷ (g─h) ∶ (h─k)›
  have h₇ := proposition_6 c e d h l k EC DE CD LH KL HK ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, h₆⟩
  exact ⟨by euclid_finish, by euclid_finish, h₇⟩

/--
Similar polygons divide into equally many similar triangles, in proportion to the wholes,
and one polygon has to the other the squared ratio of corresponding sides. For pentagons
`abcde`, `fghkl`, as in Euclid's figure: the triangles `eab`, `ebc`, `ecd` (the pentagon
`⬠e:a:b:c:d`) are similar to `lfg`, `lgh`, `lhk`, and in proportion to them, and the
pentagons are in the squared ratio of `ab : fg`. Euclid shows the triangles proportional
through the diagonals `AC`, `FH`; here by Prop. 6.19, each pair being in the squared
ratio of the same diagonals.
-/
theorem proposition_20 :
  ∀ (a b c d e f g h k l : Point) (AB BC CD DE EA FG GH HK KL LF : Line),
  pentagon a b c d e AB BC CD DE EA ∧ pentagon f g h k l FG GH HK KL LF ∧
  similarPentagons a b c d e f g h k l →
  similarTriangles e a b l f g ∧ similarTriangles e b c l g h ∧
  similarTriangles e c d l h k ∧
  △e:a:b ∶ △l:f:g ∷ △e:b:c ∶ △l:g:h ∧ △e:a:b ∶ △l:f:g ∷ △e:c:d ∶ △l:h:k ∧
  △e:a:b ∶ △l:f:g ∷ ⬠e:a:b:c:d ∶ ⬠l:f:g:h:k ∧
  SquaredRatio' (⬠e:a:b:c:d) (⬠l:f:g:h:k) (a─b) (f─g) :=
by
  euclid_intros
  -- join `BE`, `EC`, `GL`, `LH`
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points e c) as EC
  euclid_apply (line_from_points g l) as GL
  euclid_apply (line_from_points l h) as LH
  obtain ⟨h₁, h₂, h₃⟩ := proposition_20_triangles a b c d e f g h k l AB BC CD DE EA FG GH
    HK KL LF BE EC GL LH (by euclid_finish)
  have s₁ := proposition_4 e a b l f g EA AB BE LF FG GL (by euclid_finish)
  have s₂ := proposition_4 e b c l g h BE BC EC GL GH LH (by euclid_finish)
  have s₃ := proposition_4 e c d l h k EC CD DE LH HK KL (by euclid_finish)
  -- `ABE : FGL` and `EBC : LGH` are the squared ratio of `BE : GL`, and `EBC : LGH`,
  -- `ECD : LHK` of `EC : LH` [Prop. 6.19]: the same ratios
  have q₁ := proposition_19 a b e f g l AB BE EA FG GL LF
    ⟨by euclid_finish, by euclid_finish, proposition_4 a b e f g l AB BE EA FG GL LF
      (by euclid_finish)⟩
  have q₂ := proposition_19 c e b h l g EC BE BC LH GL GH
    ⟨by euclid_finish, by euclid_finish, proposition_4 c e b h l g EC BE BC LH GL GH
      (by euclid_finish)⟩
  have q₃ := proposition_19 b c e g h l BC EC BE GH LH GL
    ⟨by euclid_finish, by euclid_finish, proposition_4 b c e g h l BC EC BE GH LH GL
      (by euclid_finish)⟩
  have q₄ := proposition_19 d e c k l h DE EC CD KL LH HK
    ⟨by euclid_finish, by euclid_finish, proposition_4 d e c k l h DE EC CD KL LH HK
      (by euclid_finish)⟩
  have hbe := q₁.2.2.1
  have hgl := q₁.2.2.2.1
  have hec := q₃.2.2.1
  have hlh := q₃.2.2.2.1
  have r₁ := q₁.same q₂ (Proportional.refl hbe hgl |>.congr rfl rfl (by size_perm)
    (by size_perm))
  have r₂ := q₃.same q₄ (Proportional.refl hec hlh |>.congr rfl rfl (by size_perm)
    (by size_perm))
  have t₁ : △e:a:b ∶ △l:f:g ∷ △e:b:c ∶ △l:g:h :=
    r₁.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  have t₂ : △e:b:c ∶ △l:g:h ∷ △e:c:d ∶ △l:h:k :=
    r₂.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  -- as one of the leading is to one of the following, so are all the leading to all
  -- the following [Prop. 5.12]
  obtain ⟨heab, hlfg, hebc, hlgh, t₁'⟩ := t₁
  obtain ⟨hebc', hlgh', hecd, hlhk, t₂'⟩ := t₂
  have t₃ := Elements.Book5.proposition_12 (n := 2)
    (a := three (mag (△e:a:b) heab) (mag (△e:b:c) hebc) (mag (△e:c:d) hecd))
    (b := three (mag (△l:f:g) hlfg) (mag (△l:g:h) hlgh) (mag (△l:h:k) hlhk))
    (fun i => match i with
      | 0 => Proportion.refl _ _ | 1 => t₁' | 2 => Elements.Book5.proposition_11 t₁' t₂')
  rw [sum_three, sum_three] at t₃
  have hp : 0 < size (⬠e:a:b:c:d) := add_pos (add_pos heab hebc) hecd
  have hq : 0 < size (⬠l:f:g:h:k) := add_pos (add_pos hlfg hlgh) hlhk
  rw [mag_add (r := □e:a:b:c) (hr := add_pos heab hebc) rfl,
    mag_add (r := ⬠e:a:b:c:d) (hr := hp) rfl,
    mag_add (r := □l:f:g:h) (hr := add_pos hlfg hlgh) rfl,
    mag_add (r := ⬠l:f:g:h:k) (hr := hq) rfl] at t₃
  have t₄ : △e:a:b ∶ △l:f:g ∷ ⬠e:a:b:c:d ∶ ⬠l:f:g:h:k := ⟨heab, hlfg, hp, hq, t₃⟩
  -- and `ABE : FGL` is the squared ratio of `AB : FG` [Prop. 6.19]: so is the pentagons'
  have q₅ := proposition_19 e a b l f g EA AB BE LF FG GL (by euclid_finish)
  exact ⟨s₁, s₂, s₃, ⟨heab, hlfg, hebc, hlgh, t₁'⟩,
    ⟨heab, hlfg, hecd, hlhk, Elements.Book5.proposition_11 t₁' t₂'⟩, t₄, q₅.congr t₄⟩

/--
Corollary: in the same manner, similar quadrilaterals `abcd`, `efgh` are in the squared
ratio of corresponding sides, `ab : ef`, divided by `BD`, `FH` into similar triangles
`dab`, `dbc` and `hef`, `hfg` (the quadrilateral `□d:a:b:c`).
-/
theorem proposition_20_corollary :
  ∀ (a b c d e f g h : Point) (AB BC CD DA EF FG GH HE : Line),
  quadrilateral a b c d AB BC CD DA ∧ quadrilateral e f g h EF FG GH HE ∧
  similarQuadrilaterals a b c d e f g h →
  similarTriangles d a b h e f ∧ similarTriangles d b c h f g ∧
  △d:a:b ∶ △h:e:f ∷ △d:b:c ∶ △h:f:g ∧ △d:a:b ∶ △h:e:f ∷ □d:a:b:c ∶ □h:e:f:g ∧
  SquaredRatio' (□d:a:b:c) (□h:e:f:g) (a─b) (e─f) :=
by
  euclid_intros
  euclid_apply (line_from_points b d) as BD
  euclid_apply (line_from_points f h) as FH
  euclid_apply (sum_angles_onlyif b a c d AB BC)
  euclid_apply (sum_angles_onlyif f e g h EF FG)
  -- `ABD` is equiangular to `EFH` [Prop. 6.6]
  have h₁ := proposition_6 a b d e f h AB BD DA EF FH HE ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, ‹(d─a) ∶ (a─b) ∷ (h─e) ∶ (e─f)›.inv.congr
      (by size_perm) (by size_perm) (by size_perm) (by size_perm)⟩
  obtain ⟨-, h₂, -, -⟩ := proposition_4 a b d e f h AB BD DA EF FH HE (by euclid_finish)
  -- `DB : BC :: HF : FG` [Prop. 5.22], and `DBC` is equiangular to `HFG` [Prop. 6.6]
  have h₃ : (d─b) ∶ (a─b) ∷ (h─f) ∶ (e─f) :=
    h₂.inv.congr (by size_perm) rfl (by size_perm) rfl
  have h₄ := proposition_6 b d c f h g BD CD BC FH GH FG ⟨by euclid_finish,
    by euclid_finish, by euclid_finish, h₃.exAequali ‹(a─b) ∶ (b─c) ∷ (e─f) ∶ (f─g)›⟩
  have s₁ := proposition_4 d a b h e f DA AB BD HE EF FH (by euclid_finish)
  have s₂ := proposition_4 d b c h f g BD BC CD FH FG GH (by euclid_finish)
  -- `DAB : HEF` and `DBC : HFG` are the squared ratio of `BD : FH` [Prop. 6.19]
  have q₁ := proposition_19 a b d e f h AB BD DA EF FH HE
    ⟨by euclid_finish, by euclid_finish, proposition_4 a b d e f h AB BD DA EF FH HE
      (by euclid_finish)⟩
  have q₂ := proposition_19 c d b g h f CD BD BC GH FH FG
    ⟨by euclid_finish, by euclid_finish, proposition_4 c d b g h f CD BD BC GH FH FG
      (by euclid_finish)⟩
  have r₁ := q₁.same q₂ (Proportional.refl q₁.2.2.1 q₁.2.2.2.1 |>.congr rfl rfl
    (by size_perm) (by size_perm))
  have t₁ : △d:a:b ∶ △h:e:f ∷ △d:b:c ∶ △h:f:g :=
    r₁.congr (by size_perm) (by size_perm) (by size_perm) (by size_perm)
  -- all the leading to all the following [Prop. 5.12]
  obtain ⟨hdab, hhef, hdbc, hhfg, t₁'⟩ := t₁
  have t₂ := Elements.Book5.proposition_12 (n := 1)
    (a := two (mag (△d:a:b) hdab) (mag (△d:b:c) hdbc))
    (b := two (mag (△h:e:f) hhef) (mag (△h:f:g) hhfg))
    (fun i => match i with | 0 => Proportion.refl _ _ | 1 => t₁')
  rw [sum_two, sum_two] at t₂
  have hp : 0 < size (□d:a:b:c) := add_pos hdab hdbc
  have hq : 0 < size (□h:e:f:g) := add_pos hhef hhfg
  rw [mag_add (r := □d:a:b:c) (hr := hp) rfl, mag_add (r := □h:e:f:g) (hr := hq) rfl]
    at t₂
  have t₃ : △d:a:b ∶ △h:e:f ∷ □d:a:b:c ∶ □h:e:f:g := ⟨hdab, hhef, hp, hq, t₂⟩
  -- and `DAB : HEF` is the squared ratio of `AB : EF` [Prop. 6.19]
  have q₃ := proposition_19 d a b h e f DA AB BD HE EF FH (by euclid_finish)
  exact ⟨s₁, s₂, ⟨hdab, hhef, hdbc, hhfg, t₁'⟩, t₃, q₃.congr t₃⟩

end Elements.Book6
