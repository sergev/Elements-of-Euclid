import SystemE
import Elements.Book1.Prop13
import Elements.Book1.Prop14
import Elements.Book6.Prop01
import Elements.Book6.Prop12

namespace Elements.Book6

open Elements.Book5

/--
Equiangular parallelograms `abcd`, `cegf` (with the equal angles `bcd`, `ecg` at `c`)
have to one another the ratio compounded of their sides, `bc : cg` and `dc : ce`. They
are laid down as Euclid lays them, `bc` straight-on to `cg`.
-/
theorem proposition_23 : ∀ (a b c d e f g : Point) (AD BG AB DE GF FE : Line),
  formParallelogram a d b c AD BG AB DE ∧ formParallelogram g f c e GF DE BG FE ∧
  between b c g ∧ d.opposingSides e BG ∧ ∠ b:c:d = ∠ g:c:e →
  CompoundRatio' (□a:b:c:d) (□f:g:c:e) (b─c) (c─g) (d─c) (c─e) :=
by
  euclid_intros
  -- `DC` is straight-on to `CE` [Prop. 1.14]; complete the parallelogram `DG`, `dchg`
  euclid_apply (Elements.Book1.proposition_13 d c g b DE BG)
  euclid_apply (between_if b c g)
  have : between d c e := by
    by_contra
    euclid_apply (Elements.Book1.proposition_14 g c d e BG DE DE)
    euclid_finish
  euclid_apply (parallel_meets g AD BG GF)
  euclid_apply (intersection_lines AD GF) as h
  -- `AC : CH :: BC : CG` and `CH : CF :: DC : CE` [Prop. 6.1]
  have h₁ := proposition_1' d b c g a h AD BG AB DE GF (by euclid_finish)
  have h₂ := proposition_1' g d c e h f GF DE AD BG FE (by euclid_finish)
  -- let `K` be laid down (here `BC` itself), `BC : CG :: K : L` and `DC : CE :: L : M`
  -- [Prop. 6.12]
  obtain ⟨l₁, l₂, h₃⟩ := proposition_12 b c c g b c (by euclid_finish)
  obtain ⟨m₁, m₂, h₄⟩ := proposition_12 d c c e l₁ l₂
    ⟨by euclid_finish, by euclid_finish, size_segment_pos.mp h₃.2.2.2.1⟩
  -- so `K : L :: AC : CH` and `L : M :: CH : CF`; via equality `K : M :: AC : CF`
  -- [Prop. 5.22], and `K : M` is compounded of `K : L`, `L : M`
  obtain ⟨hbc, hcg, hk, hl, h₃⟩ := h₃
  obtain ⟨hdc, hce, hl', hm, h₄⟩ := h₄
  obtain ⟨hbc₁, hcg₁, hac, hch, h₁⟩ := h₁
  obtain ⟨hdc₁, hce₁, hch', hcf, h₂⟩ := h₂
  have h₅ := Elements.Book5.proposition_22' (Elements.Book5.proposition_11 h₃.symm h₁)
    (Elements.Book5.proposition_11 h₄.symm h₂)
  exact ⟨hac, hcf, hbc, hcg, hdc, hce, mag (b─c) hk, mag (l₁─l₂) hl, mag (m₁─m₂) hm,
    h₃, h₄, h₅.symm⟩

end Elements.Book6
