import SystemE
import Elements.Book6.Definitions
import Elements.Book6.Lemmas
import Elements.Book6.Prop01
import Elements.Book6.Prop02
import Elements.Book6.Prop03

/-
Book 6: similar figures.

Book 6 applies Book 5's proportion to figures. A proof has two kinds of step. Geometric
steps are System E's, closed by saturation, as in Books 1–4. Steps about ratios are
Book 5's propositions and Def. 5.5, applied as plain Lean terms: the equal lengths, areas
and angles come from the figure, become equal magnitudes, and Book 5 is cited.

Ratios in the figure (`Elements/Book6/Definitions.lean`):
- A figure is a magnitude through the class `Figure X K`: a straight line `(a─b)` is a
  `Length`, a triangle `△a:b:c`, quadrilateral `□a:b:c:d` or pentagon `⬠a:b:c:d:e` an
  `Area` (Book 5's kinds, positive reals). `size p` is System E's measure of it, a real,
  and `mag p h` the magnitude, given `h : 0 < size p`.
- `p ∶ q ∷ r ∶ s`, "as `p` is to `q`, so is `r` to `s`", is Def. 5.5 of the four
  magnitudes. The positivity of each, which `mag` needs, is part of it (`∃` over the
  proofs), so statements need no distinctness hypotheses for their ratios, and a
  proportion of lines says that their ends are distinct. `p`, `q` are of one kind and
  `r`, `s` of one kind: `△a:b:c ∶ △a:c:d ∷ (b─c) ∶ (c─d)` mixes areas and lengths, as
  Prop. 6.1 does. Proofs are irrelevant, so which proof of positivity is given doesn't
  matter (`Proportional.elim`).
- Bridge lemmas: figures of equal size are equal magnitudes (`mag_congr`), sizes add as
  the magnitudes do (`mag_add`, `mag_lt`), a proportion holds of figures of equal sizes
  (`Proportional.congr`); `(a─b)` is `(b─a)`, and a triangle doesn't depend on the order
  of its vertices (`size_segment_symm`, `size_triangle_rot`, `size_triangle_swap`).
  Ratios are never reals: `|(a─b)| / |(c─d)|` is not used.
- `GreaterRatio'`, `SquaredRatio'`, `CompoundRatio'` are Def. 5.7, Def. 5.9 and the
  compounded ratio of figures, the same way.

Where the definitions are. Those that are purely geometric are `@[simp] abbrev`s in
`SystemE/Book6.lean`, so that saturation sees through them: the figures `□a:b:c:d`,
`⬠a:b:c:d:e` and their areas, `equiangularQuadrilaterals`, `equiangularPentagons`
(Book 4 has `equiangularTriangles`), and `sameHeight`. Those with ratios need Book 5 and
are in `Definitions.lean`; saturation ignores their ratios and uses the rest.

The definitions:
- Def. 6.1, similar figures, written out per number of sides, with the vertices in
  corresponding order (similarly laid down): `similarTriangles a b c d e f`,
  `similarQuadrilaterals`, `similarPentagons`: equal angles, and the sides about each
  pair of equal angles proportional. That the figures are triangles, quadrilaterals or
  pentagons (Book 4's `quadrilateral`, `pentagon`) is stated separately.
- Def. 6.2, `extremeMeanRatio a b c`: `ab` cut at `c`, the whole to `ac` as `ac` to `cb`.
- Def. 6.3, the height. Prop. 6.1 means by "the same height" what its proof uses:
  `sameHeight a d AD BC`, the vertices `a`, `d` on a line `AD` parallel to the bases'
  line `BC`.
- Def. 5.9, the squared ratio (Props. 6.19, 6.20, 6.22), is Book 5's: `SquaredRatio` in
  `Magnitude.lean`. Book 6 is its first user.
- The compounded ratio (Prop. 6.23) is used by Euclid without a definition: as he uses
  it, `a : b` is compounded of `c : d` and `e : f` when it is the same as `k : m`, with
  `c : d :: k : l` and `e : f :: l : m` (`CompoundRatio`).
- Reciprocal proportion (Props. 6.14, 6.15) is written out in the statements.

Rectilinear figures and their areas. A figure's area is the sum of the triangles of the
diagonals from its first vertex: `□a:b:c:d` is `△a:b:c + △a:c:d`. Prop. 1.45 makes a
parallelogram equal to a quadrilateral given as two triangles `abd`, `dbc` with `a`, `c`
on opposite sides of `db`, which is `□b:c:d:a` up to the order of the vertices. So the
given figures of Props. 6.25, 6.28 and 6.29 are triangles, or quadrilaterals given as
1.45 takes them.
-/
