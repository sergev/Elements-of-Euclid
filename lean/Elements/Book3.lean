import Elements.Book3.Lemmas
import Elements.Book3.Prop01
import Elements.Book3.Prop02
import Elements.Book3.Prop03
import Elements.Book3.Prop04
import Elements.Book3.Prop05
import Elements.Book3.Prop06
import Elements.Book3.Prop07
import Elements.Book3.Prop08
import Elements.Book3.Prop09
import Elements.Book3.Prop10
import Elements.Book3.Prop11
import Elements.Book3.Prop12
import Elements.Book3.Prop13
import Elements.Book3.Prop14
import Elements.Book3.Prop15
import Elements.Book3.Prop16
import Elements.Book3.Prop17
import Elements.Book3.Prop18
import Elements.Book3.Prop19
import Elements.Book3.Prop20
import Elements.Book3.Prop21
import Elements.Book3.Prop22
import Elements.Book3.Prop23
import Elements.Book3.Prop24
import Elements.Book3.Prop25

/-
Book 3: circles.

Conventions. In System E, `L.intersectsCircle α` and `α.intersectsCircle β` mean that
they *cut*, at two points. Book 3's definitions are in `SystemE/Book3.lean`:
- Def. 3.1, equal circles, `equalCircles α β c₁ p₁ c₂ p₂`: equal radii `|(c₁─p₁)| = |(c₂─p₂)|`
  for centers `c₁`, `c₂` and points `p₁`, `p₂` on the circles.
- Def. 3.2, a line touching a circle, `L.touchesCircleAt α a`: `a` is on both and `L`
  does not cut `α`; every other point of `L` is then outside `α`.
- Def. 3.3, circles touching, `α.touchesCircleAt β a`: distinct circles through `a` that
  do not cut. `α.touchesInternallyAt β a`: `α` is within `β`, every point inside `α`
  inside `β`; `α.touchesExternallyAt β a`: each is outside the other, no point inside both.
- Defs. 3.6 and 3.8, segments, `c.onSegment α a b AB s`: `c` is on the circumference of
  the segment of `α` on the chord `AB`, on the side of `s`; the angle in the segment is
  `∠ a:c:b`.
- Def. 3.11, similar segments, `similarSegments α a b AB x β c d CD y`: the segments of `α`
  on `AB` toward `x` and of `β` on `CD` toward `y` admit equal angles, `∠ a:x:b = ∠ c:y:d`;
  by Prop. 3.21 one point of each segment is enough.

Prop. 3.20 is proved in the position Euclid treats, the center on the side of the angle
at the circumference, and in those he leaves out (`proposition_20'`, `proposition_20''`);
Prop. 3.21 needs them for segments not greater than a semicircle.

Props. 3.23–3.24. Unequal segments on one straight line are on different circles, so 3.23
concludes that the circles are the same. In 3.24 Euclid applies one segment to the
other; System E's superposition moves triangles, so the triangle on the chord with apex
the center is applied, and the circle about the image of the center is shown to be the
other segment's by 3.23. "Equal segments" are segments on equal chords of equal circles
(Def. 3.1), which coincide when applied.

The corollaries to 3.1 and 3.16 are `proposition_1_corollary` and `proposition_16_corollary`.
-/
