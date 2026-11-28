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

The corollaries to 3.1 and 3.16 are `proposition_1_corollary` and `proposition_16_corollary`.
-/
