#import "../functions.typ": *

#content-box[
  #parallel-proposition(21)
  #parallel(
    [Ἐὰν ἄρτιοι ἀριθμοὶ ὁποσοιοῦν συντεθῶσιν, ὁ ὅλος ἄρτιός ἐστιν.],
    [If any multitude whatsoever of even numbers is added together then the whole is even.],
  )
  #parallel-image("/Book09/fig21", 0.3in)
  #parallel(
    [Συγκείσθωσαν γὰρ ἄρτιοι ἀριθμοὶ ὁποσοιοῦν οἱ ΑΒ, ΒΓ, ΓΔ, ΔΕ· λέγω, ὅτι ὅλος ὁ ΑΕ ἄρτιός ἐστιν.],
    [For let any multitude whatsoever of even numbers, $A B$, $B C$, $C D$, $D E$, lie together. I say that the whole, $A E$, is even.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ἕκαστος τῶν ΑΒ, ΒΓ, ΓΔ, ΔΕ ἄρτιός ἐστιν, ἔχει μέρος ἥμισυ· ὥστε καὶ ὅλος ὁ ΑΕ ἔχει μέρος ἥμισυ. ἄρτιος δὲ ἀριθμός ἐστιν ὁ δίχα διαιρούμενος· ἄρτιος ἄρα ἐστὶν ὁ ΑΕ· ὅπερ ἔδει δεῖξαι.],
    [For since every one of $A B$, $B C$, $C D$, $D E$ is even, it has a half part [Def.~7.6]. And hence the whole $A E$ has a half part. And an even number is one (which can be) divided in half [Def.~7.6]. Thus, $A E$ is even. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop21.lean")
