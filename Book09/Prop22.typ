#import "../functions.typ": *

#content-box[
  #parallel-proposition(22)
  #parallel(
    [Ἐὰν περισσοὶ ἀριθμοὶ ὁποσοιοῦν συντεθῶσιν, τὸ δὲ πλῆθος αὐτῶν ἄρτιον ᾖ, ὁ ὅλος ἄρτιος ἔσται.],
    [If any multitude whatsoever of odd numbers is added together, and the multitude of them is even, then the whole will be even.],
  )
  #parallel-image("/Book09/fig21", 0.3in)
  #parallel(
    [Συγκείσθωσαν γὰρ περισσοὶ ἀριθμοὶ ὁσοιδηποτοῦν ἄρτιοι τὸ πλῆθος οἱ ΑΒ, ΒΓ, ΓΔ, ΔΕ· λέγω, ὅτι ὅλος ὁ ΑΕ ἄρτιός ἐστιν.],
    [For let any even multitude whatsoever of odd numbers, $A B$, $B C$, $C D$, $D E$, lie together. I say that the whole, $A E$, is even.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ἕκαστος τῶν ΑΒ, ΒΓ, ΓΔ, ΔΕ περιττός ἐστιν, ἀφαιρεθείσης μονάδος ἀφ᾿ ἑκάστου ἕκαστος τῶν λοιπῶν ἄρτιος ἔσται· ὥστε καὶ ὁ συγκείμενος ἐξ αὐτῶν ἄρτιος ἔσται. ἔστι δὲ καὶ τὸ πλῆθος τῶν μονάδων ἄρτιον. καὶ ὅλος ἄρα ὁ ΑΕ ἄρτιός ἐστιν· ὅπερ ἔδει δεῖξαι.],
    [For since every one of $A B$, $B C$, $C D$, $D E$ is odd then, a unit being subtracted from each, every one of the remainders will be (made) even [Def.~7.7]. And hence the sum of them will be even [Prop.~9.21]. And the multitude of the units is even. Thus, the whole $A E$ is also even [Prop.~9.21]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop22.lean")
