#import "../functions.typ": *

#content-box[
  #parallel-proposition(27)
  #parallel(
    [Ἐὰν ἀπὸ περισσοῦ ἀριθμοῦ ἄρτιος ἀφαιρεθῇ, ὁ λοιπὸς περισσὸς ἔσται.],
    [If an even (number) is subtracted from an odd number then the remainder will be odd.],
  )
  #parallel-image("/Book09/fig27", 0.3in)
  #parallel(
    [Ἀπὸ γὰρ περισσοῦ τοῦ ΑΒ ἄρτιος ἀφῃρήσθω ὁ ΒΓ· λέγω, ὅτι ὁ λοιπὸς ὁ ΓΑ περισσός ἐστιν.],
    [For let the even (number) $B C$ be subtracted from the odd (number) $A B$. I say that the remainder, $C A$, is odd.],
  )
  #parallel(
    [Ἀφῃρήσθω [γὰρ] μονὰς ἡ ΑΔ· ὁ ΔΒ ἄρα ἄρτιός ἐστιν. ἔστι δὲ καὶ ὁ ΒΓ ἄρτιος· καὶ λοιπὸς ἄρα ὁ ΓΔ ἄρτιός ἐστιν. περισσὸς ἄρα ὁ ΓΑ· ὅπερ ἔδει δεῖξαι.],
    [[For] let the unit $A D$ be subtracted (from $A B$). $D B$ is thus even [Def.~7.7]. And $B C$ is also even. Thus, the remainder $C D$ is also even [Prop.~9.24]. $C A$ (is) thus odd [Def.~7.7]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop27.lean")
