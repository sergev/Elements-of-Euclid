#import "../functions.typ": *

#content-box[
  #parallel-proposition(26)
  #parallel(
    [Ἐὰν ἀπὸ περισσοῦ ἀριθμοῦ περισσὸς ἀφαιρεθῇ, ὁ λοιπὸς ἄρτιος ἔσται.],
    [If an odd (number) is subtracted from an odd number then the remainder will be even.],
  )
  #parallel-image("/Book09/fig26", 0.3in)
  #parallel(
    [Ἀπὸ γὰρ περισσοῦ τοῦ ΑΒ περισσὸς ἀφῃρήσθω ὁ ΒΓ· λέγω, ὅτι ὁ λοιπὸς ὁ ΓΑ ἄρτιός ἐστιν.],
    [For let the odd (number) $B C$ be subtracted from the odd (number) $A B$. I say that the remainder, $C A$, is even.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ὁ ΑΒ περισσός ἐστιν, ἀφῃρήσθω μονὰς ἡ ΒΔ· λοιπὸς ἄρα ὁ ΑΔ ἄρτιός ἐστιν. διὰ τὰ αὐτὰ δὴ καὶ ὁ ΓΔ ἄρτιός ἐστιν· ὥστε καὶ λοιπὸς ὁ ΓΑ ἄρτιός ἐστιν· ὅπερ ἔδει δεῖξαι.],
    [For since $A B$ is odd, let the unit $B D$ be subtracted (from it). Thus, the remainder $A D$ is even [Def.~7.7]. So, for the same (reasons), $C D$ is also even. And hence the remainder $C A$ is even [Prop.~9.24]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop26.lean")
