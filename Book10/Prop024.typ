#import "../functions.typ": *

#content-box[
  #parallel-proposition(24)
  #parallel(
    [Τὸ ὑπὸ μέσων μήκει συμμέτρων εὐθειῶν περιεχόμενον ὀρθογώνιον μέσον ἐστίν.],
    [A rectangle contained by medial straight-lines (which are) commensurable in length is medial.],
  )
  #parallel(
    [Ὑπὸ γὰρ μέσων μήκει συμμέτρων εὐθειῶν τῶν ΑΒ, ΒΓ περιεχέσθω ὀρθογώνιον τὸ ΑΓ· λέγω, ὅτι τὸ ΑΓ μέσον ἐστίν.],
    [For let the rectangle $A C$ be contained by the medial straight-lines $A B$ and $B C$ (which are) commensurable in length. I say that $A C$ is medial.],
  )
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΑΒ τετράγωνον τὸ ΑΔ· μέσον ἄρα ἐστὶ τὸ ΑΔ. καὶ ἐπεὶ σύμμετρός ἐστιν ἡ ΑΒ τῇ ΒΓ μήκει, ἴση δὲ ἡ ΑΒ τῇ ΒΔ, σύμμετρος ἄρα ἐστὶ καὶ ἡ ΔΒ τῇ ΒΓ μήκει· ὥστε καὶ τὸ ΔΑ τῷ ΑΓ σύμμετρόν ἐστιν. μέσον δὲ τὸ ΔΑ· μέσον ἄρα καὶ τὸ ΑΓ· ὅπερ ἔδει δεῖξαι.],
    [For let the square $A D$ be described on $A B$. $A D$ is thus medial [see previous footnote]. And since $A B$ is commensurable in length with $B C$, and $A B$ (is) equal to $B D$, $D B$ is thus also commensurable in length with $B C$. Hence, $D A$ is also commensurable with $A C$ [Props.~6.1, 10.11]. And $D A$ (is) medial. Thus, $A C$ (is) also medial [Prop.~10.23 corr.]. (Which is) the very thing it was required to show.],
  )
  #parallel-image("/Book10/fig024", 2.2in)
]
#lean-proof("/lean/Elements/Book10/Prop024.lean")
