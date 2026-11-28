#import "../functions.typ": *

#content-box[
  #parallel-proposition(19)
  #parallel(
    [Τὸ ὑπὸ ῥητῶν μήκει συμμέτρων εὐθειῶν περιεχόμενον ὀρθογώνιον ῥητόν ἐστιν.],
    [The rectangle contained by rational straight-lines (which are) commensurable in length is rational.],
  )
  #parallel(
    [Ὑπὸ γὰρ ῥητῶν μήκει συμμέτρων εὐθειῶν τῶν ΑΒ, ΒΓ ὀρθογώνιον περιεχέσθω τὸ ΑΓ· λέγω, ὅτι ῥητόν ἐστι τὸ ΑΓ.],
    [For let the rectangle $A C$ be enclosed by the rational straight-lines $A B$ and $B C$ (which are) commensurable in length. I say that $A C$ is rational.],
  )
  #parallel-image("/Book10/fig019", 2in)
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΑΒ τετράγωνον τὸ ΑΔ· ῥητὸν ἄρα ἐστὶ τὸ ΑΔ. καὶ ἐπεὶ σύμμετρός ἐστιν ἡ ΑΒ τῇ ΒΓ μήκει, ἴση δέ ἐστιν ἡ ΑΒ τῇ ΒΔ, σύμμετρος ἄρα ἐστὶν ἡ ΒΔ τῇ ΒΓ μήκει. καί ἐστιν ὡς ἡ ΒΔ πρὸς τὴν ΒΓ, οὕτως τὸ ΔΑ πρὸς τὸ ΑΓ. σύμμετρον ἄρα ἐστὶ τὸ ΔΑ τῷ ΑΓ. ῥητὸν δὲ τὸ ΔΑ· ῥητὸν ἄρα ἐστὶ καὶ τὸ ΑΓ.],
    [For let the square $A D$ be described on $A B$. $A D$ is thus rational [Def.~10.4]. And since $A B$ is commensurable in length with $B C$, and $A B$ is equal to $B D$, $B D$ is thus commensurable in length with $B C$. And as $B D$ is to $B C$, so $D A$ (is) to $A C$ [Prop.~6.1]. Thus, $D A$ is commensurable with $A C$ [Prop.~10.11]. And $D A$ (is) rational. Thus, $A C$ is also rational [Def.~10.4].],
  )
  #parallel(
    [Τὸ ἄρα ὑπὸ ῥητῶν μήκει συμμέτρων, καὶ τὰ ἑξῆς.],
    [Thus, the ... by rational straight-lines ... commensurable, and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop019.lean")
