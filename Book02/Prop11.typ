#import "../functions.typ": *

#content-box[
  #parallel-proposition(11, note: [This manner of cutting a straight-line---so that the ratio of the whole to the larger piece is equal to the ratio of the larger to the smaller piece---is sometimes called the "Golden Section".])
  #parallel(
    [Τὴν δοθεῖσαν εὐθεῖαν τεμεῖν ὥστε τὸ ὑπὸ τῆς ὅλης καὶ τοῦ ἑτέρου τῶν τμημάτων περιεχόμενον ὀρθογώνιον ἴσον εἶναι τῷ ἀπὸ τοῦ λοιποῦ τμήματος τετραγώνῳ.],
    [To cut a given straight-line such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece.],
  )
  #parallel(
    [Ἔστω ἡ δοθεῖσα εὐθεῖα ἡ ΑΒ· δεῖ δὴ τὴν ΑΒ τεμεῖν ὥστε τὸ ὑπὸ τῆς ὅλης καὶ τοῦ ἑτέρου τῶν τμημάτων περιεχόμενον ὀρθογώνιον ἴσον εἶναι τῷ ἀπὸ τοῦ λοιποῦ τμήματος τετραγώνῳ.],
    [Let $A B$ be the given straight-line. So it is required to cut $A B$ such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece.],
  )
  #parallel-image("/Book02/fig11", 2.75in)
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΑΒ τετράγωνον τὸ ΑΒΔΓ, καὶ τετμήσθω ἡ ΑΓ δίχα κατὰ τὸ Ε σημεῖον, καὶ ἐπεζεύχθω ἡ ΒΕ, καὶ διήχθω ἡ ΓΑ ἐπὶ τὸ Ζ, καὶ κείσθω τῇ ΒΕ ἴση ἡ ΕΖ, καὶ ἀναγεγράφθω ἀπὸ τῆς ΑΖ τετράγωνον τὸ ΖΘ, καὶ διήχθω ἡ ΗΘ ἐπὶ τὸ Κ· λέγω, ὅτι ἡ ΑΒ τέτμηται κατὰ τὸ Θ, ὥστε τὸ ὑπὸ τῶν ΑΒ, ΒΘ περιεχόμενον ὀρθογώνιον ἴσον ποιεῖν τῷ ἀπὸ τῆς ΑΘ τετραγώνῳ.],
    [For let the square $A B D C$ be described on $A B$ [Prop.~1.46], and let $A C$ be cut in half at point $E$ [Prop.~1.10], and let $B E$ be joined. And let $C A$ be drawn through to (point) $F$, and let $E F$ be made equal to $B E$ [Prop.~1.3]. And let the square $F H$ be described on $A F$ [Prop.~1.46], and let $G H$ be drawn through to (point) $K$. I say that $A B$ has been cut at $H$ such as to make the rectangle contained by $A B$ and $B H$ equal to the square on $A H$.],
  )
  #parallel(
    [Ἐπεὶ γὰρ εὐθεῖα ἡ ΑΓ τέτμηται δίχα κατὰ τὸ Ε, πρόσκειται δὲ αὐτῇ ἡ ΖΑ, τὸ ἄρα ὑπὸ τῶν ΓΖ, ΖΑ περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς ΑΕ τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ΕΖ τετραγώνῳ. ἴση δὲ ἡ ΕΖ τῇ ΕΒ· τὸ ἄρα ὑπὸ τῶν ΓΖ, ΖΑ μετὰ τοῦ ἀπὸ τῆς ΑΕ ἴσον ἐστὶ τῷ ἀπὸ ΕΒ. ἀλλὰ τῷ ἀπὸ ΕΒ ἴσα ἐστὶ τὰ ἀπὸ τῶν ΒΑ, ΑΕ· ὀρθὴ γὰρ ἡ πρὸς τῷ Α γωνία· τὸ ἄρα ὑπὸ τῶν ΓΖ, ΖΑ μετὰ τοῦ ἀπὸ τῆς ΑΕ ἴσον ἐστὶ τοῖς ἀπὸ τῶν ΒΑ, ΑΕ. κοινὸν ἀφῃρήσθω τὸ ἀπὸ τῆς ΑΕ· λοιπὸν ἄρα τὸ ὑπὸ τῶν ΓΖ, ΖΑ περιεχόμενον ὀρθογώνιον ἴσον ἐστὶ τῷ ἀπὸ τῆς ΑΒ τετραγώνῳ. καί ἐστι τὸ μὲν ὑπὸ τῶν ΓΖ, ΖΑ τὸ ΖΚ· ἴση γὰρ ἡ ΑΖ τῇ ΖΗ· τὸ δὲ ἀπὸ τῆς ΑΒ τὸ ΑΔ· τὸ ἄρα ΖΚ ἴσον ἐστὶ τῷ ΑΔ. κοινὸν ἀρῃρήσθω τὸ ΑΚ· λοιπὸν ἄρα τὸ ΖΘ τῷ ΘΔ ἴσον ἐστίν. καί ἐστι τὸ μὲν ΘΔ τὸ ὑπὸ τῶν ΑΒ, ΒΘ· ἴση γὰρ ἡ ΑΒ τῇ ΒΔ· τὸ δὲ ΖΘ τὸ ἀπὸ τῆς ΑΘ· τὸ ἄρα ὑπὸ τῶν ΑΒ, ΒΘ περιεχόμενον ὀρθογώνιον ἴσον ἐστὶ τῷ ἀπὸ ΘΑ τετραγώνῳ.],
    [For since the straight-line $A C$ has been cut in half at $E$, and $F A$ has been added to it, the rectangle contained by $C F$ and $F A$, plus the square on $A E$, is thus equal to the square on $E F$ [Prop.~2.6]. And $E F$ (is) equal to $E B$. Thus, the (rectangle contained) by $C F$ and $F A$, plus the (square) on $A E$, is equal to the (square) on $E B$. But, the (sum of the squares) on $B A$ and $A E$ is equal to the (square) on $E B$. For the angle at $A$ (is) a right-angle [Prop.~1.47]. Thus, the (rectangle contained) by $C F$ and $F A$, plus the (square) on $A E$, is equal to the (sum of the squares) on $B A$ and $A E$. Let the square on $A E$ be subtracted from both. Thus, the remaining rectangle contained by $C F$ and $F A$ is equal to the square on $A B$. And $F K$ is the (rectangle contained) by $C F$ and $F A$. For $A F$ (is) equal to $F G$. And $A D$ (is) the (square) on $A B$. Thus, the (rectangle) $F K$ is equal to the (square) $A D$. Let (rectangle) $A K$ be subtracted from both. Thus, the remaining (square) $F H$ is equal to the (rectangle) $H D$. And $H D$ is the (rectangle contained) by $A B$ and $B H$. For $A B$ (is) equal to $B D$. And $F H$ (is) the (square) on $A H$. Thus, the rectangle contained by $A B$ and $B H$ is equal to the square on $H A$.],
  )
  #parallel(
    [Ἡ ἄρα δοθεῖσα εὐθεῖα ἡ ΑΒ τέτμηται κατὰ τὸ Θ ὥστε τὸ ὑπὸ τῶν ΑΒ, ΒΘ περιεχόμενον ὀρθογώνιον ἴσον ποιεῖν τῷ ἀπὸ τῆς ΘΑ τετραγώνῳ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the given straight-line $A B$ has been cut at (point) $H$ such as to make the rectangle contained by $A B$ and $B H$ equal to the square on $H A$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book2/Prop11.lean")
