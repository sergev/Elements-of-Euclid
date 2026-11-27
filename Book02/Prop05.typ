#import "../functions.typ": *

#content-box[
  #parallel-proposition(5, note: [This proposition is a geometric version of the algebraic identity: $a thin b +[(a+b) \/ 2-b]^(2) = [(a+b) \/ 2]^(2)$.])
  #parallel(
    [Ἐὰν εὐθεῖα γραμμὴ τμηθῇ εἰς ἴσα καὶ ἄνισα, τὸ ὑπὸ τῶν ἀνίσων τῆς ὅλης τμημάτων περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς μεταξὺ τῶν τομῶν τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ἡμισείας τετραγώνῳ.],
    [If a straight-line is cut into equal and unequal (pieces, then) the rectangle contained by the unequal pieces of the whole (straight-line), plus the square on the (difference) between the (equal and unequal) pieces, is equal to the square on half (of the straight-line).],
  )
  #parallel-image("/Book02/fig05", 1.8in)
  #parallel(
    [Εὐθεῖα γάρ τις ἡ ΑΒ τετμήσθω εἰς μὲν ἴσα κατὰ τὸ Γ, εἰς δὲ ἄνισα κατὰ τὸ Δ· λέγω, ὅτι τὸ ὑπὸ τῶν ΑΔ, ΔΒ περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς ΓΔ τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ΓΒ τετραγώνῳ.],
    [For let any straight-line $A B$ be cut---equally at $C$, and unequally at $D$. I say that the rectangle contained by $A D$ and $D B$, plus the square on $C D$, is equal to the square on $C B$.],
  )
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΓΒ τετράγωνον τὸ ΓΕΖΒ, καὶ ἐπεζεύχθω ἡ ΒΕ, καὶ διὰ μὲν τοῦ Δ ὁποτέρᾳ τῶν ΓΕ, ΒΖ παράλληλος ἤχθω ἡ ΔΗ, διὰ δὲ τοῦ Θ ὁποτέρᾳ τῶν ΑΒ, ΕΖ παράλληλος πάλιν ἤχθω ἡ ΚΜ, καὶ πάλιν διὰ τοῦ Α ὁποτέρᾳ τῶν ΓΛ, ΒΜ παράλληλος ἤχθω ἡ ΑΚ. καὶ ἐπεὶ ἴσον ἐστὶ τὸ ΓΘ παραπλήρωμα τῷ ΘΖ παραπληρώματι, κοινὸν προσκείσθω τὸ ΔΜ· ὅλον ἄρα τὸ ΓΜ ὅλῳ τῷ ΔΖ ἴσον ἐστίν. ἀλλὰ τὸ ΓΜ τῷ ΑΛ ἴσον ἐστίν, ἐπεὶ καὶ ἡ ΑΓ τῇ ΓΒ ἐστιν ἴση· καὶ τὸ ΑΛ ἄρα τῷ ΔΖ ἴσον ἐστίν. κοινὸν προσκείσθω τὸ ΓΘ· ὅλον ἄρα τὸ ΑΘ τῷ ΜΝΞ#content-box-note[Note the (presumably mistaken) double use of the label $M$ in the Greek text.] γνώμονι ἴσον ἐστίν. ἀλλὰ τὸ ΑΘ τὸ ὑπὸ τῶν ΑΔ, ΔΒ ἐστιν· ἴση γὰρ ἡ ΔΘ τῇ ΔΒ· καὶ ὁ ΜΝΞ ἄρα γνώμων ἴσος ἐστὶ τῷ ὑπὸ ΑΔ, ΔΒ. κοινὸν προσκείσθω τὸ ΛΗ, ὅ ἐστιν ἴσον τῷ ἀπὸ τῆς ΓΔ· ὁ ἄρα ΜΝΞ γνώμων καὶ τὸ ΛΗ ἴσα ἐστὶ τῷ ὑπὸ τῶν ΑΔ, ΔΒ περιεχομένῳ ὀρθογωνίῳ καὶ τῷ ἀπὸ τῆς ΓΔ τετραγώνῳ. ἀλλὰ ὁ ΜΝΞ γνώμων καὶ τὸ ΛΗ ὅλον ἐστὶ τὸ ΓΕΖΒ τετράγωνον, ὅ ἐστιν ἀπὸ τῆς ΓΒ· τὸ ἄρα ὑπὸ τῶν ΑΔ, ΔΒ περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς ΓΔ τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ΓΒ τετραγώνῳ.],
    [For let the square $C E F B$ be described on $C B$ [Prop.~1.46], and let $B E$ be joined, and let $D G$ be drawn through $D$, parallel to either of $C E$ or $B F$ [Prop.~1.31], and again let $K M$ be drawn through $H$, parallel to either of $A B$ or $E F$ [Prop.~1.31], and again let $A K$ be drawn through $A$, parallel to either of $C L$ or $B M$ [Prop.~1.31]. And since the complement $C H$ is equal to the complement $H F$ [Prop.~1.43], let the (square) $D M$ be added to both. Thus, the whole (rectangle) $C M$ is equal to the whole (rectangle) $D F$. But, (rectangle) $C M$ is equal to (rectangle) $A L$, since $A C$ is also equal to $C B$ [Prop.~1.36]. Thus, (rectangle) $A L$ is also equal to (rectangle) $D F$. Let (rectangle) $C H$ be added to both. Thus, the whole (rectangle) $A H$ is equal to the gnomon $N O P$. But, $A H$ is the (rectangle contained) by $A D$ and $D B$. For $D H$ (is) equal to $D B$. Thus, the gnomon $N O P$ is also equal to the (rectangle contained) by $A D$ and $D B$. Let $L G$, which is equal to the (square) on $C D$, be added to both. Thus, the gnomon $N O P$ and the (square) $L G$ are equal to the rectangle contained by $A D$ and $D B$, and the square on $C D$. But, the gnomon $N O P$ and the (square) $L G$ is (equivalent to) the whole square $C E F B$, which is on $C B$. Thus, the rectangle contained by $A D$ and $D B$, plus the square on $C D$, is equal to the square on $C B$.],
  )
  #parallel(
    [Ἐὰν ἄρα εὐθεῖα γραμμὴ τμηθῇ εἰς ἴσα καὶ ἄνισα, τὸ ὑπὸ τῶν ἀνίσων τῆς ὅλης τμημάτων περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς μεταξὺ τῶν τομῶν τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ἡμισείας τετραγώνῳ. ὅπερ ἔδει δεῖξαι.],
    [Thus, if a straight-line is cut into equal and unequal (pieces, then) the rectangle contained by the unequal pieces of the whole (straight-line), plus the square on the (difference) between the (equal and unequal) pieces, is equal to the square on half (of the straight-line). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book2/Prop05.lean")
