#import "../functions.typ": *

#content-box[
  #parallel-proposition(6, note: [This proposition is a geometric version of the algebraic identity: $(2 thin a+b) thin b + a^(2) = (a+b)^(2)$.])
  #parallel(
    [Ἐὰν εὐθεῖα γραμμὴ τμηθῇ δίχα, προστεθῇ δέ τις αὐτῇ εὐθεῖα ἐπ᾿ εὐθείας, τὸ ὑπὸ τῆς ὅλης σὺν τῇ προσκειμένῃ καὶ τῆς προσκειμένης περιεχόμενον ὀρθόγώνιον μετὰ τοῦ ἀπὸ τῆς ἡμισείας τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς συγκειμένης ἔκ τε τῆς ἡμισείας καὶ τῆς προσκειμένης τετραγώνῳ.],
    [If a straight-line is cut in half, and any straight-line added to it straight-on, (then) the rectangle contained by the whole (straight-line) with the (straight-line) having been added, and the (straight-line) having been added, plus the square on half (of the original straight-line), is equal to the square on the sum of half (of the original straight-line) and the (straight-line) having been added.],
  )
  #parallel-image("/Book02/fig06", 1.8in)
  #parallel(
    [Εὐθεῖα γάρ τις ἡ ΑΒ τετμήσθω δίχα κατὰ τὸ Γ σημεῖον, προσκείσθω δέ τις αὐτῇ εὐθεῖα ἐπ᾿ εὐθείας ἡ ΒΔ· λέγω, ὅτι τὸ ὑπὸ τῶν ΑΔ, ΔΒ περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς ΓΒ τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ΓΔ τετραγώνῳ.],
    [For let any straight-line $A B$ be cut in half at point $C$, and let any straight-line $B D$ be added to it straight-on. I say that the rectangle contained by $A D$ and $D B$, plus the square on $C B$, is equal to the square on $C D$.],
  )
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΓΔ τετράγωνον τὸ ΓΕΖΔ, καὶ ἐπεζεύχθω ἡ ΔΕ, καὶ διὰ μὲν τοῦ Β σημείου ὁποτέρᾳ τῶν ΕΓ, ΔΖ παράλληλος ἤχθω ἡ ΒΗ, διὰ δὲ τοῦ Θ σημείου ὁποτέρᾳ τῶν ΑΒ, ΕΖ παράλληλος ἤχθω ἡ ΚΜ, καὶ ἔτι διὰ τοῦ Α ὁποτέρᾳ τῶν ΓΛ, ΔΜ παράλληλος ἤχθω ἡ ΑΚ.],
    [For let the square $C E F D$ be described on $C D$ [Prop.~1.46], and let $D E$ be joined, and let $B G$ be drawn through point $B$, parallel to either of $E C$ or $D F$ [Prop.~1.31], and let $K M$ be drawn through point $H$, parallel to either of $A B$ or $E F$ [Prop.~1.31], and finally let $A K$ be drawn through $A$, parallel to either of $C L$ or $D M$ [Prop.~1.31].],
  )
  #parallel(
    [Ἐπεὶ οὖν ἴση ἐστὶν ἡ ΑΓ τῇ ΓΒ, ἴσον ἐστὶ καὶ τὸ ΑΛ τῷ ΓΘ. ἀλλὰ τὸ ΓΘ τῷ ΘΖ ἴσον ἐστίν. καὶ τὸ ΑΛ ἄρα τῷ ΘΖ ἐστιν ἴσον. κοινὸν προσκείσθω τὸ ΓΜ· ὅλον ἄρα τὸ ΑΜ τῷ ΝΞΟ γνώμονί ἐστιν ἴσον. ἀλλὰ τὸ ΑΜ ἐστι τὸ ὑπὸ τῶν ΑΔ, ΔΒ· ἴση γάρ ἐστιν ἡ ΔΜ τῇ ΔΒ· καὶ ὁ ΝΞΟ ἄρα γνώμων ἴσος ἐστὶ τῷ ὑπὸ τῶν ΑΔ, ΔΒ [περιεχομένῳ ὀρθογωνίῳ]. κοινὸν προσκείσθω τὸ ΛΗ, ὅ ἐστιν ἴσον τῷ ἀπὸ τῆς ΒΓ τετραγώνῳ· τὸ ἄρα ὑπὸ τῶν ΑΔ, ΔΒ περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς ΓΒ τετραγώνου ἴσον ἐστὶ τῷ ΝΞΟ γνώμονι καὶ τῷ ΛΗ. ἀλλὰ ὁ ΝΞΟ γνώμων καὶ τὸ ΛΗ ὅλον ἐστὶ τὸ ΓΕΖΔ τετράγωνον, ὅ ἐστιν ἀπὸ τῆς ΓΔ· τὸ ἄρα ὑπὸ τῶν ΑΔ, ΔΒ περιεχόμενον ὀρθογώνιον μετὰ τοῦ ἀπὸ τῆς ΓΒ τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς ΓΔ τετραγώνῳ.],
    [Therefore, since $A C$ is equal to $C B$, (rectangle) $A L$ is also equal to (rectangle) $C H$ [Prop.~1.36]. But, (rectangle) $C H$ is equal to (rectangle) $H F$ [Prop.~1.43]. Thus, (rectangle) $A L$ is also equal to (rectangle) $H F$. Let (rectangle) $C M$ be added to both. Thus, the whole (rectangle) $A M$ is equal to the gnomon $N O P$. But, $A M$ is the (rectangle contained) by $A D$ and $D B$. For $D M$ is equal to $D B$. Thus, gnomon $N O P$ is also equal to the [rectangle contained] by $A D$ and $D B$. Let $L G$, which is equal to the square on $B C$, be added to both. Thus, the rectangle contained by $A D$ and $D B$, plus the square on $C B$, is equal to the gnomon $N O P$ and the (square) $L G$. But the gnomon $N O P$ and the (square) $L G$ is (equivalent to) the whole square $C E F D$, which is on $C D$. Thus, the rectangle contained by $A D$ and $D B$, plus the square on $C B$, is equal to the square on $C D$.],
  )
  #parallel(
    [Ἐὰν ἄρα εὐθεῖα γραμμὴ τμηθῇ δίχα, προστεθῇ δέ τις αὐτῇ εὐθεῖα ἐπ᾿ εὐθείας, τὸ ὑπὸ τῆς ὅλης σὺν τῇ προσκειμένῃ καὶ τῆς προσκειμένης περιεχόμενον ὀρθόγώνιον μετὰ τοῦ ἀπὸ τῆς ἡμισείας τετραγώνου ἴσον ἐστὶ τῷ ἀπὸ τῆς συγκειμένης ἔκ τε τῆς ἡμισείας καὶ τῆς προσκειμένης τετραγώνῳ· ὅπερ ἔδει δεῖξαι.],
    [Thus, if a straight-line is cut in half, and any straight-line added to it straight-on, (then) the rectangle contained by the whole (straight-line) with the (straight-line) having been added, and the (straight-line) having been added, plus the square on half (of the original straight-line), is equal to the square on the sum of half (of the original straight-line) and the (straight-line) having been added. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book2/Prop06.lean")
