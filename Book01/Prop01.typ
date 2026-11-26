#import "../functions.typ": *

#content-box[
  #parallel-proposition(1)
  
  #parallel(
    [Ἐπὶ τῆς δοθείσης εὐθείας πεπερασμένης τρίγωνον ἰσόπλευρον συστήσασθαι.],
    [To construct an equilateral triangle on a given finite straight-line.],
  )
  #parallel(
    [Ἔστω ἡ δοθεῖσα εὐθεῖα πεπερασμένη ἡ ΑΒ.],
    [Let $A B$ be the given finite straight-line.],
  )
  #parallel(
    [Δεῖ δὴ ἐπὶ τῆς ΑΒ εὐθείας τρίγωνον ἰσόπλευρον συστήσασθαι.],
    [So it is required to construct an equilateral triangle on the straight-line $A B$.],
  )

  #parallel-image("/Book01/fig01", 1.75in)

  #parallel(
    [Κέντρῳ μὲν τῷ Α διαστήματι δὲ τῷ ΑΒ κύκλος γεγράφθω ὁ ΒΓΔ, καὶ πάλιν κέντρῳ μὲν τῷ Β διαστήματι δὲ τῷ ΒΑ κύκλος γεγράφθω ὁ ΑΓΕ, καὶ ἀπὸ τοῦ Γ σημείου, καθ᾿ ὃ τέμνουσιν ἀλλήλους οἱ κύκλοι, ἐπί τὰ Α, Β σημεῖα ἐπεζεύχθωσαν εὐθεῖαι αἱ ΓΑ, ΓΒ.],
    [Let the circle $B C D$ with center $A$ and radius $A B$ be drawn#content-box-note[Literally, "have been drawn". The use of this peculiar Greek idiom will pass without further comment.] [Post.~3], and again let the circle $A C E$ with center $B$ and radius $B A$ be drawn [Post.~3]. And let the straight-lines $C A$ and $C B$ be joined from the point $C$, where the circles cut one another,#content-box-note[The assumption that the circles do indeed cut one another should be counted as an additional postulate. There is also an implicit assumption that two straight-lines cannot share a common segment.] to the points $A$ and $B$ (respectively) [Post.~1].],
  )
  #parallel(
    [Καὶ ἐπεὶ τὸ Α σημεῖον κέντρον ἐστὶ τοῦ ΓΔΒ κύκλου, ἴση ἐστὶν ἡ ΑΓ τῇ ΑΒ· πάλιν, ἐπεὶ τὸ Β σημεῖον κέντρον ἐστὶ τοῦ ΓΑΕ κύκλου, ἴση ἐστὶν ἡ ΒΓ τῇ ΒΑ. ἐδείχθη δὲ καὶ ἡ ΓΑ τῇ ΑΒ ἴση· ἑκατέρα ἄρα τῶν ΓΑ, ΓΒ τῇ ΑΒ ἐστιν ἴση. τὰ δὲ τῷ αὐτῷ ἴσα καὶ ἀλλήλοις ἐστὶν ἴσα· καὶ ἡ ΓΑ ἄρα τῇ ΓΒ ἐστιν ἴση· αἱ τρεῖς ἄρα αἱ ΓΑ, ΑΒ, ΒΓ ἴσαι ἀλλήλαις εἰσίν.],
    [And since the point $A$ is the center of the circle $C D B$, $A C$ is equal to $A B$ [Def.~1.15]. Again, since the point $B$ is the center of the circle $C A E$, $B C$ is equal to $B A$ [Def.~1.15]. But $C A$ was also shown (to be) equal to $A B$. Thus, $C A$ and $C B$ are each equal to $A B$. But things equal to the same thing are also equal to one another [C.N.~1]. Thus, $C A$ is also equal to $C B$. Thus, the three (straight-lines) $C A$, $A B$, and $B C$ are equal to one another.],
  )
  #parallel(
    [Ἰσόπλευρον ἄρα ἐστὶ τὸ ΑΒΓ τρίγωνον. καὶ συνέσταται ἐπὶ τῆς δοθείσης εὐθείας πεπερασμένης τῆς ΑΒ. ὅπερ ἔδει ποιῆσαι.],
    [Thus, the triangle $A B C$ is equilateral, and has been constructed on the given finite straight-line $A B$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop01.lean")
