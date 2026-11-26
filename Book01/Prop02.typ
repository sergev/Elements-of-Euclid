#import "../functions.typ": *

#content-box[
  #parallel-proposition(2, note: [This proposition admits of a number of different cases, depending on the relative positions of the point $A$ and the line $B C$. In such situations, Euclid invariably only considers one particular case---usually, the most difficult---and leaves the remaining cases as exercises for the reader.])
  
  #parallel(
    [Πρὸς τῷ δοθέντι σημείῳ τῇ δοθείσῃ εὐθείᾳ ἴσην εὐθεῖαν θέσθαι.],
    [To place a straight-line equal to a given straight-line at a given point (as an extremity).],
  )

  #parallel(
    [Ἔστω τὸ μὲν δοθὲν σημεῖον τὸ Α, ἡ δὲ δοθεῖσα εὐθεῖα ἡ ΒΓ· δεῖ δὴ πρὸς τῷ Α σημείῳ τῇ δοθείσῃ εὐθείᾳ τῇ ΒΓ ἴσην εὐθεῖαν θέσθαι.],
    [Let $A$ be the given point, and $B C$ the given straight-line. So  it is required to place a straight-line at point $A$ equal to the given straight-line $B C$.],
  )

  #parallel(
    [Ἐπεζεύχθω γὰρ ἀπὸ τοῦ Α σημείου ἐπί τὸ Β σημεῖον εὐθεῖα ἡ ΑΒ, καὶ συνεστάτω ἐπ᾿ αὐτῆς τρίγωνον ἰσόπλευρον τὸ ΔΑΒ, καὶ ἐκβεβλήσθωσαν ἐπ᾿ εὐθείας ταῖς ΔΑ, ΔΒ εὐθεῖαι αἱ ΑΕ, ΒΖ, καὶ κέντρῳ μὲν τῷ Β διαστήματι δὲ τῷ ΒΓ κύκλος γεγράφθω ὁ ΓΗΘ, καὶ πάλιν κέντρῳ τῷ Δ καὶ διαστήματι τῷ ΔΗ κύκλος γεγράφθω ὁ ΗΚΛ.],
    [For  let the straight-line $A B$ be joined from point $A$ to point $B$ [Post.~1], and let the equilateral triangle $D A B$ be  constructed upon it [Prop.~1.1].  And let the straight-lines $A E$ and $B F$ be produced in a straight-line with $D A$ and $D B$  (respectively) [Post.~2]. And let the circle $C G H$ with center $B$ and radius $B C$ be drawn [Post.~3], and again let the circle $G K L$ with center $D$ and radius $D G$ be drawn [Post.~3].],
  )
  

  #parallel-image("/Book01/fig02", 3.5in)

  #parallel(
    [Ἐπεὶ οὖν τὸ Β σημεῖον κέντρον ἐστὶ τοῦ ΓΗΘ, ἴση ἐστὶν ἡ ΒΓ τῇ ΒΗ. πάλιν, ἐπεὶ τὸ Δ σημεῖον κέντρον ἐστὶ τοῦ ΗΚΛ κύκλου, ἴση ἐστὶν ἡ ΔΛ τῇ ΔΗ, ὧν ἡ ΔΑ τῇ ΔΒ ἴση ἐστίν. λοιπὴ ἄρα ἡ ΑΛ λοιπῇ τῇ ΒΗ ἐστιν ἴση. ἐδείχθη δὲ καὶ ἡ ΒΓ τῇ ΒΗ ἴση· ἑκατέρα ἄρα τῶν ΑΛ, ΒΓ τῇ ΒΗ ἐστιν ἴση. τὰ δὲ τῷ αὐτῷ ἴσα καὶ ἀλλήλοις ἐστὶν ἴσα· καὶ ἡ ΑΛ ἄρα τῇ ΒΓ ἐστιν ἴση.],
    [Therefore, since the point $B$ is the center of (the circle) $C G H$, $B C$ is equal to $B G$ [Def.~1.15]. Again, since the point $D$ is the center of the circle $G K L$, $D L$ is equal to $D G$ [Def.~1.15]. And within these,  $D A$ is equal to $D B$. Thus, the remainder $A L$ is equal to the remainder $B G$ [C.N.~3]. But $B C$ was also shown (to be)  equal to $B G$. Thus,  $A L$ and $B C$ are each equal to $B G$. But things equal to the same thing are also equal to one another [C.N.~1]. Thus, $A L$ is also equal to $B C$.],
  )

#parallel(
    [Πρὸς ἄρα τῷ δοθέντι σημείῳ τῷ Α τῇ δοθείσῃ εὐθείᾳ τῇ ΒΓ ἴση εὐθεῖα κεῖται ἡ ΑΛ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the straight-line $A L$, equal to the given straight-line $B C$, has been placed at the given point $A$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop02.lean")