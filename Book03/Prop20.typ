#import "../functions.typ": *

#content-box[
  #parallel-proposition(20)
  #parallel(
    [Ἐν κύκλῳ ἡ πρὸς τῷ κέντρῳ γωνία διπλασίων ἐστὶ τῆς πρὸς τῇ περιφερείᾳ, ὅταν τὴν αὐτὴν περιφέρειαν βάσιν ἔχωσιν αἱ γωνίαι.],
    [In a circle, the angle at the center is double that at the circumference, when the angles have the same circumference base.],
  )
  #parallel(
    [Ἔστω κύκλος ὁ ΑΒΓ, καὶ πρὸς μὲν τῷ κέντρῳ αὐτοῦ γωνία ἔστω ἡ ὑπὸ ΒΕΓ, πρὸς δὲ τῇ περιφερείᾳ ἡ ὑπὸ ΒΑΓ, ἐχέτωσαν δὲ τὴν αὐτὴν περιφέρειαν βάσιν τὴν ΒΓ· λέγω, ὅτι διπλασίων ἐστὶν ἡ ὑπὸ ΒΕΓ γωνία τῆς ὑπὸ ΒΑΓ.],
    [Let $A B C$ be a circle, and let $B E C$ be an angle at its center, and $B A C$ (one) at (its) circumference. And let them have the same circumference base $B C$. I say that angle $B E C$ is double (angle) $B A C$.],
  )
  #parallel(
    [Ἐπιζευχθεῖσα γὰρ ἡ ΑΕ διήχθω ἐπὶ τὸ Ζ.],
    [For being joined, let $A E$ be drawn through to $F$.],
  )
  #parallel(
    [Ἐπεὶ οὖν ἴση ἐστὶν ἡ ΕΑ τῇ ΕΒ, ἴση καὶ γωνία ἡ ὑπὸ ΕΑΒ τῇ ὑπὸ ΕΒΑ· αἱ ἄρα ὑπὸ ΕΑΒ, ΕΒΑ γωνίαι τῆς ὑπὸ ΕΑΒ διπλασίους εἰσίν. ἴση δὲ ἡ ὑπὸ ΒΕΖ ταῖς ὑπὸ ΕΑΒ, ΕΒΑ· καὶ ἡ ὑπὸ ΒΕΖ ἄρα τῆς ὑπὸ ΕΑΒ ἐστι διπλῆ. διὰ τὰ αὐτὰ δὴ καὶ ἡ ὑπὸ ΖΕΓ τῆς ὑπὸ ΕΑΓ ἐστι διπλῆ. ὅλη ἄρα ἡ ὑπὸ ΒΕΓ ὅλης τῆς ὑπὸ ΒΑΓ ἐστι διπλῆ.],
    [Therefore, since $E A$ is equal to $E B$, angle $E A B$ (is) also equal to $E B A$ [Prop.~1.5]. Thus, angle $E A B$ and $E B A$ is double (angle) $E A B$. And $B E F$ (is) equal to $E A B$ and $E B A$ [Prop.~1.32]. Thus, $B E F$ is also double $E A B$. So, for the same (reasons), $F E C$ is also double $E A C$. Thus, the whole (angle) $B E C$ is double the whole (angle) $B A C$.],
  )
  #parallel-image("/Book03/fig20", 2.2in)
  #parallel(
    [Κεκλάσθω δὴ πάλιν, καὶ ἔστω ἑτέρα γωνία ἡ ὑπὸ ΒΔΓ, καὶ ἐπιζευχθεῖσα ἡ ΔΕ ἐκβεβλήσθω ἐπὶ τὸ Η. ὁμοίως δὴ δείξομεν, ὅτι διπλῆ ἐστιν ἡ ὑπὸ ΗΕΓ γωνία τῆς ὑπὸ ΕΔΓ, ὧν ἡ ὑπὸ ΗΕΒ διπλῆ ἐστι τῆς ὑπὸ ΕΔΒ· λοιπὴ ἄρα ἡ ὑπὸ ΒΕΓ διπλῆ ἐστι τῆς ὑπὸ ΒΔΓ.],
    [So let another (straight-line) be inflected, and let there be another angle, $B D C$. And $D E$ being joined, let it be produced to $G$. So, similarly, we can show that angle $G E C$ is double $E D C$, of which $G E B$ is double $E D B$. Thus, the remaining (angle) $B E C$ is double the (remaining angle) $B D C$.],
  )
  #parallel(
    [Ἐν κύκλῳ ἄρα ἡ πρὸς τῷ κέντρῳ γωνία διπλασίων ἐστὶ τῆς πρὸς τῇ περιφερείᾳ, ὅταν τὴν αὐτὴν περιφέρειαν βάσιν ἔχωσιν [αἱ γωνίαι]· ὅπερ ἔδει δεῖξαι.],
    [Thus, in a circle, the angle at the center is double that at the circumference, when [the angles] have the same circumference base. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop20.lean")
