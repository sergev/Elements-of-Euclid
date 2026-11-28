#import "../functions.typ": *

#content-box[
  #parallel-proposition(21)
  #parallel(
    [Ἐν κύκλῳ αἱ ἐν τῷ αὐτῷ τμήματι γωνίαι ἴσαι ἀλλήλαις εἰσίν.],
    [In a circle, angles in the same segment are equal to one another.],
  )
  #parallel-image("/Book03/fig21", 2.2in)
  #parallel(
    [Ἔστω κύκλος ὁ ΑΒΓΔ, καὶ ἐν τῷ αὐτῷ τμήματι τῷ ΒΑΕΔ γωνίαι ἔστωσαν αἱ ὑπὸ ΒΑΔ, ΒΕΔ· λέγω, ὅτι αἱ ὑπὸ ΒΑΔ, ΒΕΔ γωνίαι ἴσαι ἀλλήλαις εἰσίν.],
    [Let $A B C D$ be a circle, and let $B A D$ and $B E D$ be angles in the same segment $B A E D$. I say that angles $B A D$ and $B E D$ are equal to one another.],
  )
  #parallel(
    [Εἰλήφθω γὰρ τοῦ ΑΒΓΔ κύκλου τὸ κέντρον, καὶ ἔστω τὸ Ζ, καὶ ἐπεζεύχθωσαν αἱ ΒΖ, ΖΔ.],
    [For let the center of circle $A B C D$ be found [Prop.~3.1], and let it be (at point) $F$. And let $B F$ and $F D$ be joined.],
  )
  #parallel(
    [Καὶ ἐπεὶ ἡ μὲν ὑπὸ ΒΖΔ γωνία πρὸς τῷ κέντρῳ ἐστίν, ἡ δὲ ὑπὸ ΒΑΔ πρὸς τῇ περιφερείᾳ, καὶ ἔχουσι τὴν αὐτὴν περιφέρειαν βάσιν τὴν ΒΓΔ, ἡ ἄρα ὑπὸ ΒΖΔ γωνία διπλασίων ἐστὶ τῆς ὑπὸ ΒΑΔ. διὰ τὰ αὐτὰ δὴ ἡ ὑπὸ ΒΖΔ καὶ τῆς ὑπὸ ΒΕΔ ἐστι διπλσίων· ἴση ἄρα ἡ ὑπὸ ΒΑΔ τῇ ὑπὸ ΒΕΔ.],
    [And since angle $B F D$ is at the center, and $B A D$ at the circumference, and they have the same circumference base $B C D$, angle $B F D$ is thus double $B A D$ [Prop.~3.20]. So, for the same (reasons), $B F D$ is also double $B E D$. Thus, $B A D$ (is) equal to $B E D$.],
  )
  #parallel(
    [Ἐν κύκλῳ ἄρα αἱ ἐν τῷ αὐτῷ τμήματι γωνίαι ἴσαι ἀλλήλαις εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, in a circle, angles in the same segment are equal to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop21.lean")
