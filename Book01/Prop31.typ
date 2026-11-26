#import "../functions.typ": *

#content-box[
  #parallel-proposition(31)
  #parallel(
    [Διὰ τοῦ δοθέντος σημείου τῇ δοθείσῃ εὐθείᾳ παράλληλον εὐθεῖαν γραμμὴν ἀγαγεῖν.],
    [To draw a straight-line parallel to a given straight-line, through a given point.],
  )
  #parallel(
    [Ἔστω τὸ μὲν δοθὲν σημεῖον τὸ Α, ἡ δὲ δοθεῖσα εὐθεῖα ἡ ΒΓ· δεῖ δὴ διὰ τοῦ Α σημείου τῇ ΒΓ εὐθείᾳ παράλληλον εὐθεῖαν γραμμὴν ἀγαγεῖν.],
    [Let $A$ be the given point, and $B C$ the given straight-line. So it is required to draw a straight-line parallel to the straight-line $B C$, through the point $A$.],
  )
  #parallel(
    [Εἰλήφθω ἐπὶ τῆς ΒΓ τυχὸν σημεῖον τὸ Δ, καὶ ἐπεζεύχθω ἡ ΑΔ· καὶ συνεστάτω πρὸς τῇ ΔΑ εὐθείᾳ καὶ τῷ πρὸς αὐτῇ σημείῳ τῷ Α τῇ ὑπὸ ΑΔΓ γωνίᾳ ἴση ἡ ὑπὸ ΔΑΕ· καὶ ἐκβεβλήσθω ἐπ᾿ εὐθείας τῇ ΕΑ εὐθεῖα ἡ ΑΖ.],
    [Let the point $D$ be taken at random on $B C$, and let $A D$ be joined. And let (angle) $D A E$, equal to angle $A D C$, be constructed on the straight-line $D A$ at the point $A$ on it [Prop.~1.23]. And let the straight-line $A F$ be produced in a straight-line with $E A$.],
  )
  #parallel-image("/Book01/fig31", 1.25in)
  #parallel(
    [Καὶ ἐπεὶ εἰς δύο εὐθείας τὰς ΒΓ, ΕΖ εὐθεῖα ἐμπίπτουσα ἡ ΑΔ τὰς ἐναλλὰξ γωνίας τὰς ὑπὸ ΕΑΔ, ΑΔΓ ἴσας ἀλλήλαις πεποίηκεν, παράλληλος ἄρα ἐστὶν ἡ ΕΑΖ τῇ ΒΓ.],
    [And since the straight-line $A D$, (in) falling across the two straight-lines $B C$ and $E F$, has made the alternate angles $E A D$ and $A D C$ equal to one another, $E A F$ is thus parallel to $B C$ [Prop.~1.27].],
  )
  #parallel(
    [Διὰ τοῦ δοθέντος ἄρα σημείου τοῦ Α τῇ δοθείσῃ εὐθείᾳ τῇ ΒΓ παράλληλος εὐθεῖα γραμμὴ ἦκται ἡ ΕΑΖ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the straight-line $E A F$ has been drawn parallel to the given straight-line $B C$, through the given point $A$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop31.lean")