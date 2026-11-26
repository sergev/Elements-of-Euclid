#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig42(letters) = fig({
  
})

#content-box[
  #parallel-proposition(42)
  #parallel(
    [Τῷ δοθέντι τριγώνῳ ἴσον παραλληλόγραμμον συστήσασθαι ἐν τῇ δοθείσῃ γωνίᾳ εὐθυγράμμῳ.],
    [To construct a parallelogram equal to a given triangle in a given rectilinear angle.],
  )
  #parallel(
    [῎Εστω τὸ μὲν δοθὲν τρίγωνον τὸ ΑΒΓ, ἡ δὲ δοθεῖσα γωνία εὐθύγραμμος ἡ Δ· δεῖ δὴ τῷ ΑΒΓ τριγώνῳ ἴσον παραλληλόγραμμον συστήσασθαι ἐν τῇ Δ γωνίᾳ εὐθυγράμμῳ.],
    [Let $A B C$ be the given triangle, and $D$ the given rectilinear angle. So it is required to construct a parallelogram equal to triangle $A B C$ in the rectilinear angle $D$.],
  )
  #parallel(
    [Τετμήσθω ἡ ΒΓ δίχα κατὰ τὸ Ε, καὶ ἐπεζεύχθω ἡ ΑΕ, καὶ συνεστάτω πρὸς τῇ ΕΓ εὐθείᾳ καὶ τῷ πρὸς αὐτῇ σημείῳ τῷ Ε τῇ Δ γωνίᾳ ἴση ἡ ὑπὸ ΓΕΖ, καὶ διὰ μὲν τοῦ Α τῇ ΕΓ παράλληλος ἤχθω ἡ ΑΗ, διὰ δὲ τοῦ Γ τῇ ΕΖ παράλληλος ἤχθω ἡ ΓΗ· παραλληλόγραμμον ἄρα ἐστὶ τὸ ΖΕΓΗ. καὶ ἐπεὶ ἴση ἐστὶν ἡ ΒΕ τῇ ΕΓ, ἴσον ἐστὶ καὶ τὸ ΑΒΕ τρίγωνον τῷ ΑΕΓ τριγώνῳ· ἐπί τε γὰρ ἴσων βάσεών εἰσι τῶν ΒΕ, ΕΓ καὶ ἐν ταῖς αὐταῖς παραλλήλοις ταῖς ΒΓ, ΑΗ· διπλάσιον ἄρα ἐστὶ τὸ ΑΒΓ τρίγωνον τοῦ ΑΕΓ τριγώνου. ἔστι δὲ καὶ τὸ ΖΕΓΗ παραλληλόγραμμον διπλάσιον τοῦ ΑΕΓ τριγώνου· βάσιν τε γὰρ αὐτῷ τὴν αὐτὴν ἔχει καὶ ἐν ταῖς αὐταῖς ἐστιν αὐτῷ παραλλήλοις· ἴσον ἄρα ἐστὶ τὸ ΖΕΓΗ παραλληλόγραμμον τῷ ΑΒΓ τριγώνῳ. καὶ ἔχει τὴν ὑπὸ ΓΕΖ γωνίαν ἴσην τῇ δοθείσῃ τῇ Δ.],
    [Let $B C$ be cut in half at $E$ [Prop. 1.10], and let $A E$ be joined. And let (angle) $C E F$, equal to angle $D$, be constructed at the point $E$ on the straight-line $E C$ [Prop. 1.23]. And let $A G$ be drawn through $A$ parallel to $E C$ [Prop. 1.31], and let $C G$ be drawn through $C$ parallel to $E F$ [Prop. 1.31]. Thus, $F E C G$ is a parallelogram. And since $B E$ is equal to $E C$, triangle $A B E$ is also equal to triangle $A E C$. For they are on the equal bases, $B E$ and $E C$, and between the same parallels, $B C$ and $A G$ [Prop. 1.38]. Thus, triangle $A B C$ is double (the area) of triangle $A E C$. And parallelogram $F E C G$ is also double (the area) of triangle $A E C$. For it has the same base (as $A E C$), and is between the same parallels (as $A E C$) [Prop. 1.41]. Thus, parallelogram $F E C G$ is equal to triangle $A B C$. ($F E C G$) also has the angle $C E F$ equal to the given (angle) $D$.],
  )
  #parallel-fig(fig42)
  #parallel(
    [Τῷ ἄρα δοθέντι τριγώνῳ τῷ ΑΒΓ ἴσον παραλληλόγραμμον συνέσταται τὸ ΖΕΓΗ ἐν γωνίᾳ τῇ ὑπὸ ΓΕΖ, ἥτις ἐστὶν ἴση τῇ Δ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, parallelogram $F E C G$, equal to the given triangle $A B C$, has been constructed in the angle $C E F$, which is equal to $D$. (Which is) the very thing it was required to do.],
  )
]