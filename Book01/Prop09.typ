#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig09(letters) = fig({
  import cetz.draw: *
  let A = (0, 0)
  let B = (-2.2, -5)
  let C = (2.2, -5)
  let D = cetz.vector.lerp(A, B, 0.5)
  let E = cetz.vector.lerp(A, C, 0.5)
  let F = (0, -4.3)
  
  // lines
  line(A, B)
  line(A, C)
  line(D, E)
  line(D, F)
  line(E, F)

  // labels
  content(A, letters.at("A"), anchor: "south")
  content(B, letters.at("B"), anchor: "south")
  content(C, letters.at("C"), anchor: "south")
  content(D, letters.at("D"), anchor: "east")
  content(E, letters.at("E"), anchor: "west")
  content(F, letters.at("F"), anchor: "north")
})

#content-box[
  #parallel-proposition(9)
  #parallel(
    [Τὴν δοθεῖσαν γωνίαν εὐθύγραμμον δίχα τεμεῖν.],
    [To cut a given rectilinear angle in half.],
  )
  #parallel(
    [῎Εστω ἡ δοθεῖσα γωνία εὐθύγραμμος ἡ ὑπὸ ΒΑΓ. δεῖ δὴ αὐτὴν δίχα τεμεῖν.],
    [Let $B A C$ be the given rectilinear angle. So it is required to cut it in half.],
  )
  #parallel(
    [Εἰλήφθω ἐπὶ τῆς ΑΒ τυχὸν σημεῖον τὸ Δ, καὶ ἀφῃρήσθω ἀπὸ τῆς ΑΓ τῇ ΑΔ ἴση ἡ ΑΕ, καὶ ἐπεζεύχθω ἡ ΔΕ, καὶ συνεστάτω ἐπὶ τῆς ΔΕ τρίγωνον ἰσόπλευρον τὸ ΔΕΖ, καὶ ἐπεζεύχθω ἡ ΑΖ· λέγω, ὅτι ἡ ὑπὸ ΒΑΓ γωνία δίχα τέτμηται ὑπὸ τῆς ΑΖ εὐθείας.],
    [Let the point $D$ be taken at random on $A B$, and let $A E$, equal to $A D$, be cut off from $A C$ [Prop.~1.3], and let $D E$ be joined. And let the equilateral triangle $D E F$ be constructed upon $D E$ [Prop.~1.1], and let $A F$ be joined. I say that the angle $B A C$ has been cut in half by the straight-line $A F$.],
  )
  #parallel(
    [᾿Επεὶ γὰρ ἴση ἐστὶν ἡ ΑΔ τῇ ΑΕ, κοινὴ δὲ ἡ ΑΖ, δύο δὴ αἱ ΔΑ, ΑΖ δυσὶ ταῖς ΕΑ, ΑΖ ἴσαι εἰσὶν ἑκατέρα ἑκατέρᾳ. καὶ βάσις ἡ ΔΖ βάσει τῇ ΕΖ ἴση ἐστίν· γωνία ἄρα ἡ ὑπὸ ΔΑΖ γωνίᾳ τῇ ὑπὸ ΕΑΖ ἴση ἐστίν.],
    [For since $A D$ is equal to $A E$, and $A F$ is common, the two (straight-lines) $D A$, $A F$ are equal to the two (straight-lines) $E A$, $A F$, respectively. And the base $D F$ is equal to the base $E F$. Thus, angle $D A F$ is equal to angle $E A F$ [Prop.~1.8].],
  )
  #parallel-fig(fig09)
  #parallel(
    [῾Η ἄρα δοθεῖσα γωνία εὐθύγραμμος ἡ ὑπὸ ΒΑΓ δίχα τέτμηται ὑπὸ τῆς ΑΖ εὐθείας· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the given rectilinear angle $B A C$ has been cut in half by the straight-line $A F$. (Which is) the very thing it was required to do.],
  )
]
