#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig12(letters) = fig({
  import cetz.draw: *
  let r = 3
  let G = (0, 0)
  let E = (r, 0)
  let C = cetz.vector.rotate-z(E, 60deg)
  let H = cetz.vector.lerp(G, E, 0.5)
  let A = cetz.vector.lerp(G, E, 0-0.5)
  let B = cetz.vector.lerp(G, E, 1+0.5)
  let Flabel = cetz.vector.add(C, (0, r))
  let CE = cetz.vector.sub(E, C)
  let D = cetz.vector.rotate-z(CE, -18deg)
  D = cetz.vector.add(C, D)
  let tick = (-0.05, 0.1)

  // lines
  line(A, B)
  line(G, E)
  line(G, C)
  line(E, C)
  line(C, H)
  circle(C, radius: r)
  line(cetz.vector.add(D, tick), cetz.vector.sub(D, tick))

  // labels
  content(A, letters.at("A"), anchor: "south")
  content(B, letters.at("B"), anchor: "south")
  content(G, letters.at("G"), anchor: "north")
  content(E, letters.at("E"), anchor: "north")
  content(C, letters.at("C"), anchor: "south")
  content(H, letters.at("H"), anchor: "north")
  content(D, letters.at("D"), anchor: "north-west")
  content(Flabel, letters.at("F"), anchor: "south")
})

#content-box[
  #parallel-proposition(12)
  #parallel(
    [᾿Επὶ τὴν δοθεῖσαν εὐθεῖαν ἄπειρον ἀπὸ τοῦ δοθέντος σημείου, ὃ μή ἐστιν ἐπ᾿ αὐτῆς, κάθετον εὐθεῖαν γραμμὴν ἀγαγεῖν.],
    [To draw a straight-line perpendicular to a given infinite straight-line from a given point which is not on it.],
  )
  #parallel-fig(fig12)
  #parallel(
    [῎Εστω ἡ μὲν δοθεῖσα εὐθεῖα ἄπειρος ἡ ΑΒ τὸ δὲ δοθὲν σημεῖον, ὃ μή ἐστιν ἐπ᾿ αὐτῆς, τὸ Γ· δεῖ δὴ ἐπὶ τὴν δοθεῖσαν εὐθεῖαν ἄπειρον τὴν ΑΒ ἀπὸ τοῦ δοθέντος σημείου τοῦ Γ, ὃ μή ἐστιν ἐπ᾿ αὐτῆς, κάθετον εὐθεῖαν γραμμὴν ἀγαγεῖν.],
    [Let $A B$ be the given infinite straight-line and $C$ the given point, which is not on it. So it is required to draw a straight-line perpendicular to the given infinite straight-line $A B$ from the given point $C$, which is not on it.],
  )
  #parallel(
    [Εἰλήφθω γὰρ ἐπὶ τὰ ἕτερα μέρη τῆς ΑΒ εὐθείας τυχὸν σημεῖον τὸ Δ, καὶ κέντρῳ μὲν τῷ Γ διαστήματι δὲ τῷ ΓΔ κύκλος γεγράφθω ὁ ΕΖΗ, καὶ τετμήσθω ἡ ΕΗ εὐθεῖα δίχα κατὰ τὸ Θ, καὶ ἐπεζεύχθωσαν αἱ ΓΗ, ΓΘ, ΓΕ εὐθεῖαι· λέγω, ὅτι ἐπὶ τὴν δοθεῖσαν εὐθεῖαν ἄπειρον τὴν ΑΒ ἀπὸ τοῦ δοθέντος σημείου τοῦ Γ, ὃ μή ἐστιν ἐπ᾿ αὐτῆς, κάθετος ᾿ῆκται ἡ ΓΘ.],
    [For let point $D$ be taken at random on the other side (to $C$) of the straight-line $A B$, and let the circle $E F G$ be drawn with center $C$ and radius $C D$ [Post. 3], and let the straight-line $E G$ be cut in half at (point) $H$ [Prop. 1.10], and let the straight-lines $C G$, $C H$, and $C E$ be joined. I say that the (straight-line) $C H$ has been drawn perpendicular to the given infinite straight-line $A B$ from the given point $C$, which is not on it.],
  )
  #parallel(
    [᾿Επεὶ γὰρ ἴση ἐστὶν ἡ ΗΘ τῇ ΘΕ, κοινὴ δὲ ἡ ΘΓ, δύο δὴ αἱ ΗΘ, ΘΓ δύο ταῖς ΕΘ, ΘΓ ἴσαι εἱσὶν ἑκατέρα ἑκατέρᾳ· καὶ βάσις ἡ ΓΗ βάσει τῇ ΓΕ ἐστιν ἴση· γωνία ἄρα ἡ ὑπὸ ΓΘΗ γωνίᾳ τῇ ὑπὸ ΕΘΓ ἐστιν ἴση. καί εἰσιν ἐφεξῆς. ὅταν δὲ εὐθεῖα ἐπ᾿ εὐθεῖαν σταθεῖσα τὰς ἐφεξῆς γωνίας ἴσας ἀλλήλαις ποιῇ, ὀρθὴ ἑκατέρα τῶν ἴσων γωνιῶν ἐστιν, καὶ ἡ ἐφεστηκυῖα εὐθεῖα κάθετος καλεῖται ἐφ᾿ ἣν ἐφέστηκεν.],
    [For since $G H$ is equal to $H E$, and $H C$ (is) common, the two (straight-lines) $G H$, $H C$ are equal to the two (straight-lines) $E H$, $H C$, respectively, and the base $C G$ is equal to the base $C E$. Thus, the angle $C H G$ is equal to the angle $E H C$ [Prop. 1.8], and they are adjacent. But when a straight-line stood on a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle, and the former straight-line is called a perpendicular to that upon which it stands [Def. 1.10].],
  )
  #parallel(
    [᾿Επὶ τὴν δοθεῖσαν ἄρα εὐθεῖαν ἄπειρον τὴν ΑΒ ἀπὸ τοῦ δοθέντος σημείου τοῦ Γ, ὃ μή ἐστιν ἐπ᾿ αὐτῆς, κάθετος ἦκται ἡ ΓΘ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the (straight-line) $C H$ has been drawn perpendicular to the given infinite straight-line $A B$ from the given point $C$, which is not on it. (Which is) the very thing it was required to do.],
  )
]
