#import "../functions.typ": *

#content-box[
  #parallel-proposition(11)
  #parallel(
    [Τῇ δοθείσῃ εὐθείᾳ ἀπὸ τοῦ πρὸς αὐτῇ δοθέντος σημείου πρὸς ὀρθὰς γωνίας εὐθεῖαν γραμμὴν ἀγαγεῖν.],
    [To draw a straight-line at right-angles to a given straight-line from a given point on it.],
  )
  #parallel(
    [Ἔστω ἡ μὲν δοθεῖσα εὐθεῖα ἡ ΑΒ τὸ δὲ δοθὲν σημεῖον ἐπ᾿ αὐτῆς τὸ Γ· δεῖ δὴ ἀπὸ τοῦ Γ σημείου τῇ ΑΒ εὐθείᾳ πρὸς ὀρθὰς γωνίας εὐθεῖαν γραμμὴν ἀγαγεῖν.],
    [Let $A B$ be the given straight-line, and $C$ the given point on it. So it is required to draw a straight-line from the point $C$ at right-angles to the straight-line $A B$.],
  )
  #parallel-image("/Book01/fig11", 1.8in)
  #parallel(
    [Εἰλήφθω ἐπὶ τῆς ΑΓ τυχὸν σημεῖον τὸ Δ, καὶ κείσθω τῇ ΓΔ ἴση ἡ ΓΕ, καὶ συνεστάτω ἐπὶ τῆς ΔΕ τρίγωνον ἰσόπλευρον τὸ ΖΔΕ, καὶ ἐπεζεύχθω ἡ ΖΓ· λέγω, ὅτι τῇ δοθείσῃ εὐθείᾳ τῇ ΑΒ ἀπὸ τοῦ πρὸς αὐτῇ δοθέντος σημείου τοῦ Γ πρὸς ὀρθὰς γωνίας εὐθεῖα γραμμὴ ἦκται ἡ ΖΓ.],
    [Let the point $D$ be taken at random on $A C$, and let $C E$ be made equal to $C D$ [Prop.~1.3], and let the equilateral triangle $F D E$ be constructed on $D E$ [Prop.~1.1], and let $F C$ be joined. I say that the straight-line $F C$ has been drawn at right-angles to the given straight-line $A B$ from the given point $C$ on it.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ἴση ἐστὶν ἡ ΔΓ τῇ ΓΕ, κοινὴ δὲ ἡ ΓΖ, δύο δὴ αἱ ΔΓ, ΓΖ δυσὶ ταῖς ΕΓ, ΓΖ ἴσαι εἰσὶν ἑκατέρα ἑκατέρᾳ· καὶ βάσις ἡ ΔΖ βάσει τῇ ΖΕ ἴση ἐστίν· γωνία ἄρα ἡ ὑπὸ ΔΓΖ γωνίᾳ τῇ ὑπὸ ΕΓΖ ἴση ἐστίν· καί εἰσιν ἐφεξῆς. ὅταν δὲ εὐθεῖα ἐπ᾿ εὐθεῖαν σταθεῖσα τὰς ἐφεξῆς γωνίας ἴσας ἀλλήλαις ποιῇ, ὀρθὴ ἑκατέρα τῶν ἴσων γωνιῶν ἐστιν· ὀρθὴ ἄρα ἐστὶν ἑκατέρα τῶν ὑπὸ ΔΓΖ, ΖΓΕ.],
    [For since $D C$ is equal to $C E$, and $C F$ is common, the two (straight-lines) $D C$, $C F$ are equal to the two (straight-lines) $E C$, $C F$, respectively. And the base $D F$ is equal to the base $F E$. Thus, the angle $D C F$ is equal to the angle $E C F$ [Prop.~1.8], and they are adjacent. But when a straight-line stood on a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle [Def.~1.10]. Thus, each of the (angles) $D C F$ and $F C E$ is a right-angle.],
  )
  #parallel(
    [Τῇ ἄρα δοθείσῃ εὐθείᾳ τῇ ΑΒ ἀπὸ τοῦ πρὸς αὐτῇ δοθέντος σημείου τοῦ Γ πρὸς ὀρθὰς γωνίας εὐθεῖα γραμμὴ ἦκται ἡ ΓΖ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the straight-line $C F$ has been drawn at right-angles to the given straight-line $A B$ from the given point $C$ on it. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop11.lean")
