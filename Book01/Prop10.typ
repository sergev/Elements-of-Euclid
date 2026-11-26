#import "../functions.typ": *

#content-box[
  #parallel-proposition(10)
  #parallel(
    [Τὴν δοθεῖσαν εὐθεῖαν πεπερασμένην δίχα τεμεῖν.],
    [To cut a given finite straight-line in half.],
  )
  #parallel(
    [Ἔστω ἡ δοθεῖσα εὐθεῖα πεπερασμένη ἡ ΑΒ· δεῖ δὴ τὴν ΑΒ εὐθεῖαν πεπερασμένην δίχα τεμεῖν.],
    [Let $A B$ be the given finite straight-line. So it is required to cut the finite straight-line $A B$ in half.],
  )
  #parallel(
    [Συνεστάτω ἐπ᾿ αὐτῆς τρίγωνον ἰσόπλευρον τὸ ΑΒΓ, καὶ τετμήσθω ἡ ὑπὸ ΑΓΒ γωνία δίχα τῇ ΓΔ εὐθείᾳ· λέγω, ὅτι ἡ ΑΒ εὐθεῖα δίχα τέτμηται κατὰ τὸ Δ σημεῖον.],
    [Let the equilateral triangle $A B C$ be constructed upon ($A B$) [Prop.~1.1], and let the angle $A C B$ be cut in half by the straight-line $C D$ [Prop.~1.9]. I say that the straight-line $A B$ has been cut in half at point $D$.],
  )
  #parallel-image("/Book01/fig10", 2in)
  #parallel(
    [Ἐπεὶ γὰρ ἴση ἐστὶν ἡ ΑΓ τῇ ΓΒ, κοινὴ δὲ ἡ ΓΔ, δύο δὴ αἱ ΑΓ, ΓΔ δύο ταῖς ΒΓ, ΓΔ ἴσαι εἰσὶν ἑκατέρα ἑκατέρᾳ· καὶ γωνία ἡ ὑπὸ ΑΓΔ γωνίᾳ τῇ ὑπὸ ΒΓΔ ἴση ἐστίν· βάσις ἄρα ἡ ΑΔ βάσει τῇ ΒΔ ἴση ἐστίν.],
    [For since $A C$ is equal to $C B$, and $C D$ (is) common, the two (straight-lines) $A C$, $C D$ are equal to the two (straight-lines) $B C$, $C D$, respectively. And the angle $A C D$ is equal to the angle $B C D$. Thus, the base $A D$ is equal to the base $B D$ [Prop.~1.4].],
  )
  #parallel(
    [Ἡ ἄρα δοθεῖσα εὐθεῖα πεπερασμένη ἡ ΑΒ δίχα τέτμηται κατὰ τὸ Δ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, the given finite straight-line $A B$ has been cut in half at (point) $D$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop10.lean")
