#import "../functions.typ": *

#content-box[
  #parallel-proposition(9)
  #parallel(
    [Περὶ τὸ δοθὲν τετράγωνον κύκλον περιγράψαι.],
    [To circumscribe a circle about a given square.],
  )
  #parallel(
    [Ἔστω τὸ δοθὲν τετράγωνον τὸ ΑΒΓΔ· δεῖ δὴ περὶ τὸ ΑΒΓΔ τετράγωνον κύκλον περιγράψαι.],
    [Let $A B C D$ be the given square. So it is required to circumscribe a circle about square $A B C D$.],
  )
  #parallel(
    [Ἐπιζευχθεῖσαι γὰρ αἱ ΑΓ, ΒΔ τεμνέτωσαν ἀλλήλας κατὰ τὸ Ε.],
    [$A C$ and $B D$ being joined, let them cut one another at $E$.],
  )
  #parallel-image("/Book04/fig06", 2.2in)
  #parallel(
    [Καὶ ἐπεὶ ἴση ἐστὶν ἡ ΔΑ τῇ ΑΒ, κοινὴ δὲ ἡ ΑΓ, δύο δὴ αἱ ΔΑ, ΑΓ δυσὶ ταῖς ΒΑ, ΑΓ ἴσαι εἰσίν· καὶ βάσις ἡ ΔΓ βάσει τῇ ΒΓ ἴση· γωνία ἄρα ἡ ὑπὸ ΔΑΓ γωνίᾳ τῇ ὑπὸ ΒΑΓ ἴση ἐστίν· ἡ ἄρα ὑπὸ ΔΑΒ γωνία δίχα τέτμηται ὑπὸ τῆς ΑΓ. ὁμοίως δὴ δείξομεν, ὅτι καὶ ἑκάστη τῶν ὑπὸ ΑΒΓ, ΒΓΔ, ΓΔΑ δίχα τέτμηται ὑπὸ τῶν ΑΓ, ΔΒ εὐθειῶν. καὶ ἐπεὶ ἴση ἐστὶν ἡ ὑπὸ ΔΑΒ γωνία τῇ ὑπὸ ΑΒΓ, καί ἐστι τῆς μὲν ὑπὸ ΔΑΒ ἡμίσεια ἡ ὑπὸ ΕΑΒ, τῆς δὲ ὑπὸ ΑΒΓ ἡμίσεια ἡ ὑπὸ ΕΒΑ, καὶ ἡ ὑπὸ ΕΑΒ ἄρα τῇ ὑπὸ ΕΒΑ ἐστιν ἴση· ὥστε καὶ πλευρὰ ἡ ΕΑ τῇ ΕΒ ἐστιν ἴση. ὁμοίως δὴ δείξομεν, ὅτι καὶ ἑκατέρα τῶν ΕΑ, ΕΒ [εὐθειῶν] ἑκατέρᾳ τῶν ΕΓ, ΕΔ ἴση ἐστίν. αἱ τέσσαρες ἄρα αἱ ΕΑ, ΕΒ, ΕΓ, ΕΔ ἴσαι ἀλλήλαις εἰσίν. ὁ ἄρα κέντρῳ τῷ Ε καὶ διαστήματι ἑνὶ τῶν Α, Β, Γ, Δ κύκλος γραφόμενος ἥξει καὶ διὰ τῶν λοιπῶν σημείων καὶ ἔσται περιγεγραμμένος περὶ τὸ ΑΒΓΔ τετράγωνον. περιγεγράφθω ὡς ὁ ΑΒΓΔ.],
    [And since $D A$ is equal to $A B$, and $A C$ (is) common, the two (straight-lines) $D A$, $A C$ are thus equal to the two (straight-lines) $B A$, $A C$. And the base $D C$ (is) equal to the base $B C$. Thus, angle $D A C$ is equal to angle $B A C$ [Prop.~1.8]. Thus, the angle $D A B$ has been cut in half by $A C$. So, similarly, we can show that $A B C$, $B C D$, and $C D A$ have each been cut in half by the straight-lines $A C$ and $D B$. And since angle $D A B$ is equal to $A B C$, and $E A B$ is half of $D A B$, and $E B A$ half of $A B C$, $E A B$ is thus also equal to $E B A$. So that side $E A$ is also equal to $E B$ [Prop.~1.6]. So, similarly, we can show that each of the [straight-lines] $E A$ and $E B$ are also equal to each of $E C$ and $E D$. Thus, the four (straight-lines) $E A$, $E B$, $E C$, and $E D$ are equal to one another. Thus, the circle drawn with center $E$, and radius one of $A$, $B$, $C$, or $D$, will also go through the remaining points, and will be circumscribed about the square $A B C D$. Let it be (so) circumscribed, like $A B C D$ (in the figure).],
  )
  #parallel(
    [Περὶ τὸ δοθὲν ἄρα τετράγωνον κύκλος περιγέγραπται· ὅπερ ἔδει ποιῆσαι.],
    [Thus, a circle has been circumscribed about the given square. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book4/Prop09.lean")
