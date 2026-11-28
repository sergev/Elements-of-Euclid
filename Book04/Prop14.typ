#import "../functions.typ": *

#content-box[
  #parallel-proposition(14)
  #parallel(
    [Περὶ τὸ δοθὲν πεντάγωνον, ὅ ἐστιν ἰσόπλευρόν τε καὶ ἰσογώνιον, κύκλον περιγράψαι.],
    [To circumscribe a circle about a given pentagon which is equilateral and equiangular.],
  )
  #parallel(
    [Ἔστω τὸ δοθὲν πεντάγωνον, ὅ ἐστιν ἰσόπλευρόν τε καὶ ἰσογώνιον, τὸ ΑΒΓΔΕ· δεῖ δὴ περὶ τὸ ΑΒΓΔΕ πεντάγωνον κύκλον περιγράψαι.],
    [Let $A B C D E$ be the given pentagon which is equilateral and equiangular. So it is required to circumscribe a circle about the pentagon $A B C D E$.],
  )
  #parallel-image("/Book04/fig14", 2.2in)
  #parallel(
    [Τετμήσθω δὴ ἑκατέρα τῶν ὑπὸ ΒΓΔ, ΓΔΕ γωνιῶν δίχα ὑπὸ ἑκατέρας τῶν ΓΖ, ΔΖ, καὶ ἀπὸ τοῦ Ζ σημείου, καθ᾿ ὃ συμβάλλουσιν αἱ εὐθεῖαι, ἐπὶ τὰ Β, Α, Ε σημεῖα ἐπεζεύχθωσαν εὐθεῖαι αἱ ΖΒ, ΖΑ, ΖΕ. ὁμοίως δὴ τῷ πρὸ τούτου δειχθήσεται, ὅτι καὶ ἑκάστη τῶν ὑπὸ ΓΒΑ, ΒΑΕ, ΑΕΔ γωνιῶν δίχα τέτμηται ὑπὸ ἑκάστης τῶν ΖΒ, ΖΑ, ΖΕ εὐθειῶν. καὶ ἐπεὶ ἴση ἐστὶν ἡ ὑπὸ ΒΓΔ γωνία τῇ ὑπὸ ΓΔΕ, καί ἐστι τῆς μὲν ὑπὸ ΒΓΔ ἡμίσεια ἡ ὑπὸ ΖΓΔ, τῆς δὲ ὑπὸ ΓΔΕ ἡμίσεια ἡ ὑπὸ ΓΔΖ, καὶ ἡ ὑπὸ ΖΓΔ ἄρα τῇ ὑπὸ ΖΔΓ ἐστιν ἴση· ὥστε καὶ πλευρὰ ἡ ΖΓ πλευρᾷ τῇ ΖΔ ἐστιν ἴση. ὁμοίως δὴ δειχθήσεται, ὅτι καὶ ἑκάστη τῶν ΖΒ, ΖΑ, ΖΕ ἑκατέρᾳ τῶν ΖΓ, ΖΔ ἐστιν ἴση· αἱ πέντε ἄρα εὐθεῖαι αἱ ΖΑ, ΖΒ, ΖΓ, ΖΔ, ΖΕ ἴσαι ἀλλήλαις εἰσίν. ὀ ἄρα κέντρῳ τῷ Ζ καὶ διαστήματι ἑνὶ τῶν ΖΑ, ΖΒ, ΖΓ, ΖΔ, ΖΕ κύκλος γραφόμενος ἥξει καὶ διὰ τῶν λοιπῶν σημείων καὶ ἔσται περιγεγραμμένος. περιγεγράφθω καὶ ἔστω ὁ ΑΒΓΔΕ.],
    [So let angles $B C D$ and $C D E$ have been cut in half by the (straight-lines) $C F$ and $D F$, respectively [Prop.~1.9]. And let the straight-lines $F B$, $F A$, and $F E$ be joined from point $F$, at which the straight-lines meet, to the points $B$, $A$, and $E$ (respectively). So, similarly, to the (proposition) before this (one), it can be shown that angles $C B A$, $B A E$, and $A E D$ have also been cut in half by the straight-lines $F B$, $F A$, and $F E$, respectively. And since angle $B C D$ is equal to $C D E$, and $F C D$ is half of $B C D$, and $C D F$ half of $C D E$, $F C D$ is thus also equal to $F D C$. So that side $F C$ is also equal to side $F D$ [Prop.~1.6]. So, similarly, it can be shown that $F B$, $F A$, and $F E$ are also each equal to each of $F C$ and $F D$. Thus, the five straight-lines $F A$, $F B$, $F C$, $F D$, and $F E$ are equal to one another. Thus, the circle drawn with center $F$, and radius one of $F A$, $F B$, $F C$, $F D$, or $F E$, will also go through the remaining points, and will be circumscribed. Let it be (so) circumscribed, and let it be $A B C D E$.],
  )
  #parallel(
    [Περὶ ἄρα τὸ δοθὲν πεντάγωνον, ὅ ἐστιν ἰσόπλευρόν τε καὶ ἰσογώνιον, κύκλος περιγέγραπται· ὅπερ ἔδει ποιῆσαι.],
    [Thus, a circle has been circumscribed about the given pentagon, which is equilateral and equiangular. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book4/Prop14.lean")
