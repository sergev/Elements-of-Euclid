#import "../functions.typ": *

#content-box[
  #parallel-proposition(1)
  #parallel(
    [Τοῦ δοθέντος κύκλου τὸ κέντρον εὑρεῖν.],
    [To find the center of a given circle.],
  )
  #parallel(
    [Ἔστω ὁ δοθεὶς κύκλος ὁ ΑΒΓ· δεῖ δὴ τοῦ ΑΒΓ κύκλου τὸ κέντρον εὑρεῖν.],
    [Let $A B C$ be the given circle. So it is required to find the center of circle $A B C$.],
  )
  #parallel(
    [Διήχθω τις εἰς αὐτόν, ὡς ἔτυχεν, εὐθεῖα ἡ ΑΒ, καὶ τετμήσθω δίχα κατὰ τὸ Δ σημεῖον, καὶ ἀπὸ τοῦ Δ τῇ ΑΒ πρὸς ὀρθὰς ἤχθω ἡ ΔΓ καὶ διήχθω ἐπὶ τὸ Ε, καὶ τετμήσθω ἡ ΓΕ δίχα κατὰ τὸ Ζ· λέγω, ὅτι τὸ Ζ κέντρον ἐστὶ τοῦ ΑΒΓ [κύκλου].],
    [Let some straight-line $A B$ be drawn through ($A B C$), at random, and let ($A B$) be cut in half at point $D$ [Prop.~1.9]. And let $D C$ be drawn from $D$, at right-angles to $A B$ [Prop.~1.11]. And let ($C D$) be drawn through to $E$. And let $C E$ be cut in half at $F$ [Prop.~1.9]. I say that (point) $F$ is the center of the [circle] $A B C$.],
  )
  #parallel(
    [μὴ γάρ, ἀλλ᾿ εἰ δυνατόν, ἔστω τὸ Η, καὶ ἐπεζεύχθωσαν αἱ ΗΑ, ΗΔ, ΗΒ. καὶ ἐπεὶ ἴση ἐστὶν ἡ ΑΔ τῇ ΔΒ, κοινὴ δὲ ἡ ΔΗ, δύο δὴ αἱ ΑΔ, ΔΗ δύο ταῖς ΗΔ, ΔΒ ἴσαι εἰσὶν ἑκατέρα ἑκατέρᾳ· καὶ βάσις ἡ ΗΑ βάσει τῇ ΗΒ ἐστιν ἴση· ἐκ κέντρου γάρ· γωνία ἄρα ἡ ὑπὸ ΑΔΗ γωνίᾳ τῇ ὑπὸ ΗΔΒ ἴση ἐστίν. ὅταν δὲ εὐθεῖα ἐπ᾿ εὐθεῖαν σταθεῖσα τὰς ἐφεξῆς γωνίας ἴσας ἀλλήλαις ποιῇ, ὀρθὴ ἑκατέρα τῶν ἴσων γωνιῶν ἐστιν· ὀρθὴ ἄρα ἐστὶν ἡ ὑπὸ ΗΔΒ. ἐστὶ δὲ καὶ ἡ ὑπὸ ΖΔΒ ὀρθή· ἴση ἄρα ἡ ὑπὸ ΖΔΒ τῇ ὑπὸ ΗΔΒ, ἡ μείζων τῇ ἐλάττονι· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα τὸ Η κέντρον ἐστὶ τοῦ ΑΒΓ κύκλου. ὁμοίως δὴ δείξομεν, ὅτι οὐδ᾿ ἄλλο τι πλὴν τοῦ Ζ.],
    [For (if) not (then), if possible, let $G$ (be the center of the circle), and let $G A$, $G D$, and $G B$ be joined. And since $A D$ is equal to $D B$, and $D G$ (is) common, the two (straight-lines) $A D$, $D G$ are equal to the two (straight-lines) $B D$, $D G$,#content-box-note[The Greek text has "$G D$, $D B$", which is obviously a mistake.] respectively. And the base $G A$ is equal to the base $G B$. For (they are both) radii. Thus, angle $A D G$ is equal to angle $G D B$ [Prop.~1.8]. And when a straight-line stood upon (another) straight-line makes adjacent angles (which are) equal to one another, each of the equal angles is a right-angle [Def.~1.10]. Thus, $G D B$ is a right-angle. And $F D B$ is also a right-angle. Thus, $F D B$ (is) equal to $G D B$, the greater to the lesser. The very thing is impossible. Thus, (point) $G$ is not the center of the circle $A B C$. So, similarly, we can show that neither is any other (point) except $F$.],
  )
  #parallel-image("/Book03/fig01", 2.2in)
  #parallel(
    [Τὸ Ζ ἄρα σημεῖον κέντρον ἐστὶ τοῦ ΑΒΓ [κύκλου].],
    [Thus, point $F$ is the center of the [circle] $A B C$.],
  )
  #parallel-subheading([Πόρισμα.], [Corollary])
  #parallel(
    [Ἐκ δὴ τούτου φανερόν, ὅτι ἐὰν ἐν κύκλῳ εὐθεῖά τις εὐθεῖάν τινα δίχα καὶ πρὸς ὀρθὰς τέμνῃ, ἐπὶ τῆς τεμνούσης ἐστὶ τὸ κέντρον τοῦ κύκλου. --- ὅπερ ἔδει ποιῆσαι.],
    [So, from this, (it is) manifest that if any straight-line in a circle cuts any (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line). --- (Which is) the very thing it was required to do.],
  )
]
