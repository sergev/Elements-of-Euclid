#import "../functions.typ": *

#content-box[
  #parallel-proposition(15)
  #parallel(
    [Ἐὰν δύο εὐθεῖαι τέμνωσιν ἀλλήλας, τὰς κατὰ κορυφὴν γωνίας ἴσας ἀλλήλαις ποιοῦσιν.],
    [If two straight-lines cut one another (then) they make the vertically opposite angles equal to one another.],
  )
  #parallel(
    [Δύο γὰρ εὐθεῖαι αἱ ΑΒ, ΓΔ τεμνέτωσαν ἀλλήλας κατὰ τὸ Ε σημεῖον· λέγω, ὅτι ἴση ἐστὶν ἡ μὲν ὑπὸ ΑΕΓ γωνία τῇ ὑπὸ ΔΕΒ, ἡ δὲ ὑπὸ ΓΕΒ τῇ ὑπὸ ΑΕΔ.],
    [For let the two straight-lines $A B$ and $C D$ cut one another at the point $E$. I say that angle $A E C$ is equal to (angle) $D E B$, and (angle) $C E B$ to (angle) $A E D$.],
  )
  #parallel-image("/Book01/fig15", 2.3in)
  #parallel(
    [Ἐπεὶ γὰρ εὐθεῖα ἡ ΑΕ ἐπ᾿ εὐθεῖαν τὴν ΓΔ ἐφέστηκε γωνίας ποιοῦσα τὰς ὑπὸ ΓΕΑ, ΑΕΔ, αἱ ἄρα ὑπὸ ΓΕΑ, ΑΕΔ γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν. πάλιν, ἐπεὶ εὐθεῖα ἡ ΔΕ ἐπ᾿ εὐθεῖαν τὴν ΑΒ ἐφέστηκε γωνίας ποιοῦσα τὰς ὑπὸ ΑΕΔ, ΔΕΒ, αἱ ἄρα ὑπὸ ΑΕΔ, ΔΕΒ γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν. ἐδείχθησαν δὲ καὶ αἱ ὑπὸ ΓΕΑ, ΑΕΔ δυσὶν ὀρθαῖς ἴσαι· αἱ ἄρα ὑπὸ ΓΕΑ, ΑΕΔ ταῖς ὑπὸ ΑΕΔ, ΔΕΒ ἴσαι εἰσίν. κοινὴ ἀφῃρήσθω ἡ ὑπὸ ΑΕΔ· λοιπὴ ἄρα ἡ ὑπὸ ΓΕΑ λοιπῇ τῇ ὑπὸ ΒΕΔ ἴση ἐστίν· ὁμοίως δὴ δειχθήσεται, ὅτι καὶ αἱ ὑπὸ ΓΕΒ, ΔΕΑ ἴσαι εἰσίν.],
    [For since the straight-line $A E$ stands on the straight-line $C D$, making the angles $C E A$ and $A E D$, the (sum of the) angles $C E A$ and $A E D$ is thus equal to two right-angles [Prop.~1.13]. Again, since the straight-line $D E$ stands on the straight-line $A B$, making the angles $A E D$ and $D E B$, the (sum of the) angles $A E D$ and $D E B$ is thus equal to two right-angles [Prop.~1.13]. But (the sum of) $C E A$ and $A E D$ was also shown (to be) equal to two right-angles. Thus, (the sum of) $C E A$ and $A E D$ is equal to (the sum of) $A E D$ and $D E B$ [C.N.~1]. Let $A E D$ be subtracted from both. Thus, the remainder $C E A$ is equal to the remainder $B E D$ [C.N.~3]. Similarly, it can be shown that $C E B$ and $D E A$ are also equal.],
  )
  #parallel(
    [Ἐὰν ἄρα δύο εὐθεῖαι τέμνωσιν ἀλλήλας, τὰς κατὰ κορυφὴν γωνίας ἴσας ἀλλήλαις ποιοῦσιν· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two straight-lines cut one another (then) they make the vertically opposite angles equal to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop15.lean")
