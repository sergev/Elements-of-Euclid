#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig24(letters) = fig({
  
})

#content-box[
  #parallel-proposition(24)
  #parallel(
    [Ἐὰν δύο τρίγωνα τὰς δύο πλευρὰς [ταῖς] δύο πλευραῖς ἴσας ἔχῃ ἑκατέραν ἑκατέρᾳ, τὴν δὲ γωνίαν τῆς γωνίας μείζονα ἔχῃ τὴν ὑπὸ τῶν ἴσων εὐθειῶν περιεχομένην, καὶ τὴν βάσιν τῆς βάσεως μείζονα ἕξει.],
    [If two triangles have two sides equal to two sides, respectively, but (one) has the angle encompassed by the equal straight-lines greater than the (corresponding) angle (in the other), (then the former triangle) will also have a base greater than the base (of the latter).],
  )
  #parallel(
    [Ἔστω δύο τρίγωνα τὰ ΑΒΓ, ΔΕΖ τὰς δύο πλευρὰς τὰς ΑΒ, ΑΓ ταῖς δύο πλευραῖς ταῖς ΔΕ, ΔΖ ἴσας ἔχοντα ἑκατέραν ἑκατέρᾳ, τὴν μὲν ΑΒ τῇ ΔΕ τὴν δὲ ΑΓ τῇ ΔΖ, ἡ δὲ πρὸς τῷ Α γωνία τῆς πρὸς τῷ Δ γωνίας μείζων ἔστω· λέγω, ὅτι καὶ βάσις ἡ ΒΓ βάσεως τῆς ΕΖ μείζων ἐστίν.],
    [Let $A B C$ and $D E F$ be two triangles having the two sides $A B$ and $A C$ equal to the two sides $D E$ and $D F$, respectively. (That is), $A B$ (equal) to $D E$, and $A C$ to $D F$. Let them also have the angle at $A$ greater than the angle at $D$. I say that the base $B C$ is also greater than the base $E F$.],
  )
  #parallel-fig(fig24)
  #parallel(
    [Ἐπεὶ γὰρ μείζων ἡ ὑπὸ ΒΑΓ γωνία τῆς ὑπὸ ΕΔΖ γωνίας, συνεστάτω πρὸς τῇ ΔΕ εὐθείᾳ καὶ τῷ πρὸς αὐτῇ σημείῳ τῷ Δ τῇ ὑπὸ ΒΑΓ γωνίᾳ ἴση ἡ ὑπὸ ΕΔΗ, καὶ κείσθω ὁποτέρᾳ τῶν ΑΓ, ΔΖ ἴση ἡ ΔΗ, καὶ ἐπεζεύχθωσαν αἱ ΕΗ, ΖΗ.],
    [For since angle $B A C$ is greater than angle $E D F$, let (angle) $E D G$, equal to angle $B A C$, be constructed at the point $D$ on the straight-line $D E$ [Prop.~1.23]. And let $D G$ be made equal to either of $A C$ or $D F$ [Prop.~1.3], and let $E G$ and $F G$ be joined.],
  )
  #parallel(
    [Ἐπεὶ οὖν ἴση ἐστὶν ἡ μὲν ΑΒ τῇ ΔΕ, ἡ δὲ ΑΓ τῇ ΔΗ, δύο δὴ αἱ ΒΑ, ΑΓ δυσὶ ταῖς ΕΔ, ΔΗ ἴσαι εἰσὶν ἑκατέρα ἑκατέρᾳ· καὶ γωνία ἡ ὑπὸ ΒΑΓ γωνίᾳ τῇ ὑπὸ ΕΔΗ ἴση· βάσις ἄρα ἡ ΒΓ βάσει τῇ ΕΗ ἐστιν ἴση. πάλιν, ἐπεὶ ἴση ἐστὶν ἡ ΔΖ τῇ ΔΗ, ἴση ἐστὶ καὶ ἡ ὑπὸ ΔΗΖ γωνία τῇ ὑπὸ ΔΖΗ· μείζων ἄρα ἡ ὑπὸ ΔΖΗ τῆς ὑπὸ ΕΗΖ· πολλῷ ἄρα μείζων ἐστὶν ἡ ὑπὸ ΕΖΗ τῆς ὑπὸ ΕΗΖ. καὶ ἐπεὶ τρίγωνόν ἐστι τὸ ΕΖΗ μείζονα ἔχον τὴν ὑπὸ ΕΖΗ γωνίαν τῆς ὑπὸ ΕΗΖ, ὑπὸ δὲ τὴν μείζονα γωνίαν ἡ μείζων πλευρὰ ὑποτείνει, μείζων ἄρα καὶ πλευρὰ ἡ ΕΗ τῆς ΕΖ. ἴση δὲ ἡ ΕΗ τῇ ΒΓ· μείζων ἄρα καὶ ἡ ΒΓ τῆς ΕΖ.],
    [Therefore, since $A B$ is equal to $D E$ and $A C$ to $D G$, the two (straight-lines) $B A$, $A C$ are equal to the two (straight-lines) $E D$, $D G$, respectively. Also the angle $B A C$ is equal to the angle $E D G$. Thus, the base $B C$ is equal to the base $E G$ [Prop.~1.4]. Again, since $D F$ is equal to $D G$, angle $D G F$ is also equal to angle $D F G$ [Prop.~1.5]. Thus, $D F G$ (is) greater than $E G F$. Thus, $E F G$ is much greater than $E G F$. And since triangle $E F G$ has angle $E F G$ greater than $E G F$, and the greater angle is subtended by the greater side [Prop.~1.19], side $E G$ (is) thus also greater than $E F$. But $E G$ (is) equal to $B C$. Thus, $B C$ (is) also greater than $E F$.],
  )
  #parallel(
    [Ἐὰν ἄρα δύο τρίγωνα τὰς δύο πλευρὰς δυσὶ πλευραῖς ἴσας ἔχῃ ἑκατέραν ἑκατέρᾳ, τὴν δὲ γωνίαν τῆς γωνίας μείζονα ἔχῃ τὴν ὑπὸ τῶν ἴσων εὐθειῶν περιεχομένην, καὶ τὴν βάσιν τῆς βάσεως μείζονα ἕξει· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two triangles have two sides equal to two sides, respectively, but (one) has the angle encompassed by the equal straight-lines greater than the (corresponding) angle (in the other), (then the former triangle) will also have a base greater than the base (of the latter). (Which is) the very thing it was required to show.],
  )
]





