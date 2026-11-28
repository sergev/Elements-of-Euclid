#import "../functions.typ": *

#content-box[
  #parallel-proposition(5)
  #parallel(
    [Ἐὰν δύο τρίγωνα τὰς πλευρὰς ἀνάλογον ἔχῃ, ἰσογώνια ἔσται τὰ τρίγωνα καὶ ἴσας ἕξει τὰς γωνίας, ὑφ᾿ ἃς αἱ ὁμόλογοι πλευραὶ ὑποτείνουσιν.],
    [If two triangles have proportional sides, (then) the triangles will be equiangular, and will have the angles which corresponding sides subtend equal.],
  )
  #parallel(
    [Ἔστω δύο τρίγωνα τὰ ΑΒΓ, ΔΕΖ τὰς πλευρὰς ἀνάλογον ἔχοντα, ὡς μὲν τὴν ΑΒ πρὸς τὴν ΒΓ, οὕτως τὴν ΔΕ πρὸς τὴν ΕΖ, ὡς δὲ τὴν ΒΓ πρὸς τὴν ΓΑ, οὕτως τὴν ΕΖ πρὸς τὴν ΖΔ, καὶ ἔτι ὡς τὴν ΒΑ πρὸς τὴν ΑΓ, οὕτως τὴν ΕΔ πρὸς τὴν ΔΖ. λέγω, ὅτι ἰσογώνιόν ἐστι τὸ ΑΒΓ τρίγωνον τῷ ΔΕΖ τριγώνῳ καὶ ἴσας ἕξουσι τὰς γωνίας, ὑφ᾿ ἃς αἱ ὁμόλογοι πλευραὶ ὑποτείνουσιν, τὴν μὲν ὑπὸ ΑΒΓ τῇ ὑπὸ ΔΕΖ, τὴν δὲ ὑπὸ ΒΓΑ τῇ ὑπὸ ΕΖΔ καὶ ἔτι τὴν ὑπὸ ΒΑΓ τῇ ὑπὸ ΕΔΖ.],
    [Let $A B C$ and $D E F$ be two triangles having proportional sides, (so that) as $A B$ (is) to $B C$, so $D E$ (is) to $E F$, and as $B C$ (is) to $C A$, so $E F$ (is) to $F D$, and, further, as $B A$ (is) to $A C$, so $E D$ (is) to $D F$. I say that triangle $A B C$ is equiangular to triangle $D E F$, and (that the triangles) will have the angles which corresponding sides subtend equal. (That is), (angle) $A B C$ (equal) to $D E F$, $B C A$ to $E F D$, and, further, $B A C$ to $E D F$.],
  )
  #parallel(
    [Συνεστάτω γὰρ πρὸς τῇ ΕΖ εὐθείᾳ καὶ τοῖς πρὸς αὐτῇ σημείοις τοῖς Ε, Ζ τῇ μὲν ὑπὸ ΑΒΓ γωνίᾳ ἴση ἡ ὑπὸ ΖΕΗ, τῇ δὲ ὑπὸ ΑΓΒ ἴση ἡ ὑπὸ ΕΖΗ· λοιπὴ ἄρα ἡ πρὸς τῷ Α λοιπῇ τῇ πρὸς τῷ Η ἐστιν ἴση.],
    [For let (angle) $F E G$, equal to angle $A B C$, and (angle) $E F G$, equal to $A C B$, be constructed on the straight-line $E F$ at the points $E$ and $F$ on it (respectively) [Prop.~1.23]. Thus, the remaining (angle) at $A$ is equal to the remaining (angle) at $G$ [Prop.~1.32].],
  )
  #parallel-image("/Book06/fig05", 2.2in)
  #parallel(
    [Ἴσογώνιον ἄρα ἐστὶ τὸ ΑΒΓ τρίγωνον τῷ ΕΗΖ [τριγώνῳ]. τῶν ἄρα ΑΒΓ, ΕΗΖ τριγώνων ἀνάλογόν εἰσιν αἱ πλευραὶ αἱ περὶ τὰς ἴσας γωνίας καὶ ὁμόλογοι αἱ ὑπὸ τὰς ἴσας γωνίας ὑποτείνουσαι· ἔστιν ἄρα ὡς ἡ ΑΒ πρὸς τὴν ΒΓ, [οὕτως] ἡ ΗΕ πρὸς τὴν ΕΖ. ἀλλ᾿ ὡς ἡ ΑΒ πρὸς τὴν ΒΓ, οὕτως ὑπόκειται ἡ ΔΕ πρὸς τὴν ΕΖ· ὡς ἄρα ἡ ΔΕ πρὸς τὴν ΕΖ, οὕτως ἡ ΗΕ πρὸς τὴν ΕΖ. ἑκατέρα ἄρα τῶν ΔΕ, ΗΕ πρὸς τὴν ΕΖ τὸν αὐτὸν ἔχει λόγον· ἴση ἄρα ἐστὶν ἡ ΔΕ τῇ ΗΕ. διὰ τὰ αὐτὰ δὴ καὶ ἡ ΔΖ τῇ ΗΖ ἐστιν ἴση. ἐπεὶ οὖν ἴση ἐστὶν ἡ ΔΕ τῇ ΕΗ, κοινὴ δὲ ἡ ΕΖ, δύο δὴ αἱ ΔΕ, ΕΖ δυσὶ ταῖς ΗΕ, ΕΖ ἴσαι εἰσίν· καὶ βάσις ἡ ΔΖ βάσει τῇ ΖΗ [ἐστιν] ἴση· γωνία ἄρα ἡ ὑπὸ ΔΕΖ γωνίᾳ τῇ ὑπὸ ΗΕΖ ἐστιν ἴση, καὶ τὸ ΔΕΖ τρίγωνον τῷ ΗΕΖ τριγώνῳ ἴσον, καὶ αἱ λοιπαὶ γωνίαι ταῖς λοιπαῖς γωνίαις ἴσαι, ὑφ᾿ ἃς αἱ ἴσαι πλευραὶ ὑποτείνουσιν. ἴση ἄρα ἐστὶ καὶ ἡ μὲν ὑπὸ ΔΖΕ γωνία τῇ ὑπὸ ΗΖΕ, ἡ δὲ ὑπὸ ΕΔΖ τῇ ὑπὸ ΕΗΖ. καὶ ἐπεὶ ἡ μὲν ὑπὸ ΖΕΔ τῇ ὑπὸ ΗΕΖ ἐστιν ἴση, ἀλλ᾿ ἡ ὑπὸ ΗΕΖ τῇ ὑπὸ ΑΒΓ, καὶ ἡ ὑπὸ ΑΒΓ ἄρα γωνία τῇ ὑπὸ ΔΕΖ ἐστιν ἴση. διὰ τὰ αὐτὰ δὴ καὶ ἡ ὑπὸ ΑΓΒ τῇ ὑπὸ ΔΖΕ ἐστιν ἴση, καὶ ἔτι ἡ πρὸς τῷ Α τῇ πρὸς τῷ Δ· ἰσογώνιον ἄρα ἐστὶ τὸ ΑΒΓ τρίγωνον τῷ ΔΕΖ τριγώνῳ.],
    [Thus, triangle $A B C$ is equiangular to [triangle] $E G F$. Thus, for triangles $A B C$ and $E G F$, the sides about the equal angles are proportional, and (those) sides subtending equal angles correspond [Prop.~6.4]. Thus, as $A B$ is to $B C$, [so] $G E$ (is) to $E F$. But, as $A B$ (is) to $B C$, so, it was assumed, (is) $D E$ to $E F$. Thus, as $D E$ (is) to $E F$, so $G E$ (is) to $E F$ [Prop.~5.11]. Thus, $D E$ and $G E$ each have the same ratio to $E F$. Thus, $D E$ is equal to $G E$ [Prop.~5.9]. So, for the same (reasons), $D F$ is also equal to $G F$. Therefore, since $D E$ is equal to $E G$, and $E F$ (is) common, the two (sides) $D E$, $E F$ are equal to the two (sides) $G E$, $E F$ (respectively). And base $D F$ [is] equal to base $F G$. Thus, angle $D E F$ is equal to angle $G E F$ [Prop.~1.8], and triangle $D E F$ (is) equal to triangle $G E F$, and the remaining angles (are) equal to the remaining angles which the equal sides subtend [Prop.~1.4]. Thus, angle $D F E$ is also equal to $G F E$, and (angle) $E D F$ to $E G F$. And since (angle) $F E D$ is equal to $G E F$, and (angle) $G E F$ to $A B C$, angle $A B C$ is thus also equal to $D E F$. So, for the same (reasons), (angle) $A C B$ is also equal to $D F E$, and, further, the (angle) at $A$ to the (angle) at $D$. Thus, triangle $A B C$ is equiangular to triangle $D E F$.],
  )
  #parallel(
    [Ἐὰν ἄρα δύο τρίγωνα τὰς πλευρὰς ἀνάλογον ἔχῃ, ἰσογώνια ἔσται τὰ τρίγωνα καὶ ἴσας ἕξει τὰς γωνίας, ὑφ᾿ ἃς αἱ ὁμόλογοι πλευραὶ ὑποτείνουσιν· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two triangles have proportional sides, (then) the triangles will be equiangular, and will have the angles which corresponding sides subtend equal. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book6/Prop05.lean")
