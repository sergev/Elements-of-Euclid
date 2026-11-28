#import "../functions.typ": *

#content-box[
  #parallel-proposition(3)
  #parallel(
    [Ἐὰν τριγώνου ἡ γωνία δίχα τμηθῇ, ἡ δὲ τέμνουσα τὴν γωνίαν εὐθεῖα τέμνῃ καὶ τὴν βάσιν, τὰ τῆς βάσεως τμήματα τὸν αὐτὸν ἕξει λόγον ταῖς λοιπαῖς τοῦ τριγώνου πλευραῖς· καὶ ἐὰν τὰ τῆς βάσεως τμήματα τὸν αὐτὸν ἔχῃ λόγον ταῖς λοιπαῖς τοῦ τριγώνου πλευραῖς, ἡ ἀπὸ τῆς κορυφῆς ἐπὶ τὴν τομὴν ἐπιζευγνυμένη εὐθεῖα δίχα τεμεῖ τὴν τοῦ τριγώνου γωνίαν.],
    [If an angle of a triangle is cut in half, and the straight-line cutting the angle also cuts the base, (then) the segments of the base will have the same ratio as the remaining sides of the triangle. And if the segments of the base have the same ratio as the remaining sides of the triangle, (then) the straight-line joining the vertex to the cutting (point) will cut the angle of the triangle in half.],
  )
  #parallel(
    [Ἔστω τρίγωνον τὸ ΑΒΓ, καὶ τετμήσθω ἡ ὑπὸ ΒΑΓ γωνία δίχα ὑπὸ τῆς ΑΔ εὐθείας· λέγω, ὅτι ἐστὶν ὡς ἡ ΒΔ πρὸς τὴν ΓΔ, οὕτως ἡ ΒΑ πρὸς τὴν ΑΓ.],
    [Let $A B C$ be a triangle. And let the angle $B A C$ be cut in half by the straight-line $A D$. I say that as $B D$ is to $C D$, so $B A$ (is) to $A C$.],
  )
  #parallel(
    [Ἤχθω γὰρ διὰ τοῦ Γ τῇ ΔΑ παράλληλος ἡ ΓΕ, καὶ διαχθεῖσα ἡ ΒΑ συμπιπτέτω αὐτῇ κατὰ τὸ Ε.],
    [For let $C E$ be drawn through (point) $C$ parallel to $D A$. And, $B A$ being drawn through, let it meet ($C E$) at (point) $E$.#content-box-note[The fact that the two straight-lines meet follows because the sum of $A C E$ and $C A E$ is less than two right-angles, as can easily be demonstrated. See Post.~5.]],
  )
  #parallel(
    [Καὶ ἐπεὶ εἰς παραλλήλους τὰς ΑΔ, ΕΓ εὐθεῖα ἐνέπεσεν ἡ ΑΓ, ἡ ἄρα ὑπὸ ΑΓΕ γωνία ἴση ἐστὶ τῇ ὑπὸ ΓΑΔ. ἀλλ᾿ ἡ ὑπὸ ΓΑΔ τῇ ὑπὸ ΒΑΔ ὑπόκειται ἴση· καὶ ἡ ὑπὸ ΒΑΔ ἄρα τῇ ὑπὸ ΑΓΕ ἐστιν ἴση. πάλιν, ἐπεὶ εἰς παραλλήλους τὰς ΑΔ, ΕΓ εὐθεῖα ἐνέπεσεν ἡ ΒΑΕ, ἡ ἐκτὸς γωνία ἡ ὑπὸ ΒΑΔ ἴση ἐστὶ τῇ ἐντὸς τῇ ὑπὸ ΑΕΓ. ἐδείχθη δὲ καὶ ἡ ὑπὸ ΑΓΕ τῇ ὑπὸ ΒΑΔ ἴση· καὶ ἡ ὑπὸ ΑΓΕ ἄρα γωνία τῇ ὑπὸ ΑΕΓ ἐστιν ἴση· ὥστε καὶ πλευρὰ ἡ ΑΕ πλευρᾷ τῇ ΑΓ ἐστιν ἴση. καὶ ἐπεὶ τριγώνου τοῦ ΒΓΕ παρὰ μίαν τῶν πλευρῶν τὴν ΕΓ ἦκται ἡ ΑΔ, ἀνάλογον ἄρα ἐστὶν ὡς ἡ ΒΔ πρὸς τὴν ΔΓ, οὕτως ἡ ΒΑ πρὸς τὴν ΑΕ. ἴση δὲ ἡ ΑΕ τῇ ΑΓ· ὡς ἄρα ἡ ΒΔ πρὸς τὴν ΔΓ, οὕτως ἡ ΒΑ πρὸς τὴν ΑΓ.],
    [And since the straight-line $A C$ falls across the parallel (straight-lines) $A D$ and $E C$, angle $A C E$ is thus equal to $C A D$ [Prop.~1.29]. But, (angle) $C A D$ is assumed (to be) equal to $B A D$. Thus, (angle) $B A D$ is also equal to $A C E$. Again, since the straight-line $B A E$ falls across the parallel (straight-lines) $A D$ and $E C$, the external angle $B A D$ is equal to the internal (angle) $A E C$ [Prop.~1.29]. And (angle) $A C E$ was also shown (to be) equal to $B A D$. Thus, angle $A C E$ is also equal to $A E C$. And, hence, side $A E$ is equal to side $A C$ [Prop.~1.6]. And since $A D$ has been drawn parallel to one of the sides $E C$ of triangle $B C E$, thus, proportionally, as $B D$ is to $D C$, so $B A$ (is) to $A E$ [Prop.~6.2]. And $A E$ (is) equal to $A C$. Thus, as $B D$ (is) to $D C$, so $B A$ (is) to $A C$.],
  )
  #parallel-image("/Book06/fig03", 2in)
  #parallel(
    [Ἀλλὰ δὴ ἔστω ὡς ἡ ΒΔ πρὸς τὴν ΔΓ, οὕτως ἡ ΒΑ πρὸς τὴν ΑΓ, καὶ ἐπεζεύχθω ἡ ΑΔ· λέγω, ὅτι δίχα τέτμηται ἡ ὑπὸ ΒΑΓ γωνία ὑπὸ τῆς ΑΔ εὐθείας.],
    [And so, let $B D$ be to $D C$, as $B A$ (is) to $A C$. And let $A D$ be joined. I say that angle $B A C$ has been cut in half by the straight-line $A D$.],
  )
  #parallel(
    [Τῶν γὰρ αὐτῶν κατασκευασθέντων, ἐπεί ἐστιν ὡς ἡ ΒΔ πρὸς τὴν ΔΓ, οὕτως ἡ ΒΑ πρὸς τὴν ΑΓ, ἀλλὰ καὶ ὡς ἡ ΒΔ πρὸς τὴν ΔΓ, οὕτως ἐστὶν ἡ ΒΑ πρὸς τὴν ΑΕ· τριγώνου γὰρ τοῦ ΒΓΕ παρὰ μίαν τὴν ΕΓ ἦκται ἡ ΑΔ· καὶ ὡς ἄρα ἡ ΒΑ πρὸς τὴν ΑΓ, οὕτως ἡ ΒΑ πρὸς τὴν ΑΕ. ἴση ἄρα ἡ ΑΓ τῇ ΑΕ· ὥστε καὶ γωνία ἡ ὑπὸ ΑΕΓ τῇ ὑπὸ ΑΓΕ ἐστιν ἴση. ἀλλ᾿ ἡ μὲν ὑπὸ ΑΕΓ τῇ ἐκτὸς τῇ ὑπὸ ΒΑΔ [ἐστιν] ἴση, ἡ δὲ ὑπὸ ΑΓΕ τῇ ἐναλλὰξ τῇ ὑπὸ ΓΑΔ ἐστιν ἴση· καὶ ἡ ὑπὸ ΒΑΔ ἄρα τῇ ὑπὸ ΓΑΔ ἐστιν ἴση. ἡ ἄρα ὑπὸ ΒΑΓ γωνία δίχα τέτμηται ὑπὸ τῆς ΑΔ εὐθείας.],
    [For, by the same construction, since as $B D$ is to $D C$, so $B A$ (is) to $A C$, (then) also as $B D$ (is) to $D C$, so $B A$ is to $A E$. For $A D$ has been drawn parallel to one (of the sides) $E C$ of triangle $B C E$ [Prop.~6.2]. Thus, also, as $B A$ (is) to $A C$, so $B A$ (is) to $A E$ [Prop.~5.11]. Thus, $A C$ (is) equal to $A E$ [Prop.~5.9]. And, hence, angle $A E C$ is equal to $A C E$ [Prop.~1.5]. But, $A E C$ [is] equal to the external (angle) $B A D$, and $A C E$ is equal to the alternate (angle) $C A D$ [Prop.~1.29]. Thus, (angle) $B A D$ is also equal to $C A D$. Thus, angle $B A C$ has been cut in half by the straight-line $A D$.],
  )
  #parallel(
    [Ἐὰν ἄρα τριγώνου ἡ γωνία δίχα τμηθῇ, ἡ δὲ τέμνουσα τὴν γωνίαν εὐθεῖα τέμνῃ καὶ τὴν βάσιν, τὰ τῆς βάσεως τμήματα τὸν αὐτὸν ἕξει λόγον ταῖς λοιπαῖς τοῦ τριγώνου πλευραῖς· καὶ ἐὰν τὰ τῆς βάσεως τμήματα τὸν αὐτὸν ἔχῃ λόγον ταῖς λοιπαῖς τοῦ τριγώνου πλευραῖς, ἡ ἀπὸ τῆς κορυφῆς ἐπὶ τὴν τομὴν ἐπιζευγνυμένη εὐθεῖα δίχα τέμνει τὴν τοῦ τριγώνου γωνίαν· ὅπερ ἔδει δεῖξαι.],
    [Thus, if an angle of a triangle is cut in half, and the straight-line cutting the angle also cuts the base, (then) the segments of the base will have the same ratio as the remaining sides of the triangle. And if the segments of the base have the same ratio as the remaining sides of the triangle, (then) the straight-line joining the vertex to the cutting (point) will cut the angle of the triangle in half. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book6/Prop03.lean")
