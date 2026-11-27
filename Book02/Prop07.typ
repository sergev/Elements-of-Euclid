#import "../functions.typ": *

#content-box[
  #parallel-proposition(7, note: [This proposition is a geometric version of the algebraic identity: $(a+b)^(2)+a^2 =2 thin (a+b) thin a+b^(2)$.])
  #parallel(
    [Ἐὰν εὐθεῖα γραμμὴ τμηθῇ, ὡς ἔτυχεν, τὸ ἀπὸ τῆς ὅλης καὶ τὸ ἀφ᾿ ἑνὸς τῶν τμημάτων τὰ συναμφότερα τετράγωνα ἴσα ἐστὶ τῷ τε δὶς ὑπὸ τῆς ὅλης καὶ τοῦ εἰρημένου τμήματος περιεχομένῳ ὀρθογωνίῳ καὶ τῷ ἀπὸ τοῦ λοιποῦ τμήματος τετραγώνῳ.],
    [If a straight-line is cut at random, (then) the sum of the squares on the whole (straight-line), and one of the pieces (of the straight-line), is equal to twice the rectangle contained by the whole, and the said piece, and the square on the remaining piece.],
  )
  #parallel-image("/Book02/fig07", 2.2in)
  #parallel(
    [Εὐθεῖα γάρ τις ἡ ΑΒ τετμήσθω, ὡς ἔτυχεν, κατὰ τὸ Γ σημεῖον· λέγω, ὅτι τὰ ἀπὸ τῶν ΑΒ, ΒΓ τετράγωνα ἴσα ἐστὶ τῷ τε δὶς ὑπὸ τῶν ΑΒ, ΒΓ περιεχομένῳ ὀρθογωνίῳ καὶ τῷ ἀπὸ τῆς ΓΑ τετραγώνῳ.],
    [For let any straight-line $A B$ be cut, at random, at point $C$. I say that the (sum of the) squares on $A B$ and $B C$ is equal to twice the rectangle contained by $A B$ and $B C$, and the square on $C A$.],
  )
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΑΒ τετράγωνον τὸ ΑΔΕΒ· καὶ καταγεγράφθω τὸ σχῆμα.],
    [For let the square $A D E B$ be described on $A B$ [Prop.~1.46], and let the (rest of) the figure be drawn.],
  )
  #parallel(
    [Ἐπεὶ οὖν ἴσον ἐστὶ τὸ ΑΗ τῷ ΗΕ, κοινὸν προσκείσθω τὸ ΓΖ· ὅλον ἄρα τὸ ΑΖ ὅλῳ τῷ ΓΕ ἴσον ἐστίν· τὰ ἄρα ΑΖ, ΓΕ διπλάσιά ἐστι τοῦ ΑΖ. ἀλλὰ τὰ ΑΖ, ΓΕ ὁ ΚΛΜ ἐστι γνώμων καὶ τὸ ΓΖ τετράγωνον· ὁ ΚΛΜ ἄρα γνώμων καὶ τὸ ΓΖ διπλάσιά ἐστι τοῦ ΑΖ. ἔστι δὲ τοῦ ΑΖ διπλάσιον καὶ τὸ δὶς ὑπὸ τῶν ΑΒ, ΒΓ· ἴση γὰρ ἡ ΒΖ τῇ ΒΓ· ὁ ἄρα ΚΛΜ γνώμων καὶ τὸ ΓΖ τετράγωνον ἴσον ἐστὶ τῷ δὶς ὑπὸ τῶν ΑΒ, ΒΓ. κοινὸν προσκείσθω τὸ ΔΗ, ὅ ἐστιν ἀπὸ τῆς ΑΓ τετράγωνον· ὁ ἄρα ΚΛΜ γνώμων καὶ τὰ ΒΗ, ΗΔ τετράγωνα ἴσα ἐστὶ τῷ τε δὶς ὑπὸ τῶν ΑΒ, ΒΓ περιεχομένῳ ὀρθογωνίῳ καὶ τῷ ἀπὸ τῆς ΑΓ τετραγώνῳ. ἀλλὰ ὁ ΚΛΜ γνώμων καὶ τὰ ΒΗ, ΗΔ τετράγωνα ὅλον ἐστὶ τὸ ΑΔΕΒ καὶ τὸ ΓΖ, ἅ ἐστιν ἀπὸ τῶν ΑΒ, ΒΓ τετράγωνα· τὰ ἄρα ἀπὸ τῶν ΑΒ, ΒΓ τετράγωνα ἴσα ἐστὶ τῷ [τε] δὶς ὑπὸ τῶν ΑΒ, ΒΓ περιεχομένῳ ὀρθογωνίῳ μετὰ τοῦ ἀπὸ τῆς ΑΓ τετραγώνου.],
    [Therefore, since (rectangle) $A G$ is equal to (rectangle) $G E$ [Prop.~1.43], let the (square) $C F$ be added to both. Thus, the whole (rectangle) $A F$ is equal to the whole (rectangle) $C E$. Thus, (rectangle) $A F$ plus (rectangle) $C E$ is double (rectangle) $A F$. But, (rectangle) $A F$ plus (rectangle) $C E$ is the gnomon $K L M$, and the square $C F$. Thus, the gnomon $K L M$, and the square $C F$, is double the (rectangle) $A F$. But double the (rectangle) $A F$ is also twice the (rectangle contained) by $A B$ and $B C$. For $B F$ (is) equal to $B C$. Thus, the gnomon $K L M$, and the square $C F$, are equal to twice the (rectangle contained) by $A B$ and $B C$. Let $D G$, which is the square on $A C$, be added to both. Thus, the gnomon $K L M$, and the squares $B G$ and $G D$, are equal to twice the rectangle contained by $A B$ and $B C$, and the square on $A C$. But, the gnomon $K L M$ and the squares $B G$ and $G D$ is (equivalent to) the whole of $A D E B$ and $C F$, which are the squares on $A B$ and $B C$ (respectively). Thus, the (sum of the) squares on $A B$ and $B C$ is equal to twice the rectangle contained by $A B$ and $B C$, and the square on $A C$.],
  )
  #parallel(
    [Ἐὰν ἄρα εὐθεῖα γραμμὴ τμηθῇ, ὡς ἔτυχεν, τὸ ἀπὸ τῆς ὅλης καὶ τὸ ἀφ᾿ ἑνὸς τῶν τμημάτων τὰ συναμφότερα τετράγωνα ἴσα ἐστὶ τῷ τε δὶς ὑπὸ τῆς ὅλης καὶ τοῦ εἰρημένου τμήματος περιεχομένῳ ὀρθογωνίῳ καὶ τῷ ἀπὸ τοῦ λοιποῦ τμήματος τετραγώνῳ· ὅπερ ἔδει δεῖξαι.],
    [Thus, if a straight-line is cut at random, (then) the sum of the squares on the whole (straight-line), and one of the pieces (of the straight-line), is equal to twice the rectangle contained by the whole, and the said piece, and the square on the remaining piece. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book2/Prop07.lean")
