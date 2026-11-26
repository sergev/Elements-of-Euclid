#import "../functions.typ": *

#content-box[
  #parallel-proposition(13, note: [This proposition is equivalent to the well-known cosine formula: $A C^(2) = A B^(2) + B C^(2) -2 thin A B thin B C thin cos A B C$, since $cos A B C = B D \/ A B$.])
  #parallel(
    [Ἐν τοῖς ὀξυγωνίοις τριγώνοις τὸ ἀπὸ τῆς τὴν ὀξεῖαν γωνίαν ὑποτεινούσης πλευρᾶς τετράγωνον ἔλαττόν ἐστι τῶν ἀπὸ τῶν τὴν ὀξεῖαν γωνίαν περιεχουσῶν πλευρῶν τετραγώνων τῷ περιεχομένῳ δὶς ὑπό τε μιᾶς τῶν περὶ τὴν ὀξεῖαν γωνίαν, ἐφ᾿ ἣν ἡ κάθετος πίπτει, καὶ τῆς ἀπολαμβανομένης ἐντὸς ὑπὸ τῆς καθέτου πρὸς τῇ ὀξείᾳ γωνίᾳ.],
    [In acute-angled triangles, the square on the side subtending the acute angle is less than the (sum of the) squares on the sides containing the acute angle by twice the (rectangle) contained by one of the sides around the acute angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off inside (the triangle) by the perpendicular (straight-line) towards the acute angle.],
  )
  #parallel-image("/Book02/fig13", 2in)
  #parallel(
    [Ἔστω ὀξυγώνιον τρίγωνον τὸ ΑΒΓ ὀξεῖαν ἔχον τὴν πρὸς τῷ Β γωνίαν, καὶ ἤχθω ἀπὸ τοῦ Α σημείου ἐπὶ τὴν ΒΓ κάθετος ἡ ΑΔ· λέγω, ὅτι τὸ ἀπὸ τῆς ΑΓ τετράγωνον ἔλαττόν ἐστι τῶν ἀπὸ τῶν ΓΒ, ΒΑ τετραγώνων τῷ δὶς ὑπὸ τῶν ΓΒ, ΒΔ περιεχομένῳ ὀρθογωνίῳ.],
    [Let $A B C$ be an acute-angled triangle, having the angle at (point) $B$ acute. And let $A D$ be drawn from point $A$, perpendicular to $B C$ [Prop.~1.12]. I say that the square on $A C$ is less than the (sum of the) squares on $C B$ and $B A$ by twice the rectangle contained by $C B$ and $B D$.],
  )
  #parallel(
    [Ἐπεὶ γὰρ εὐθεῖα ἡ ΓΒ τέτμηται, ὡς ἔτυχεν, κατὰ τὸ Δ, τὰ ἄρα ἀπὸ τῶν ΓΒ, ΒΔ τετράγωνα ἴσα ἐστὶ τῷ τε δὶς ὑπὸ τῶν ΓΒ, ΒΔ περιεχομένῳ ὀρθογωνίῳ καὶ τῷ ἀπὸ τῆς ΔΓ τετραγώνῳ. κοινὸν προσκείσθω τὸ ἀπὸ τῆς ΔΑ τετράγωνον· τὰ ἄρα ἀπὸ τῶν ΓΒ, ΒΔ, ΔΑ τετράγωνα ἴσα ἐστὶ τῷ τε δὶς ὑπὸ τῶν ΓΒ, ΒΔ περιεχομένῳ ὀρθογωνίῳ καὶ τοῖς ἀπὸ τῶν ΑΔ, ΔΓ τετραγώνιος. ἀλλὰ τοῖς μὲν ἀπὸ τῶν ΒΔ, ΔΑ ἴσον τὸ ἀπὸ τῆς ΑΒ· ὀρθὴ γὰρ ἡ πρὸς τῷ Δ γωνίᾳ· τοῖς δὲ ἀπὸ τῶν ΑΔ, ΔΓ ἴσον τὸ ἀπὸ τῆς ΑΓ· τὰ ἄρα ἀπὸ τῶν ΓΒ, ΒΑ ἴσα ἐστὶ τῷ τε ἀπὸ τῆς ΑΓ καὶ τῷ δὶς ὑπὸ τῶν ΓΒ, ΒΔ· ὥστε μόνον τὸ ἀπὸ τῆς ΑΓ ἔλαττόν ἐστι τῶν ἀπὸ τῶν ΓΒ, ΒΑ τετραγώνων τῷ δὶς ὑπὸ τῶν ΓΒ, ΒΔ περιεχομένῳ ὀρθογωνίῳ.],
    [For since the straight-line $C B$ has been cut, at random, at (point) $D$, the (sum of the) squares on $C B$ and $B D$ is thus equal to twice the rectangle contained by $C B$ and $B D$, and the square on $D C$ [Prop.~2.7]. Let the square on $D A$ be added to both. Thus, the (sum of the) squares on $C B$, $B D$, and $D A$ is equal to twice the rectangle contained by $C B$ and $B D$, and the (sum of the) squares on $A D$ and $D C$. But, the (square) on $A B$ (is) equal to the (sum of the squares) on $B D$ and $D A$. For the angle at (point) $D$ is a right-angle [Prop.~1.47]. And the (square) on $A C$ (is) equal to the (sum of the squares) on $A D$ and $D C$ [Prop.~1.47]. Thus, the (sum of the squares) on $C B$ and $B A$ is equal to the (square) on $A C$, and twice the (rectangle contained) by $C B$ and $B D$. So the (square) on $A C$ alone is less than the (sum of the) squares on $C B$ and $B A$ by twice the rectangle contained by $C B$ and $B D$.],
  )
  #parallel(
    [Ἐν ἄρα τοῖς ὀξυγωνίοις τριγώνοις τὸ ἀπὸ τῆς τὴν ὀξεῖαν γωνίαν ὑποτεινούσης πλευρᾶς τετράγωνον ἔλαττόν ἐστι τῶν ἀπὸ τῶν τὴν ὀξεῖαν γωνίαν περιεχουσῶν πλευρῶν τετραγώνων τῷ περιεχομένῳ δὶς ὑπό τε μιᾶς τῶν περὶ τὴν ὀξεῖαν γωνίαν, ἐφ᾿ ἣν ἡ κάθετος πίπτει, καὶ τῆς ἀπολαμβανομένης ἐντὸς ὑπὸ τῆς καθέτου πρὸς τῇ ὀξείᾳ γωνίᾳ· ὅπερ ἔδει δεῖξαι.],
    [Thus, in acute-angled triangles, the square on the side subtending the acute angle is less than the (sum of the) squares on the sides containing the acute angle by twice the (rectangle) contained by one of the sides around the acute angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off inside (the triangle) by the perpendicular (straight-line) towards the acute angle. (Which is) the very thing it was required to show.],
  )
]
