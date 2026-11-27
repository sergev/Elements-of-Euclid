#import "../functions.typ": *

#content-box[
  #parallel-proposition(12, note: [This proposition is equivalent to the well-known cosine formula: $B C^(2) = A B^(2) + A C^(2) -2 thin A B thin A C thin cos B A C$, since $cos B A C = - A D \/ A B$.])
  #parallel(
    [Ἐν τοῖς ἀμβλυγωνίοις τριγώνοις τὸ ἀπὸ τῆς τὴν ἀμβλεῖαν γωνίαν ὑποτεινούσης πλευρᾶς τετράγωνον μεῖζόν ἐστι τῶν ἀπὸ τῶν τὴν ἀμβλεῖαν γωνίαν περιεχουσῶν πλευρῶν τετραγώνων τῷ περιεχομένῳ δὶς ὑπὸ τε μιᾶς τῶν περὶ τὴν ἀμβλεῖαν γωνίαν, ἐφ᾿ ἣν ἡ κάθετος πίπτει, καὶ τῆς ἀπολαμβανομένης ἐκτὸς ὑπὸ τῆς καθέτου πρὸς τῇ ἀμβλείᾳ γωνίᾳ.],
    [In obtuse-angled triangles, the square on the side subtending the obtuse angle is greater than the (sum of the) squares on the sides containing the obtuse angle by twice the (rectangle) contained by one of the sides around the obtuse angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off outside (the triangle) by the perpendicular (straight-line) towards the obtuse angle.],
  )
  #parallel(
    [Ἔστω ἀμβλυγώνιον τρίγωνον τὸ ΑΒΓ ἀμβλεῖαν ἔχον τὴν ὑπὸ ΒΑΓ, καὶ ἤχθω ἀπὸ τοῦ Β σημείου ἐπὶ τὴν ΓΑ ἐκβληθεῖσαν κάθετος ἡ ΒΔ. λέγω, ὅτι τὸ ἀπὸ τῆς ΒΓ τετράγωνον μεῖζόν ἐστι τῶν ἀπὸ τῶν ΒΑ, ΑΓ τετραγώνων τῷ δὶς ὑπὸ τῶν ΓΑ, ΑΔ περιεχομένῳ ὀρθογωνίῳ.],
    [Let $A B C$ be an obtuse-angled triangle, having the angle $B A C$ obtuse. And let $B D$ be drawn from point $B$, perpendicular to $C A$ produced [Prop.~1.12]. I say that the square on $B C$ is greater than the (sum of the) squares on $B A$ and $A C$ by twice the rectangle contained by $C A$ and $A D$.],
  )
  #parallel-image("/Book02/fig12", 1.8in)
  #parallel(
    [Ἐπεὶ γὰρ εὐθεῖα ἡ ΓΔ τέτμηται, ὡς ἔτυχεν, κατὰ τὸ Α σημεῖον, τὸ ἄρα ἀπὸ τῆς ΔΓ ἴσον ἐστὶ τοῖς ἀπὸ τῶν ΓΑ, ΑΔ τετραγώνοις καὶ τῷ δὶς ὑπὸ τῶν ΓΑ, ΑΔ περιεχομένῳ ὀρθογωνίῳ. κοινὸν προσκείσθω τὸ ἀπὸ τῆς ΔΒ· τὰ ἄρα ἀπὸ τῶν ΓΔ, ΔΒ ἴσα ἐστὶ τοῖς τε ἀπὸ τῶν ΓΑ, ΑΔ, ΔΒ τετραγώνοις καὶ τῷ δὶς ὑπὸ τῶν ΓΑ, ΑΔ [περιεχομένῳ ὀρθογωνίῳ]. ἀλλὰ τοῖς μὲν ἀπὸ τῶν ΓΔ, ΔΒ ἴσον ἐστὶ τὸ ἀπὸ τῆς ΓΒ· ὀρθὴ γὰρ ἡ προς τῷ Δ γωνία· τοῖς δὲ ἀπὸ τῶν ΑΔ, ΔΒ ἴσον τὸ ἀπὸ τῆς ΑΒ· τὸ ἄρα ἀπὸ τῆς ΓΒ τετράγωνον ἴσον ἐστὶ τοῖς τε ἀπὸ τῶν ΓΑ, ΑΒ τετραγώνοις καὶ τῷ δὶς ὑπὸ τῶν ΓΑ, ΑΔ περιεχομένῳ ὀρθογωνίῳ· ὥστε τὸ ἀπὸ τῆς ΓΒ τετράγωνον τῶν ἀπὸ τῶν ΓΑ, ΑΒ τετραγώνων μεῖζόν ἐστι τῷ δὶς ὑπὸ τῶν ΓΑ, ΑΔ περιεχομένῳ ὀρθογωνίῳ.],
    [For since the straight-line $C D$ has been cut, at random, at point $A$, the (square) on $D C$ is thus equal to the (sum of the) squares on $C A$ and $A D$, and twice the rectangle contained by $C A$ and $A D$ [Prop.~2.4]. Let the (square) on $D B$ be added to both. Thus, the (sum of the squares) on $C D$ and $D B$ is equal to the (sum of the) squares on $C A$, $A D$, and $D B$, and twice the [rectangle contained] by $C A$ and $A D$. But, the (square) on $C B$ is equal to the (sum of the squares) on $C D$ and $D B$. For the angle at $D$ (is) a right-angle [Prop.~1.47]. And the (square) on $A B$ (is) equal to the (sum of the squares) on $A D$ and $D B$ [Prop.~1.47]. Thus, the square on $C B$ is equal to the (sum of the) squares on $C A$ and $A B$, and twice the rectangle contained by $C A$ and $A D$. So the square on $C B$ is greater than the (sum of the) squares on $C A$ and $A B$ by twice the rectangle contained by $C A$ and $A D$.],
  )
  #parallel(
    [Ἐν ἄρα τοῖς ἀμβλυγωνίοις τριγώνοις τὸ ἀπὸ τῆς τὴν ἀμβλεῖαν γωνίαν ὑποτεινούσης πλευρᾶς τετράγωνον μεῖζόν ἐστι τῶν ἀπὸ τῶν τὴν ἀμβλεῖαν γωνίαν περιεχουσῶν πλευρῶν τετραγώνων τῷ περιχομένῳ δὶς ὑπό τε μιᾶς τῶν περὶ τὴν ἀμβλεῖαν γωνίαν, ἐφ᾿ ἣν ἡ κάθετος πίπτει, καὶ τῆς ἀπολαμβανομένης ἐκτὸς ὑπὸ τῆς καθέτου πρὸς τῇ ἀμβλείᾳ γωνίᾳ· ὅπερ ἔδει δεῖξαι.],
    [Thus, in obtuse-angled triangles, the square on the side subtending the obtuse angle is greater than the (sum of the) squares on the sides containing the obtuse angle by twice the (rectangle) contained by one of the sides around the obtuse angle, to which a perpendicular (straight-line) falls, and the (straight-line) cut off outside (the triangle) by the perpendicular (straight-line) towards the obtuse angle. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book2/Prop12.lean")
