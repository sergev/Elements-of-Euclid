#import "../functions.typ": *

#content-box[
  #parallel-proposition(21)
  #parallel(
    [Ἅπασα στερεὰ γωνία ὑπὸ ἐλασσόνων [ἢ] τεσσάρων ὀρθῶν γωνιῶν ἐπιπέδων περιέχεται.],
    [Any solid angle is contained by plane angles (whose sum is) less [than] four right-angles.#content-box-note[This proposition is only proved for the case of a solid angle contained by three plane angles. However, the generalization to a solid angle contained by more than three plane angles is straightforward.]],
  )
  #parallel-image("/Book11/fig21", 1.5in)
  #parallel(
    [Ἔστω στερεὰ γωνία ἡ πρὸς τῷ Α περιεχομένη ὑπὸ ἐπιπέδων γωνιῶν τῶν ὑπὸ ΒΑΓ, ΓΑΔ, ΔΑΒ· λέγω, ὅτι αἱ ὑπὸ ΒΑΓ, ΓΑΔ, ΔΑΒ τεσσάρων ὀρθῶν ἐλάσσονές εἰσιν.],
    [Let the solid angle $A$ be contained by the plane angles $B A C$, $C A D$, and $D A B$. I say that (the sum of) $B A C$, $C A D$, and $D A B$ is less than four right-angles.],
  )
  #parallel(
    [Εἰλήφθω γὰρ ἐφ᾿ ἑκάστης τῶν ΑΒ, ΑΓ, ΑΔ τυχόντα σημεῖα τὰ Β, Γ, Δ, καὶ ἐπεζεύχθωσαν αἱ ΒΓ, ΓΔ, ΔΒ. καὶ ἐπεὶ στερεὰ γωνία ἡ πρὸς τῷ Β ὑπὸ τριῶν γωνιῶν ἐπιπέδων περιέχεται τῶν ὑπὸ ΓΒΑ, ΑΒΔ, ΓΒΔ, δύο ὁποιαιοῦν τῆς λοιπῆς μείζονές εἰσιν· αἱ ἄρα ὑπὸ ΓΒΑ, ΑΒΔ τῆς ὑπὸ ΓΒΔ μείζονές εἰσιν. διὰ τὰ αὐτὰ δὴ καὶ αἱ μὲν ὑπὸ ΒΓΑ, ΑΓΔ τῆς ὑπὸ ΒΓΔ μείζονές εἰσιν, αἱ δὲ ὑπὸ ΓΔΑ, ΑΔΒ τῆς ὑπὸ ΓΔΒ μείζονές εἰσιν· αἱ ἓξ ἄρα γωνίαι αἱ ὑπὸ ΓΒΑ, ΑΒΔ, ΒΓΑ, ΑΓΔ, ΓΔΑ, ΑΔΒ τριῶν τῶν ὑπὸ ΓΒΔ, ΒΓΑ, ΓΔΒ μείζονές εἰσιν. ἀλλὰ αἱ τρεῖς αἱ ὑπὸ ΓΒΔ, ΒΔΓ, ΒΓΔ δυσὶν ὀρθαῖς ἴσαι εἰσίν· αἱ ἓξ ἄρα αἱ ὑπὸ ΓΒΑ, ΑΒΔ, ΒΓΑ, ΑΓΔ, ΓΔΑ, ΑΔΒ δύο ὀρθῶν μείζονές εἰσιν. καὶ ἐπεὶ ἑκάστου τῶν ΑΒΓ, ΑΓΔ, ΑΔΒ τριγώνων αἱ τρεῖς γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν, αἱ ἄρα τῶν τριῶν τριγώνων ἐννέα γωνίαι αἱ ὑπὸ ΓΒΑ, ΑΓΒ, ΒΑΓ, ΑΓΔ, ΓΔΑ, ΓΑΔ, ΑΔΒ, ΔΒΑ, ΒΑΔ ἓξ ὀρθαῖς ἴσαι εἰσίν, ὧν αἱ ὑπὸ ΑΒΓ, ΒΓΑ, ΑΓΔ, ΓΔΑ, ΑΔΒ, ΔΒΑ ἓξ γωνίαι δύο ὀρθῶν εἰσι μείζονες· λοιπαὶ ἄρα αἱ ὑπὸ ΒΑΓ, ΓΑΔ, ΔΑΒ τρεῖς [γωνίαι] περιέχουσαι τὴν στερεὰν γωνίαν τεσσάρων ὀρθῶν ἐλάσσονές εἰσιν.],
    [For let the random points $B$, $C$, and $D$ be taken on each of (the straight-lines) $A B$, $A C$, and $A D$ (respectively). And let $B C$, $C D$, and $D B$ be joined. And since the solid angle at $B$ is contained by the three plane angles $C B A$, $A B D$, and $C B D$, (the sum of) any two is greater than the remaining (one) [Prop.~11.20]. Thus, (the sum of) $C B A$ and $A B D$ is greater than $C B D$. So, for the same (reasons), (the sum of) $B C A$ and $A C D$ is also greater than $B C D$, and (the sum of) $C D A$ and $A D B$ is greater than $C D B$. Thus, the (sum of the) six angles $C B A$, $A B D$, $B C A$, $A C D$, $C D A$, and $A D B$ is greater than the (sum of the) three (angles) $C B D$, $B C D$, and $C D B$. But, the (sum of the) three (angles) $C B D$, $B D C$, and $B C D$ is equal to two right-angles [Prop.~1.32]. Thus, the (sum of the) six angles $C B A$, $A B D$, $B C A$, $A C D$, $C D A$, and $A D B$ is greater than two right-angles. And since the (sum of the) three angles of each of the triangles $A B C$, $A C D$, and $A D B$ is equal to two right-angles, the (sum of the) nine angles $C B A$, $A C B$, $B A C$, $A C D$, $C D A$, $C A D$, $A D B$, $D B A$, and $B A D$ of the three triangles is equal to six right-angles, of which the (sum of the) six angles $A B C$, $B C A$, $A C D$, $C D A$, $A D B$, and $D B A$ is greater than two right-angles. Thus, the (sum of the) remaining three [angles] $B A C$, $C A D$, and $D A B$, containing the solid angle, is less than four right-angles.],
  )
  #parallel(
    [Ἅπασα ἄρα στερεὰ γωνία ὑπὸ ἐλασσόνων [ἤ] τεσσάρων ὀρθῶν γωνιῶν ἐπιπέδων περιέχεται· ὅπερ ἔδει δεῖξαι.],
    [Thus, any solid angle is contained by plane angles (whose sum is) less [than] four right-angles. (Which is) the very thing it was required to show.],
  )
]
