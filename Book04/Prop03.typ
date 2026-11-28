#import "../functions.typ": *

#content-box[
  #parallel-proposition(3)
  #parallel(
    [Περὶ τὸν δοθέντα κύκλον τῷ δοθέντι τριγώνῳ ἰσογώνιον τρίγωνον περιγράψαι.],
    [To circumscribe a triangle, equiangular with a given triangle, about a given circle.],
  )
  #parallel-image("/Book04/fig03", 1.8in)
  #parallel(
    [Ἔστω ὁ δοθεὶς κύκλος ὁ ΑΒΓ, τὸ δὲ δοθὲν τρίγωνον τὸ ΔΕΖ· δεῖ δὴ περὶ τὸν ΑΒΓ κύκλον τῷ ΔΕΖ τριγώνῳ ἰσογώνιον τρίγωνον περιγράψαι.],
    [Let $A B C$ be the given circle, and $D E F$ the given triangle. So it is required to circumscribe a triangle, equiangular with triangle $D E F$, about circle $A B C$.],
  )
  #parallel(
    [Ἐκβεβλήσθω ἡ ΕΖ ἐφ᾿ ἑκάτερα τὰ μέρη κατὰ τὰ Η, Θ σημεῖα, καὶ εἰλήφθω τοῦ ΑΒΓ κύκλου κέντρον τὸ Κ, καὶ διήχθω, ὡς ἔτυχεν, εὐθεῖα ἡ ΚΒ, καὶ συνεστάτω πρὸς τῇ ΚΒ εὐθείᾳ καὶ τῷ πρὸς αὐτῇ σημείῳ τῷ Κ τῇ μὲν ὑπὸ ΔΕΗ γωνίᾳ ἴση ἡ ὑπὸ ΒΚΑ, τῇ δὲ ὑπὸ ΔΖΘ ἴση ἡ ὑπὸ ΒΚΓ, καὶ διὰ τῶν Α, Β, Γ σημείων ἤχθωσαν ἐφαπτόμεναι τοῦ ΑΒΓ κύκλου αἱ ΛΑΜ, ΜΒΝ, ΝΓΛ.],
    [Let $E F$ be produced in each direction to points $G$ and $H$. And let the center $K$ of circle $A B C$ be found [Prop.~3.1]. And let the straight-line $K B$ be drawn, at random, across ($A B C$). And let (angle) $B K A$, equal to angle $D E G$, be constructed on the straight-line $K B$ at the point $K$ on it, and (angle) $B K C$, equal to $D F H$ [Prop.~1.23]. And let the (straight-lines) $L A M$, $M B N$, and $N C L$ be drawn through the points $A$, $B$, and $C$ (respectively), touching the circle $A B C$.#content-box-note[See the footnote to Prop.~3.34.]],
  )
  #parallel(
    [Καὶ ἐπεὶ ἐφάπτονται τοῦ ΑΒΓ κύκλου αἱ ΛΜ, ΜΝ, ΝΛ κατὰ τὰ Α, Β, Γ σημεῖα, ἀπὸ δὲ τοῦ Κ κέντρου ἐπὶ τὰ Α, Β, Γ σημεῖα ἐπεζευγμέναι εἰσὶν αἱ ΚΑ, ΚΒ, ΚΓ, ὀρθαὶ ἄρα εἰσὶν αἱ πρὸς τοῖς Α, Β, Γ σημείοις γωνίαι. καὶ ἐπεὶ τοῦ ΑΜΒΚ τετραπλεύρου αἱ τέσσαρες γωνίαι τέτρασιν ὀρθαῖς ἴσαι εἰσίν, ἐπειδήπερ καὶ εἰς δύο τρίγωνα διαιρεῖται τὸ ΑΜΒΚ, καί εἰσιν ὀρθαὶ αἱ ὑπὸ ΚΑΜ, ΚΒΜ γωνίαι, λοιπαὶ ἄρα αἱ ὑπὸ ΑΚΒ, ΑΜΒ δυσὶν ὀρθαῖς ἴσαι εἰσίν. εἰσὶ δὲ καὶ αἱ ὑπὸ ΔΕΗ, ΔΕΖ δυσὶν ὀρθαῖς ἴσαι· αἱ ἄρα ὑπὸ ΑΚΒ, ΑΜΒ ταῖς ὑπὸ ΔΕΗ, ΔΕΖ ἴσαι εἰσίν, ὧν ἡ ὑπὸ ΑΚΒ τῇ ὑπὸ ΔΕΗ ἐστιν ἴση· λοιπὴ ἄρα ἡ ὑπὸ ΑΜΒ λοιπῇ τῇ ὑπὸ ΔΕΖ ἐστιν ἴση. ὁμοίως δὴ δειχθήσεται, ὅτι καὶ ἡ ὑπὸ ΛΝΒ τῇ ὑπὸ ΔΖΕ ἐστιν ἴση· καὶ λοιπὴ ἄρα ἡ ὑπὸ ΜΛΝ [λοιπῇ] τῇ ὑπὸ ΕΔΖ ἐστιν ἴση. ἰσογώνιον ἄρα ἐστὶ τὸ ΛΜΝ τρίγωνον τῷ ΔΕΖ τριγώνῳ· καὶ περιγέγραπται περὶ τὸν ΑΒΓ κύκλον.],
    [And since $L M$, $M N$, and $N L$ touch circle $A B C$ at points $A$, $B$, and $C$ (respectively), and $K A$, $K B$, and $K C$ are joined from the center $K$ to points $A$, $B$, and $C$ (respectively), the angles at points $A$, $B$, and $C$ are thus right-angles [Prop.~3.18]. And since the (sum of the) four angles of quadrilateral $A M B K$ is equal to four right-angles, inasmuch as $A M B K$ (can) also (be) divided into two triangles [Prop.~1.32], and angles $K A M$ and $K B M$ are (both) right-angles, the (sum of the) remaining (angles), $A K B$ and $A M B$, is thus equal to two right-angles. And $D E G$ and $D E F$ is also equal to two right-angles [Prop.~1.13]. Thus, $A K B$ and $A M B$ is equal to $D E G$ and $D E F$, of which $A K B$ is equal to $D E G$. Thus, the remainder $A M B$ is equal to the remainder $D E F$. So, similarly, it can be shown that $L N B$ is also equal to $D F E$. Thus, the remaining (angle) $M L N$ is also equal to the [remaining] (angle) $E D F$ [Prop.~1.32]. Thus, triangle $L M N$ is equiangular with triangle $D E F$. And it has been drawn around circle $A B C$.],
  )
  #parallel(
    [Περὶ τὸν δοθέντα ἄρα κύκλον τῷ δοθέντι τριγώνῳ ἰσογώνιον τρίγωνον περιγέγραπται· ὅπερ ἔδει ποιῆσαι.],
    [Thus, a triangle, equiangular with the given triangle, has been circumscribed about the given circle. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book4/Prop03.lean")
