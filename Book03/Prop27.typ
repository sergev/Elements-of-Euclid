#import "../functions.typ": *

#content-box[
  #parallel-proposition(27)
  #parallel(
    [Ἐν τοῖς ἴσοις κύκλοις αἱ ἐπὶ ἴσων περιφερειῶν βεβηκυῖαι γωνίαι ἴσαι ἀλλήλαις εἰσίν, ἐάν τε πρὸς τοῖς κέντροις ἐάν τε πρὸς ταῖς περιφερείαις ὦσι βεβηκυῖαι.],
    [In equal circles, angles standing upon equal circumferences are equal to one another, whether they are standing at the center or at the circumference.],
  )
  #parallel-image("/Book03/fig27", 1.5in)
  #parallel(
    [Ἐν γὰρ ἴσοις κύκλοις τοῖς ΑΒΓ, ΔΕΖ ἐπὶ ἴσων περιφερειῶν τῶν ΒΓ, ΕΖ πρὸς μὲν τοῖς Η, Θ κέντροις γωνίαι βεβηκέτωσαν αἱ ὑπὸ ΒΗΓ, ΕΘΖ, πρὸς δὲ ταῖς περιφερείαις αἱ ὑπὸ ΒΑΓ, ΕΔΖ· λέγω, ὅτι ἡ μὲν ὑπὸ ΒΗΓ γωνία τῇ ὑπὸ ΕΘΖ ἐστιν ἴση, ἡ δὲ ὑπὸ ΒΑΓ τῇ ὑπὸ ΕΔΖ ἐστιν ἴση.],
    [For let the angles $B G C$ and $E H F$ at the centers $G$ and $H$, and the (angles) $B A C$ and $E D F$ at the circumferences, stand upon the equal circumferences $B C$ and $E F$, in the equal circles $A B C$ and $D E F$ (respectively). I say that angle $B G C$ is equal to (angle) $E H F$, and $B A C$ is equal to $E D F$.],
  )
  #parallel(
    [Εἰ γὰρ ἄνισός ἐστιν ἡ ὑπὸ ΒΗΓ τῇ ὑπὸ ΕΘΖ, μία αὐτῶν μείζων ἐστίν. ἔστω μείζων ἡ ὑπὸ ΒΗΓ, καὶ συνεστάτω πρὸς τῇ ΒΗ εὐθείᾳ καὶ τῷ πρὸς αὐτῇ σημείῳ τῷ Η τῇ ὑπὸ ΕΘΖ γωνίᾳ ἴση ἡ ὑπὸ ΒΗΚ· αἱ δὲ ἴσαι γωνίαι ἐπὶ ἴσων περιφερειῶν βεβήκασιν, ὅταν πρὸς τοῖς κέντροις ὦσιν· ἴση ἄρα ἡ ΒΚ περιφέρεια τῇ ΕΖ περιφερείᾳ. ἀλλὰ ἡ ΕΖ τῇ ΒΓ ἐστιν ἴση· καὶ ἡ ΒΚ ἄρα τῇ ΒΓ ἐστιν ἴση ἡ ἐλάττων τῇ μείζονι· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἄνισός ἐστιν ἡ ὑπὸ ΒΗΓ γωνία τῇ ὑπὸ ΕΘΖ· ἴση ἄρα. καί ἐστι τῆς μὲν ὑπὸ ΒΗΓ ἡμίσεια ἡ πρὸς τῷ Α, τῆς δὲ ὑπὸ ΕΘΖ ἡμίσεια ἡ πρὸς τῷ Δ· ἴση ἄρα καὶ ἡ πρὸς τῷ Α γωνία τῇ πρὸς τῷ Δ.],
    [For if $B G C$ is unequal to $E H F$, one of them is greater. Let $B G C$ be greater, and let the (angle) $B G K$, equal to angle $E H F$, be constructed on the straight-line $B G$, at the point $G$ on it [Prop.~1.23]. But equal angles (in equal circles) stand upon equal circumferences, when they are at the centers [Prop.~3.26]. Thus, circumference $B K$ (is) equal to circumference $E F$. But, $E F$ is equal to $B C$. Thus, $B K$ is also equal to $B C$, the lesser to the greater. The very thing is impossible. Thus, angle $B G C$ is not unequal to $E H F$. Thus, (it is) equal. And the (angle) at $A$ is half $B G C$, and the (angle) at $D$ half $E H F$ [Prop.~3.20]. Thus, the angle at $A$ (is) also equal to the (angle) at $D$.],
  )
  #parallel(
    [Ἐν ἄρα τοῖς ἴσοις κύκλοις αἱ ἐπὶ ἴσων περιφερειῶν βεβηκυῖαι γωνίαι ἴσαι ἀλλήλαις εἰσίν, ἐάν τε πρὸς τοῖς κέντροις ἐάν τε πρὸς ταῖς περιφερείαις ὦσι βεβηκυῖαι· ὅπερ ἔδει δεῖξαι.],
    [Thus, in equal circles, angles standing upon equal circumferences are equal to one another, whether they are standing at the center or at the circumference. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop27.lean")
