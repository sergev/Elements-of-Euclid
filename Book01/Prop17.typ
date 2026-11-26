#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig17(letters) = fig({
  
})

#content-box[
  #parallel-proposition(17)
  #parallel(
    [Παντὸς τριγώνου αἱ δύο γωνίαι δύο ὀρθῶν ἐλάσσονές εἰσι πάντῇ μεταλαμβανόμεναι.],
    [For any triangle, (the sum of) two angles taken together in any (possible way) is less than two right-angles.],
  )
  #parallel(
    [῎Εστω τρίγωνον τὸ ΑΒΓ· λέγω, ὅτι τοῦ ΑΒΓ τριγώνου αἱ δύο γωνίαι δύο ὀρθῶν ἐλάττονές εἰσι πάντῃ μεταλαμβανόμεναι.
᾿Εκβεβλήσθω γὰρ ἡ ΒΓ ἐπὶ τὸ Δ.],
    [Let $A B C$ be a triangle. I say that (the sum of) two angles of triangle $A B C$ taken together in any (possible way) is less than two right-angles.],
  )
  #parallel(
    [Καὶ ἐπεὶ τριγώνου τοῦ ΑΒΓ ἐκτός ἐστι γωνία ἡ ὑπὸ ΑΓΔ, μείζων ἐστὶ τῆς ἐντὸς καὶ ἀπεναντίον τῆς ὑπὸ ΑΒΓ. κοινὴ προσκείσθω ἡ ὑπὸ ΑΓΒ· αἱ ἄρα ὑπὸ ΑΓΔ, ΑΓΒ τῶν ὑπὸ ΑΒΓ, ΒΓΑ μείζονές εἰσιν. ἀλλ᾿ αἱ ὑπὸ ΑΓΔ, ΑΓΒ δύο ὀρθαῖς ἴσαι εἰσίν· αἱ ἄρα ὑπὸ ΑΒΓ, ΒΓΑ δύο ὀρθῶν ἐλάσσονές εἰσιν.],
    [For let $B C$ be produced to $D$.],
  )
  #parallel(
    [ὁμοίως δὴ δείξομεν, ὅτι καὶ αἱ ὑπὸ ΒΑΓ, ΑΓΒ δύο ὀρθῶν ἐλάσσονές εἰσι καὶ ἔτι αἱ ὑπὸ ΓΑΒ, ΑΒΓ.],
    [And since the angle $A C D$ is external to triangle $A B C$, it is greater than the internal and opposite angle $A B C$ [Prop. 1.16]. Let $A C B$ be added to both. Thus, the (sum of the angles) $A C D$ and $A C B$ is greater than the (sum of the angles) $A B C$ and $B C A$. But, (the sum of) $A C D$ and $A C B$ is equal to two right-angles [Prop. 1.13]. Thus, (the sum of) $A B C$ and $B C A$ is less than two right-angles. Similarly, we can show that (the sum of) $B A C$ and $A C B$ is also less than two right-angles, and further (that the sum of) $C A B$ and $A B C$ (is less than two right-angles).],
  )
  #parallel-fig(fig17)
  #parallel(
    [Παντὸς ἄρα τριγώνου αἱ δύο γωνίαι δύο ὀρθῶν ἐλάσσονές εἰσι πάντῇ μεταλαμβανόμεναι· ὅπερ ἔδει δεῖξαι.],
    [Thus, for any triangle, (the sum of) two angles taken together in any (possible way) is less than two right-angles. (Which is) the very thing it was required to show.],
  )
]
