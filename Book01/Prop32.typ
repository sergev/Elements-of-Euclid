#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig32(letters) = fig({
  
})

#content-box[
  #parallel-proposition(32)
  #parallel(
    [Παντὸς τριγώνου μιᾶς τῶν πλευρῶν προσεκβληθείσης ἡ ἐκτὸς γωνία δυσὶ ταῖς ἐντὸς καὶ ἀπεναντίον ἴση ἐστίν, καὶ αἱ ἐντὸς τοῦ τριγώνου τρεῖς γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν.],
    [In any triangle, (if) one of the sides (is) produced (then) the external angle is equal to the (sum of the) two internal and opposite (angles), and the (sum of the) three internal angles of the triangle is equal to two right-angles.],
  )
  #parallel-fig(fig32)
  #parallel(
    [Ἔστω τρίγωνον τὸ ΑΒΓ, καὶ προσεκβεβλήσθω αὐτοῦ μία πλευρὰ ἡ ΒΓ ἐπὶ τὸ Δ· λέγω, ὅτι ἡ ἐκτὸς γωνία ἡ ὑπὸ ΑΓΔ ἴση ἐστὶ δυσὶ ταῖς ἐντὸς καὶ ἀπεναντίον ταῖς ὑπὸ ΓΑΒ, ΑΒΓ, καὶ αἱ ἐντὸς τοῦ τριγώνου τρεῖς γωνίαι αἱ ὑπὸ ΑΒΓ, ΒΓΑ, ΓΑΒ δυσὶν ὀρθαῖς ἴσαι εἰσίν.],
    [Let $A B C$ be a triangle, and let one of its sides $B C$ be produced to $D$. I say that the external angle $A C D$ is equal to the (sum of the) two internal and opposite angles $C A B$ and $A B C$, and the (sum of the) three internal angles of the triangle---$A B C$, $B C A$, and $C A B$---is equal to two right-angles.],
  )
  #parallel(
    [Ἤχθω γὰρ διὰ τοῦ Γ σημείου τῇ ΑΒ εὐθείᾳ παράλληλος ἡ ΓΕ.],
    [For let $C E$ be drawn through point $C$ parallel to the straight-line $A B$ [Prop.~1.31].],
  )
  #parallel(
    [Καὶ ἐπεὶ παράλληλός ἐστιν ἡ ΑΒ τῇ ΓΕ, καὶ εἰς αὐτὰς ἐμπέπτωκεν ἡ ΑΓ, αἱ ἐναλλὰξ γωνίαι αἱ ὑπὸ ΒΑΓ, ΑΓΕ ἴσαι ἀλλήλαις εἰσίν. πάλιν, ἐπεὶ παράλληλός ἐστιν ἡ ΑΒ τῇ ΓΕ, καὶ εἰς αὐτὰς ἐμπέπτωκεν εὐθεῖα ἡ ΒΔ, ἡ ἐκτὸς γωνία ἡ ὑπὸ ΕΓΔ ἴση ἐστὶ τῇ ἐντὸς καὶ ἀπεναντίον τῇ ὑπὸ ΑΒΓ. ἐδείχθη δὲ καὶ ἡ ὑπὸ ΑΓΕ τῇ ὑπὸ ΒΑΓ ἴση· ὅλη ἄρα ἡ ὑπὸ ΑΓΔ γωνία ἴση ἐστὶ δυσὶ ταῖς ἐντὸς καὶ ἀπεναντίον ταῖς ὑπὸ ΒΑΓ, ΑΒΓ.],
    [And since $A B$ is parallel to $C E$, and $A C$ has fallen across them, the alternate angles $B A C$ and $A C E$ are equal to one another [Prop.~1.29]. Again, since $A B$ is parallel to $C E$, and the straight-line $B D$ has fallen across them, the external angle $E C D$ is equal to the internal and opposite (angle) $A B C$ [Prop.~1.29]. But $A C E$ was also shown (to be) equal to $B A C$. Thus, the whole angle $A C D$ is equal to the (sum of the) two internal and opposite (angles) $B A C$ and $A B C$.],
  )
  #parallel(
    [Κοινὴ προσκείσθω ἡ ὑπὸ ΑΓΒ· αἱ ἄρα ὑπὸ ΑΓΔ, ΑΓΒ τρισὶ ταῖς ὑπὸ ΑΒΓ, ΒΓΑ, ΓΑΒ ἴσαι εἰσίν. ἀλλ᾿ αἱ ὑπὸ ΑΓΔ, ΑΓΒ δυσὶν ὀρθαῖς ἴσαι εἰσίν· καὶ αἱ ὑπὸ ΑΓΒ, ΓΒΑ, ΓΑΒ ἄρα δυσὶν ὀρθαῖς ἴσαι εἰσίν.],
    [Let $A C B$ be added to both. Thus, (the sum of) $A C D$ and $A C B$ is equal to the (sum of the) three (angles) $A B C$, $B C A$, and $C A B$. But, (the sum of) $A C D$ and $A C B$ is equal to two right-angles [Prop.~1.13]. Thus, (the sum of) $A C B$, $C B A$, and $C A B$ is also equal to two right-angles.],
  )
  #parallel(
    [Παντὸς ἄρα τριγώνου μιᾶς τῶν πλευρῶν προσεκβληθείσης ἡ ἐκτὸς γωνία δυσὶ ταῖς ἐντὸς καὶ ἀπεναντίον ἴση ἐστίν, καὶ αἱ ἐντὸς τοῦ τριγώνου τρεῖς γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, in any triangle, (if) one of the sides (is) produced (then) the external angle is equal to the (sum of the) two internal and opposite (angles), and the (sum of the) three internal angles of the triangle is equal to two right-angles. (Which is) the very thing it was required to show.],
  )
]