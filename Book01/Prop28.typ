#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig28(letters) = fig({
  
})

#content-box[
  #parallel-proposition(28)
  #parallel(
    [᾿Εὰν εἰς δύο εὐθείας εὐθεῖα ἐμπίπτουσα τὴν ἐκτὸς γωνίαν τῇ ἐντὸς καὶ ἀπεναντίον καὶ ἐπὶ τὰ αὐτὰ μέρη ἴσην ποιῇ ἢ τὰς ἐντὸς καὶ ἐπὶ τὰ αὐτὰ μέρη δυσὶν ὀρθαῖς ἴσας, παράλληλοι ἔσονται ἀλλήλαις αἱ εὐθεῖαι.],
    [If a straight-line falling across two straight-lines makes the external angle equal to the internal and opposite angle on the same side, or (makes) the (sum of the) internal (angles) on the same side equal to two right-angles, (then) the (two) straight-lines will be parallel to one another.],
  )
  #parallel(
    [Εἰς γὰρ δύο εὐθείας τὰς ΑΒ, ΓΔ εὐθεῖα ἐμπίπτουσα ἡ ΕΖ τὴν ἐκτὸς γωνίαν τὴν ὑπὸ ΕΗΒ τῇ ἐντὸς καὶ ἀπεναντίον γωνίᾳ τῇ ὑπὸ ΗΘΔ ἴσην ποιείτω ἢ τὰς ἐντὸς καὶ ἐπὶ τὰ αὐτὰ μέρη τὰς ὑπὸ ΒΗΘ, ΗΘΔ δυσὶν ὀρθαῖς ἴσας· λέγω, ὅτι παράλληλός ἐστιν ἡ ΑΒ τῇ ΓΔ.],
    [For let $E F$, falling across the two straight-lines $A B$ and $C D$, make the external angle $E G B$ equal to the internal and opposite angle $G H D$, or the (sum of the) internal (angles) on the same side, $B G H$ and $G H D$, equal to two right-angles. I say that $A B$ is parallel to $C D$.],
  )
  #parallel(
    [᾿Επεὶ γὰρ ἴση ἐστὶν ἡ ὑπὸ ΕΗΒ τῇ ὑπὸ ΗΘΔ, ἀλλὰ ἡ ὑπὸ ΕΗΒ τῇ ὑπὸ ΑΗΘ ἐστιν ἴση, καὶ ἡ ὑπὸ ΑΗΘ ἄρα τῇ ὑπὸ ΗΘΔ ἐστιν ἴση· καί εἰσιν ἐναλλάξ· παράλληλος ἄρα ἐστὶν ἡ ΑΒ τῇ ΓΔ.],
    [For since (in the first case) $E G B$ is equal to $G H D$, but $E G B$ is equal to $A G H$ [Prop. 1.15], $A G H$ is thus also equal to $G H D$. And they are alternate (angles). Thus, $A B$ is parallel to $C D$ [Prop. 1.27].],
  )
  #parallel(
    [Πάλιν, ἐπεὶ αἱ ὑπὸ ΒΗΘ, ΗΘΔ δύο ὀρθαῖς ἴσαι εἰσίν, εἰσὶ δὲ καὶ αἱ ὑπὸ ΑΗΘ, ΒΗΘ δυσὶν ὀρθαῖς ἴσαι, αἱ ἄρα ὑπὸ ΑΗΘ, ΒΗΘ ταῖς ὑπὸ ΒΗΘ, ΗΘΔ ἴσαι εἰσίν· κοινὴ ἀφῃρήσθω ἡ ὑπὸ ΒΗΘ· λοιπὴ ἄρα ἡ ὑπὸ ΑΗΘ λοιπῇ τῇ ὑπὸ ΗΘΔ ἐστιν ἴση· καί εἰσιν ἐναλλάξ· παράλληλος ἄρα ἐστὶν ἡ ΑΒ τῇ ΓΔ.],
    [Again, since (in the second case, the sum of) $B G H$ and $G H D$ is equal to two right-angles, and (the sum of) $A G H$ and $B G H$ is also equal to two right-angles [Prop. 1.13], (the sum of) $A G H$ and $B G H$ is thus equal to (the sum of) $B G H$ and $G H D$. Let $B G H$ be subtracted from both. Thus, the remainder $A G H$ is equal to the remainder $G H D$. And they are alternate (angles). Thus, $A B$ is parallel to $C D$ [Prop. 1.27].],
  )
  #parallel-fig(fig28)
  #parallel(
    [᾿Εὰν ἄρα εἰς δύο εὐθείας εὐθεῖα ἐμπίπτουσα τὴν ἐκτὸς γωνίαν τῇ ἐντὸς καὶ ἀπεναντίον καὶ ἐπὶ τὰ αὐτὰ μέρη ἴσην ποιῇ ἢ τὰς ἐντὸς καὶ ἐπὶ τὰ αὐτὰ μέρη δυσὶν ὀρθαῖς ἴσας, παράλληλοι ἔσονται αἱ εὐθεῖαι· ὅπερ ἔδει δεῖξαι.],
    [Thus, if a straight-line falling across two straight-lines makes the external angle equal to the internal and opposite angle on the same side, or (makes) the (sum of the) internal (angles) on the same side equal to two right-angles, (then) the (two) straight-lines will be parallel (to one another). (Which is) the very thing it was required to show.],
  )
]