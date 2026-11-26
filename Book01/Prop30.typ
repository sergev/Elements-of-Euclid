#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig30(letters) = fig({
  
})

#content-box[
  #parallel-proposition(30)
  #parallel(
    [Αἱ τῇ αὐτῇ εὐθείᾳ παράλληλοι καὶ ἀλλήλαις εἰσὶ παράλληλοι.],
    [(Straight-lines) parallel to the same straight-line are also parallel to one another.],
  )
  #parallel(
    [῎Εστω ἑκατέρα τῶν ΑΒ, ΓΔ τῇ ΕΖ παράλληλος· λέγω, ὅτι καὶ ἡ ΑΒ τῇ ΓΔ ἐστι παράλληλος.],
    [Let each of the (straight-lines) $A B$ and $C D$ be parallel to $E F$. I say that $A B$ is also parallel to $C D$.],
  )
  #parallel(
    [᾿Εμπιπτέτω γὰρ εἰς αὐτὰς εὐθεῖα ἡ ΗΚ.],
    [For let the straight-line $G K$ fall across ($A B$, $C D$, and $E F$).],
  )
  #parallel-fig(fig30)
  #parallel(
    [Καὶ ἐπεὶ εἰς παραλλήλους εὐθείας τὰς ΑΒ, ΕΖ εὐθεῖα ἐμπέπτωκεν ἡ ΗΚ, ἴση ἄρα ἡ ὑπὸ ΑΗΚ τῇ ὑπὸ ΗΘΖ. πάλιν, ἐπεὶ εἰς παραλλήλους εὐθείας τὰς ΕΖ, ΓΔ εὐθεῖα ἐμπέπτωκεν ἡ ΗΚ, ἴση ἐστὶν ἡ ὑπὸ ΗΘΖ τῇ ὑπὸ ΗΚΔ. ἐδείχθη δὲ καὶ ἡ ὑπὸ ΑΗΚ τῇ ὑπὸ ΗΘΖ ἴση. καὶ ἡ ὑπὸ ΑΗΚ ἄρα τῇ ὑπὸ ΗΚΔ ἐστιν ἴση· καί εἰσιν ἐναλλάξ. παράλληλος ἄρα ἐστὶν ἡ ΑΒ τῇ ΓΔ.],
    [And since the straight-line $G K$ has fallen across the parallel straight-lines $A B$ and $E F$, (angle) $A G K$ (is) thus equal to $G H F$ [Prop. 1.29]. Again, since the straight-line $G K$ has fallen across the parallel straight-lines $E F$ and $C D$, (angle) $G H F$ is equal to $G K D$ [Prop. 1.29]. But $A G K$ was also shown (to be) equal to $G H F$. Thus, $A G K$ is also equal to $G K D$. And they are alternate (angles). Thus, $A B$ is parallel to $C D$ [Prop. 1.27].],
  )
  #parallel(
    [[Αἱ ἄρα τῇ αὐτῇ εὐθείᾳ παράλληλοι καὶ ἀλλήλαις εἰσὶ παράλληλοι·] ὅπερ ἔδει δεῖξαι.],
    [[Thus, (straight-lines) parallel to the same straight-line are also parallel to one another.] (Which is) the very thing it was required to show.],
  )
]