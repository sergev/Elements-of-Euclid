#import "../functions.typ": *

#content-box[
  #parallel-proposition(27)
  #parallel(
    [Ἐὰν εἰς δύο εὐθείας εὐθεῖα ἐμπίπτουσα τὰς ἐναλλὰξ γωνίας ἴσας ἀλλήλαις ποιῇ, παράλληλοι ἔσονται ἀλλήλαις αἱ εὐθεῖαι.],
    [If a straight-line falling across two straight-lines makes the alternate angles equal to one another (then) the (two) straight-lines will be parallel to one another.],
  )
  #parallel-image("/Book01/fig27", 1.5in)
  #parallel(
    [Εἰς γὰρ δύο εὐθείας τὰς ΑΒ, ΓΔ εὐθεῖα ἐμπίπτουσα ἡ ΕΖ τὰς ἐναλλὰξ γωνίας τὰς ὑπὸ ΑΕΖ, ΕΖΔ ἴσας ἀλλήλαις ποιείτω· λέγω, ὅτι παράλληλός ἐστιν ἡ ΑΒ τῇ ΓΔ.],
    [For let the straight-line $E F$, falling across the two straight-lines $A B$ and $C D$, make the alternate angles $A E F$ and $E F D$ equal to one another. I say that $A B$ and $C D$ are parallel.],
  )
  #parallel(
    [Εἰ γὰρ μή, ἐκβαλλόμεναι αἱ ΑΒ, ΓΔ συμπεσοῦνται ἤτοι ἐπὶ τὰ Β, Δ μέρη ἢ ἐπὶ τὰ Α, Γ. ἐκβεβλήσθωσαν καὶ συμπιπτέτωσαν ἐπὶ τὰ Β, Δ μέρη κατὰ τὸ Η. τριγώνου δὴ τοῦ ΗΕΖ ἡ ἐκτὸς γωνία ἡ ὑπὸ ΑΕΖ ἴση ἐστὶ τῇ ἐντὸς καὶ ἀπεναντίον τῇ ὑπὸ ΕΖΗ· ὅπερ ἐστὶν ἀδύνατον· οὐκ ἄρα αἱ ΑΒ, ΔΓ ἐκβαλλόμεναι συμπεσοῦνται ἐπὶ τὰ Β, Δ μέρη. ὁμοίως δὴ δειχθήσεται, ὅτι οὐδὲ ἐπὶ τὰ Α, Γ· αἱ δὲ ἐπὶ μηδέτερα τὰ μέρη συμπίπτουσαι παράλληλοί εἰσιν· παράλληλος ἄρα ἐστὶν ἡ ΑΒ τῇ ΓΔ.],
    [For if not, being produced, $A B$ and $C D$ will certainly meet together: either in the direction of $B$ and $D$, or (in the direction) of $A$ and $C$ [Def.~1.23]. Let them be produced, and let them meet together in the direction of $B$ and $D$ at (point) $G$. So, for the triangle $G E F$, the external angle $A E F$ is equal to the internal and opposite (angle) $E F G$. The very thing is impossible [Prop.~1.16]. Thus, being produced, $A B$ and $C D$ will not meet together in the direction of $B$ and $D$. Similarly, it can be shown that neither (will they meet together) in (the direction of) $A$ and $C$. But (straight-lines) meeting in neither direction are parallel [Def.~1.23]. Thus, $A B$ and $C D$ are parallel.],
  )
  #parallel(
    [Ἐὰν ἄρα εἰς δύο εὐθείας εὐθεῖα ἐμπίπτουσα τὰς ἐναλλὰξ γωνίας ἴσας ἀλλήλαις ποιῇ, παράλληλοι ἔσονται αἱ εὐθεῖαι· ὅπερ ἔδει δεῖξαι.],
    [Thus, if a straight-line falling across two straight-lines makes the alternate angles equal to one another (then) the (two) straight-lines will be parallel (to one another). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book1/Prop27.lean")