#import "../functions.typ": *

#content-box[
  #parallel-proposition(7)
  #parallel(
    [Ἐὰν σύνθετος ἀριθμὸς ἀριθμόν τινα πολλαπλασιάσας ποιῇ τινα, ὁ γενόμενος στερεὸς ἔσται.],
    [If a composite number makes some (number by) multiplying some (other) number then the created (number) will be solid.],
  )
  #parallel-image("/Book09/fig07", 1.5in)
  #parallel(
    [Σύνθετος γὰρ ἀριθμὸς ὁ Α ἀριθμόν τινα τὸν Β πολλαπλασιάσας τὸν Γ ποιείτω· λέγω, ὅτι ὁ Γ στερεός ἐστιν.],
    [For let the composite number $A$ make $C$ (by) multiplying some number $B$. I say that $C$ is solid.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ὁ Α σύνθετός ἐστιν, ὑπὸ ἀριθμοῦ τινος μετρηθήσεται. μετρείσθω ὑπὸ τοῦ Δ, καὶ ὁσάκις ὁ Δ τὸν Α μετρεῖ, τοσαῦται μονάδες ἔστωσαν ἐν τῷ Ε. ἐπεὶ οὖν ὁ Δ τὸν Α μετρεῖ κατὰ τὰς ἐν τῷ Ε μονάδας, ὁ Ε ἄρα τὸν Δ πολλαπλασιάσας τὸν Α πεποίηκεν. καὶ ἐπεὶ ὁ Α τὸν Β πολλαπλασιάσας τὸν Γ πεποίηκεν, ὁ δὲ Α ἐστιν ὁ ἐκ τῶν Δ, Ε, ὁ ἄρα ἐκ τῶν Δ, Ε τὸν Β πολλαπλασιάσας τὸν Γ πεποίηκεν. ὁ Γ ἄρα στερεός ἐστιν, πλευραὶ δὲ αὐτοῦ εἰσιν οἱ Δ, Ε, Β· ὅπερ ἔδει δεῖξαι.],
    [For since $A$ is a composite (number), it will be measured by some number. Let it be measured by $D$. And, as many times as $D$ measures $A$, so many units let there be in $E$. Therefore, since $D$ measures $A$ according to the units in $E$, $E$ has thus made $A$ (by) multiplying $D$ [Def.~7.15]. And since $A$ has made $C$ (by) multiplying $B$, and $A$ is the (number created) from (multiplying) $D$, $E$, the (number created) from (multiplying) $D$, $E$ has thus made $C$ (by) multiplying $B$. Thus, $C$ is solid, and its sides are $D$, $E$, $B$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop07.lean")
