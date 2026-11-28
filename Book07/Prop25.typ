#import "../functions.typ": *

#content-box[
  #parallel-proposition(25)
  #parallel(
    [Ἐὰν δύο ἀριθμοὶ πρῶτοι πρὸς ἀλλήλους ὦσιν, ὁ ἐκ τοῦ ἑνὸς αὐτῶν γενόμενος πρὸς τὸν λοιπὸν πρῶτος ἔσται.],
    [If two numbers are prime to one another, (then) the number created from (squaring) one of them will be prime to the remaining (number).],
  )
  #parallel(
    [Ἔστωσαν δύο ἀριθμοὶ πρῶτοι πρὸς ἀλλήλους οἱ Α, Β, καὶ ὁ Α ἑαυτὸν πολλαπλασιάσας τὸν Γ ποιείτω· λέγω, ὅτι οἱ Β, Γ πρῶτοι πρὸς ἀλλὴλους εἰσίν.],
    [Let $A$ and $B$ be two numbers (which are) prime to one another. And let $A$ make $C$ (by) multiplying itself. I say that $B$ and $C$ are prime to one another.],
  )
  #parallel-image("/Book07/fig25", 2in)
  #parallel(
    [Κείσθω γὰρ τῷ Α ἴσος ὁ Δ. ἐπεὶ οἱ Α, Β πρῶτοι πρὸς ἀλλήλους εἰσίν, ἴσος δὲ ὁ Α τῷ Δ, καί οἱ Δ, Β ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν. ἑκάτερος ἄρα τῶν Δ, Α πρὸς τὸν Β πρῶτός ἐστιν· καὶ ὁ ἐκ τῶν Δ, Α ἄρα γενόμενος πρὸς τὸν Β πρῶτος ἔσται. ὁ δὲ ἐκ τῶν Δ, Α γενόμενος ἀριθμός ἐστιν ὁ Γ. οἱ Γ, Β ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [For let $D$ be made equal to $A$. Since $A$ and $B$ are prime to one another, and $A$ (is) equal to $D$, $D$ and $B$ are thus also prime to one another. Thus, $D$ and $A$ are each prime to $B$. Thus, the (number) created from (multiplying) $D$ and $A$ will also be prime to $B$ [Prop.~7.24]. And $C$ is the number created from (multiplying) $D$ and $A$. Thus, $C$ and $B$ are prime to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop25.lean")
