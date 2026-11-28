#import "../functions.typ": *

#content-box[
  #parallel-proposition(26)
  #parallel(
    [Ἐὰν δύο ἀριθμοὶ πρὸς δύο ἀριθμοὺς ἀμφότεροι πρὸς ἑκάτερον πρῶτοι ὦσιν, καὶ οἱ ἐξ αὐτῶν γενόμενοι πρῶτοι πρὸς ἀλλήλους ἔσονται.],
    [If two numbers are both prime to each of two numbers, (then) the (numbers) created from (multiplying) them will also be prime to one another.],
  )
  #parallel(
    [Δύο γὰρ ἀριθμοὶ οἱ Α, Β πρὸς δύο ἀριθμοὺς τοὺς Γ, Δ ἀμφότεροι πρὸς ἑκάτερον πρῶτοι ἔστωσαν, καὶ ὁ μὲν Α τὸν Β πολλαπλασιάσας τὸν Ε ποιείτω, ὁ δὲ Γ τὸν Δ πολλαπλασιάσας τὸν Ζ ποιείτω· λέγω, ὅτι οἱ Ε, Ζ πρῶτοι πρὸς ἀλλήλους εἰσίν.],
    [For let two numbers, $A$ and $B$, both be prime to each of two numbers, $C$ and $D$. And let $A$ make $E$ (by) multiplying $B$, and let $C$ make $F$ (by) multiplying $D$. I say that $E$ and $F$ are prime to one another.],
  )
  #parallel-image("/Book07/fig26", 1in)
  #parallel(
    [Ἐπεὶ γὰρ ἑκάτερος τῶν Α, Β πρὸς τὸν Γ πρῶτός ἐστιν, καὶ ὁ ἐκ τῶν Α, Β ἄρα γενόμενος πρὸς τὸν Γ πρῶτος ἔσται. ὁ δὲ ἐκ τῶν Α, Β γενόμενός ἐστιν ὁ Ε· οἱ Ε, Γ ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν. διὰ τὰ αὐτὰ δὴ καὶ οἱ Ε, Δ πρῶτοι πρὸς ἀλλήλους εἰσίν. ἑκάτερος ἄρα τῶν Γ, Δ πρὸς τὸν Ε πρῶτός ἐστιν. καὶ ὁ ἐκ τῶν Γ, Δ ἄρα γενόμενος πρὸς τὸν Ε πρῶτος ἔσται. ὁ δὲ ἐκ τῶν Γ, Δ γενόμενός ἐστιν ὁ Ζ. οἱ Ε, Ζ ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [For since $A$ and $B$ are each prime to $C$, the (number) created from (multiplying) $A$ and $B$ will thus also be prime to $C$ [Prop.~7.24]. And $E$ is the (number) created from (multiplying) $A$ and $B$. Thus, $E$ and $C$ are prime to one another. So, for the same (reasons), $E$ and $D$ are also prime to one another. Thus, $C$ and $D$ are each prime to $E$. Thus, the (number) created from (multiplying) $C$ and $D$ will also be prime to $E$ [Prop.~7.24]. And $F$ is the (number) created from (multiplying) $C$ and $D$. Thus, $E$ and $F$ are prime to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop26.lean")
