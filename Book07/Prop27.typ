#import "../functions.typ": *

#content-box[
  #parallel-proposition(27, note: [In modern notation, this proposition states that if $a$ is prime to $b$, then $a^2$ is also prime to $b^2$, as well as $a^3$ to $b^3$, etc., where all symbols denote numbers.])
  #parallel(
    [Ἐὰν δύο ἀριθμοὶ πρῶτοι πρὸς ἀλλήλους ὦσιν, καὶ πολλαπλασιάσας ἑκάτερος ἑαυτὸν ποιῇ τινα, οἱ γενόμενοι ἐξ αὐτῶν πρῶτοι πρὸς ἀλλήλους ἔσονται, κἂν οἱ ἐξ ἀρχῆς τοὺς γενομένους πολλαπλασιάσαντες ποιῶσί τινας, κἀκεῖνοι πρῶτοι πρὸς ἀλλήλους ἔσονται [καὶ ἀεὶ περὶ τοὺς ἄκρους τοῦτο συμβαίνει].],
    [If two numbers are prime to one another and each makes some (number by) multiplying itself, (then) the numbers created from them will be prime to one another, and if the original (numbers) make some (more numbers by) multiplying the created (numbers, then) these will also be prime to one another [and this always happens with the extremes].],
  )
  #parallel-image("/Book07/fig27", 2in)
  #parallel(
    [Ἔστωσαν δύο ἀριθμοὶ πρῶτοι πρὸς ἀλλήλους οἱ Α, Β, καὶ ὁ Α ἑαυτὸν μὲν πολλαπλασιάσας τὸν Γ ποιείτω, τὸν δὲ Γ πολλαπλασιάσας τὸν Δ ποιείτω, ὁ δὲ Β ἑαυτὸν μὲν πολλαπλασιάσας τὸν Ε ποιείτω, τὸν δὲ Ε πολλαπλασιάσας τὸν Ζ ποιείτω· λέγω, ὅτι οἵ τε Γ, Ε καὶ οἱ Δ, Ζ πρῶτοι πρὸς ἀλλήλους εἰσίν.],
    [Let $A$ and $B$ be two numbers prime to one another, and let $A$ make $C$ (by) multiplying itself, and let it make $D$ (by) multiplying $C$. And let $B$ make $E$ (by) multiplying itself, and let it make $F$ (by) multiplying $E$. I say that $C$ and $E$, and $D$ and $F$, are prime to one another.],
  )
  #parallel(
    [Ἐπεὶ γὰρ οἱ Α, Β πρῶτοι πρὸς ἀλλήλους εἰσίν, καὶ ὁ Α ἑαυτὸν πολλαπλασιάσας τὸν Γ πεποίηκεν, οἱ Γ, Β ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν. ἐπεὶ οὖν οἱ Γ, Β πρῶτοι πρὸς ἀλλήλους εἰσίν, καὶ ὁ Β ἑαυτὸν πολλαπλασιάσας τὸν Ε πεποίηκεν, οἱ Γ, Ε ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν. πάλιν, ἐπεὶ οἱ Α, Β πρῶτοι πρὸς ἀλλήλους εἰσίν, καὶ ὁ Β ἑαυτὸν πολλαπλασιάσας τὸν Ε πεποίηκεν, οἱ Α, Ε ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν. ἐπεὶ οὖν δύο ἀριθμοὶ οἱ Α, Γ πρὸς δύο ἀριθμοὺς τοὺς Β, Ε ἀμφότεροι πρὸς ἑκάτερον πρῶτοί εἰσιν, καὶ ὁ ἐκ τῶν Α, Γ ἄρα γενόμενος πρὸς τὸν ἐκ τῶν Β, Ε πρῶτός ἐστιν. καί ἐστιν ὁ μὲν ἐκ τῶν Α, Γ ὁ Δ, ὁ δὲ ἐκ τῶν Β, Ε ὁ Ζ. οἱ Δ, Ζ ἄρα πρῶτοι πρὸς ἀλλήλους εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [For since $A$ and $B$ are prime to one another, and $A$ has made $C$ (by) multiplying itself, $C$ and $B$ are thus prime to one another [Prop.~7.25]. Therefore, since $C$ and $B$ are prime to one another, and $B$ has made $E$ (by) multiplying itself, $C$ and $E$ are thus prime to one another [Prop.~7.25]. Again, since $A$ and $B$ are prime to one another, and $B$ has made $E$ (by) multiplying itself, $A$ and $E$ are thus prime to one another [Prop.~7.25]. Therefore, since the two numbers $A$ and $C$ are both prime to each of the two numbers $B$ and $E$, the (number) created from (multiplying) $A$ and $C$ is thus prime to the (number created) from (multiplying) $B$ and $E$ [Prop.~7.26]. And $D$ is the (number created) from (multiplying) $A$ and $C$, and $F$ the (number created) from (multiplying) $B$ and $E$. Thus, $D$ and $F$ are prime to one another. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop27.lean")
