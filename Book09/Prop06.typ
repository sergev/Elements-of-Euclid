#import "../functions.typ": *

#content-box[
  #parallel-proposition(6)
  #parallel(
    [Ἐὰν ἀριθμὸς ἑαυτὸν πολλαπλασιάσας κύβον ποιῇ, καὶ αὐτὸς κύβος ἔσται.],
    [If a number makes a cube (number by) multiplying itself then it itself will also be cube.],
  )
  #parallel(
    [Ἀριθμὸς γὰρ ὁ Α ἑαυτὸν πολλαπλασιάσας κύβον τὸν Β ποιείτω· λέγω, ὅτι καὶ ὁ Α κύβος ἐστίν.],
    [For let the number $A$ make the cube (number) $B$ (by) multiplying itself. I say that $A$ is also cube.],
  )
  #parallel-image("/Book09/fig06", 0.8in)
  #parallel(
    [Ὁ γὰρ Α τὸν Β πολλαπλασιάσας τὸν Γ ποιείτω. ἐπεὶ οὖν ὁ Α ἑαυτὸν μὲν πολλαπλασιάσας τὸν Β πεποίηκεν, τὸν δὲ Β πολλαπλασιάσας τὸν Γ πεποίηκεν, ὁ Γ ἄρα κύβος ἐστίν. καὶ ἐπεὶ ὁ Α ἑαυτὸν πολλαπλασιάσας τὸν Β πεποίηκεν, ὁ Α ἄρα τὸν Β μετρεῖ κατὰ τὰς ἐν αὐτῷ μονάδας. μετρεῖ δὲ καὶ ἡ μονὰς τὸν Α κατὰ τὰς ἐν αὐτῷ μονάδας. ἔστιν ἄρα ὡς ἡ μονὰς πρὸς τὸν Α, οὕτως ὁ Α πρὸς τὸν Β. καὶ ἐπεὶ ὁ Α τὸν Β πολλαπλασιάσας τὸν Γ πεποίηκεν, ὁ Β ἄρα τὸν Γ μετρεῖ κατὰ τὰς ἐν τῷ Α μονάδας. μετρεῖ δὲ καὶ ἡ μονὰς τὸν Α κατὰ τὰς ἐν αὐτῷ μονάδας. ἔστιν ἄρα ὡς ἡ μονὰς πρὸς τὸν Α, οὕτως ὁ Β πρὸς τὸν Γ. ἀλλ᾿ ὡς ἡ μονὰς πρὸς τὸν Α, οὕτως ὁ Α πρὸς τὸν Β· καὶ ὡς ἄρα ὁ Α πρὸς τὸν Β, ὁ Β πρὸς τὸν Γ. καὶ ἐπεὶ οἱ Β, Γ κύβοι εἰσίν, ὅμοιοι στερεοί εἰσιν. τῶν Β, Γ ἄρα δύο μέσοι ἀνάλογόν εἰσιν ἀριθμοί. καί ἐστιν ὡς ὁ Β πρὸς τὸν Γ, ὁ Α πρὸς τὸν Β. καὶ τῶν Α, Β ἄρα δύο μέσοι ἀνάλογόν εἰσιν ἀριθμοί. καί ἐστιν κύβος ὁ Β· κύβος ἄρα ἐστὶ καὶ ὁ Α· ὅπερ ἔδει δεῖξαι.],
    [For let $A$ make $C$ (by) multiplying $B$. Therefore, since $A$ has made $B$ (by) multiplying itself, and has made $C$ (by) multiplying $B$, $C$ is thus cube. And since $A$ has made $B$ (by) multiplying itself, $A$ thus measures $B$ according to the units in ($A$). And a unit also measures $A$ according to the units in it. Thus, as a unit is to $A$, so $A$ (is) to $B$. And since $A$ has made $C$ (by) multiplying $B$, $B$ thus measures $C$ according to the units in $A$. And a unit also measures $A$ according to the units in it. Thus, as a unit is to $A$, so $B$ (is) to $C$. But, as a unit (is) to $A$, so $A$ (is) to $B$. And thus as $A$ (is) to $B$, (so) $B$ (is) to $C$. And since $B$ and $C$ are cube, they are similar solid (numbers). Thus, there exist two numbers in mean proportion (between) $B$ and $C$ [Prop.~8.19]. And as $B$ is to $C$, (so) $A$ (is) to $B$. Thus, there also exist two numbers in mean proportion (between) $A$ and $B$ [Prop.~8.8]. And $B$ is cube. Thus, $A$ is also cube [Prop.~8.23]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop06.lean")
