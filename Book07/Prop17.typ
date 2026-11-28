#import "../functions.typ": *

#content-box[
  #parallel-proposition(17, note: [In modern notation, this proposition states that if $d = a thin b$ and $e=a thin c$ then $d:e::b:c$, where all symbols denote numbers.])
  #parallel(
    [Ἐὰν ἀριθμὸς δύο ἀριθμοὺς πολλαπλασιάσας ποιῇ τινας, οἱ γενόμενοι ἐξ αὐτῶν τὸν αὐτὸν ἕξουσι λόγον τοῖς πολλαπλασιασθεῖσιν.],
    [If a number multiplying two numbers makes some (numbers, then) the (numbers) generated from them will have the same ratio as the multiplied (numbers).],
  )
  #parallel-image("/Book07/fig17", 0.9in)
  #parallel(
    [Ἀριθμὸς γὰρ ὁ Α δύο ἀριθμοὺς τοὺς Β, Γ πολλαπλασιάσας τοὺς Δ, Ε ποιείτω· λέγω, ὅτι ἐστὶν ὡς ὁ Β πρὸς τὸν Γ, οὕτως ὁ Δ πρὸς τὸν Ε.],
    [For let the number $A$ make (the numbers) $D$ and $E$ (by) multiplying the two numbers $B$ and $C$ (respectively). I say that as $B$ is to $C$, so $D$ (is) to $E$.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ὁ Α τὸν Β πολλαπλασιάσας τὸν Δ πεποίηκεν, ὁ Β ἄρα τὸν Δ μετρεῖ κατὰ τὰς ἐν τῷ Α μονάδας. μετρεῖ δὲ καὶ ἡ Ζ μονὰς τὸν Α ἀριθμὸν κατὰ τὰς ἐν αὐτῷ μονάδας· ἰσάκις ἄρα ἡ Ζ μονὰς τὸν Α ἀριθμὸν μετρεῖ καὶ ὁ Β τὸν Δ. ἔστιν ἄρα ὡς ἡ Ζ μονὰς πρὸς τὸν Α ἀριθμόν, οὕτως ὁ Β πρὸς τὸν Δ. διὰ τὰ αὐτὰ δὴ καὶ ὡς ἡ Ζ μονὰς πρὸς τὸν Α ἀριθμόν, οὕτως ὁ Γ πρὸς τὸν Ε· καὶ ὡς ἄρα ὁ Β πρὸς τὸν Δ, οὕτως ὁ Γ πρὸς τὸν Ε. ἐναλλὰξ ἄρα ἐστὶν ὡς ὁ Β πρὸς τὸν Γ, οὕτως ὁ Δ πρὸς τὸν Ε· ὅπερ ἔδει δεῖξαι.],
    [For since $A$ has made $D$ (by) multiplying $B$, $B$ thus measures $D$ according to the units in $A$ [Def.~7.15]. And the unit $F$ also measures the number $A$ according to the units in it. Thus, the unit $F$ measures the number $A$ as many times as $B$ (measures) $D$. Thus, as the unit $F$ is to the number $A$, so $B$ (is) to $D$ [Def.~7.20]. And so, for the same (reasons), as the unit $F$ (is) to the number $A$, so $C$ (is) to $E$. And thus, as $B$ (is) to $D$, so $C$ (is) to $E$. Thus, alternately, as $B$ is to $C$, so $D$ (is) to $E$ [Prop.~7.13]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop17.lean")
