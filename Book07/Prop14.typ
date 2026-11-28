#import "../functions.typ": *

#content-box[
  #parallel-proposition(14, note: [In modern notation, this proposition states that if $a:b::d:e$ and $b:c::e:f$ then $a:c::d:f$, where all symbols denote numbers.])
  #parallel(
    [Ἐὰν ὦσιν ὁποσοιοῦν ἀριθμοὶ καὶ ἄλλοι αὐτοῖς ἴσοι τὸ πλῆθος σύνδυο λαμβανόμενοι καὶ ἐν τῷ αὐτῷ λόγῳ, καὶ δι᾿ ἴσου ἐν τῷ αὐτῷ λόγῷ ἔσονται.],
    [If there are any multitude of numbers whatsoever, and (some) other (numbers) of equal multitude to them, (which are) also in the same ratio taken two by two, (then) they will also be in the same ratio via equality.],
  )
  #parallel-image("/Book07/fig14", 0.65in)
  #parallel(
    [Ἔστωσαν ὁποσοιοῦν ἀριθμοὶ οἱ Α, Β, Γ καὶ ἄλλοι αὐτοῖς ἴσοι τὸ πλῆθος σύνδυο λαμβανόμενοι ἐν τῷ αὐτῷ λόγῳ οἱ Δ, Ε, Ζ, ὡς μὲν ὁ Α πρὸς τὸν Β, οὕτως ὁ Δ πρὸς τὸν Ε, ὡς δὲ ὁ Β πρὸς τὸν Γ, οὕτως ὁ Ε πρὸς τὸν Ζ· λέγω, ὅτι καὶ δι᾿ ἴσου ἐστὶν ὡς ὁ Α πρὸς τὸν Γ, οὕτως ὁ Δ πρὸς τὸν Ζ.],
    [Let there be any multitude of numbers whatsoever, $A$, $B$, $C$, and (some) other (numbers), $D$, $E$, $F$, of equal multitude to them, (which are) in the same ratio taken two by two, (such that) as $A$ (is) to $B$, so $D$ (is) to $E$, and as $B$ (is) to $C$, so $E$ (is) to $F$. I say that also, via equality, as $A$ is to $C$, so $D$ (is) to $F$.],
  )
  #parallel(
    [Ἐπεὶ γάρ ἐστιν ὡς ὁ Α πρὸς τὸν Β, οὕτως ὁ Δ πρὸς τὸν Ε, ἐναλλὰξ ἄρα ἐστὶν ὡς ὁ Α πρὸς τὸν Δ, οὕτως ὁ Β πρὸς τὸν Ε. πάλιν, ἐπεί ἐστιν ὡς ὁ Β πρὸς τὸν Γ, οὕτως ὁ Ε πρὸς τὸν Ζ, ἐναλλὰξ ἄρα ἐστὶν ὡς ὁ Β πρὸς τὸν Ε, οὕτως ὁ Γ πρὸς τὸν Ζ. ὡς δὲ ὁ Β πρὸς τὸν Ε, οὕτως ὁ Α πρὸς τὸν Δ· καὶ ὡς ἄρα ὁ Α πρὸς τὸν Δ, οὕτως ὁ Γ πρὸς τὸν Ζ· ἐναλλὰξ ἄρα ἐστὶν ὡς ὁ Α πρὸς τὸν Γ, οὕτως ὁ Δ πρὸς τὸν Ζ· ὅπερ ἔδει δεῖξαι.],
    [For since as $A$ is to $B$, so $D$ (is) to $E$, thus, alternately, as $A$ is to $D$, so $B$ (is) to $E$ [Prop.~7.13]. Again, since as $B$ is to $C$, so $E$ (is) to $F$, thus, alternately, as $B$ is to $E$, so $C$ (is) to $F$ [Prop.~7.13]. And as $B$ (is) to $E$, so $A$ (is) to $D$. Thus, also, as $A$ (is) to $D$, so $C$ (is) to $F$. Thus, alternately, as $A$ is to $C$, so $D$ (is) to $F$ [Prop.~7.13]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop14.lean")
