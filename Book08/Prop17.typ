#import "../functions.typ": *

#content-box[
  #parallel-proposition(17)
  #parallel(
    [Ἐὰν κύβος ἀριθμὸς κύβον ἀριθμὸν μὴ μετρῇ, οὐδὲ ἡ πλευρὰ τὴν πλευρὰν μετρήσει· κἂν ἡ πλευρὰ τὴν πλευρὰν μὴ μετρῇ, οὐδὲ ὁ κύβος τὸν κύβον μετρήσει.],
    [If a cube number does not measure a(nother) cube number then the side (of the former) will not measure the side (of the latter) either. And if the side (of a cube number) does not measure the side (of another cube number) then the (former) cube (number) will not measure the (latter) cube (number) either.],
  )
  #parallel-image("/Book08/fig16", 0.5in)
  #parallel(
    [Κύβος γὰρ ἀριθμὸς ὁ Α κύβον ἀριθμὸν τὸν Β μὴ μετρείτω, καὶ τοῦ μὲν Α πλευρὰ ἔστω ὁ Γ, τοῦ δὲ Β ὁ Δ· λέγω, ὅτι ὁ Γ τὸν Δ οὐ μετρήσει.],
    [For let the cube number $A$ not measure the cube number $B$. And let $C$ be the side of $A$, and $D$ (the side) of $B$. I say that $C$ will not measure $D$.],
  )
  #parallel(
    [Εἰ γὰρ μετρεῖ ὁ Γ τὸν Δ, καὶ ὁ Α τὸν Β μετρήσει. οὐ μετρεῖ δὲ ὁ Α τὸν Β· οὐδ᾿ ἄρα ὁ Γ τὸν Δ μετρεῖ.],
    [For if $C$ measures $D$ then $A$ will also measure $B$ [Prop.~8.15]. And $A$ does not measure $B$. Thus, $C$ does not measure $D$ either.],
  )
  #parallel(
    [Ἀλλὰ δὴ μὴ μετρείτω ὁ Γ τὸν Δ· λέγω, ὅτι οὐδὲ ὁ Α τὸν Β μετρήσει.],
    [And so let $C$ not measure $D$. I say that $A$ will not measure $B$ either.],
  )
  #parallel(
    [Εἰ γὰρ ὁ Α τὸν Β μετρεῖ, καὶ ὁ Γ τὸν Δ μετρήσει. οὐ μετρεῖ δὲ ὁ Γ τὸν Δ· οὐδ᾿ ἄρα ὁ Α τὸν Β μετρήσει· ὅπερ ἔδει δεῖξαι.],
    [For if $A$ measures $B$ then $C$ will also measure $D$ [Prop.~8.15]. And $C$ does not measure $D$. Thus, $A$ will not measure $B$ either. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book8/Prop17.lean")
