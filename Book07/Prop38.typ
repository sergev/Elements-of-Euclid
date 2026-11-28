#import "../functions.typ": *

#content-box[
  #parallel-proposition(38)
  #parallel(
    [Ἐὰν ἀριθμος μέρος ἔχῃ ὁτιοῦν, ὑπὸ ὁμωνύμου ἀριθμοῦ μετρηθήσεται τῷ μέρει.],
    [If a number has any part whatever, (then) it will be measured by a number called the same as the part.],
  )
  #parallel-image("/Book07/fig38", 1.2in)
  #parallel(
    [Ἀριθμὸς γὰρ ὁ Α μέρος ἐχέτω ὁτιοῦν τὸν Β, καὶ τῷ Β μέρει ὁμώνυμος ἔστω [ἀριθμὸς] ὁ Γ· λέγω, ὅτι ὁ Γ τὸν Α μετρεῖ.],
    [For let the number $A$ have any part whatever, $B$. And let the [number] $C$ be called the same as the part $B$ (i.e., $B$ is the $C$th part of $A$). I say that $C$ measures $A$.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ὁ Β τοῦ Α μέρος ἐστὶν ὁμώνυμον τῷ Γ, ἔστι δὲ καὶ ἡ Δ μονὰς τοῦ Γ μέρος ὁμώνυμον αὐτῷ, ὃ ἄρα μέρος ἐστὶν ἡ Δ μονὰς τοῦ Γ ἀριθμοῦ, τὸ αὐτὸ μέρος ἐστὶ καὶ ὁ Β τοῦ Α· ἰσάκις ἄρα ἡ Δ μονὰς τὸν Γ ἀριθμὸν μετρεῖ καὶ ὁ Β τὸν Α. ἐναλλὰξ ἄρα ἰσάκις ἡ Δ μονὰς τὸν Β ἀριθμὸν μετρεῖ καὶ ὁ Γ τὸν Α. ὁ Γ ἄρα τὸν Α μετρεῖ· ὅπερ ἔδει δεὶξαι.],
    [For since $B$ is a part of $A$ called the same as $C$, and the unit $D$ is also a part of $C$ called the same as it (i.e., $D$ is the $C$th part of $C$), thus which(ever) part the unit $D$ is of the number $C$, $B$ is also the same part of $A$. Thus, the unit $D$ measures the number $C$ as many times as $B$ (measures) $A$. Thus, alternately, the unit $D$ measures the number $B$ as many times as $C$ (measures) $A$ [Prop.~7.15]. Thus, $C$ measures $A$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop38.lean")
