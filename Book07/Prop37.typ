#import "../functions.typ": *

#content-box[
  #parallel-proposition(37)
  #parallel(
    [Ἐὰν ἀριθμὸς ὑπό τινος ἀριθμοῦ μετρῆται, ὁ μετρούμενος ὁμώνυμον μέρος ἕξει τῷ μετροῦντι.],
    [If a number is measured by some number, (then) the (number) measured will have a part called the same as the measuring (number).],
  )
  #parallel-image("/Book07/fig37", 1.2in)
  #parallel(
    [Ἀριθμὸς γάρ ὁ Α ὑπό τινος ἀριθμοῦ τοῦ Β μετρείσθω· λέγω, ὅτι ὁ Α ὁμώνυμον μέρος ἔχει τῷ Β.],
    [For let the number $A$ be measured by some number $B$. I say that $A$ has a part called the same as $B$.],
  )
  #parallel(
    [Ὁσάκις γὰρ ὁ Β τὸν Α μετρεῖ, τοσαῦται μονάδες ἔστωσαν ἐν τῷ Γ. ἐπεὶ ὁ Β τὸν Α μετρεῖ κατὰ τὰς ἐν τῷ Γ μονάδας, μετρεῖ δὲ καὶ ἡ Δ μονὰς τὸν Γ ἀριθμὸν κατὰ τὰς ἐν αὐτῷ μονάδας, ἰσάκις ἄρα ἡ Δ μονὰς τὸν Γ ἀριθμὸν μετρεῖ καὶ ὁ Β τὸν Α. ἐναλλὰξ ἄρα ἰσάκις ἡ Δ μονὰς τὸν Β ἀριθμὸν μετρεῖ καὶ ὁ Γ τὸν Α· ὃ ἄρα μέρος ἐστὶν ἡ Δ μονὰς τοῦ Β ἀριθμοῦ, τὸ αὐτὸ μέρος ἐστὶ καὶ ὁ Γ τοῦ Α. ἡ δὲ Δ μονὰς τοῦ Β ἀριθμοῦ μέρος ἐστὶν ὁμώνυμον αὐτῷ· καὶ ὁ Γ ἄρα τοῦ Α μέρος ἐστὶν ὁμώνυμον τῷ Β. ὥστε ὁ Α μέρος ἔχει τὸν Γ ὁμώνυμον ὄντα τῷ Β· ὅπερ ἔδει δεῖξαι.],
    [For as many times as $B$ measures $A$, so many units let there be in $C$. Since $B$ measures $A$ according to the units in $C$, and the unit $D$ also measures $C$ according to the units in it, the unit $D$ thus measures the number $C$ as many times as $B$ (measures) $A$. Thus, alternately, the unit $D$ measures the number $B$ as many times as $C$ (measures) $A$ [Prop.~7.15]. Thus, which(ever) part the unit $D$ is of the number $B$, $C$ is also the same part of $A$. And the unit $D$ is a part of the number $B$ called the same as it (i.e., a $B$th part). Thus, $C$ is also a part of $A$ called the same as $B$ (i.e., $C$ is the $B$th part of $A$). Hence, $A$ has a part $C$ which is called the same as $B$ (i.e., $A$ has a $B$th part). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop37.lean")
