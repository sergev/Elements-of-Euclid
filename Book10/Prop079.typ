#import "../functions.typ": *

#content-box[
  #parallel-proposition(79)
  #parallel(
    [Τῇ ἀποτομῇ μία [μόνον] προσαρμόζει εὐθεῖα ῥητὴ δυνάμει μόνον σύμμετρος οὖσα τῇ ὅλῃ.],
    [[Only] one rational straight-line, which is commensurable in square only with the whole, can be attached to an apotome.#content-box-note[This proposition is equivalent to Prop.~10.42, with minus signs instead of plus signs.]],
  )
  #parallel-image("/Book10/fig079", 0.26in)
  #parallel(
    [Ἔστω ἀποτομὴ ἡ ΑΒ, προσαρμόζουσα δὲ αὐτῇ ἡ ΒΓ· αἱ ΑΓ, ΓΒ ἄρα ῥηταί εἰσι δυνάμει μόνον σύμμετροι· λέγω, ὅτι τῇ ΑΒ ἑτέρα οὐ προσαρμόζει ῥητὴ δυνάμει μόνον σύμμετρος οὖσα τῇ ὅλῇ.],
    [Let $A B$ be an apotome, with $B C$ (so) attached to it. $A C$ and $C B$ are thus rational (straight-lines which are) commensurable in square only [Prop.~10.73]. I say that another rational (straight-line), which is commensurable in square only with the whole, cannot be attached to $A B$.],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν, προσαρμοζέτω ἡ ΒΔ· καὶ αἱ ΑΔ, ΔΒ ἄρα ῥηταί εἰσι δυνάμει μόνον σύμμετροι. καὶ ἐπεί, ᾧ ὑπερέχει τὰ ἀπὸ τῶν ΑΔ, ΔΒ τοῦ δὶς ὑπὸ τῶν ΑΔ, ΔΒ, τούτῳ ὑπερέχει καὶ τὰ ἀπὸ τῶν ΑΓ, ΓΒ τοῦ δὶς ὑπὸ τῶν ΑΓ, ΓΒ· τῷ γὰρ αὐτῷ τῷ ἀπὸ τῆς ΑΒ ἀμφότερα ὑπερέχει· ἐναλλὰξ ἄρα, ᾧ ὑπερέχει τὰ ἀπὸ τῶν ΑΔ, ΔΒ τῶν ἀπὸ τῶν ΑΓ, ΓΒ, τούτῳ ὑπερέχει [καὶ] τὸ δὶς ὑπὸ τῶν ΑΔ, ΔΒ τοῦ δὶς ὑπὸ τῶν ΑΓ, ΓΒ. τὰ δὲ ἀπὸ τῶν ΑΔ, ΔΒ τῶν ἀπὸ τῶν ΑΓ, ΓΒ ὑπερέχει ῥητῷ· ῥητὰ γὰρ ἀμφότερα. καὶ τὸ δὶς ἄρα ὑπὸ τῶν ΑΔ, ΔΒ τοῦ δὶς ὑπὸ τῶν ΑΓ, ΓΒ ὑπερέχει ῥητῷ· ὅπερ ἐστὶν ἀδύνατον· μέσα γὰρ ἀμφότερα, μέσον δὲ μέσου οὐχ ὑπερέχει ῥητῷ. τῇ ἄρα ΑΒ ἑτέρα οὐ προσαρμόζει ῥητὴ δυνάμει μόνον σύμμετρος οὖσα τῇ ὅλῃ.],
    [For, if possible, let $B D$ be (so) attached (to $A B$). Thus, $A D$ and $D B$ are also rational (straight-lines which are) commensurable in square only [Prop.~10.73]. And since by whatever (area) the (sum of the squares) on $A D$ and $D B$ exceeds twice the (rectangle contained) by $A D$ and $D B$, the (sum of the squares) on $A C$ and $C B$ also exceeds twice the (rectangle contained) by $A C$ and $C B$ by this (same area). For both exceed by the same (area)---(namely), the (square) on $A B$ [Prop.~2.7]. Thus, alternately, by whatever (area) the (sum of the squares) on $A D$ and $D B$ exceeds the (sum of the squares) on $A C$ and $C B$, twice the (rectangle contained) by $A D$ and $D B$ [also] exceeds twice the (rectangle contained) by $A C$ and $C B$ by this (same area). And the (sum of the squares) on $A D$ and $D B$ exceeds the (sum of the squares) on $A C$ and $C B$ by a rational (area). For both (are) rational (areas). Thus, twice the (rectangle contained) by $A D$ and $D B$ also exceeds twice the (rectangle contained) by $A C$ and $C B$ by a rational (area). The very thing is impossible. For both are medial (areas) [Prop.~10.21], and a medial (area) cannot exceed a(nother) medial (area) by a rational (area) [Prop.~10.26]. Thus, another rational (straight-line), which is commensurable in square only with the whole, cannot be attached to $A B$.],
  )
  #parallel(
    [Μία ἄρα μόνη τῇ ἀποτομῇ προσαρμόζει ῥητὴ δυνάμει μόνον σύμμετρος οὖσα τῇ ὅλῃ· ὅπερ ἔδει δεῖξαι.],
    [Thus, only one rational (straight-line), which is commensurable in square only with the whole, can be attached to an apotome. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop079.lean")
