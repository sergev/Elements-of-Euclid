#import "../functions.typ": *

#content-box[
  #parallel-proposition(23)
  #parallel(
    [Ἡ τῇ μέσῃ σύμμετρος μέση ἐστίν.],
    [A (straight-line) commensurable with a medial (straight-line) is medial.],
  )
  #parallel(
    [Ἔστω μέση ἡ Α, καὶ τῇ Α σύμμετρος ἔστω ἡ Β· λέγω, ὅτι καὶ ἡ Β μέση ἐστίν.],
    [Let $A$ be a medial (straight-line), and let $B$ be commensurable with $A$. I say that $B$ is also a medial (straight-line).],
  )
  #parallel(
    [Ἐκκείσθω γὰρ ῥητὴ ἡ ΓΔ, καὶ τῷ μὲν ἀπὸ τῆς Α ἴσον παρὰ τὴν ΓΔ παραβεβλήσθω χωρίον ὀρθογώνιον τὸ ΓΕ πλάτος ποιοῦν τὴν ΕΔ· ῥητὴ ἄρα ἐστὶν ἡ ΕΔ καὶ ἀσύμμετρος τῂ ΓΔ μήκει. τῷ δὲ ἀπὸ τῆς Β ἴσον παρὰ τὴν ΓΔ παραβεβλήσθω χωρίον ὀρθογώνιον τὸ ΓΖ πλάτος ποιοῦν τὴν ΔΖ. ἐπεὶ οὖν σύμμετρός ἐστιν ἡ Α τῇ Β, σύμμετρόν ἐστι καὶ τὸ ἀπὸ τῆς Α τῷ ἀπὸ τῆς Β. ἀλλὰ τῷ μὲν ἀπὸ τῆς Α ἴσον ἐστὶ τὸ ΕΓ, τῷ δὲ ἀπὸ τῆς Β ἴσον ἐστὶ τὸ ΓΖ· σύμμετρον ἄρα ἐστὶ τὸ ΕΓ τῷ ΓΖ. καί ἐστιν ὡς τὸ ΕΓ πρὸς τὸ ΓΖ, οὕτως ἡ ΕΔ πρὸς τὴν ΔΖ· σύμμετρος ἄρα ἐστὶν ἡ ΕΔ τῇ ΔΖ μήκει. ῥητὴ δέ ἐστιν ἡ ΕΔ καὶ ἀσύμμετρος τῇ ΔΓ μήκει· ῥητὴ ἄρα ἐστὶ καὶ ἡ ΔΖ καὶ ἀσύμμετρος τῇ ΔΓ μήκει· αἱ ΓΔ, ΔΖ ἄρα ῥηταί εἰσι δυνάμει μόνον σύμμετροι. ἡ δὲ τὸ ὑπὸ ῥητῶν δυνάμει μόνον συμμέτρων δυναμένη μέση ἐστίν. ἡ ἄρα τὸ ὑπὸ τῶν ΓΔ, ΔΖ δυναμένη μέση ἐστίν· καὶ δύναται τὸ ὑπὸ τῶν ΓΔ, ΔΖ ἡ Β· μέση ἄρα ἐστὶν ἡ Β.],
    [Let the rational (straight-line) $C D$ be set out, and let the rectangular area $C E$, equal to the (square) on $A$, be applied to $C D$, producing $E D$ as width. $E D$ is thus rational, and incommensurable in length with $C D$ [Prop.~10.22]. And let the rectangular area $C F$, equal to the (square) on $B$, be applied to $C D$, producing $D F$ as width. Therefore, since $A$ is commensurable with $B$, the (square) on $A$ is also commensurable with the (square) on $B$. But, $E C$ is equal to the (square) on $A$, and $C F$ is equal to the (square) on $B$. Thus, $E C$ is commensurable with $C F$. And as $E C$ is to $C F$, so $E D$ (is) to $D F$ [Prop.~6.1]. Thus, $E D$ is commensurable in length with $D F$ [Prop.~10.11]. And $E D$ is rational, and incommensurable in length with $C D$. $D F$ is thus also rational [Def.~10.3], and incommensurable in length with $D C$ [Prop.~10.13]. Thus, $C D$ and $D F$ are rational, and commensurable in square only. And the square-root of a (rectangle contained) by rational (straight-lines which are) commensurable in square only is medial [Prop.~10.21]. Thus, the square-root of the (rectangle contained) by $C D$ and $D F$ is medial. And the square on $B$ is equal to the (rectangle contained) by $C D$ and $D F$. Thus, $B$ is a medial (straight-line).],
  )
  #parallel-image("/Book10/fig023", 2.1in)
  #parallel-subheading([Πόρισμα.], [Corollary])
  #parallel(
    [Ἐκ δὴ τούτου φανερόν, ὅτι τὸ τῷ μέσῳ χωρίῳ σύμμετρον μέσον ἐστίν.],
    [And (it is) clear, from this, that an (area) commensurable with a medial area#content-box-note[A medial area is equal to the square on some medial straight-line. Hence, a medial area is expressible as $k^(1 \/ 2)$.] is medial.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop023.lean")
