#import "../functions.typ": *

#content-box[
  #parallel-proposition(20)
  #parallel(
    [Ἐὰν ῥητὸν παρὰ ῥητὴν παραβληθῇ, πλάτος ποιεῖ ῥητὴν καὶ σύμμετρον τῇ, παρ᾿ ἣν παράκειται, μήκει.],
    [If a rational (area) is applied to a rational (straight-line) then it produces as breadth a (straight-line which is) rational, and commensurable in length with the (straight-line) to which it is applied.],
  )
  #parallel-image("/Book10/fig020", 2.4in)
  #parallel(
    [Ῥητὸν γὰρ τὸ ΑΓ παρὰ ῥητὴν τὴν ΑΒ παραβεβλήσθω πλάτος ποιοῦν τὴν ΒΓ· λέγω, ὅτι ῥητή ἐστιν ἡ ΒΓ καὶ σύμμετρος τῇ ΒΑ μήκει.],
    [For let the rational (area) $A C$ be applied to the rational (straight-line) $A B$, producing the (straight-line) $B C$ as breadth. I say that $B C$ is rational, and commensurable in length with $B A$.],
  )
  #parallel(
    [Ἀναγεγράφθω γὰρ ἀπὸ τῆς ΑΒ τετράγωνον τὸ ΑΔ· ῥητὸν ἄρα ἐστὶ τὸ ΑΔ. ῥητὸν δὲ καὶ τὸ ΑΓ· σύμμετρον ἄρα ἐστὶ τὸ ΔΑ τῷ ΑΓ. καί ἐστιν ὡς τὸ ΔΑ πρὸς τὸ ΑΓ, οὕτως ἡ ΔΒ πρὸς τὴν ΒΓ. σύμμετρος ἄρα ἐστὶ καὶ ἡ ΔΒ τῇ ΒΓ· ἴση δὲ ἡ ΔΒ τῇ ΒΑ· σύμμετρος ἄρα καὶ ἡ ΑΒ τῇ ΒΓ. ῥητὴ δέ ἐστιν ἡ ΑΒ· ῥητὴ ἄρα ἐστὶ καὶ ἡ ΒΓ καὶ σύμμετρος τῇ ΑΒ μήκει.],
    [For let the square $A D$ be described on $A B$. $A D$ is thus rational [Def.~10.4]. And $A C$ (is) also rational. $D A$ is thus commensurable with $A C$. And as $D A$ is to $A C$, so $D B$ (is) to $B C$ [Prop.~6.1]. Thus, $D B$ is also commensurable (in length) with $B C$ [Prop.~10.11]. And $D B$ (is) equal to $B A$. Thus, $A B$ (is) also commensurable (in length) with $B C$. And $A B$ is rational. Thus, $B C$ is also rational, and commensurable in length with $A B$ [Def.~10.3].],
  )
  #parallel(
    [Ἐὰν ἄρα ῥητὸν παρὰ ῥητὴν παραβληθῇ, καὶ τὰ ἑξῆς.],
    [Thus, if a rational (area) is applied to a rational (straight-line), and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop020.lean")
