#import "../functions.typ": *

#content-box[
  #parallel-proposition(109)
  #parallel(
    [Ἀπὸ μέσου ῥητοῦ ἀφαιρουμένου ἄλλαι δύο ἄλογοι γίνονται ἤτοι μέσης ἀποτομὴ πρώτη ἢ μετὰ ῥητοῦ μέσον τὸ ὅλον ποιοῦσα.],
    [A rational (area) being subtracted from a medial (area), two other irrational (straight-lines) arise (as the square-root of the remaining area)---either a first apotome of a medial (straight-line), or that (straight-line) which with a rational (area) makes a medial whole.],
  )
  #parallel(
    [Ἀπὸ γὰρ μέσου τοῦ ΒΓ ῥητὸν ἀφῃρήσθω τὸ ΒΔ. λέγω, ὅτι ἡ τὸ λοιπὸν τὸ ΕΓ δυναμένη μία δύο ἀλόγων γίνεται ἤτοι μέσης ἀποτομὴ πρώτη ἢ μετὰ ῥητοῦ μέσον τὸ ὅλον ποιοῦσα.],
    [For let the rational (area) $B D$ be subtracted from the medial (area) $B C$. I say that one of two irrational (straight-lines) arise (as) the square-root of the remaining (area), $E C$---either a first apotome of a medial (straight-line), or that (straight-line) which with a rational (area) makes a medial whole.],
  )
  #parallel(
    [Ἐκκείσθω γὰρ ῥητὴ ἡ ΖΗ, καὶ παραβεβλήσθω ὁμοίως τὰ χωρία. ἔστι δὴ ἀκολούθως ῥητὴ μὲν ἡ ΖΘ καὶ ἀσύμμετρος τῇ ΖΗ μήκει, ῥητὴ δὲ ἡ ΚΖ καὶ σύμμετρος τῇ ΖΗ μήκει· αἱ ΖΘ, ΖΚ ἄρα ῥηταί εἰσι δυνάμει μόνον σύμμετροι· ἀποτομὴ ἄρα ἐστὶν ἡ ΚΘ, προσαρμόζουσα δὲ ταύτῃ ἡ ΖΚ. ἤτοι δὴ ἡ ΘΖ τῆς ΖΚ μεῖζον δύναται τῷ ἀπὸ συμμέτρου ἑαυτῇ ἢ τῷ ἀπὸ ἀσυμμέτρου.],
    [For let the rational (straight-line) $F G$ be laid down, and let similar areas (to the preceding proposition) have been applied (to it). So, accordingly, $F H$ is rational, and incommensurable in length with $F G$, and $K F$ (is) also rational, and commensurable in length with $F G$. Thus, $F H$ and $F K$ are rational (straight-lines which are) commensurable in square only [Prop.~10.13]. $K H$ is thus an apotome [Prop.~10.73], and $F K$ an attachment to it. So, the square on $H F$ is greater than (the square on) $F K$ either by the (square) on (some straight-line) commensurable (in length) with ($H F$), or by the (square) on (some straight-line) incommensurable (in length with $H F$).],
  )
  #parallel-image("/Book10/fig109", 2in)
  #parallel(
    [Εἰ μὲν οὖν ἡ ΘΖ τῆς ΖΚ μεῖζον δύναται τῷ ἀπὸ συμμέτρου ἑαυτῇ, καί ἐστιν ἡ προσαρμόζουσα ἡ ΖΚ σύμμετρος τῇ ἐκκειμένῃ ῥητῇ μήκει τῇ ΖΗ, ἀποτομὴ δευτέρα ἐστὶν ἡ ΚΘ. ῥητὴ δὲ ἡ ΖΗ· ὥστε ἡ τὸ ΛΘ, τουτέστι τὸ ΕΓ, δυναμένη μέσης ἀποτομὴ πρώτη ἐστίν.],
    [Therefore, if the square on $H F$ is greater than (the square on) $F K$ by the (square) on (some straight-line) commensurable (in length) with ($H F$), and (since) the attachment $F K$ is commensurable in length with the (previously) laid down rational (straight-line) $F G$, $K H$ is a second apotome [Def.~10.12]. And $F G$ (is) rational. Hence, the square-root of $L H$---that is to say, (of) $E C$---is a first apotome of a medial (straight-line) [Prop.~10.92].],
  )
  #parallel(
    [Εἰ δὲ ἡ ΘΖ τῆς ΖΚ μεῖζον δύναται τῷ ἀπὸ ἀσυμμέτρου, καί ἐστιν ἡ προσαρμόζουσα ἡ ΖΚ σύμμετρος τῇ ἐκκειμένῃ ῥητῇ μήκει τῇ ΖΗ, ἀποτομὴ πέμπτη ἐστὶν ἡ ΚΘ· ὥστε ἡ τὸ ΕΓ δυναμένη μετὰ ῥητοῦ μέσον τὸ ὅλον ποιοῦσά ἐστιν· ὅπερ ἔδει δεῖξαι.],
    [And if the square on $H F$ is greater than (the square on) $F K$ by the (square) on (some straight-line) incommensurable (in length with $H F$), and (since) the attachment $F K$ is commensurable in length with the (previously) laid down rational (straight-line) $F G$, $K H$ is a fifth apotome [Def.~10.15]. Hence, the square-root of $E C$ is that (straight-line) which with a rational (area) makes a medial whole [Prop.~10.95]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop109.lean")
