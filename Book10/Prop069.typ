#import "../functions.typ": *

#content-box[
  #parallel-proposition(69)
  #parallel(
    [Ἡ τῇ ῥητὸν καὶ μέσον δυναμένῃ σύμμετρος [καὶ αὐτὴ] ῥητὸν καὶ μέσον δυναμένη ἐστίν.],
    [A (straight-line) commensurable (in length) with the square-root of a rational plus a medial (area) is [itself also] the square-root of a rational plus a medial (area).],
  )
  #parallel-image("/Book10/fig066", 0.7in)
  #parallel(
    [Ἔστω ῥητὸν καὶ μέσον δυναμένη ἡ ΑΒ, καὶ τῇ ΑΒ σύμμετρος ἔστω ἡ ΓΔ· δεικτέον, ὅτι καὶ ἡ ΓΔ ῥητὸν καὶ μέσον δυναμένη ἐστίν.],
    [Let $A B$ be the square-root of a rational plus a medial (area), and let $C D$ be commensurable (in length) with $A B$. We must show that $C D$ is also the square-root of a rational plus a medial (area).],
  )
  #parallel(
    [Διῃρήσθω ἡ ΑΒ εἰς τὰς εὐθείας κατὰ τὸ Ε· αἱ ΑΕ, ΕΒ ἄρα δυνάμει εἰσὶν ἀσύμμετροι ποιοῦσαι τὸ μὲν συγκείμενον ἐκ τῶν ἀπ᾿ αὐτῶν τετραγώνων μέσον, τὸ δ᾿ ὑπ᾿ αὐτῶν ῥητόν· καὶ τὰ αὐτὰ κατεσκευάσθω τοῖς πρότερον. ὁμοίως δὴ δείξομεν, ὅτι καὶ αἱ ΓΖ, ΖΔ δυνάμει εἰσὶν ἀσύμμετροι, καὶ σύμμετρον τὸ μὲν συγκείμενον ἐκ τῶν ἀπὸ τῶν ΑΕ, ΕΒ τῷ συγκειμένῳ ἐκ τῶν ἀπὸ τῶν ΓΖ, ΖΔ, τὸ δὲ ὑπὸ ΑΕ, ΕΒ τῷ ὑπὸ ΓΖ, ΖΔ· ὥστε καὶ τὸ [μὲν] συγκείμενον ἐκ τῶν ἀπὸ τῶν ΓΖ, ΖΔ τετραγώνων ἐστὶ μέσον, τὸ δ᾿ ὑπὸ τῶν ΓΖ, ΖΔ ῥητόν.],
    [Let $A B$ be divided into its (component) straight-lines at $E$. $A E$ and $E B$ are thus incommensurable in square, making the sum of the squares on them medial, and the (rectangle contained) by them rational [Prop.~10.40]. And let the same construction be made as in the previous (propositions). So, similarly, we can show that $C F$ and $F D$ are also incommensurable in square, and that the sum of the (squares) on $A E$ and $E B$ (is) commensurable with the sum of the (squares) on $C F$ and $F D$, and the (rectangle contained) by $A E$ and $E B$ with the (rectangle contained) by $C F$ and $F D$. And hence the sum of the squares on $C F$ and $F D$ is medial, and the (rectangle contained) by $C F$ and $F D$ (is) rational.],
  )
  #parallel(
    [Ῥητὸν ἄρα καὶ μέσον δυναμένη ἐστὶν ἡ ΓΔ· ὅπερ ἔδει δεῖξαι.],
    [Thus, $C D$ is the square-root of a rational plus a medial (area) [Prop.~10.40]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop069.lean")
