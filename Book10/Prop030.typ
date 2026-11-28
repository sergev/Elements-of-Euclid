#import "../functions.typ": *

#content-box[
  #parallel-proposition(30)
  #parallel(
    [Εὑρεῖν δύο ῥητὰς δυνάμει μόνον συμμέτρους, ὥστε τὴν μείζονα τῆς ἐλάσσονος μεῖζον δύνασθαι τῷ ἀπὸ ἀσυμμέτρου ἑαυτῇ μήκει.],
    [To find two rational (straight-lines which are) commensurable in square only, such that the square on the greater is larger than the (square on the) lesser by the (square) on (some straight-line which is) incommensurable in length with the greater.],
  )
  #parallel-image("/Book10/fig030", 1.7in)
  #parallel(
    [Ἐκκείσθω ῥητὴ ἡ ΑΒ καὶ δύο τετράγωνοι ἀριθμοὶ οἱ ΓΕ, ΕΔ, ὥστε τὸν συγκείμενον ἐξ αὐτῶν τὸν ΓΔ μὴ εἶναι τετράγωνον, καὶ γεγράφθω ἐπὶ τῆς ΑΒ ἡμικύκλιον τὸ ΑΖΒ, καὶ πεποιήσθω ὡς ὁ ΔΓ πρὸς τὸν ΓΕ, οὕτως τὸ ἀπὸ τῆς ΒΑ πρὸς τὸ ἀπὸ τῆς ΑΖ, καὶ ἐπεζεύχθω ἡ ΖΒ.],
    [Let the rational (straight-line) $A B$ be laid out, and the two square numbers, $C E$ and $E D$, such that the sum of them, $C D$, is not square [Prop.~10.28 lem. II]. And let the semi-circle $A F B$ be drawn on $A B$. And let it be contrived that as $D C$ (is) to $C E$, so the (square) on $B A$ (is) to the (square) on $A F$ [Prop.~10.6 corr.]. And let $F B$ be joined.],
  )
  #parallel(
    [Ὁμοίως δὴ δείξομεν τῷ πρὸ τούτου, ὅτι αἱ ΒΑ, ΑΖ ῥηταί εἰσι δυνάμει μόνον σύμμετροι. καὶ ἐπεί ἐστιν ὡς ὁ ΔΓ πρὸς τὸν ΓΕ, οὕτως τὸ ἀπὸ τῆς ΒΑ πρὸς τὸ ἀπὸ τῆς ΑΖ, ἀναστρέψαντι ἄρα ὡς ὁ ΓΔ πρὸς τὸν ΔΕ, οὕτως τὸ ἀπὸ τῆς ΑΒ πρὸς τὸ ἀπὸ τῆς ΒΖ. ὁ δὲ ΓΔ πρὸς τὸν ΔΕ λόγον οὐκ ἔχει, ὃν τετράγωνος ἀριθμὸς πρὸς τετράγωνον ἀριθμόν· οὐδ᾿ ἄρα τὸ ἀπὸ τῆς ΑΒ πρὸς τὸ ἀπὸ τῆς ΒΖ λόγον ἔχει, ὃν τετράγωνος ἀριθμὸς πρὸς τετράγωνον ἀριθμόν· ἀσύμμετρος ἄρα ἐστὶν ἡ ΑΒ τῇ ΒΖ μήκει. καὶ δύναται ἡ ΑΒ τῆς ΑΖ μεῖζον τῷ ἀπὸ τῆς ΖΒ ἀσυμμέτρου ἑαυτῇ.],
    [So, similarly to the (proposition) before this, we can show that $B A$ and $A F$ are rational (straight-lines which are) commensurable in square only. And since as $D C$ is to $C E$, so the (square) on $B A$ (is) to the (square) on $A F$, thus, via conversion, as $C D$ (is) to $D E$, so the (square) on $A B$ (is) to the (square) on $B F$ [Props.~5.19 corr., 3.31, 1.47]. And $C D$ does not have to $D E$ the ratio which (some) square number (has) to (some) square number. Thus, the (square) on $A B$ does not have to the (square) on $B F$ the ratio which (some) square number (has) to (some) square number either. Thus, $A B$ is incommensurable in length with $B F$ [Prop.~10.9]. And the square on $A B$ is greater than the (square on) $A F$ by the (square) on $F B$ [Prop.~1.47], (which is) incommensurable (in length) with ($A B$).],
  )
  #parallel(
    [Αἱ ΑΒ, ΑΖ ἄρα ῥηταί εἰσι δυνάμει μόνον σύμμετροι, καὶ ἡ ΑΒ τῆς ΑΖ μεῖζον δύναται τῷ ἀπὸ τῆς ΖΒ ἀσυμμέτρου ἑαυτῇ μήκει· ὅπερ ἔδει δεῖξαι.],
    [Thus, $A B$ and $A F$ are rational (straight-lines which are) commensurable in square only, and the square on $A B$ is greater than (the square on) $A F$ by the (square) on $F B$, (which is) incommensurable (in length) with ($A B$).#content-box-note[$A B$ and $A F$ have lengths $1$ and $1 \/ sqrt(1+k^2)$ times that of $A B$, respectively, where $k= sqrt(D E \/ C E)$.] (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop030.lean")
