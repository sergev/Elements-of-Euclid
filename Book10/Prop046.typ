#import "../functions.typ": *

#content-box[
  #parallel-proposition(46)
  #parallel(
    [Ἡ ῥητὸν καὶ μέσον δυναμένη καθ᾿ ἓν μόνον σημεῖον διαιρεῖται.],
    [The square-root of a rational plus a medial (area) can be divided (into its component terms) at one point only.#content-box-note[In other words, $sqrt([(1+k^2)^(1 \/ 2)+k] \/ [2 thin (1+k^2)]) + sqrt([(1+k^2)^(1 \/ 2)-k] \/ [2 thin (1+k^2)]) = sqrt([(1+k'^2)^(1 \/ 2)+k'] \/ [2 thin (1+k'^2)])$ $+ sqrt([(1+k'^2)^(1 \/ 2)-k'] \/ [2 thin (1+k'^2)])$ has only one solution: i.e., $k'=k$.]],
  )
  #parallel-image("/Book10/fig042", 0.3in)
  #parallel(
    [Ἔστω ῥητὸν καὶ μέσον δυναμένη ἡ ΑΒ διῃρημένη κατὰ τὸ Γ, ὥστε τὰς ΑΓ, ΓΒ δυνάμει ἀσυμμέτρους εἶναι ποιούσας τὸ μὲν συγκείμενον ἐκ τῶν ἀπὸ τῶν ΑΓ, ΓΒ μέσον, τὸ δὲ δὶς ὑπὸ τῶν ΑΓ, ΓΒ ῥητόν· λέγω, ὅτι ἡ ΑΒ κατ᾿ ἄλλο σημεῖον οὐ διαιρεῖται.],
    [Let $A B$ be the square-root of a rational plus a medial (area) which has been divided at $C$, so that $A C$ and $C B$ are incommensurable in square, making the sum of the (squares) on $A C$ and $C B$ medial, and twice the (rectangle contained) by $A C$ and $C B$ rational [Prop.~10.40]. I say that $A B$ cannot be (so) divided at another point.],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν, διῃρήσθω καὶ κατὰ τὸ Δ, ὥστε καὶ τὰς ΑΔ, ΔΒ δυνάμει ἀσυμμέτρους εἶναι ποιούσας τὸ μὲν συγκείμενον ἐκ τῶν ἀπὸ τῶν ΑΔ, ΔΒ μέσον, τὸ δὲ δὶς ὑπὸ τῶν ΑΔ, ΔΒ ῥητόν. ἐπεὶ οὖν, ᾧ διαφέρει τὸ δὶς ὑπὸ τῶν ΑΓ, ΓΒ τοῦ δὶς ὑπὸ τῶν ΑΔ, ΔΒ, τούτῳ διαφέρει καὶ τὰ ἀπὸ τῶν ΑΔ, ΔΒ τῶν ἀπὸ τῶν ΑΓ, ΓΒ, τὸ δὲ δὶς ὑπὸ τῶν ΑΓ, ΓΒ τοῦ δὶς ὑπὸ τῶν ΑΔ, ΔΒ ὑπερέχει ῥητῷ, καὶ τὰ ἀπὸ τῶν ΑΔ, ΔΒ ἄρα τῶν ἀπὸ τῶν ΑΓ, ΓΒ ὑπερέχει ῥητῷ μέσα ὄντα· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἡ ῥητὸν καὶ μέσον δυναμένη κατ᾿ ἄλλο καὶ ἄλλο σημεῖον διαιρεῖται. κατὰ ἓν ἄρα σημεῖον διαιρεῖται· ὅπερ ἔδει δεῖξαι.],
    [For, if possible, let it also be divided at $D$, so that $A D$ and $D B$ are also incommensurable in square, making the sum of the (squares) on $A D$ and $D B$ medial, and twice the (rectangle contained) by $A D$ and $D B$ rational. Therefore, since by whatever (amount) twice the (rectangle contained) by $A C$ and $C B$ differs from twice the (rectangle contained) by $A D$ and $D B$, (the sum of) the (squares) on $A D$ and $D B$ also differs from (the sum of) the (squares) on $A C$ and $C B$ by this (same amount). And twice the (rectangle contained) by $A C$ and $C B$ exceeds twice the (rectangle contained) by $A D$ and $D B$ by a rational (area). (The sum of) the (squares) on $A D$ and $D B$ thus also exceeds (the sum of) the (squares) on $A C$ and $C B$ by a rational (area), (despite both) being medial (areas). The very thing is impossible [Prop.~10.26]. Thus, the square-root of a rational plus a medial (area) cannot be divided (into its component terms) at different points. Thus, it can be (so) divided at one point (only). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop046.lean")
