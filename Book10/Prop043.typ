#import "../functions.typ": *

#content-box[
  #parallel-proposition(43)
  #parallel(
    [Ἡ ἐκ δύο μέσων πρώτη καθ᾿ ἓν μόνον σημεῖον διαιρεῖται.],
    [A first bimedial (straight-line) can be divided (into its component terms) at one point only.#content-box-note[In other words, $k^(1 \/ 4) + k^(3 \/ 4) = k'^(1 \/ 4) + k'^(3 \/ 4)$ has only one solution: i.e., $k'=k$.]],
  )
  #parallel-image("/Book10/fig042", 0.3in)
  #parallel(
    [Ἔστω ἐκ δύο μέσων πρώτη ἡ ΑΒ διῃρημένη κατὰ τὸ Γ, ὥστε τὰς ΑΓ, ΓΒ μέσας εἶναι δυνάμει μόνον συμμέτρους ῥητὸν περιεχούσας· λέγω, ὅτι ἡ ΑΒ κατ᾿ ἄλλο σημεῖον οὐ διαιρεῖται.],
    [Let $A B$ be a first bimedial (straight-line) which has been divided at $C$, such that $A C$ and $C B$ are medial (straight-lines), commensurable in square only, (and) containing a rational (area) [Prop.~10.37]. I say that $A B$ cannot be (so) divided at another point.],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν διῃρήσθω καὶ κατὰ τὸ Δ, ὥστε καὶ τὰς ΑΔ, ΔΒ μέσας εἶναι δυνάμει μόνον συμμέτρους ῥητὸν περιεχούσας. ἐπεὶ οὖν, ᾧ διαφέρει τὸ δὶς ὑπὸ τῶν ΑΔ, ΔΒ τοῦ δὶς ὑπὸ τῶν ΑΓ, ΓΒ, τούτῳ διαφέρει τὰ ἀπὸ τῶν ΑΓ, ΓΒ τῶν ἀπὸ τῶν ΑΔ, ΔΒ, ῥητῷ δὲ διαφέρει τὸ δὶς ὑπὸ τῶν ΑΔ, ΔΒ τοῦ δὶς ὑπὸ τῶν ΑΓ, ΓΒ· ῥητὰ γὰρ ἀμφότερα· ῥητῷ ἄρα διαφέρει καὶ τὰ ἀπὸ τῶν ΑΓ, ΓΒ τῶν ἀπὸ τῶν ΑΔ, ΔΒ μέσα ὄντα· ὅπερ ἄτοπον.],
    [For, if possible, let it also be divided at $D$, such that $A D$ and $D B$ are also medial (straight-lines), commensurable in square only, (and) containing a rational (area). Since, therefore, by whatever (amount) twice the (rectangle contained) by $A D$ and $D B$ differs from twice the (rectangle contained) by $A C$ and $C B$, (the sum of) the (squares) on $A C$ and $C B$ differs from (the sum of) the (squares) on $A D$ and $D B$ by this (same amount) [Prop.~10.41 lem.]. And twice the (rectangle contained) by $A D$ and $D B$ differs from twice the (rectangle contained) by $A C$ and $C B$ by a rational (area). For (they are) both rational (areas). (The sum of) the (squares) on $A C$ and $C B$ thus differs from (the sum of) the (squares) on $A D$ and $D B$ by a rational (area, despite both) being medial (areas). The very thing is absurd [Prop.~10.26].],
  )
  #parallel(
    [Οὐκ ἄρα ἡ ἐκ δύο μέσων πρώτη κατ᾿ ἄλλο καὶ ἄλλο σημεῖον διαιρεῖται εἰς τὰ ὀνόματα· καθ᾿ ἓν ἄρα μόνον· ὅπερ ἔδει δεῖξαι.],
    [Thus, a first bimedial (straight-line) cannot be divided into its (component) terms at different points. Thus, (it can be so divided) at one point only. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop043.lean")
