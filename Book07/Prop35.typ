#import "../functions.typ": *

#content-box[
  #parallel-proposition(35)
  #parallel(
    [Ἐὰν δύο ἀριθμοὶ ἀριθμόν τινα μετρῶσιν, καὶ ὁ ἐλάχιστος ὑπ᾿ αὐτῶν μετρούμενος τὸν αὐτὸν μετρήσει.],
    [If two numbers (both) measure some number, (then) the least (number) measured by them will also measure the same (number).],
  )
  #parallel-image("/Book07/fig35", 1in)
  #parallel(
    [Δύο γὰρ ἀριθμοὶ οἱ Α, Β ἀριθμόν τινα τὸν ΓΔ μετρείτωσαν, ἐλάχιστον δὲ τὸν Ε· λέγω, ὅτι καὶ ὁ Ε τὸν ΓΔ μετρεῖ.],
    [For let two numbers, $A$ and $B$, (both) measure some number $C D$, and (let) $E$ (be the) least (number measured by both $A$ and $B$). I say that $E$ also measures $C D$.],
  )
  #parallel(
    [Εἰ γὰρ οὐ μετρεῖ ὁ Ε τὸν ΓΔ, ὁ Ε τὸν ΔΖ μετρῶν λειπέτω ἑαυτοῦ ἐλάσσονα τὸν ΓΖ. καὶ ἐπεὶ οἱ Α, Β τὸν Ε μετροῦσιν, ὁ δὲ Ε τὸν ΔΖ μετρεῖ, καὶ οἱ Α, Β ἄρα τὸν ΔΖ μετρήσουσιν. μετροῦσι δὲ καὶ ὅλον τὸν ΓΔ· καὶ λοιπὸν ἄρα τὸν ΓΖ μετρήσουσιν ἐλάσσονα ὄντα τοῦ Ε· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα οὐ μετρεῖ ὁ Ε τὸν ΓΔ· μετρεῖ ἄρα· ὅπερ ἔδει δεῖξαι.],
    [For if $E$ does not measure $C D$, (then) let $E$ leave $C F$ less than itself (in) measuring $D F$. And since $A$ and $B$ (both) measure $E$, and $E$ measures $D F$, $A$ and $B$ will thus also measure $D F$. And ($A$ and $B$) also measure the whole of $C D$. Thus, they will also measure the remainder $C F$, which is less than $E$. The very thing is impossible. Thus, $E$ cannot not measure $C D$. Thus, ($E$) measures ($C D$). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop35.lean")
