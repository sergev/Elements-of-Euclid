#import "../functions.typ": *

#content-box[
  #parallel-proposition(7)
  #parallel(
    [Ἐὰν ὦσιν ὁποσοιοῦν ἀριθμοὶ [ἑξῆς] ἀνάλογον, ὁ δὲ πρῶτος τὸν ἔσχατον μετρῇ, καὶ τὸν δεύτερον μετρήσει.],
    [If there are any multitude whatsoever of [continuously] proportional numbers, and the first measures the last, then (the first) will also measure the second.],
  )
  #parallel-image("/Book08/fig07", 1.2in)
  #parallel(
    [Ἔστωσαν ὁποσοιοῦν ἀριθμοὶ ἑξῆς ἀνάλογον οἱ Α, Β, Γ, Δ, ὁ δὲ Α τὸν Δ μετρείτω· λέγω, ὅτι καὶ ὁ Α τὸν Β μετρεῖ.],
    [Let $A$, $B$, $C$, $D$ be any number whatsoever of continuously proportional numbers. And let $A$ measure $D$. I say that $A$ also measures $B$.],
  )
  #parallel(
    [Εἰ γὰρ οὐ μετρεῖ ὁ Α τὸν Β, οὐδὲ ἄλλος οὐδεὶς οὐδένα μετρήσει· μετρεῖ δὲ ὁ Α τὸν Δ. μετρεῖ ἄρα καὶ ὁ Α τὸν Β· ὅπερ ἔδει δεῖξαι.],
    [For if $A$ does not measure $B$ then no other (number) will measure any other (number) either [Prop.~8.6]. But $A$ measures $D$. Thus, $A$ also measures $B$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book8/Prop07.lean")
