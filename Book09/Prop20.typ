#import "../functions.typ": *

#content-box[
  #parallel-proposition(20)
  #parallel(
    [Οἱ πρῶτοι ἀριθμοὶ πλείους εἰσὶ παντὸς τοῦ προτεθέντος πλήθους πρώτων ἀριθμῶν.],
    [The (set of all) prime numbers is more numerous than any assigned multitude of prime numbers.],
  )
  #parallel-image("/Book09/fig20", 1.3in)
  #parallel(
    [Ἔστωσαν οἱ προτεθέντες πρῶτοι ἀριθμοὶ οἱ Α, Β, Γ· λέγω, ὅτι τῶν Α, Β, Γ πλείους εἰσὶ πρῶτοι ἀριθμοί.],
    [Let $A$, $B$, $C$ be the assigned prime numbers. I say that the (set of all) prime numbers is more numerous than $A$, $B$, $C$.],
  )
  #parallel(
    [Εἰλήφθω γὰρ ὁ ὑπὸ τῶν Α, Β, Γ ἐλάχιστος μετρούμενος καὶ ἔστω ΔΕ, καὶ προσκείσθω τῷ ΔΕ μονὰς ἡ ΔΖ. ὁ δὴ ΕΖ ἤτοι πρῶτός ἐστιν ἢ οὔ. ἔστω πρότερον πρῶτος· εὐρημένοι ἄρα εἰσὶ πρῶτοι ἀριθμοὶ οἱ Α, Β, Γ, ΕΖ πλείους τῶν Α, Β, Γ.],
    [For let the least number measured by $A$, $B$, $C$ be taken, and let it be $D E$ [Prop.~7.36]. And let the unit $D F$ be added to $D E$. So $E F$ is either prime, or not. Let it, first of all, be prime. Thus, the (set of) prime numbers $A$, $B$, $C$, $E F$, (which is) more numerous than $A$, $B$, $C$, has been found.],
  )
  #parallel(
    [Ἀλλὰ δὴ μὴ ἔστω ὁ ΕΖ πρῶτος· ὑπὸ πρώτου ἄρα τινὸς ἀριθμοῦ μετρεῖται. μετρείσθω ὑπὸ πρώτου τοῦ Η· λέγω, ὅτι ὁ Η οὐδενὶ τῶν Α, Β, Γ ἐστιν ὁ αὐτός. εἰ γὰρ δυνατόν, ἔστω. οἱ δὲ Α, Β, Γ τὸν ΔΕ μετροῦσιν· καὶ ὁ Η ἄρα τὸν ΔΕ μετρήσει. μετρεῖ δὲ καὶ τὸν ΕΖ· καὶ λοιπὴν τὴν ΔΖ μονάδα μετρήσει ὁ Η ἀριθμὸς ὤν· ὄπερ ἄτοπον. οὐκ ἄρα ὁ Η ἑνὶ τῶν Α, Β, Γ ἐστιν ὁ αὐτός. καὶ ὑπόκειται πρῶτος. εὑρημένοι ἄρα εἰσὶ πρῶτοι ἀριθμοὶ πλείους τοῦ προτεθέντος πλήθους τῶν Α, Β, Γ οἱ Α, Β, Γ, Η· ὅπερ ἔδει δεῖξαι.],
    [And so let $E F$ not be prime. Thus, it is measured by some prime number [Prop.~7.31]. Let it be measured by the prime (number) $G$. I say that $G$ is not the same as any of $A$, $B$, $C$. For, if possible, let it be (the same). And $A$, $B$, $C$ (all) measure $D E$. Thus, $G$ will also measure $D E$. And it also measures $E F$. (So) $G$ will also measure the remainder, unit $D F$, (despite) being a number [Prop.~7.28]. The very thing (is) absurd. Thus, $G$ is not the same as one of $A$, $B$, $C$. And it was assumed (to be) prime. Thus, the (set of) prime numbers $A$, $B$, $C$, $G$, (which is) more numerous than the assigned multitude (of prime numbers), $A$, $B$, $C$, has been found. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop20.lean")
