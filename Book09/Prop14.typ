#import "../functions.typ": *

#content-box[
  #parallel-proposition(14)
  #parallel(
    [Ἐὰν ἐλάχιστος ἀριθμὸς ὑπὸ πρώτων ἀριθμῶν μετρῆται, ὑπ᾿ οὑδενὸς ἄλλου πρώτου ἀριθμοῦ μετρηθήσεται παρὲξ τῶν ἐξ ἀρχῆς μετρούντων.],
    [If a least number is measured by (some) prime numbers then it will not be measured by any other prime number except (one of) the original measuring (numbers).],
  )
  #parallel(
    [Ἐλάχιστος γὰρ ἀριθμὸς ὁ Α ὑπὸ πρώτων ἀριθμῶν τῶν Β, Γ, Δ μετρείσθω· λέγω, ὅτι ὁ Α ὑπ᾿ οὐδενὸς ἄλλου πρώτου ἀριθμοῦ μετρηθήσεται παρὲξ τῶν Β, Γ, Δ.],
    [For let $A$ be the least number measured by the prime numbers $B$, $C$, $D$. I say that $A$ will not be measured by any other prime number except (one of) $B$, $C$, $D$.],
  )
  #parallel-image("/Book09/fig14", 0.9in)
  #parallel(
    [Εἰ γὰρ δυνατόν, μετρείσθω ὑπὸ πρώτου τοῦ Ε, καὶ ὁ Ε μηδενὶ τῶν Β, Γ, Δ ἔστω ὁ αὐτός. καὶ ἐπεὶ ὁ Ε τὸν Α μετρεῖ, μετρείτω αὐτὸν κατὰ τὸν Ζ· ὁ Ε ἄρα τὸν Ζ πολλαπλασιάσας τὸν Α πεποίηκεν. καὶ μετρεῖται ὁ Α ὑπὸ πρώτων ἀριθμῶν τῶν Β, Γ, Δ. ἐὰν δὲ δύο ἀριθμοὶ πολλαπλασιάσαντες ἀλλήλους ποιῶσί τινα, τὸν δὲ γενόμενον ἐξ αὐτῶν μετρῇ τις πρῶτος ἀριθμός, καὶ ἕνα τῶν ἐξ ἀρχῆς μετρήσει· οἱ Β, Γ, Δ ἄρα ἕνα τῶν Ε, Ζ μετρήσουσιν. τὸν μὲν οὖν Ε οὐ μετρήσουσιν· ὁ γὰρ Ε πρῶτός ἐστι καὶ οὐδενὶ τῶν Β, Γ, Δ ὁ αὐτός. τὸν Ζ ἄρα μετροῦσιν ἐλάσσονα ὄντα τοῦ Α· ὅπερ ἀδύνατον. ὁ γὰρ Α ὑπόκειται ἐλάχιστος ὑπὸ τῶν Β, Γ, Δ μετρούμενος. οὐκ ἄρα τὸν Α μετρήσει πρῶτος ἀριθμὸς παρὲξ τῶν Β, Γ, Δ· ὅπερ ἔδει δεῖξαι.],
    [For, if possible, let it be measured by the prime (number) $E$. And let $E$ not be the same as one of $B$, $C$, $D$. And since $E$ measures $A$, let it measure it according to $F$. Thus, $E$ has made $A$ (by) multiplying $F$. And $A$ is measured by the prime numbers $B$, $C$, $D$. And if two numbers make some (number by) multiplying one another, and some prime number measures the number created from them, then (the prime number) will also measure one of the original (numbers) [Prop.~7.30]. Thus, $B$, $C$, $D$ will measure one of $E$, $F$. In fact, they do not measure $E$. For $E$ is prime, and not the same as one of $B$, $C$, $D$. Thus, they (all) measure $F$, which is less than $A$. The very thing (is) impossible. For $A$ was assumed (to be) the least (number) measured by $B$, $C$, $D$. Thus, no prime number can measure $A$ except (one of) $B$, $C$, $D$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop14.lean")
