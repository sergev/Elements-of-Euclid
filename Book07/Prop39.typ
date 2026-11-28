#import "../functions.typ": *

#content-box[
  #parallel-proposition(39)
  #parallel(
    [Ἀριθμὸν εὐρεῖν, ὃς ἐλάχιστος ὢν ἕξει τὰ δοθέντα μέρη.],
    [To find the least number that will have given parts.],
  )
  #parallel-image("/Book07/fig39", 2.2in)
  #parallel(
    [Ἔστω τὰ δοθέντα μέρη τὰ Α, Β, Γ· δεῖ δὴ ἀριθμὸν εὑρεῖν, ὃς ἐλάχιστος ὢν ἕξει τὰ Α, Β, Γ μέρη.],
    [Let $A$, $B$, and $C$ be the given parts. So it is required to find the least number which will have the parts $A$, $B$, and $C$ (i.e., an $A$th part, a $B$th part, and a $C$th part).],
  )
  #parallel(
    [Ἔστωσαν γὰρ τοῖς Α, Β, Γ μέρεσιν ὁμώνυμοι ἀριθμοὶ οἱ Δ, Ε, Ζ, καὶ εἰλήφθω ὑπὸ τῶν Δ, Ε, Ζ ἐλάχιστος μετρούμενος ἀριθμὸς ὁ Η.],
    [For let $D$, $E$, and $F$ be numbers having the same names as the parts $A$, $B$, and $C$ (respectively). And let the least number, $G$, measured by $D$, $E$, and $F$, be taken [Prop.~7.36].],
  )
  #parallel(
    [Ὁ Η ἄρα ὁμώνυμα μέρη ἔχει τοῖς Δ, Ε, Ζ. τοῖς δὲ Δ, Ε, Ζ ὁμώνυμα μέρη ἐστὶ τὰ Α, Β, Γ· ὁ Η ἄρα ἔχει τὰ Α, Β, Γ μέρη. λέγω δή, ὅτι καὶ ἐλάχιστος ὤν, εἰ γὰρ μή, ἔσται τις τοῦ Η ἐλάσσων ἀριθμός, ὃς ἕξει τὰ Α, Β, Γ μέρη. ἔστω ὁ Θ. ἐπεὶ ὁ Θ ἔχει τὰ Α, Β, Γ μέρη, ὁ Θ ἄρα ὑπὸ ὁμωνύμων ἀριθμῶν μετρηθήσεται τοῖς Α, Β, Γ μέρεσιν. τοῖς δὲ Α, Β, Γ μέρεσιν ὁμώνυμοι ἀριθμοί εἰσιν οἱ Δ, Ε, Ζ· ὁ Θ ἄρα ὑπὸ τῶν Δ, Ε, Ζ μετρεῖται. καί ἐστιν ἐλάσσων τοῦ Η· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἔσται τις τοῦ Η ἐλάσσων ἀριθμός, ὃς ἕξει τὰ Α, Β, Γ μέρη· ὅπερ ἔδει δεῖξαι.],
    [Thus, $G$ has parts called the same as $D$, $E$, and $F$ [Prop.~7.37]. And $A$, $B$, and $C$ are parts called the same as $D$, $E$, and $F$ (respectively). Thus, $G$ has the parts $A$, $B$, and $C$. So I say that ($G$) is also the least (number having the parts $A$, $B$, and $C$). For if not, there will be some number less than $G$ which will have the parts $A$, $B$, and $C$. Let it be $H$. Since $H$ has the parts $A$, $B$, and $C$, $H$ will thus be measured by numbers called the same as the parts $A$, $B$, and $C$ [Prop.~7.38]. And $D$, $E$, and $F$ are numbers called the same as the parts $A$, $B$, and $C$ (respectively). Thus, $H$ is measured by $D$, $E$, and $F$. And ($H$) is less than $G$. The very thing is impossible. Thus, there cannot be some number less than $G$ which will have the parts $A$, $B$, and $C$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop39.lean")
