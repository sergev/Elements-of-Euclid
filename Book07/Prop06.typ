#import "../functions.typ": *

#content-box[
  #parallel-proposition(6, note: [In modern notation, this proposition states that if $a = (m \/ n) thin b$ and $c=(m \/ n) thin d$ then $(a+c) = (m \/ n) thin (b+d)$, where all symbols denote numbers.])
  #parallel(
    [Ἐὰν ἀριθμὸς ἀριθμοῦ μέρη ᾖ, καὶ ἕτερος ἑτέρου τὰ αὐτὰ μέρη ᾖ, καὶ συναμφότερος συναμφοτέρου τὰ αὐτὰ μέρη ἔσται, ὅπερ ὁ εἷς τοῦ ἑνός.],
    [If a number is parts of a number, and another (number) is the same parts of another, (then) the sum (of the leading numbers) will also be the same parts of the sum (of the following numbers) that one (number) is of another.],
  )
  #parallel-image("/Book07/fig06", 2in)
  #parallel(
    [Ἀριθμὸς γὰρ ὁ ΑΒ ἀριθμοῦ τοῦ Γ μέρη ἔστω, καὶ ἕτερος ὁ ΔΕ ἑτέρου τοῦ Ζ τὰ αὐτὰ μέρη, ἅπερ ὁ ΑΒ τοῦ Γ· λέγω, ὅτι καὶ συναμφότερος ὁ ΑΒ, ΔΕ συναμφοτέρου τοῦ Γ, Ζ τὰ αὐτὰ μέρη ἐστίν, ἅπερ ὁ ΑΒ τοῦ Γ.],
    [For let a number $A B$ be parts of a number $C$, and another (number) $D E$ (be) the same parts of another (number) $F$ that $A B$ (is) of $C$. I say that the sum $A B$, $D E$ is also the same parts of the sum $C$, $F$ that $A B$ (is) of $C$.],
  )
  #parallel(
    [Ἐπεὶ γάρ, ἃ μέρη ἐστὶν ὁ ΑΒ τοῦ Γ, τὰ αὐτὰ μέρη καὶ ὁ ΔΕ τοῦ Ζ, ὅσα ἄρα ἐστὶν ἐν τῷ ΑΒ μέρη τοῦ Γ, τοσαῦτά ἐστι καὶ ἐν τῷ ΔΕ μέρη τοῦ Ζ. διῃρήσθω ὁ μὲν ΑΒ εἰς τὰ τοῦ Γ μέρη τὰ ΑΗ, ΗΒ, ὁ δὲ ΔΕ εἰς τὰ τοῦ Ζ μέρη τὰ ΔΘ, ΘΕ· ἔσται δὴ ἴσον τὸ πλῆθος τῶν ΑΗ, ΗΒ τῷ πλήθει τῶν ΔΘ, ΘΕ. καὶ ἐπεί, ὃ μέρος ἐστὶν ὁ ΑΗ τοῦ Γ, τὸ αὐτὸ μέρος ἐστὶ καὶ ὁ ΔΘ τοῦ Ζ, ὃ ἄρα μέρος ἐστὶν ὁ ΑΗ τοῦ Γ, τὸ αὐτὸ μέρος ἐστὶ καὶ συναμφότερος ὁ ΑΗ, ΔΘ συναμφοτέρου τοῦ Γ, Ζ. διὰ τὰ αὐτὰ δὴ καὶ ὃ μέρος ἐστὶν ὁ ΗΒ τοῦ Γ, τὸ αὐτὸ μέρος ἐστὶ καὶ συναμφότερος ὁ ΗΒ, ΘΕ συναμφοτέρου τοῦ Γ, Ζ. ἃ ἄρα μέρη ἐστὶν ὁ ΑΒ τοῦ Γ, τὰ αὐτὰ μέρη ἐστὶ καὶ συναμφότερος ὁ ΑΒ, ΔΕ συναμφοτέρου τοῦ Γ, Ζ· ὅπερ ἔδει δεῖξαι.],
    [For since which(ever) parts $A B$ is of $C$, $D E$ (is) also the same parts of $F$, thus as many parts of $C$ as are in $A B$, so many parts of $F$ are also in $D E$. Let $A B$ be divided into the parts of $C$, $A G$ and $G B$, and $D E$ into the parts of $F$, $D H$ and $H E$. So the multitude of (divisions) $A G$, $G B$ will be equal to the multitude of (divisions) $D H$, $H E$. And since which(ever) part $A G$ is of $C$, $D H$ is also the same part of $F$, thus which(ever) part $A G$ is of $C$, the sum $A G$, $D H$ is also the same part of the sum $C$, $F$ [Prop.~7.5]. And so, for the same (reasons), which(ever) part $G B$ is of $C$, the sum $G B$, $H E$ is also the same part of the sum $C$, $F$. Thus, which(ever) parts $A B$ is of $C$, the sum $A B$, $D E$ is also the same parts of the sum $C$, $F$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book7/Prop06.lean")
