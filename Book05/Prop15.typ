#import "../functions.typ": *

#content-box[
  #parallel-proposition(15, note: [In modern notation, this proposition reads that $alpha : beta ::m thin alpha :m thin beta$.])
  #parallel(
    [Τὰ μέρη τοῖς ὡσαύτως πολλαπλασίοις τὸν αὐτὸν ἔχει λόγον ληφθέντα κατάλληλα.],
    [Parts have the same ratio as similar multiples, taken in corresponding order.],
  )
  #parallel-image("/Book05/fig15", 0.8in)
  #parallel(
    [Ἔστω γὰρ ἰσάκις πολλαπλάσιον τὸ ΑΒ τοῦ Γ καὶ το ΔΕ τοῦ Ζ· λέγω, ὅτι ἐστὶν ὡς τὸ Γ πρὸς τὸ Ζ, οὕτως τὸ ΑΒ πρὸς τὸ ΔΕ.],
    [For let $A B$ and $D E$ be equal multiples of $C$ and $F$ (respectively). I say that as $C$ is to $F$, so $A B$ (is) to $D E$.],
  )
  #parallel(
    [Ἐπεὶ γὰρ ἰσάκις ἐστὶ πολλαπλάσιον τὸ ΑΒ τοῦ Γ καὶ τὸ ΔΕ τοῦ Ζ, ὅσα ἄρα ἐστὶν ἐν τῷ ΑΒ μεγέθη ἴσα τῷ Γ, τοσαῦτα καὶ ἐν τῷ ΔΕ ἴσα τῷ Ζ. διῃρήσθω τὸ μὲν ΑΒ εἰς τὰ τῷ Γ ἴσα τὰ ΑΗ, ΗΘ, ΘΒ, τὸ δὲ ΔΕ εἰς τὰ τῷ Ζ ἴσα τὰ ΔΚ, ΚΛ, ΛΕ· ἔσται δὴ ἴσον τὸ πλῆθος τῶν ΑΗ, ΗΘ, ΘΒ τῷ πλήθει τῶν ΔΚ, ΚΛ, ΛΕ. καὶ ἐπεὶ ἴσα ἐστὶ τὰ ΑΗ, ΗΘ, ΘΒ ἀλλήλοις, ἔστι δὲ καὶ τὰ ΔΚ, ΚΛ, ΛΕ ἴσα ἀλλήλοις, ἔστιν ἄρα ὡς τὸ ΑΗ πρὸς τὸ ΔΚ, οὕτως τὸ ΗΘ πρὸς τὸ ΚΛ, καὶ τὸ ΘΒ πρὸς τὸ ΛΕ. ἔσται ἄρα καὶ ὡς ἓν τῶν ἡγουμένων πρὸς ἓν τῶν ἑπομένων, οὕτως ἅπαντα τὰ ἡγουμένα πρὸς ἅπαντα τὰ ἑπόμενα· ἔστιν ἄρα ὡς τὸ ΑΗ πρὸς τὸ ΔΚ, οὕτως τὸ ΑΒ πρὸς τὸ ΔΕ. ἴσον δὲ τὸ μὲν ΑΗ τῷ Γ, τὸ δὲ ΔΚ τῷ Ζ· ἔστιν ἄρα ὡς τὸ Γ πρὸς τὸ Ζ οὕτως τὸ ΑΒ πρὸς τὸ ΔΕ.],
    [For since $A B$ and $D E$ are equal multiples of $C$ and $F$ (respectively), thus as many magnitudes as there are in $A B$ equal to $C$, so many (are there) also in $D E$ equal to $F$. Let $A B$ be divided into (magnitudes) $A G$, $G H$, $H B$, equal to $C$, and $D E$ into (magnitudes) $D K$, $K L$, $L E$, equal to $F$. So, the number of (magnitudes) $A G$, $G H$, $H B$ will equal the number of (magnitudes) $D K$, $K L$, $L E$. And since $A G$, $G H$, $H B$ are equal to one another, and $D K$, $K L$, $L E$ are also equal to one another, thus as $A G$ is to $D K$, so $G H$ (is) to $K L$, and $H B$ to $L E$ [Prop.~5.7]. And, thus (for proportional magnitudes), as one of the leading (magnitudes) will be to one of the following, so all of the leading (magnitudes will be) to all of the following [Prop.~5.12]. Thus, as $A G$ is to $D K$, so $A B$ (is) to $D E$. And $A G$ is equal to $C$, and $D K$ to $F$. Thus, as $C$ is to $F$, so $A B$ (is) to $D E$.],
  )
  #parallel(
    [Τὰ ἄρα μέρη τοῖς ὡσαύτως πολλαπλασίοις τὸν αὐτὸν ἔχει λόγον ληφθέντα κατάλληλα· ὅπερ ἔδει δεῖξαι.],
    [Thus, parts have the same ratio as similar multiples, taken in corresponding order. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book5/Prop15.lean")
