#import "../functions.typ": *

#content-box[
  #parallel-proposition(12)
  #parallel(
    [Τριῶν δοθεισῶν εὐθειῶν τετάρτην ἀνάλογον προσευρεῖν.],
    [To find a fourth (straight-line) proportional to three given straight-lines.],
  )
  #parallel-image("/Book06/fig12", 2.2in)
  #parallel(
    [Ἔστωσαν αἱ δοθεῖσαι τρεῖς εὐθεῖαι αἱ Α, Β, Γ· δεῖ δὴ τῶν Α, Β, Γ τετράτην ἀνάλογον προσευρεῖν.],
    [Let $A$, $B$, and $C$ be the three given straight-lines. So it is required to find a fourth (straight-line) proportional to $A$, $B$, and $C$.],
  )
  #parallel(
    [Ἐκκείσθωσαν δύο εὐθεῖαι αἱ ΔΕ, ΔΖ γωνίαν περιέχουσαι [τυχοῦσαν] τὴν ὑπὸ ΕΔΖ· καὶ κείσθω τῇ μὲν Α ἴση ἡ ΔΗ, τῇ δὲ Β ἴση ἡ ΗΕ, καὶ ἔτι τῇ Γ ἴση ἡ ΔΘ· καὶ ἐπιζευχθείσης τῆς ΗΘ παράλληλος αὐτῇ ἤχθω διὰ τοῦ Ε ἡ ΕΖ.],
    [Let the two straight-lines $D E$ and $D F$ be set out encompassing the [random] angle $E D F$. And let $D G$ be made equal to $A$, and $G E$ to $B$, and, further, $D H$ to $C$ [Prop.~1.3]. And $G H$ being joined, let $E F$ be drawn through (point) $E$ parallel to it [Prop.~1.31].],
  )
  #parallel(
    [Ἐπεὶ οὖν τριγώνου τοῦ ΔΕΖ παρὰ μίαν τὴν ΕΖ ἦκται ἡ ΗΘ, ἔστιν ἄρα ὡς ἡ ΔΗ πρὸς τὴν ΗΕ, οὕτως ἡ ΔΘ πρὸς τὴν ΘΖ. ἴση δὲ ἡ μὲν ΔΗ τῇ Α, ἡ δὲ ΗΕ τῇ Β, ἡ δὲ ΔΘ τῇ Γ· ἔστιν ἄρα ὡς ἡ Α πρὸς τὴν Β, οὕτως ἡ Γ πρὸς τὴν ΘΖ.],
    [Therefore, since $G H$ has been drawn parallel to one of the sides $E F$ of triangle $D E F$, thus as $D G$ is to $G E$, so $D H$ (is) to $H F$ [Prop.~6.2]. And $D G$ (is) equal to $A$, and $G E$ to $B$, and $D H$ to $C$. Thus, as $A$ is to $B$, so $C$ (is) to $H F$.],
  )
  #parallel(
    [Τριῶν ἄρα δοθεισῶν εὐθειῶν τῶν Α, Β, Γ τετάρτη ἀνάλογον προσεύρηται ἡ ΘΖ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, a fourth (straight-line), $H F$, has been found (which is) proportional to the three given straight-lines, $A$, $B$, and $C$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book6/Prop12.lean")
