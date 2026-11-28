#import "../functions.typ": *

#content-box[
  #parallel-proposition(11)
  #parallel(
    [Δύο δοθεισῶν εὐθειῶν τρίτην ἀνάλογον προσευρεῖν.],
    [To find a third (straight-line) proportional to two given straight-lines.],
  )
  #parallel(
    [Ἔστωσαν αἱ δοθεῖσαι [δύο εὐθεῖαι] αἱ ΒΑ, ΑΓ καὶ κείσθωσαν γωνίαν περιέχουσαι τυχοῦσαν. δεῖ δὴ τῶν ΒΑ, ΑΓ τρίτην ἀνάλογον προσευρεῖν. ἐκβεβλήσθωσαν γὰρ ἐπὶ τὰ Δ, Ε σημεῖα, καὶ κείσθω τῇ ΑΓ ἴση ἡ ΒΔ, καὶ ἐπεζεύχθω ἡ ΒΓ, καὶ διὰ τοῦ Δ παράλληλος αὐτῇ ἤχθω ἡ ΔΕ.],
    [Let $B A$ and $A C$ be the [two] given [straight-lines], and let them be laid down encompassing a random angle. So it is required to find a third (straight-line) proportional to $B A$ and $A C$. For let ($B A$ and $A C$) be produced to points $D$ and $E$ (respectively), and let $B D$ be made equal to $A C$ [Prop.~1.3]. And let $B C$ be joined. And let $D E$ be drawn through (point) $D$ parallel to it [Prop.~1.31].],
  )
  #parallel-image("/Book06/fig11", 2.5in)
  #parallel(
    [Ἐπεὶ οὖν τριγώνου τοῦ ΑΔΕ παρὰ μίαν τῶν πλευρῶν τὴν ΔΕ ἦκται ἡ ΒΓ, ἀνάλογόν ἐστιν ὡς ἡ ΑΒ πρὸς τὴν ΒΔ, οὕτως ἡ ΑΓ πρὸς τὴν ΓΕ. ἴση δὲ ἡ ΒΔ τῇ ΑΓ. ἔστιν ἄρα ὡς ἡ ΑΒ πρὸς τὴν ΑΓ, οὕτως ἡ ΑΓ πρὸς τὴν ΓΕ.],
    [Therefore, since $B C$ has been drawn parallel to one of the sides $D E$ of triangle $A D E$, proportionally, as $A B$ is to $B D$, so $A C$ (is) to $C E$ [Prop.~6.2]. And $B D$ (is) equal to $A C$. Thus, as $A B$ is to $A C$, so $A C$ (is) to $C E$.],
  )
  #parallel(
    [Δύο ἄρα δοθεισῶν εὐθειῶν τῶν ΑΒ, ΑΓ τρίτη ἀνάλογον αὐταῖς προσεύρηται ἡ ΓΕ· ὅπερ ἔδει ποιῆσαι.],
    [Thus, a third (straight-line), $C E$, has been found (which is) proportional to the two given straight-lines, $A B$ and $A C$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book6/Prop11.lean")
