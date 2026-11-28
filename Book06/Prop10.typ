#import "../functions.typ": *

#content-box[
  #parallel-proposition(10)
  #parallel(
    [Τὴν δοθεῖσαν εὐθεῖαν ἄτμητον τῇ δοθείσῃ τετμημένῃ ὁμοίως τεμεῖν.],
    [To cut a given uncut straight-line similarly to a given cut (straight-line).],
  )
  #parallel(
    [Ἔστω ἡ μὲν δοθεῖσα εὐθεῖα ἅτμητος ἡ ΑΒ, ἡ δὲ τετμημένη ἡ ΑΓ κατὰ τὰ Δ, Ε σημεῖα, καὶ κείσθωσαν ὥστε γωνίαν τυχοῦσαν περιέχειν, καὶ ἐπεζεύχθω ἡ ΓΒ, καὶ διὰ τῶν Δ, Ε τῇ ΒΓ παράλληλοι ἤχθωσαν αἱ ΔΖ, ΕΗ, διὰ δὲ τοῦ Δ τῇ ΑΒ παράλληλος ἤχθω ἡ ΔΘΚ.],
    [Let $A B$ be the given uncut straight-line, and $A C$ a (straight-line) cut at points $D$ and $E$, and let ($A C$) be laid down so as to encompass a random angle (with $A B$). And let $C B$ be joined. And let $D F$ and $E G$ be drawn through (points) $D$ and $E$ (respectively), parallel to $B C$, and let $D H K$ be drawn through (point) $D$, parallel to $A B$ [Prop.~1.31].],
  )
  #parallel-image("/Book06/fig10", 2.2in)
  #parallel(
    [Παραλληλόγραμμον ἄρα ἐστὶν ἑκάτερον τῶν ΖΘ, ΘΒ· ἴση ἄρα ἡ μὲν ΔΘ τῇ ΖΗ, ἡ δὲ ΘΚ τῇ ΗΒ. καὶ ἐπεὶ τριγώνου τοῦ ΔΚΓ παρὰ μίαν τῶν πλευρῶν τὴν ΚΓ εὐθεῖα ἦκται ἡ ΘΕ, ἀνάλογον ἄρα ἐστὶν ὡς ἡ ΓΕ πρὸς τὴν ΕΔ, οὕτως ἡ ΚΘ πρὸς τὴν ΘΔ. ἴση δὲ ἡ μὲν ΚΘ τῇ ΒΗ, ἡ δὲ ΘΔ τῇ ΗΖ. ἔστιν ἄρα ὡς ἡ ΓΕ πρὸς τὴν ΕΔ, οὕτως ἡ ΒΗ πρὸς τὴν ΗΖ. πάλιν, ἐπεὶ τριγώνου τοῦ ΑΗΕ παρὰ μίαν τῶν πλευρῶν τὴν ΗΕ ἦκται ἡ ΖΔ, ἀνάλογον ἄρα ἐστὶν ὡς ἡ ΕΔ πρὸς τὴν ΔΑ, οὕτως ἡ ΗΖ πρὸς τὴν ΖΑ. ἐδείχθη δὲ καὶ ὡς ἡ ΓΕ πρὸς τὴν ΕΔ, οὕτως ἡ ΒΗ πρὸς τὴν ΗΖ· ἔστιν ἄρα ὡς μὲν ἡ ΓΕ πρὸς τὴν ΕΔ, οὕτως ἡ ΒΗ πρὸς τὴν ΗΖ, ὡς δὲ ἡ ΕΔ πρὸς τὴν ΔΑ, οὕτως ἡ ΗΖ πρὸς τὴν ΖΑ.],
    [Thus, $F H$ and $H B$ are each parallelograms. Thus, $D H$ (is) equal to $F G$, and $H K$ to $G B$ [Prop.~1.34]. And since the straight-line $H E$ has been drawn parallel to one of the sides, $K C$, of triangle $D K C$, thus, proportionally, as $C E$ is to $E D$, so $K H$ (is) to $H D$ [Prop.~6.2]. And $K H$ (is) equal to $B G$, and $H D$ to $G F$. Thus, as $C E$ is to $E D$, so $B G$ (is) to $G F$. Again, since $F D$ has been drawn parallel to one of the sides, $G E$, of triangle $A G E$, thus, proportionally, as $E D$ is to $D A$, so $G F$ (is) to $F A$ [Prop.~6.2]. And it was also shown that as $C E$ (is) to $E D$, so $B G$ (is) to $G F$. Thus, as $C E$ is to $E D$, so $B G$ (is) to $G F$, and as $E D$ (is) to $D A$, so $G F$ (is) to $F A$.],
  )
  #parallel(
    [Ἡ ἄρα δοθεῖσα εὐθεῖα ἄτμητος ἡ ΑΒ τῇ δοθείσῃ εὐθείᾳ τετμημένῃ τῇ ΑΓ ὁμοίως τέτμηται· ὅπερ ἔδει ποιῆσαι·],
    [Thus, the given uncut straight-line, $A B$, has been cut similarly to the given cut straight-line, $A C$. (Which is) the very thing it was required to do.],
  )
]
#lean-proof("/lean/Elements/Book6/Prop10.lean")
