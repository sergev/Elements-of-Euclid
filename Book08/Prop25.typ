#import "../functions.typ": *

#content-box[
  #parallel-proposition(25)
  #parallel(
    [Ἐὰν δύο ἀριθμοὶ πρὸς ἀλλήλους λόγον ἔχωσιν, ὃν κύβος ἀριθμὸς πρὸς κύβον ἀριθμόν, ὁ δὲ πρῶτος κύβος ᾖ, καὶ ὁ δεύτερος κύβος ἔσται.],
    [If two numbers have to one another the ratio which a cube number (has) to a(nother) cube number, and the first is cube, then the second will also be cube.],
  )
  #parallel-image("/Book08/fig25", 0.9in)
  #parallel(
    [Δύο γὰρ ἀριθμοὶ οἱ Α, Β πρὸς ἀλλήλους λόγον ἐχέτωσαν, ὃν κύβος ἀριθμὸς ὁ Γ πρὸς κύβον ἀριθμὸν τὸν Δ, κύβος δὲ ἔστω ὁ Α· λέγω [δή], ὅτι καὶ ὁ Β κύβος ἐστίν.],
    [For let two numbers, $A$ and $B$, have to one another the ratio which the cube number $C$ (has) to the cube number $D$. And let $A$ be cube. [So] I say that $B$ is also cube.],
  )
  #parallel(
    [Ἐπεὶ γὰρ οἱ Γ, Δ κύβοι εἰσίν, οἱ Γ, Δ ὅμοιοι στερεοί εἰσιν· τῶν Γ, Δ ἄρα δύο μέσοι ἀνάλογον ἐμπίπτουσιν ἀριθμοί. ὅσοι δὲ εἰς τοὺς Γ, Δ μεταξὺ κατὰ τὸ συνεχὲς ἀνάλογον ἐμπίπτουσιν, τοσοῦτοι καὶ εἰς τοὺς τὸν αὐτὸν λόγον ἔχοντας αὐτοῖς· ὥστε καὶ τῶν Α, Β δύο μέσοι ἀνάλογον ἐμπίπτουσιν ἀριθμοί. ἐμπιπτέτωσαν οἱ Ε, Ζ. ἐπεὶ οὖν τέσσαρες ἀριθμοὶ οἱ Α, Ε, Ζ, Β ἑξῆς ἀνάλογόν εἰσιν, καί ἐστι κύβος ὁ Α, κύβος ἄρα καὶ ὁ Β· ὅπερ ἔδει δεῖξαι.],
    [For since $C$ and $D$ are cube (numbers), $C$ and $D$ are (thus) similar solid (numbers). Thus, two numbers fall (between) $C$ and $D$ in mean proportion [Prop.~8.19]. And as many (numbers) as fall in between $C$ and $D$ in continued proportion, so many also (fall) in (between) those (numbers) having the same ratio as them (in continued proportion) [Prop.~8.8]. And hence two numbers fall (between) $A$ and $B$ in mean proportion. Let $E$ and $F$ (so) fall. Therefore, since the four numbers $A$, $E$, $F$, $B$ are continuously proportional, and $A$ is cube, $B$ (is) thus also cube [Prop.~8.23]. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book8/Prop25.lean")
