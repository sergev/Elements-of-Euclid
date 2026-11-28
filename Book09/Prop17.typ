#import "../functions.typ": *

#content-box[
  #parallel-proposition(17)
  #parallel(
    [Ἐὰν ὦσιν ὁσοιδηποτοῦν ἀριθμοὶ ἑξῆς ἀνάλογον, οἱ δὲ ἄκροι αὐτῶν πρῶτοι πρὸς ἀλλήλους ὦσιν, οὐκ ἔσται ὡς ὁ πρῶτος πρὸς τὸν δεύτερον, οὕτως ὁ ἔσχατος πρὸς ἄλλον τινά.],
    [If any multitude whatsoever of numbers is continuously proportional, and the outermost of them are prime to one another, then as the first (is) to the second, so the last will not be to some other (number).],
  )
  #parallel(
    [Ἔστωσαν ὁσοιδηποτοῦν ἀριθμοὶ ἑξῆς ἀνάλογον οἱ Α, Β, Γ, Δ, οἱ δὲ ἄκροι αὐτῶν οἱ Α, Δ πρῶτοι πρὸς ἀλλήλους ἔστωσαν· λέγω, ὅτι οὐκ ἔστιν ὡς ὁ Α πρὸς τὸν Β, οὕτως ὁ Δ πρὸς ἄλλον τινά.],
    [Let $A$, $B$, $C$, $D$ be any multitude whatsoever of continuously proportional numbers. And let the outermost of them, $A$ and $D$, be prime to one another. I say that as $A$ is to $B$, so $D$ (is) not to some other (number).],
  )
  #parallel-image("/Book09/fig17", 1.3in)
  #parallel(
    [Εἰ γὰρ δυνατόν, ἔστω ὡς ὁ Α πρὸς τὸν Β, οὕτως ὁ Δ πρὸς τὸν Ε· ἐναλλὰξ ἄρα ἐστὶν ὡς ὁ Α πρὸς τὸν Δ, ὁ Β πρὸς τὸν Ε. οἱ δὲ Α, Δ πρῶτοι, οἱ δὲ πρῶτοι καὶ ἐλάχιστοι, οἱ δὲ ἐλάχιστοι ἀριθμοὶ μετροῦσι τοὺς τὸν αὐτὸν λόγον ἔχοντας ἰσάκις ὅ τε ἡγούμενος τὸν ἡγούμενον καὶ ὁ ἑπόμενος τὸν ἑπόμενον. μετρεῖ ἄρα ὁ Α τὸν Β. καί ἐστιν ὡς ὁ Α πρὸς τὸν Β, ὁ Β πρὸς τὸν Γ. καὶ ὁ Β ἄρα τὸν Γ μετρεῖ'· ὥστε καὶ ὁ Α τὸν Γ μετρεῖ. καὶ ἐπεί ἐστιν ὡς ὁ Β πρὸς τὸν Γ, ὁ Γ πρὸς τὸν Δ, μετρεῖ δὲ ὁ Β τὸν Γ, μετρεῖ ἄρα καὶ ὁ Γ τὸν Δ. ἀλλ᾿ ὁ Α τὸν Γ ἐμέτρει· ὥστε ὁ Α καὶ τὸν Δ μετρεῖ. μετρεῖ δὲ καὶ ἑαυτόν. ὁ Α ἄρα τοὺς Α, Δ μετρεῖ πρώτους ὄντας πρὸς ἀλλήλους· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἔσται ὡς ὁ Α πρὸς τὸν Β, οὕτως ὁ Δ πρὸς ἄλλον τινά· ὅπερ ἔδει δεῖξαι.],
    [For, if possible, let it be that as $A$ (is) to $B$, so $D$ (is) to $E$. Thus, alternately, as $A$ is to $D$, (so) $B$ (is) to $E$ [Prop.~7.13]. And $A$ and $D$ are prime (to one another). And (numbers) prime (to one another are) also the least (of those numbers having the same ratio as them) [Prop.~7.21]. And the least numbers measure those (numbers) having the same ratio (as them) an equal number of times, the leading (measuring) the leading, and the following the following [Prop.~7.20]. Thus, $A$ measures $B$. And as $A$ is to $B$, (so) $B$ (is) to $C$. Thus, $B$ also measures $C$. And hence $A$ measures $C$ [Def.~7.20]. And since as $B$ is to $C$, (so) $C$ (is) to $D$, and $B$ measures $C$, $C$ thus also measures $D$ [Def.~7.20]. But, $A$ was (found to be) measuring $C$. And hence $A$ also measures $D$. And ($A$) also measures itself. Thus, $A$ measures $A$ and $D$, which are prime to one another. The very thing is impossible. Thus, as $A$ (is) to $B$, so $D$ cannot be to some other (number). (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop17.lean")
