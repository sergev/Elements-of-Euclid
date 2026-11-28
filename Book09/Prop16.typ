#import "../functions.typ": *

#content-box[
  #parallel-proposition(16)
  #parallel(
    [Ἐὰν δύο ἀριθμοὶ πρῶτοι πρὸς ἀλλήλους ὦσιν, οὐκ ἔσται ὡς ὁ πρῶτος πρὸς τὸν δεύτερον, οὕτως ὁ δεύτερος πρὸς ἄλλον τινά.],
    [If two numbers are prime to one another then as the first is to the second, so the second (will) not (be) to some other (number).],
  )
  #parallel-image("/Book09/fig16", 0.9in)
  #parallel(
    [Δύο γὰρ ἀριθμοὶ οἱ Α, Β πρῶτοι πρὸς ἀλλήλους ἔστωσαν· λέγω, ὅτι οὐκ ἔστιν ὡς ὁ Α πρὸς τὸν Β, οὕτως ὁ Β πρὸς ἄλλον τινά.],
    [For let the two numbers $A$ and $B$ be prime to one another. I say that as $A$ is to $B$, so $B$ is not to some other (number).],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν, ἔστω ὡς ὁ Α πρὸς τὸν Β, ὁ Β πρὸς τὸν Γ. οἱ δὲ Α, Β πρῶτοι, οἱ δὲ πρῶτοι καὶ ἐλάχιστοι, οἱ δὲ ἐλάχιστοι ἀριθμοὶ μετροῦσι τοὺς τὸν αὐτὸν λόγον ἔχοντας ἰσάκις ὅ τε ἡγούμενος τὸν ἡγούμενον καὶ ὁ ἑπόμενος τὸν ἑπόμενον· μετρεῖ ἄρα ὁ Α τὸν Β ὡς ἡγούμενος ἡγούμενον. μετρεῖ δὲ καὶ ἑαυτόν· ὁ Α ἄρα τοὺς Α, Β μετρεῖ πρώτους ὄντας πρὸς ἀλλήλους· ὅπερ ἄτοπον. οὐκ ἄρα ἔσται ὡς ὁ Α πρὸς τὸν Β, οὕτως ὁ Β πρὸς τὸν Γ· ὅπερ ἔδει δεῖξαι.],
    [For, if possible, let it be that as $A$ (is) to $B$, (so) $B$ (is) to $C$. And $A$ and $B$ (are) prime (to one another). And (numbers) prime (to one another are) also the least (of those numbers having the same ratio as them) [Prop.~7.21]. And the least numbers measure those (numbers) having the same ratio (as them) an equal number of times, the leading (measuring) the leading, and the following the following [Prop.~7.20]. Thus, $A$ measures $B$, as the leading (measuring) the leading. And ($A$) also measures itself. Thus, $A$ measures $A$ and $B$, which are prime to one another. The very thing (is) absurd. Thus, as $A$ (is) to $B$, so $B$ cannot be to $C$. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book9/Prop16.lean")
