#import "../functions.typ": *

#content-box[
  #parallel-proposition(12)
  #parallel(
    [Ἐὰν δύο κύκλοι ἐφάπτωνται ἀλλήλων ἐκτός, ἡ ἐπὶ τὰ κέντρα αὐτῶν ἐπιζευγνυμένη διὰ τῆς ἐπαφῆς ἐλεύσεται.],
    [If two circles touch one another externally, (then) the (straight-line) joining their centers will go through the point of union.],
  )
  #parallel-image("/Book03/fig12", 2.5in)
  #parallel(
    [Δύο γὰρ κύκλοι οἱ ΑΒΓ, ΑΔΕ ἐφαπτέσθωσαν ἀλλήλων ἐκτὸς κατὰ τὸ Α σημεῖον, καὶ εἰλήφθω τοῦ μὲν ΑΒΓ κέντρον τὸ Ζ, τοῦ δὲ ΑΔΕ τὸ Η· λέγω, ὅτι ἡ ἀπὸ τοῦ Ζ ἐπὶ τὸ Η ἐπιζευγνυμένη εὐθεῖα διὰ τῆς κατὰ τὸ Α ἐπαφῆς ἐλεύσεται.],
    [For let two circles, $A B C$ and $A D E$, touch one another externally at point $A$, and let the center $F$ of $A B C$ be found [Prop.~3.1], and (the center) $G$ of $A D E$ [Prop.~3.1]. I say that the straight-line joining $F$ to $G$ will go through the point of union at $A$.],
  )
  #parallel(
    [μὴ γάρ, ἀλλ᾿ εἰ δυνατόν, ἐρχέσθω ὡς ἡ ΖΓΔΗ, καὶ ἐπεζεύχθωσαν αἱ ΑΖ, ΑΗ.],
    [For (if) not (then), if possible, let it go like $F C D G$ (in the figure), and let $A F$ and $A G$ be joined.],
  )
  #parallel(
    [Ἐπεὶ οὖν τὸ Ζ σημεῖον κέντρον ἐστὶ τοῦ ΑΒΓ κύκλου, ἴση ἐστὶν ἡ ΖΑ τῇ ΖΓ. πάλιν, ἐπεὶ τὸ Η σημεῖον κέντρον ἐστὶ τοῦ ΑΔΕ κύκλου, ἴση ἐστὶν ἡ ΗΑ τῇ ΗΔ. ἐδείχθη δὲ καὶ ἡ ΖΑ τῇ ΖΓ ἴση· αἱ ἄρα ΖΑ, ΑΗ ταῖς ΖΓ, ΗΔ ἴσαι εἰσίν· ὥστε ὅλη ἡ ΖΗ τῶν ΖΑ, ΑΗ μείζων ἐστίν· ἀλλὰ καὶ ἐλάττων· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἡ ἀπὸ τοῦ Ζ ἐπὶ τὸ Η ἐπιζευγνυμένη εὐθεῖα διὰ τῆς κατὰ τὸ Α ἐπαφῆς οὐκ ἐλεύσεται· δι᾿ αὐτῆς ἄρα.],
    [Therefore, since point $F$ is the center of circle $A B C$, $F A$ is equal to $F C$. Again, since point $G$ is the center of circle $A D E$, $G A$ is equal to $G D$. And $F A$ was also shown (to be) equal to $F C$. Thus, the (straight-lines) $F A$ and $A G$ are equal to the (straight-lines) $F C$ and $G D$. So the whole of $F G$ is greater than $F A$ and $A G$. But, (it is) also less [Prop.~1.20]. The very thing is impossible. Thus, the straight-line joining $F$ to $G$ cannot not go through the point of union at $A$. Thus, (it will go) through it.],
  )
  #parallel(
    [Ἐὰν ἄρα δύο κύκλοι ἐφάπτωνται ἀλλήλων ἐκτός, ἡ ἐπὶ τὰ κέντρα αὐτῶν ἐπιζευγνυμένη [εὐθεῖα] διὰ τῆς ἐπαφῆς ἐλεύσεται· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two circles touch one another externally, (then) the [straight-line] joining their centers will go through the point of union. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop12.lean")
