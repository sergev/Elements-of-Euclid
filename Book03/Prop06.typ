#import "../functions.typ": *

#content-box[
  #parallel-proposition(6)
  #parallel(
    [Ἐὰν δύο κύκλοι ἐφάπτωνται ἀλλήλων, οὐκ ἔσται αὐτῶν τὸ αὐτὸ κέντρον.],
    [If two circles touch one another, (then) they will not have the same center.],
  )
  #parallel(
    [Δύο γὰρ κύκλοι οἱ ΑΒΓ, ΓΔΕ ἐφαπτέσθωσαν ἀλλήλων κατὰ τὸ Γ σημεῖον· λέγω, ὅτι οὐκ ἔσται αὐτῶν τὸ αὐτὸ κέντρον.],
    [For let the two circles $A B C$ and $C D E$ touch one another at point $C$. I say that they will not have the same center.],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν, ἔστω τὸ Ζ, καὶ ἐπεζεύχθω ἡ ΖΓ, καὶ διήχθω, ὡς ἔτυχεν, ἡ ΖΕΒ.],
    [For, if possible, let $F$ be (the common center), and let $F C$ be joined, and let $F E B$ be drawn through (the two circles), at random.],
  )
  #parallel(
    [Ἐπεὶ οὖν τὸ Ζ σημεῖον κέντρον ἐστὶ τοῦ ΑΒΓ κύκλου, ἴση ἐστὶν ἡ ΖΓ τῇ ΖΒ. πάλιν, ἐπεὶ τὸ Ζ σημεῖον κέντρον ἐστὶ τοῦ ΓΔΕ κύκλου, ἴση ἐστὶν ἡ ΖΓ τῇ ΖΕ. ἐδείχθη δὲ ἡ ΖΓ τῇ ΖΒ ἴση· καὶ ἡ ΖΕ ἄρα τῇ ΖΒ ἐστιν ἴση, ἡ ἐλάττων τῇ μείζονι· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα τὸ Ζ σημεῖον κέντρον ἐστὶ τῶν ΑΒΓ, ΓΔΕ κύκλων.],
    [Therefore, since point $F$ is the center of the circle $A B C$, $F C$ is equal to $F B$. Again, since point $F$ is the center of the circle $C D E$, $F C$ is equal to $F E$. But $F C$ was shown (to be) equal to $F B$. Thus, $F E$ is also equal to $F B$, the lesser to the greater. The very thing is impossible. Thus, point $F$ is not the (common) center of the circles $A B C$ and $C D E$.],
  )
  #parallel-image("/Book03/fig06", 2.2in)
  #parallel(
    [Ἐὰν ἄρα δύο κύκλοι ἐφάπτωνται ἀλλήλων, οὐκ ἔσται αὐτῶν τὸ αὐτὸ κέντρον· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two circles touch one another, (then) they will not have the same center. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop06.lean")
