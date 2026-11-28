#import "../functions.typ": *

#content-box[
  #parallel-proposition(5)
  #parallel(
    [Ἐὰν δύο κύκλοι τέμνωσιν ἀλλήλους, οὐκ ἔσται αὐτῶν τὸ αὐτὸ κέντρον.],
    [If two circles cut one another, (then) they will not have the same center.],
  )
  #parallel-image("/Book03/fig05", 2in)
  #parallel(
    [Δύο γὰρ κύκλοι οἱ ΑΒΓ, ΓΔΗ τεμνέτωσαν ἀλλήλους κατὰ τὰ Β, Γ σημεῖα. λέγω, ὅτι οὐκ ἔσται αὐτῶν τὸ αὐτὸ κέντρον.],
    [For let the two circles $A B C$ and $C D G$ cut one another at points $B$ and $C$. I say that they will not have the same center.],
  )
  #parallel(
    [Εἰ γὰρ δυνατόν, ἔστω τὸ Ε, καὶ ἐπεζεύχθω ἡ ΕΓ, καὶ διήχθω ἡ ΕΖΗ, ὡς ἔτυχεν. καὶ ἐπεὶ τὸ Ε σημεῖον κέντρον ἐστὶ τοῦ ΑΒΓ κύκλου, ἵση ἐστὶν ἡ ΕΓ τῇ ΕΖ. πάλιν, ἐπεὶ τὸ Ε σημεῖον κέντρον ἐστὶ τοῦ ΓΔΗ κύκλου, ἴση ἐστὶν ἡ ΕΓ τῇ ΕΗ· ἐδείχθη δὲ ἡ ΕΓ καὶ τῇ ΕΖ ἴση· καὶ ἡ ΕΖ ἄρα τῇ ΕΗ ἐστιν ἴση ἡ ἐλάσσων τῇ μείζονι· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα τὸ Ε σημεῖον κέντρον ἐστὶ τῶν ΑΒΓ, ΓΔΗ κύκλων.],
    [For, if possible, let $E$ be (the common center), and let $E C$ be joined, and let $E F G$ be drawn through (the two circles), at random. And since point $E$ is the center of the circle $A B C$, $E C$ is equal to $E F$. Again, since point $E$ is the center of the circle $C D G$, $E C$ is equal to $E G$. But $E C$ was also shown (to be) equal to $E F$. Thus, $E F$ is also equal to $E G$, the lesser to the greater. The very thing is impossible. Thus, point $E$ is not the (common) center of the circles $A B C$ and $C D G$.],
  )
  #parallel(
    [Ἐὰν ἄρα δύο κύκλοι τέμνωσιν ἀλλήλους, οὐκ ἔστιν αὐτῶν τὸ αὐτὸ κέντρον· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two circles cut one another, (then) they will not have the same center. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop05.lean")
