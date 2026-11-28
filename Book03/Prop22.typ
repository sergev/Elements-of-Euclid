#import "../functions.typ": *

#content-box[
  #parallel-proposition(22)
  #parallel(
    [Τῶν ἐν τοῖς κύκλοις τετραπλεύρων αἱ ἀπεναντίον γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν.],
    [For quadrilaterals within circles, the (sum of the) opposite angles is equal to two right-angles.],
  )
  #parallel-image("/Book03/fig22", 2.2in)
  #parallel(
    [Ἔστω κύκλος ὁ ΑΒΓΔ, καὶ ἐν αὐτῷ τετράπλευρον ἔστω τὸ ΑΒΓΔ· λέγω, ὅτι αἱ ἀπεναντίον γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν.],
    [Let $A B C D$ be a circle, and let $A B C D$ be a quadrilateral within it. I say that the (sum of the) opposite angles is equal to two right-angles.],
  )
  #parallel(
    [Ἐπεζεύχθωσαν αἱ ΑΓ, ΒΔ.],
    [Let $A C$ and $B D$ be joined.],
  )
  #parallel(
    [Ἐπεὶ οὖν παντὸς τριγώνου αἱ τρεῖς γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν, τοῦ ΑΒΓ ἄρα τριγώνου αἱ τρεῖς γωνίαι αἱ ὑπὸ ΓΑΒ, ΑΒΓ, ΒΓΑ δυσὶν ὀρθαῖς ἴσαι εἰσίν. ἴση δὲ ἡ μὲν ὑπὸ ΓΑΒ τῇ ὑπὸ ΒΔΓ· ἐν γὰρ τῷ αὐτῷ τμήματί εἰσι τῷ ΒΑΔΓ· ἡ δὲ ὑπὸ ΑΓΒ τῇ ὑπὸ ΑΔΒ· ἐν γὰρ τῷ αὐτῷ τμήματί εἰσι τῷ ΑΔΓΒ· ὅλη ἄρα ἡ ὑπὸ ΑΔΓ ταῖς ὑπὸ ΒΑΓ, ΑΓΒ ἴση ἐστίν. κοινὴ προσκείσθω ἡ ὑπὸ ΑΒΓ· αἱ ἄρα ὑπὸ ΑΒΓ, ΒΑΓ, ΑΓΒ ταῖς ὑπὸ ΑΒΓ, ΑΔΓ ἴσαι εἰσίν. ἀλλ᾿ αἱ ὑπὸ ΑΒΓ, ΒΑΓ, ΑΓΒ δυσὶν ὀρθαῖς ἴσαι εἰσίν. καὶ αἱ ὑπὸ ΑΒΓ, ΑΔΓ ἄρα δυσὶν ὀρθαῖς ἴσαι εἰσίν. ὁμοίως δὴ δείξομεν, ὅτι καὶ αἱ ὑπὸ ΒΑΔ, ΔΓΒ γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν.],
    [Therefore, since the three angles of any triangle are equal to two right-angles [Prop.~1.32], the three angles $C A B$, $A B C$, and $B C A$ of triangle $A B C$ are thus equal to two right-angles. And $C A B$ (is) equal to $B D C$. For they are in the same segment $B A D C$ [Prop.~3.21]. And $A C B$ (is equal) to $A D B$. For they are in the same segment $A D C B$ [Prop.~3.21]. Thus, the whole of $A D C$ is equal to $B A C$ and $A C B$. Let $A B C$ be added to both. Thus, $A B C$, $B A C$, and $A C B$ are equal to $A B C$ and $A D C$. But, $A B C$, $B A C$, and $A C B$ are equal to two right-angles. Thus, $A B C$ and $A D C$ are also equal to two right-angles. Similarly, we can show that angles $B A D$ and $D C B$ are also equal to two right-angles.],
  )
  #parallel(
    [Τῶν ἄρα ἐν τοῖς κύκλοις τετραπλεύρων αἱ ἀπεναντίον γωνίαι δυσὶν ὀρθαῖς ἴσαι εἰσίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, for quadrilaterals within circles, the (sum of the) opposite angles is equal to two right-angles. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop22.lean")
