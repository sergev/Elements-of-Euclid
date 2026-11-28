#import "../functions.typ": *

#content-box[
  #parallel-proposition(2)
  #parallel(
    [Ἐὰν κύκλου ἐπὶ τῆς περιφερείας ληφθῇ δύο τυχόντα σημεῖα, ἡ ἐπὶ τὰ σημεῖα ἐπιζευγνυμένη εὐθεῖα ἐντὸς πεσεῖται τοῦ κύκλου.],
    [If two points are taken at random on the circumference of a circle, (then) the straight-line joining the points will fall inside the circle.],
  )
  #parallel(
    [Ἔστω κύκλος ὁ ΑΒΓ, καὶ ἐπὶ τῆς περιφερείας αὐτοῦ εἰλήφθω δύο τυχόντα σημεῖα τὰ Α, Β· λέγω, ὅτι ἡ ἀπὸ τοῦ Α ἐπὶ τὸ Β ἐπιζευγνυμένη εὐθεῖα ἐντὸς πεσεῖται τοῦ κύκλου.],
    [Let $A B C$ be a circle, and let two points $A$ and $B$ be taken at random on its circumference. I say that the straight-line joining $A$ to $B$ will fall inside the circle.],
  )
  #parallel(
    [μὴ γάρ, ἀλλ᾿ εἰ δυνατόν, πιπτέτω ἐκτὸς ὡς ἡ ΑΕΒ, καὶ εἰλήφθω τὸ κέντρον τοῦ ΑΒΓ κύκλου, καὶ ἔστω τὸ Δ, καὶ ἐπεζεύχθωσαν αἱ ΔΑ, ΔΒ, καὶ διήχθω ἡ ΔΖΕ.],
    [For (if) not (then), if possible, let it fall outside (the circle), like $A E B$ (in the figure). And let the center of the circle $A B C$ be found [Prop.~3.1], and let it be (at point) $D$. And let $D A$ and $D B$ be joined, and let $D F E$ be drawn through.],
  )
  #parallel(
    [Ἐπεὶ οὖν ἴση ἐστὶν ἡ ΔΑ τῇ ΔΒ, ἴση ἄρα καὶ γωνία ἡ ὑπὸ ΔΑΕ τῇ ὑπὸ ΔΒΕ· καὶ ἐπεὶ τριγώνου τοῦ ΔΑΕ μία πλευρὰ προσεκβέβληται ἡ ΑΕΒ, μείζων ἄρα ἡ ὑπὸ ΔΕΒ γωνία τῆς ὑπὸ ΔΑΕ. ἴση δὲ ἡ ὑπὸ ΔΑΕ τῇ ὑπὸ ΔΒΕ· μείζων ἄρα ἡ ὑπὸ ΔΕΒ τῆς ὑπὸ ΔΒΕ. ὑπὸ δὲ τὴν μείζονα γωνίαν ἡ μείζων πλευρὰ ὑποτείνει· μείζων ἄρα ἡ ΔΒ τῆς ΔΕ. ἴση δὲ ἡ ΔΒ τῇ ΔΖ. μείζων ἄρα ἡ ΔΖ τῆς ΔΕ ἡ ἐλάττων τῆς μείζονος· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἡ ἀπὸ τοῦ Α ἐπὶ τὸ Β ἐπιζευγνυμένη εὐθεῖα ἐκτὸς πεσεῖται τοῦ κύκλου. ὁμοίως δὴ δείξομεν, ὅτι οὐδὲ ἐπ᾿ αὐτῆς τῆς περιφερείας· ἐντὸς ἄρα.],
    [Therefore, since $D A$ is equal to $D B$, the angle $D A E$ (is) thus also equal to $D B E$ [Prop.~1.5]. And since in triangle $D A E$ the one side, $A E B$, has been produced, angle $D E B$ (is) thus greater than $D A E$ [Prop.~1.16]. And $D A E$ (is) equal to $D B E$ [Prop.~1.5]. Thus, $D E B$ (is) greater than $D B E$. And the greater angle is subtended by the greater side [Prop.~1.19]. Thus, $D B$ (is) greater than $D E$. And $D B$ (is) equal to $D F$. Thus, $D F$ (is) greater than $D E$, the lesser than the greater. The very thing is impossible. Thus, the straight-line joining $A$ to $B$ will not fall outside the circle. So, similarly, we can show that neither (will it fall) on the circumference itself. Thus, (it will fall) inside (the circle).],
  )
  #parallel-image("/Book03/fig02", 2.2in)
  #parallel(
    [Ἐὰν ἄρα κύκλου ἐπὶ τῆς περιφερείας ληφθῇ δύο τυχόντα σημεῖα, ἡ ἐπὶ τὰ σημεῖα ἐπιζευγνυμένη εὐθεῖα ἐντὸς πεσεῖται τοῦ κύκλου· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two points are taken at random on the circumference of a circle, (then) the straight-line joining the points will fall inside the circle. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop02.lean")
