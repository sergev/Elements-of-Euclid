#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig20(letters) = fig({
  
})

#content-box[
  #parallel-proposition(20)
  #parallel(
    [Παντὸς τριγώνου αἱ δύο πλευραὶ τῆς λοιπῆς μείζονές εἰσι πάντῃ μεταλαμβανόμεναι.],
    [In any triangle, (the sum of) two sides taken together in any (possible way) is greater than the remaining (side).],
  )
  #parallel-fig(fig20)
  #parallel(
    [Ἔστω γὰρ τρίγωνον τὸ ΑΒΓ· λέγω, ὅτι τοῦ ΑΒΓ τριγώνου αἱ δύο πλευραὶ τῆς λοιπῆς μείζονές εἰσι πάντῃ μεταλαμβανόμεναι, αἱ μὲν ΒΑ, ΑΓ τῆς ΒΓ, αἱ δὲ ΑΒ, ΒΓ τῆς ΑΓ, αἱ δὲ ΒΓ, ΓΑ τῆς ΑΒ.],
    [For let $A B C$ be a triangle. I say that in triangle $A B C$ (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). (So), (the sum of) $B A$ and $A C$ (is greater) than $B C$, (the sum of) $A B$ and $B C$ than $A C$, and (the sum of) $B C$ and $C A$ than $A B$.],
  )
  #parallel(
    [Διήχθω γὰρ ἡ ΒΑ ἐπὶ τὸ Δ σημεῖον, καὶ κείσθω τῇ ΓΑ ἴση ἡ ΑΔ, καὶ ἐπεζεύχθω ἡ ΔΓ.],
    [For let $B A$ be drawn through to point $D$, and let $A D$ be made equal to $C A$ [Prop.~1.3], and let $D C$ be joined.],
  )
  #parallel(
    [Ἐπεὶ οὖν ἴση ἐστὶν ἡ ΔΑ τῇ ΑΓ, ἴση ἐστὶ καὶ γωνία ἡ ὑπὸ ΑΔΓ τῇ ὑπὸ ΑΓΔ· μείζων ἄρα ἡ ὑπὸ ΒΓΔ τῆς ὑπὸ ΑΔΓ· καὶ ἐπεὶ τρίγωνόν ἐστι τὸ ΔΓΒ μείζονα ἔχον τὴν ὑπὸ ΒΓΔ γωνίαν τῆς ὑπὸ ΒΔΓ, ὑπὸ δὲ τὴν μείζονα γωνίαν ἡ μείζων πλευρὰ ὑποτείνει, ἡ ΔΒ ἄρα τῆς ΒΓ ἐστι μείζων. ἴση δὲ ἡ ΔΑ τῇ ΑΓ· μείζονες ἄρα αἱ ΒΑ, ΑΓ τῆς ΒΓ· ὁμοίως δὴ δείξομεν, ὅτι καὶ αἱ μὲν ΑΒ, ΒΓ τῆς ΓΑ μείζονές εἰσιν, αἱ δὲ ΒΓ, ΓΑ τῆς ΑΒ.],
    [Therefore, since $D A$ is equal to $A C$, the angle $A D C$ is also equal to $A C D$ [Prop.~1.5]. Thus, $B C D$ is greater than $A D C$. And since $D C B$ is a triangle having the angle $B C D$ greater than $B D C$, and the greater angle subtends the greater side [Prop.~1.19], $D B$ is thus greater than $B C$. But $D A$ is equal to $A C$. Thus, (the sum of) $B A$ and $A C$ is greater than $B C$. Similarly, we can show that (the sum of) $A B$ and $B C$ is also greater than $C A$, and (the sum of) $B C$ and $C A$ than $A B$.],
  )
  #parallel(
    [Παντὸς ἄρα τριγώνου αἱ δύο πλευραὶ τῆς λοιπῆς μείζονές εἰσι πάντῃ μεταλαμβανόμεναι· ὅπερ ἔδει δεῖξαι.],
    [Thus, in any triangle, (the sum of) two sides taken together in any (possible way) is greater than the remaining (side). (Which is) the very thing it was required to show.],
  )
]
