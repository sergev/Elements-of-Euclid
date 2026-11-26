#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig18(letters) = fig({
  
})

#content-box[
  #parallel-proposition(18)
  #parallel(
    [Παντὸς τριγώνου ἡ μείζων πλευρὰ τὴν μείζονα γωνίαν ὑποτείνει.],
    [In any triangle, the greater side subtends the greater angle.],
  )
  #parallel(
    [Ἔστω γὰρ τρίγωνον τὸ ΑΒΓ μείζονα ἔχον τὴν ΑΓ πλευρὰν τῆς ΑΒ· λέγω, ὅτι καὶ γωνία ἡ ὑπὸ ΑΒΓ μείζων ἐστὶ τῆς ὑπὸ ΒΓΑ.],
    [For let $A B C$ be a triangle having side $A C$ greater than $A B$. I say that angle $A B C$ is also greater than $B C A$.],
  )
  #parallel-fig(fig18)
  #parallel(
    [Ἐπεὶ γὰρ μείζων ἐστὶν ἡ ΑΓ τῆς ΑΒ, κείσθω τῇ ΑΒ ἴση ἡ ΑΔ, καὶ ἐπεζεύχθω ἡ ΒΔ.],
    [For since $A C$ is greater than $A B$, let $A D$ be made equal to $A B$ [Prop.~1.3], and let $B D$ be joined.],
  )
  #parallel(
    [Καὶ ἐπεὶ τριγώνου τοῦ ΒΓΔ ἐκτός ἐστι γωνία ἡ ὑπὸ ΑΔΒ, μείζων ἐστὶ τῆς ἐντὸς καὶ ἀπεναντίον τῆς ὑπὸ ΔΓΒ· ἴση δὲ ἡ ὑπὸ ΑΔΒ τῇ ὑπὸ ΑΒΔ, ἐπεὶ καὶ πλευρὰ ἡ ΑΒ τῇ ΑΔ ἐστιν ἴση· μείζων ἄρα καὶ ἡ ὑπὸ ΑΒΔ τῆς ὑπὸ ΑΓΒ· πολλῷ ἄρα ἡ ὑπὸ ΑΒΓ μείζων ἐστὶ τῆς ὑπὸ ΑΓΒ.],
    [And since angle $A D B$ is external to triangle $B C D$, it is greater than the internal and opposite (angle) $D C B$ [Prop.~1.16]. But $A D B$ (is) equal to $A B D$, since side $A B$ is also equal to side $A D$ [Prop.~1.5]. Thus, $A B D$ is also greater than $A C B$. Thus, $A B C$ is much greater than $A C B$.],
  )
  #parallel(
    [Παντὸς ἄρα τριγώνου ἡ μείζων πλευρὰ τὴν μείζονα γωνίαν ὑποτείνει· ὅπερ ἔδει δεῖξαι.],
    [Thus, in any triangle, the greater side subtends the greater angle. (Which is) the very thing it was required to show.],
  )
]
