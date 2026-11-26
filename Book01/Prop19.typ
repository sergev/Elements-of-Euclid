#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig19(letters) = fig({
  
})

#content-box[
  #parallel-proposition(19)
  #parallel(
    [Παντὸς τριγώνου ὑπὸ τὴν μείζονα γωνίαν ἡ μείζων πλευρὰ ὑποτείνει.],
    [In any triangle, the greater angle is subtended by the greater side.],
  )
  #parallel(
    [Ἔστω τρίγωνον τὸ ΑΒΓ μείζονα ἔχον τὴν ὑπὸ ΑΒΓ γωνίαν τῆς ὑπὸ ΒΓΑ· λέγω, ὅτι καὶ πλευρὰ ἡ ΑΓ πλευρᾶς τῆς ΑΒ μείζων ἐστίν.],
    [Let $A B C$ be a triangle having the angle $A B C$ greater than $B C A$. I say that side $A C$ is also greater than side $A B$.],
  )
  #parallel-fig(fig19)
  #parallel(
    [Εἰ γὰρ μή, ἤτοι ἴση ἐστὶν ἡ ΑΓ τῇ ΑΒ ἢ ἐλάσσων· ἴση μὲν οὖν οὐκ ἔστιν ἡ ΑΓ τῇ ΑΒ· ἴση γὰρ ἂν ἦν καὶ γωνία ἡ ὑπὸ ΑΒΓ τῇ ὑπὸ ΑΓΒ· οὐκ ἔστι δέ· οὐκ ἄρα ἴση ἐστὶν ἡ ΑΓ τῇ ΑΒ. οὐδὲ μὴν ἐλάσσων ἐστὶν ἡ ΑΓ τῆς ΑΒ· ἐλάσσων γὰρ ἂν ἦν καὶ γωνία ἡ ὑπὸ ΑΒΓ τῆς ὑπὸ ΑΓΒ· οὐκ ἔστι δέ· οὐκ ἄρα ἐλάσσων ἐστὶν ἡ ΑΓ τῆς ΑΒ. ἐδείχθη δέ, ὅτι οὐδὲ ἴση ἐστίν. μείζων ἄρα ἐστὶν ἡ ΑΓ τῆς ΑΒ.],
    [For if not, $A C$ is certainly either equal to, or less than, $A B$. In fact, $A C$ is not equal to $A B$. For then angle $A B C$ would also be equal to $A C B$ [Prop.~1.5]. But it is not. Thus, $A C$ is not equal to $A B$. Neither, indeed, is $A C$ less than $A B$. For then angle $A B C$ would also be less than $A C B$ [Prop.~1.18]. But it is not. Thus, $A C$ is not less than $A B$. But it was shown that ($A C$) is not equal (to $A B$) either. Thus, $A C$ is greater than $A B$.],
  )
  #parallel(
    [Παντὸς ἄρα τριγώνου ὑπὸ τὴν μείζονα γωνίαν ἡ μείζων πλευρὰ ὑποτείνει· ὅπερ ἔδει δεῖξαι.],
    [Thus, in any triangle, the greater angle is subtended by the greater side. (Which is) the very thing it was required to show.],
  )
]
