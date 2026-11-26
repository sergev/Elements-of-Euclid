#import "../functions.typ": *
#import "@preview/cetz:0.4.2"

#let fig25(letters) = fig({
  
})

#content-box[
  #parallel-proposition(25)
  #parallel(
    [᾿Εὰν δύο τρίγωνα τὰς δύο πλευρὰς δυσὶ πλευραῖς ἴσας ἔχῃ ἑκατέραν ἑκατέρᾳ, τὴν δὲ βάσιν τῆς βάσεως μείζονα ἔχῃ, καὶ τὴν γωνίαν τῆς γωνίας μείζονα ἕξει τὴν ὑπὸ τῶν ἴσων εὐθειῶν περιεχομένην.],
    [If two triangles have two sides equal to two sides, respectively, but (one) has a base greater than the base (of the other), (then the former triangle) will also have the angle encompassed by the equal straight-lines greater than the (corresponding) angle (in the latter).],
  )
  #parallel(
    [῎Εστω δύο τρίγωνα τὰ ΑΒΓ, ΔΕΖ τὰς δύο πλευρὰς τὰς ΑΒ, ΑΓ ταῖς δύο πλευραῖς ταῖς ΔΕ, ΔΖ ἴσας ἔχοντα ἑκατέραν ἑκατέρᾳ, τὴν μὲν ΑΒ τῇ ΔΕ, τὴν δὲ ΑΓ τῇ ΔΖ· βάσις δὲ ἡ ΒΓ βάσεως τῆς ΕΖ μείζων ἔστω· λέγω, ὅτι καὶ γωνία ἡ ὑπὸ ΒΑΓ γωνίας τῆς ὑπὸ ΕΔΖ μείζων ἐστίν.],
    [Let $A B C$ and $D E F$ be two triangles having the two sides $A B$ and $A C$ equal to the two sides $D E$ and $D F$, respectively. (That is), $A B$ (equal) to $D E$, and $A C$ to $D F$. And let the base $B C$ be greater than the base $E F$. I say that angle $B A C$ is also greater than $E D F$.],
  )
  #parallel(
    [Εἰ γὰρ μή, ἤτοι ἴση ἐστὶν αὐτῇ ἢ ἐλάσσων· ἴση μὲν ο᾿ῦν οὐκ ἔστιν ἡ ὑπὸ ΒΑΓ τῇ ὑπὸ ΕΔΖ· ἴση γὰρ ἂν ᾿ῆν καὶ βάσις ἡ ΒΓ βάσει τῇ ΕΖ· οὐκ ἔστι δέ. οὐκ ἄρα ἴση ἐστὶ γωνία ἡ ὑπὸ ΒΑΓ τῇ ὑπὸ ΕΔΖ· οὐδὲ μὴν ἐλάσσων ἐστὶν ἡ ὑπὸ ΒΑΓ τῆς ὑπὸ ΕΔΖ· ἐλάσσων γὰρ ἂν ᾿ῆν καὶ βάσις ἡ ΒΓ βάσεως τῆς ΕΖ· οὐκ ἔστι δέ· οὐκ ἄρα ἐλάσσων ἐστὶν ἡ ὑπὸ ΒΑΓ γωνία τῆς ὑπὸ ΕΔΖ. ἐδείχθη δέ, ὅτι οὐδὲ ἴση· μείζων ἄρα ἐστὶν ἡ ὑπὸ ΒΑΓ τῆς ὑπὸ ΕΔΖ.],
    [For if not, ($B A C$) is certainly either equal to, or less than, ($E D F$). In fact, $B A C$ is not equal to $E D F$. For then the base $B C$ would also be equal to the base $E F$ [Prop. 1.4]. But it is not. Thus, angle $B A C$ is not equal to $E D F$. Neither, indeed, is $B A C$ less than $E D F$. For then the base $B C$ would also be less than the base $E F$ [Prop. 1.24]. But it is not. Thus, angle $B A C$ is not less than $E D F$. But it was shown that ($B A C$ is) not equal (to $E D F$) either. Thus, $B A C$ is greater than $E D F$.],
  )
  #parallel-fig(fig25)
  #parallel(
    [᾿Εὰν ἄρα δύο τρίγωνα τὰς δύο πλευρὰς δυσὶ πλευραῖς ἴσας ἔχῃ ἑκατέραν ἑκάτερᾳ, τὴν δὲ βασίν τῆς βάσεως μείζονα ἔχῃ, καὶ τὴν γωνίαν τῆς γωνίας μείζονα ἕξει τὴν ὑπὸ τῶν ἴσων εὐθειῶν περιεχομένην· ὅπερ ἔδει δεῖξαι.],
    [Thus, if two triangles have two sides equal to two sides, respectively, but (one) has a base greater than the base (of the other), (then the former triangle) will also have the angle encompassed by the equal straight-lines greater than the (corresponding) angle (in the latter). (Which is) the very thing it was required to show.],
  )
]




