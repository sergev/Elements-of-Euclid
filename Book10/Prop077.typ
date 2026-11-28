#import "../functions.typ": *

#content-box[
  #parallel-proposition(77)
  #parallel(
    [Ἐὰν ἀπὸ εὐθείας εὐθεῖα ἀφαιρεθῇ δυνάμει ἀσύμμετρος οὖσα τῇ ὅλῃ, μετὰ δὲ τῆς ὅλης ποιοῦσα τὸ μὲν συγκείμενον ἐκ τῶν ἀπ᾿ αὐτῶν τετραγώνων μέσον, τὸ δὲ δὶς ὑπ᾿ αὐτῶν ῥητόν, ἡ λοιπὴ ἄλογός ἐστιν· καλείσθω δὲ ἡ μετὰ ῥητοῦ μέσον τὸ ὅλον ποιοῦσα.],
    [If a straight-line, which is incommensurable in square with the whole, and with the whole makes the sum of the squares on them medial, and twice the (rectangle contained) by them rational, is subtracted from a(nother) straight-line then the remainder is an irrational (straight-line). Let it be called that which makes with a rational (area) a medial whole.],
  )
  #parallel-image("/Book10/fig073", 0.27in)
  #parallel(
    [Ἀπὸ γὰρ εὐθείας τῆς ΑΒ εὐθεῖα ἀφῃρήσθω ἡ ΒΓ δυνάμει ἀσύμμετος οὖσα τῇ ΑΒ ποιοῦσα τὰ προκείμενα· λέγω, ὅτι ἡ λοιπὴ ἡ ΑΓ ἄλογός ἐστιν ἡ προειρημένη.],
    [For let the straight-line $B C$, which is incommensurable in square with $A B$, and fulfils the (other) prescribed (conditions), be subtracted from the straight-line $A B$ [Prop.~10.34]. I say that the remainder $A C$ is the aforementioned irrational (straight-line).],
  )
  #parallel(
    [Ἐπεὶ γὰρ τὸ μὲν συγκείμενον ἐκ τῶν ἀπὸ τῶν ΑΒ, ΒΓ τετραγώνων μέσον ἐστίν, τὸ δὲ δὶς ὑπὸ τῶν ΑΒ, ΒΓ ῥητόν, ἀσύμμετρα ἄρα ἐστὶ τὰ ἀπὸ τῶν ΑΒ, ΒΓ τῷ δὶς ὑπὸ τῶν ΑΒ, ΒΓ· καὶ λοιπὸν ἄρα τὸ ἀπὸ τῆς ΑΓ ἀσύμμετρόν ἐστι τῷ δὶς ὑπὸ τῶν ΑΒ, ΒΓ. καί ἐστι τὸ δὶς ὑπὸ τῶν ΑΒ, ΒΓ ῥητόν· τὸ ἄρα ἀπὸ τῆς ΑΓ ἄλογόν ἐστιν· ἄλογος ἄρα ἐστὶν ἡ ΑΓ· καλείσθω δὲ ἡ μετὰ ῥητοῦ μέσον τὸ ὅλον ποιοῦσα. ὅπερ ἔδει δεῖξαι.],
    [For since the sum of the squares on $A B$ and $B C$ is medial, and twice the (rectangle contained) by $A B$ and $B C$ rational, the (sum of the squares) on $A B$ and $B C$ is thus incommensurable with twice the (rectangle contained) by $A B$ and $B C$. Thus, the remaining (square) on $A C$ is also incommensurable with twice the (rectangle contained) by $A B$ and $B C$ [Props.~2.7, 10.16]. And twice the (rectangle contained) by $A B$ and $B C$ is rational. Thus, the (square) on $A C$ is irrational. Thus, $A C$ is an irrational (straight-line) [Def.~10.4]. And let it be called that which makes with a rational (area) a medial whole.#content-box-note[See footnote to Prop.~10.40.] (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop077.lean")
