#import "../functions.typ": *

#content-box[
  #parallel-proposition(74)
  #parallel(
    [Ἐὰν ἀπὸ μέσης μέση ἀφαιρεθῇ δυνάμει μόνον σύμμετρος οὖσα τῇ ὅλῃ, μετὰ δὲ τῆς ὅλης ῥητὸν περιέχουσα, ἡ λοιπὴ ἄλογός ἐστιν· καλείσθω δὲ μέσης ἀποτομὴ πρώτη.],
    [If a medial (straight-line), which is commensurable in square only with the whole, and which contains a rational (area) with the whole, is subtracted from a(nother) medial (straight-line) then the remainder is an irrational (straight-line). Let it be called a first apotome of a medial (straight-line).],
  )
  #parallel-image("/Book10/fig073", 0.3in)
  #parallel(
    [Ἀπὸ γὰρ μέσης τῆς ΑΒ μέση ἀφῃρήσθω ἡ ΒΓ δυνάμει μόνον σύμμετρος οὖσα τῇ ΑΒ, μετὰ δὲ τῆς ΑΒ ῥητὸν ποιοῦσα τὸ ὑπὸ τῶν ΑΒ, ΒΓ· λέγω, ὅτι ἡ λοιπὴ ἡ ΑΓ ἄλογός ἐστιν· καλείσθω δὲ μέσης ἀποτομὴ πρώτη.],
    [For let the medial (straight-line) $B C$, which is commensurable in square only with $A B$, and which makes with $A B$ the rational (rectangle contained) by $A B$ and $B C$, be subtracted from the medial (straight-line) $A B$ [Prop.~10.27]. I say that the remainder $A C$ is an irrational (straight-line). Let it be called a first apotome of a medial (straight-line).],
  )
  #parallel(
    [Ἐπεὶ γὰρ αἱ ΑΒ, ΒΓ μέσαι εἰσίν, μέσα ἐστὶ καὶ τὰ ἀπὸ τῶν ΑΒ, ΒΓ. ῥητὸν δὲ τὸ δὶς ὑπὸ τῶν ΑΒ, ΒΓ· ἀσύμμετρα ἄρα τὰ ἀπὸ τῶν ΑΒ, ΒΓ τῷ δὶς ὑπὸ τῶν ΑΒ, ΒΓ· καὶ λοιπῷ ἄρα τῷ ἀπὸ τῆς ΑΓ ἀσύμμετρόν ἐστι τὸ δὶς ὑπὸ τῶν ΑΒ, ΒΓ, ἐπεὶ κἂν τὸ ὅλον ἑνὶ αὐτῶν ἀσύμμετρον ᾖ, καὶ τὰ ἐξ ἀρχῆς μεγέθη ἀσύμμετρα ἔσται. ῥητὸν δὲ τὸ δὶς ὑπὸ τῶν ΑΒ, ΒΓ· ἄλογον ἄρα τὸ ἀπὸ τῆς ΑΓ· ἄλογος ἄρα ἐστὶν ἡ ΑΓ· καλείσθω δὲ μέσης ἀποτομὴ πρώτη.],
    [For since $A B$ and $B C$ are medial (straight-lines), the (sum of the squares) on $A B$ and $B C$ is also medial. And twice the (rectangle contained) by $A B$ and $B C$ (is) rational. The (sum of the squares) on $A B$ and $B C$ (is) thus incommensurable with twice the (rectangle contained) by $A B$ and $B C$. Thus, twice the (rectangle contained) by $A B$ and $B C$ is also incommensurable with the remaining (square) on $A C$ [Prop.~2.7], since if the whole is incommensurable with one of the (constituent magnitudes) then the original magnitudes will also be incommensurable (with one another) [Prop.~10.16]. And twice the (rectangle contained) by $A B$ and $B C$ (is) rational. Thus, the (square) on $A C$ is irrational. Thus, $A C$ is an irrational (straight-line) [Def.~10.4]. Let it be called a first apotome of a medial (straight-line).#content-box-note[See footnote to Prop.~10.37.]],
  )
]
#lean-proof("/lean/Elements/Book10/Prop074.lean")
