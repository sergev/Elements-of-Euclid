#import "../functions.typ": *

#content-box[
  #parallel-proposition(26)
  #parallel(
    [Ἐὰν ἀπὸ παραλληλογράμμου παραλληλόγραμμον ἀφαιρεθῇ ὅμοιόν τε τῷ ὅλῳ καὶ ὁμοίως κείμενον κοινὴν γωνίαν ἔχον αὐτῷ, περὶ τὴν αὐτὴν διάμετρόν ἐστι τῷ ὅλῳ.],
    [If from a parallelogram a(nother) parallelogram is subtracted (which is) similar, and similarly laid out, to the whole, having a common angle with it, (then the subtracted parallelogram) is about the same diagonal as the whole.],
  )
  #parallel(
    [Ἀπὸ γὰρ παραλληλογράμμου τοῦ ΑΒΓΔ παραλληλόγραμμον ἀφῃρήσθω τὸ ΑΖ ὅμοιον τῷ ΑΒΓΔ καὶ ὁμοίως κείμενον κοινὴν γωνίαν ἔχον αὐτῷ τὴν ὑπὸ ΔΑΒ· λέγω, ὅτι περὶ τὴν αὐτὴν διάμετρόν ἐστι τὸ ΑΒΓΔ τῷ ΑΖ.],
    [For, from parallelogram $A B C D$, let (parallelogram) $A F$ be subtracted (which is) similar, and similarly laid out, to $A B C D$, having the common angle $D A B$ with it. I say that $A B C D$ is about the same diagonal as $A F$.],
  )
  #parallel-image("/Book06/fig26", 2in)
  #parallel(
    [μὴ γάρ, ἀλλ᾿ εἰ δυνατόν, ἔστω [αὐτῶν] διάμετρος ἡ ΑΘΓ, καὶ ἐκβληθεῖσα ἡ ΗΖ διήχθω ἐπὶ τὸ Θ, καὶ ἤχθω διὰ τοῦ Θ ὁπορέρᾳ τῶν ΑΔ, ΒΓ παράλληλος ἡ ΘΚ.],
    [For (if) not, (then), if possible, let $A H C$ be [$A B C D$'s] diagonal. And producing $G F$, let it be drawn through to (point) $H$. And let $H K$ be drawn through (point) $H$, parallel to either of $A D$ or $B C$ [Prop.~1.31].],
  )
  #parallel(
    [Ἐπεὶ οὖν περὶ τὴν αὐτὴν διάμετρόν ἐστι τὸ ΑΒΓΔ τῷ ΚΗ, ἔστιν ἄρα ὡς ἡ ΔΑ πρὸς τὴν ΑΒ, οὕτως ἡ ΗΑ πρὸς τὴν ΑΚ. ἔστι δὲ καὶ διὰ τὴν ὁμοιότητα τῶν ΑΒΓΔ, ΕΗ καὶ ὡς ἡ ΔΑ πρὸς τὴν ΑΒ, οὕτως ἡ ΗΑ πρὸς τὴν ΑΕ· καὶ ὡς ἄρα ἡ ΗΑ πρὸς τὴν ΑΚ, οὕτως ἡ ΗΑ πρὸς τὴν ΑΕ. ἡ ΗΑ ἄρα πρὸς ἑκατέραν τῶν ΑΚ, ΑΕ τὸν αὐτὸν ἔχει λόγον. ἴση ἄρα ἐστὶν ἡ ΑΕ τῇ ΑΚ ἡ ἐλάττων τῇ μείζονι· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα οὔκ ἐστι περὶ τὴν αὐτὴν διάμετρον τὸ ΑΒΓΔ τῷ ΑΖ· περὶ τὴν αὐτὴν ἄρα ἐστὶ διάμετρον τὸ ΑΒΓΔ παραλληλόγραμμον τῷ ΑΖ παραλληλογράμμῳ.],
    [Therefore, since $A B C D$ is about the same diagonal as $K G$, thus as $D A$ is to $A B$, so $G A$ (is) to $A K$ [Prop.~6.24]. And, on account of the similarity of $A B C D$ and $E G$, also, as $D A$ (is) to $A B$, so $G A$ (is) to $A E$. Thus, also, as $G A$ (is) to $A K$, so $G A$ (is) to $A E$. Thus, $G A$ has the same ratio to each of $A K$ and $A E$. Thus, $A E$ is equal to $A K$ [Prop.~5.9], the lesser to the greater. The very thing is impossible. Thus, $A B C D$ is not not about the same diagonal as $A F$. Thus, parallelogram $A B C D$ is about the same diagonal as parallelogram $A F$.],
  )
  #parallel(
    [Ἐὰν ἄρα ἀπὸ παραλληλογράμμου παραλληλόγραμμον ἀφαιρεθῇ ὅμοιόν τε τῷ ὅλῳ καὶ ὁμοίως κείμενον κοινὴν γωνίαν ἔχον αὐτῷ, περὶ τὴν αὐτὴν διάμετρόν ἐστι τῷ ὅλῳ· ὅπερ ἔδει δεῖξαι.],
    [Thus, if from a parallelogram a(nother) parallelogram is subtracted (which is) similar, and similarly laid out, to the whole, having a common angle with it, (then the subtracted parallelogram) is about the same diagonal as the whole. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book6/Prop26.lean")
