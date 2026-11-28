#import "../functions.typ": *

#content-box[
  #parallel-proposition(27)
  #parallel(
    [Μέσας εὑρεῖν δυνάμει μόνον συμμέτρους ῥητὸν περιεχούσας.],
    [To find (two) medial (straight-lines), containing a rational (area), (which are) commensurable in square only.],
  )
  #parallel-image("/Book10/fig027", 1.6in)
  #parallel(
    [Ἐκκείσθωσαν δύο ῥηταὶ δυνάμει μόνον σύμμετροι αἱ Α, Β, καὶ εἰλήφθω τῶν Α, Β μέση ἀνάλογον ἡ Γ, καὶ γεγονέτω ὡς ἡ Α πρὸς τὴν Β, οὕτως ἡ Γ πρὸς τὴν Δ.],
    [Let the two rational (straight-lines) $A$ and $B$, (which are) commensurable in square only, be laid down. And let $C$---the mean proportional (straight-line) to $A$ and $B$---be taken [Prop.~6.13]. And let it be contrived that as $A$ (is) to $B$, so $C$ (is) to $D$ [Prop.~6.12].],
  )
  #parallel(
    [Καὶ ἐπεὶ αἱ Α, Β ῥηταί εἰσι δυνάμει μόνον σύμμετροι, τὸ ἄρα ὑπὸ τῶν Α, Β, τουτέστι τὸ ἀπὸ τῆς Γ, μέσον ἐστίν. μέση ἄρα ἡ Γ. καὶ ἐπεί ἐστιν ὡς ἡ Α πρὸς τὴν Β, [οὕτως] ἡ Γ πρὸς τὴν Δ, αἱ δὲ Α, Β δυνάμει μόνον [εἰσὶ] σύμμετροι, καὶ αἱ Γ, Δ ἄρα δυνάμει μόνον εἰσὶ σύμμετροι. καί ἐστι μέση ἡ Γ· μέση ἄρα καὶ ἡ Δ. αἱ Γ, Δ ἄρα μέσαι εἰσὶ δυνάμει μόνον σύμμετροι. λέγω, ὅτι καὶ ῥητὸν περιέχουσιν. ἐπεὶ γάρ ἐστιν ὡς ἡ Α πρὸς τὴν Β, οὕτως ἡ Γ πρὸς τὴν Δ, ἐναλλὰξ ἄρα ἐστὶν ὡς ἡ Α πρὸς τὴν Γ, ἡ Β πρὸς τὴν Δ. ἀλλ᾿ ὡς ἡ Α πρὸς τὴν Γ, ἡ Γ πρὸς τὴν Β· καὶ ὡς ἄρα ἡ Γ πρὸς τὴν Β, οὕτως ἡ Β πρὸς τὴν Δ· τὸ ἄρα ὑπὸ τῶν Γ, Δ ἴσον ἐστὶ τῷ ἀπὸ τῆς Β. ῥητὸν δὲ τὸ ἀπὸ τῆς Β· ῥητὸν ἄρα [ἐστὶ] καὶ τὸ ὑπὸ τῶν Γ, Δ.],
    [And since the rational (straight-lines) $A$ and $B$ are commensurable in square only, the (rectangle contained) by $A$ and $B$---that is to say, the (square) on $C$ [Prop.~6.17]---is thus medial [Prop.~10.21]. Thus, $C$ is medial [Prop.~10.21]. And since as $A$ is to $B$, [so] $C$ (is) to $D$, and $A$ and $B$ [are] commensurable in square only, $C$ and $D$ are thus also commensurable in square only [Prop.~10.11]. And $C$ is medial. Thus, $D$ is also medial [Prop.~10.23]. Thus, $C$ and $D$ are medial (straight-lines which are) commensurable in square only. I say that they also contain a rational (area). For since as $A$ is to $B$, so $C$ (is) to $D$, thus, alternately, as $A$ is to $C$, so $B$ (is) to $D$ [Prop.~5.16]. But, as $A$ (is) to $C$, (so) $C$ (is) to $B$. And thus as $C$ (is) to $B$, so $B$ (is) to $D$ [Prop.~5.11]. Thus, the (rectangle contained) by $C$ and $D$ is equal to the (square) on $B$ [Prop.~6.17]. And the (square) on $B$ (is) rational. Thus, the (rectangle contained) by $C$ and $D$ [is] also rational.],
  )
  #parallel(
    [Εὕρηνται ἄρα μέσαι δυνάμει μόνον σύμμετροι ῥητὸν περιέχουσαι· ὅπερ ἔδει δεῖξαι.],
    [Thus, (two) medial (straight-lines, $C$ and $D$), containing a rational (area), (which are) commensurable in square only, have been found.#content-box-note[$C$ and $D$ have lengths $k^(1 \/ 4)$ and $k^(3 \/ 4)$ times that of $A$, respectively, where the length of $B$ is $k^(1 \/ 2)$ times that of $A$.] (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book10/Prop027.lean")
