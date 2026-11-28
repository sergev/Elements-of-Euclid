#import "../functions.typ": *

#content-box[
  #parallel-proposition(18)
  #parallel(
    [Ἐὰν κύκλου ἐφάπτηταί τις εὐθεῖα, ἀπὸ δὲ τοῦ κέντρου ἐπὶ τὴν ἁφὴν ἐπιζευχθῇ τις εὐθεῖα, ἡ ἐπιζευχθεῖσα κάθετος ἔσται ἐπὶ τὴν ἐφαπτομένην.],
    [If some straight-line touches a circle, and some (other) straight-line is joined from the center (of the circle) to the point of contact, (then) the (straight-line) so joined will be perpendicular to the tangent.],
  )
  #parallel(
    [Κύκλου γὰρ τοῦ ΑΒΓ ἐφαπτέσθω τις εὐθεῖα ἡ ΔΕ κατὰ τὸ Γ σημεῖον, καὶ εἰλήφθω τὸ κέντρον τοῦ ΑΒΓ κύκλου τὸ Ζ, καὶ ἀπὸ τοῦ Ζ ἐπὶ τὸ Γ ἐπεζεύχθω ἡ ΖΓ· λέγω, ὅτι ἡ ΖΓ κάθετός ἐστιν ἐπὶ τὴν ΔΕ.],
    [For let some straight-line $D E$ touch the circle $A B C$ at point $C$, and let the center $F$ of circle $A B C$ be found [Prop.~3.1], and let $F C$ be joined from $F$ to $C$. I say that $F C$ is perpendicular to $D E$.],
  )
  #parallel(
    [Εἰ γὰρ μή, ἤχθω ἀπὸ τοῦ Ζ ἐπὶ τὴν ΔΕ κάθετος ἡ ΖΗ.],
    [For if not, let $F G$ be drawn from $F$, perpendicular to $D E$ [Prop.~1.12].],
  )
  #parallel(
    [Ἐπεὶ οὖν ἡ ὑπὸ ΖΗΓ γωνία ὀρθή ἐστιν, ὀξεῖα ἄρα ἐστὶν ἡ ὑπὸ ΖΓΗ· ὑπὸ δὲ τὴν μείζονα γωνίαν ἡ μείζων πλευρὰ ὑποτείνει· μείζων ἄρα ἡ ΖΓ τῆς ΖΗ· ἴση δὲ ἡ ΖΓ τῇ ΖΒ· μείζων ἄρα καὶ ἡ ΖΒ τῆς ΖΗ ἡ ἐλάττων τῆς μείζονος· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα ἡ ΖΗ κάθετός ἐστιν ἐπὶ τὴν ΔΕ. ὁμοίως δὴ δεῖξομεν, ὅτι οὐδ᾿ ἄλλη τις πλὴν τῆς ΖΓ· ἡ ΖΓ ἄρα κάθετός ἐστιν ἐπὶ τὴν ΔΕ.],
    [Therefore, since angle $F G C$ is a right-angle, (angle) $F C G$ is thus acute [Prop.~1.17]. And the greater angle is subtended by the greater side [Prop.~1.19]. Thus, $F C$ (is) greater than $F G$. And $F C$ (is) equal to $F B$. Thus, $F B$ (is) also greater than $F G$, the lesser than the greater. The very thing is impossible. Thus, $F G$ is not perpendicular to $D E$. So, similarly, we can show that neither (is) any other (straight-line) except $F C$. Thus, $F C$ is perpendicular to $D E$.],
  )
  #parallel-image("/Book03/fig18", 2.2in)
  #parallel(
    [Ἐὰν ἄρα κύκλου ἐφάπτηταί τις εὐθεῖα, ἀπὸ δὲ τοῦ κέντρου ἐπὶ τὴν ἁφὴν ἐπιζευχθῇ τις εὐθεῖα, ἡ ἐπιζευχθεῖσα κάθετος ἔσται ἐπὶ τὴν ἐφαπτομένην· ὅπερ ἔδει δεῖξαι.],
    [Thus, if some straight-line touches a circle, and some (other) straight-line is joined from the center (of the circle) to the point of contact, (then) the (straight-line) so joined will be perpendicular to the tangent. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop18.lean")
