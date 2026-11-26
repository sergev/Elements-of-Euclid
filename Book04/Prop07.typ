#import "../functions.typ": *

#content-box[
  #parallel-proposition(7)
  #parallel(
    [Περὶ τὸν δοθέντα κύκλον τετράγωνον περιγράψαι.],
    [To circumscribe a square about a given circle.],
  )
  #parallel(
    [Ἔστω ὁ δοθεὶς κύκλος ὁ ΑΒΓΔ· δεῖ δὴ περὶ τὸν ΑΒΓΔ κύκλον τετράγωνον περιγράψαι.],
    [Let $A B C D$ be the given circle. So it is required to circumscribe a square about circle $A B C D$.],
  )
  #parallel(
    [Ἤχθωσαν τοῦ ΑΒΓΔ κύκλου δύο διάμετροι πρὸς ὀρθὰς ἀλλήλαις αἱ ΑΓ, ΒΔ, καὶ διὰ τῶν Α, Β, Γ, Δ σημείων ἤχθωσαν ἐφαπτόμεναι τοῦ ΑΒΓΔ κύκλου αἱ ΖΗ, ΗΘ, ΘΚ, ΚΖ.],
    [Let two diameters of circle $A B C D$, $A C$ and $B D$, be drawn at right-angles to one another.#content-box-note[See the footnote to the previous proposition.] And let $F G$, $G H$, $H K$, and $K F$ be drawn through points $A$, $B$, $C$, and $D$ (respectively), touching circle $A B C D$.#content-box-note[See the footnote to Prop.~3.34.]],
  )
  #parallel-image("/Book04/fig07", 2.2in)
  #parallel(
    [Ἐπεὶ οὖν ἐφάπτεται ἡ ΖΗ τοῦ ΑΒΓΔ κύκλου, ἀπὸ δὲ τοῦ Ε κέντρου ἐπὶ τὴν κατὰ τὸ Α ἐπαφὴν ἐπέζευκται ἡ ΕΑ, αἱ ἄρα πρὸς τῷ Α γωνίαι ὀρθαί εἰσιν. διὰ τὰ αὐτὰ δὴ καὶ αἱ πρὸς τοῖς Β, Γ, Δ σημείοις γωνίαι ὀρθαί εἰσιν. καὶ ἐπεὶ ὀρθή ἐστιν ἡ ὑπὸ ΑΕΒ γωνία, ἐστὶ δὲ ὀρθὴ καὶ ἡ ὑπὸ ΕΒΗ, παράλληλος ἄρα ἐστὶν ἡ ΗΘ τῇ ΑΓ. διὰ τὰ αὐτὰ δὴ καὶ ἡ ΑΓ τῇ ΖΚ ἐστι παράλληλος. ὥστε καὶ ἡ ΗΘ τῇ ΖΚ ἐστι παράλληλος. ὁμοίως δὴ δείξομεν, ὅτι καὶ ἑκατέρα τῶν ΗΖ, ΘΚ τῇ ΒΕΔ ἐστι παράλληλος. παραλληλόγραμμα ἄρα ἐστὶ τὰ ΗΚ, ΗΓ, ΑΚ, ΖΒ, ΒΚ· ἴση ἄρα ἐστὶν ἡ μὲν ΗΖ τῇ ΘΚ, ἡ δὲ ΗΘ τῇ ΖΚ. καὶ ἐπεὶ ἴση ἐστὶν ἡ ΑΓ τῇ ΒΔ, ἀλλὰ καὶ ἡ μὲν ΑΓ ἑκατέρᾳ τῶν ΗΘ, ΖΚ, ἡ δὲ ΒΔ ἑκατέρᾳ τῶν ΗΖ, ΘΚ ἐστιν ἴση [καὶ ἑκατέρα ἄρα τῶν ΗΘ, ΖΚ ἑκατέρᾳ τῶν ΗΖ, ΘΚ ἐστιν ἴση], ἰσόπλευρον ἄρα ἐστὶ τὸ ΖΗΘΚ τετράπλευρον. λέγω δή, ὅτι καὶ ὀρθογώνιον. ἐπεὶ γὰρ παραλληλόγραμμόν ἐστι τὸ ΗΒΕΑ, καί ἐστιν ὀρθὴ ἡ ὑπὸ ΑΕΒ, ὀρθὴ ἄρα καὶ ἡ ὑπὸ ΑΗΒ. ὁμοίως δὴ δείξομεν, ὅτι καὶ αἱ πρὸς τοῖς Θ, Κ, Ζ γωνίαι ὀρθαί εἰσιν. ὀρθογώνιον ἄρα ἐστὶ τὸ ΖΗΘΚ. ἐδείχθη δὲ καὶ ἰσόπλευρον· τετράγωνον ἄρα ἐστίν. καὶ περιγέγραπται περὶ τὸν ΑΒΓΔ κύκλον.],
    [Therefore, since $F G$ touches circle $A B C D$, and $E A$ has been joined from the center $E$ to the point of contact $A$, the angles at $A$ are thus right-angles [Prop.~3.18]. So, for the same (reasons), the angles at points $B$, $C$, and $D$ are also right-angles. And since angle $A E B$ is a right-angle, and $E B G$ is also a right-angle, $G H$ is thus parallel to $A C$ [Prop.~1.29]. So, for the same (reasons), $A C$ is also parallel to $F K$. So that $G H$ is also parallel to $F K$ [Prop.~1.30]. So, similarly, we can show that $G F$ and $H K$ are each parallel to $B E D$. Thus, $G K$, $G C$, $A K$, $F B$, and $B K$ are (all) parallelograms. Thus, $G F$ is equal to $H K$, and $G H$ to $F K$ [Prop.~1.34]. And since $A C$ is equal to $B D$, but $A C$ (is) also (equal) to each of $G H$ and $F K$, and $B D$ is equal to each of $G F$ and $H K$ [Prop.~1.34] [and each of $G H$ and $F K$ is thus equal to each of $G F$ and $H K$], the quadrilateral $F G H K$ is thus equilateral. So I say that (it is) also right-angled. For since $G B E A$ is a parallelogram, and $A E B$ is a right-angle, $A G B$ is thus also a right-angle [Prop.~1.34]. So, similarly, we can show that the angles at $H$, $K$, and $F$ are also right-angles. Thus, $F G H K$ is right-angled. And it was also shown (to be) equilateral. Thus, it is a square [Def.~1.22]. And it has been circumscribed about circle $A B C D$.],
  )
  #parallel(
    [Περὶ τὸν δοθέντα ἄρα κύκλον τετράγωνον περιγέγραπται· ὅπερ ἔδει ποιῆσαι.],
    [Thus, a square has been circumscribed about the given circle. (Which is) the very thing it was required to do.],
  )
]
