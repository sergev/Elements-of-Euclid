#import "../functions.typ": *

#content-box[
  #parallel-proposition(15)
  #parallel(
    [Ἐν κύκλῳ μεγίστη μὲν ἡ διάμετρος, τῶν δὲ ἄλλων ἀεὶ ἡ ἔγγιον τοῦ κέντρου τῆς ἀπώτερον μείζων ἐστίν.],
    [In a circle, a diameter (is) the greatest (straight-line), and for the others, a (straight-line) nearer to the center is always greater than one further away.],
  )
  #parallel(
    [Ἔστω κύκλος ὁ ΑΒΓΔ, διάμετρος δὲ αὐτοῦ ἔστω ἡ ΑΔ, κέντρον δὲ τὸ Ε, καὶ ἔγγιον μὲν τῆς ΑΔ διαμέτρου ἔστω ἡ ΒΓ, ἀπώτερον δὲ ἡ ΖΗ· λέγω, ὅτι μεγίστη μέν ἐστιν ἡ ΑΔ, μείζων δὲ ἡ ΒΓ τῆς ΖΗ.],
    [Let $A B C D$ be a circle, and let $A D$ be its diameter, and $E$ (its) center. And let $B C$ be nearer to the diameter $A D$,#content-box-note[Euclid should have said "to the center", rather than "to the diameter $A D$", since $B C$, $A D$ and $F G$ are not necessarily parallel.] and $F G$ further away. I say that $A D$ is the greatest (straight-line), and $B C$ (is) greater than $F G$.],
  )
  #parallel(
    [Ἤχθωσαν γὰρ ἀπὸ τοῦ Ε κέντρου ἐπὶ τὰς ΒΓ, ΖΗ κάθετοι αἱ ΕΘ, ΕΚ. καὶ ἐπεὶ ἔγγιον μὲν τοῦ κέντρου ἐστὶν ἡ ΒΓ, ἀπώτερον δὲ ἡ ΖΗ, μείζων ἄρα ἡ ΕΚ τῆς ΕΘ. κείσθω τῇ ΕΘ ἴση ἡ ΕΛ, καὶ διὰ τοῦ Λ τῇ ΕΚ πρὸς ὀρθὰς ἀχθεῖσα ἡ ΛΜ διήχθω ἐπὶ τὸ Ν, καὶ ἐπεζεύχθωσαν αἱ ΜΕ, ΕΝ, ΖΕ, ΕΗ.],
    [For let $E H$ and $E K$ be drawn from the center $E$, at right-angles to $B C$ and $F G$ (respectively) [Prop.~1.12]. And since $B C$ is nearer to the center, and $F G$ further away, $E K$ (is) thus greater than $E H$ [Def.~3.5]. Let $E L$ be made equal to $E H$ [Prop.~1.3]. And $L M$ being drawn through $L$, at right-angles to $E K$ [Prop.~1.11], let it be drawn through to $N$. And let $M E$, $E N$, $F E$, and $E G$ be joined.],
  )
  #parallel(
    [Καὶ ἐπεὶ ἴση ἐστὶν ἡ ΕΘ τῇ ΕΛ, ἴση ἐστὶ καὶ ἡ ΒΓ τῇ ΜΝ. πάλιν, ἐπεὶ ἴση ἐστὶν ἡ μὲν ΑΕ τῇ ΕΜ, ἡ δὲ ΕΔ τῇ ΕΝ, ἡ ἄρα ΑΔ ταῖς ΜΕ, ΕΝ ἴση ἐστίν. ἀλλ᾿ αἱ μὲν ΜΕ, ΕΝ τῆς ΜΝ μείζονές εἰσιν [καὶ ἡ ΑΔ τῆς ΜΝ μείζων ἐστίν], ἴση δὲ ἡ ΜΝ τῇ ΒΓ· ἡ ΑΔ ἄρα τῆς ΒΓ μείζων ἐστίν. καὶ ἐπεὶ δύο αἱ ΜΕ, ΕΝ δύο ταῖς ΖΕ, ΕΗ ἴσαι εἰσίν, καὶ γωνία ἡ ὑπὸ ΜΕΝ γωνίας τῆς ὑπὸ ΖΕΗ μείζων [ἐστίν], βάσις ἄρα ἡ ΜΝ βάσεως τῆς ΖΗ μείζων ἐστίν. ἀλλὰ ἡ ΜΝ τῇ ΒΓ ἐδείχθη ἴση [καὶ ἡ ΒΓ τῆς ΖΗ μείζων ἐστίν]. μεγίστη μὲν ἄρα ἡ ΑΔ διάμετρος, μείζων δὲ ἡ ΒΓ τῆς ΖΗ.],
    [And since $E H$ is equal to $E L$, $B C$ is also equal to $M N$ [Prop.~3.14]. Again, since $A E$ is equal to $E M$, and $E D$ to $E N$, $A D$ is thus equal to $M E$ and $E N$. But, $M E$ and $E N$ is greater than $M N$ [Prop.~1.20] [also $A D$ is greater than $M N$], and $M N$ (is) equal to $B C$. Thus, $A D$ is greater than $B C$. And since the two (straight-lines) $M E$, $E N$ are equal to the two (straight-lines) $F E$, $E G$ (respectively), and angle $M E N$ [is] greater than angle $F E G$,#content-box-note[This is not proved, except by reference to the figure.] the base $M N$ is thus greater than the base $F G$ [Prop.~1.24]. But, $M N$ was shown (to be) equal to $B C$ [(so) $B C$ is also greater than $F G$]. Thus, the diameter $A D$ (is) the greatest (straight-line), and $B C$ (is) greater than $F G$.],
  )
  #parallel-image("/Book03/fig15", 2.2in)
  #parallel(
    [Ἐν κύκλῳ ἄρα μεγίστη μὲν έστιν ἡ διάμετρος, τῶν δὲ ἄλλων ἀεὶ ἡ ἔγγιον τοῦ κέντρου τῆς ἀπώτερον μείζων ἐστίν· ὅπερ ἔδει δεῖξαι.],
    [Thus, in a circle, a diameter (is) the greatest (straight-line), and for the others, a (straight-line) nearer to the center is always greater than one further away. (Which is) the very thing it was required to show.],
  )
]
#lean-proof("/lean/Elements/Book3/Prop15.lean")
