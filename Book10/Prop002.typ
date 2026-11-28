#import "../functions.typ": *

#content-box[
  #parallel-proposition(2)
  #parallel(
    [Ἐὰν δύο μεγεθῶν [ἐκκειμένων] ἀνίσων ἀνθυφαιρουμένου ἀεὶ τοῦ ἐλάσσονος ἀπὸ τοῦ μείζονος τὸ καταλειπόμενον μηδέποτε καταμετρῇ τὸ πρὸ ἑαυτοῦ, ἀσύμμετρα ἔσται τὰ μεγέθη.],
    [If the remainder of two unequal magnitudes (which are) [laid out] never measures the (magnitude) before it, (when) the lesser (magnitude is) continually subtracted in turn from the greater, then the (original) magnitudes will be incommensurable.],
  )
  #parallel-image("/Book10/fig002", 0.9in)
  #parallel(
    [Δύο γὰρ μεγεθῶν ὄντων ἀνίσων τῶν ΑΒ, ΓΔ καὶ ἐλάσσονος τοῦ ΑΒ ἀνθυφαιρουμένου ἀεὶ τοῦ ἐλάσσονος ἀπὸ τοῦ μείζονος τὸ περιλειπόμενον μηδέποτε καταμετρείτω τὸ πρὸ ἑαυτοῦ· λέγω, ὅτι ἀσύμμετρά ἐστι τὰ ΑΒ, ΓΔ μεγέθη.],
    [For, $A B$ and $C D$ being two unequal magnitudes, and $A B$ (being) the lesser, let the remainder never measure the (magnitude) before it, (when) the lesser (magnitude is) continually subtracted in turn from the greater. I say that the magnitudes $A B$ and $C D$ are incommensurable.],
  )
  #parallel(
    [Εἰ γάρ ἐστι σύμμετρα, μετρήσει τι αὐτὰ μέγεθος. μετρείτω, εἰ δυνατόν, καὶ ἔστω τὸ Ε· καὶ τὸ μὲν ΑΒ τὸ ΖΔ καταμετροῦν λειπέτω ἑαυτοῦ ἔλασσον τὸ ΓΖ, τὸ δὲ ΓΖ τὸ ΒΗ καταμετροῦν λειπέτω ἑαυτοῦ ἔλασσον τὸ ΑΗ, καὶ τοῦτο ἀεὶ γινέσθω, ἕως οὗ λειφθῇ τι μέγεθος, ὅ ἐστιν ἔλασσον τοῦ Ε. γεγονέτω, καὶ λελείφθω τὸ ΑΗ ἔλασσον τοῦ Ε. ἐπεὶ οὖν τὸ Ε τὸ ΑΒ μετρεῖ, ἀλλὰ τὸ ΑΒ τὸ ΔΖ μετρεῖ, καὶ τὸ Ε ἄρα τὸ ΖΔ μετρήσει. μετρεῖ δὲ καὶ ὅλον τὸ ΓΔ· καὶ λοιπὸν ἄρα τὸ ΓΖ μετρήσει. ἀλλὰ τὸ ΓΖ τὸ ΒΗ μετρεῖ· καὶ τὸ Ε ἄρα τὸ ΒΗ μετρεῖ. μετρεῖ δὲ καὶ ὅλον τὸ ΑΒ· καὶ λοιπὸν ἄρα τὸ ΑΗ μετρήσει, τὸ μεῖζον τὸ ἔλασσον· ὅπερ ἐστὶν ἀδύνατον. οὐκ ἄρα τὰ ΑΒ, ΓΔ μεγέθη μετρήσει τι μέγεθος· ἀσύμμετρα ἄρα ἐστὶ τὰ ΑΒ, ΓΔ μεγέθη.],
    [For if they are commensurable then some magnitude will measure them (both). If possible, let it (so) measure (them), and let it be $E$. And let $A B$ leave $C F$ less than itself (in) measuring $F D$, and let $C F$ leave $A G$ less than itself (in) measuring $B G$, and let this happen continually, until some magnitude which is less than $E$ is left. Let (this) have occurred,#content-box-note[The fact that this will eventually occur is guaranteed by Prop.~10.1.] and let $A G$, (which is) less than $E$, be left. Therefore, since $E$ measures $A B$, but $A B$ measures $D F$, $E$ will thus also measure $F D$. And it also measures the whole (of) $C D$. Thus, it will also measure the remainder $C F$. But, $C F$ measures $B G$. Thus, $E$ also measures $B G$. And it also measures the whole (of) $A B$. Thus, it will also measure the remainder $A G$, the greater (measuring) the lesser. The very thing is impossible. Thus, some magnitude cannot measure (both) the magnitudes $A B$ and $C D$. Thus, the magnitudes $A B$ and $C D$ are incommensurable [Def.~10.1].],
  )
  #parallel(
    [Ἐὰν ἄρα δύο μεγεθῶν ἀνίσων, καὶ τὰ ἑξῆς.],
    [Thus, if ... of two unequal magnitudes, and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop002.lean")
