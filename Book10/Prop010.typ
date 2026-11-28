#import "../functions.typ": *

#content-box[
  #parallel-proposition(10, note: [This whole proposition is regarded by Heiberg as an interpolation into the original text.])
  #parallel(
    [Τῇ προτεθείσῃ εὐθείᾳ προσευρεῖν δύο εὐθείας ἀσυμμέτρους, τὴν μὲν μήκει μόνον, τὴν δὲ καὶ δυνάμει.],
    [To find two straight-lines incommensurable with a given straight-line, the one (incommensurable) in length only, the other also (incommensurable) in square.],
  )
  #parallel-image("/Book10/fig010", 1.5in)
  #parallel(
    [Ἔστω ἡ προτεθεῖσα εὐθεῖα ἡ Α· δεῖ δὴ τῇ Α προσευρεῖν δύο εὐθείας ἀσυμμέτρους, τὴν μὲν μήκει μόνον, τὴν δὲ καὶ δυνάμει.],
    [Let $A$ be the given straight-line. So it is required to find two straight-lines incommensurable with $A$, the one (incommensurable) in length only, the other also (incommensurable) in square.],
  )
  #parallel(
    [Ἐκκείσθωσαν γὰρ δύο αριθμοὶ οἱ Β, Γ πρὸς ἀλλήλους λόγον μὴ ἔχοντες, ὃν τετράγωνος ἀριθμὸς πρὸς τετράγωνον ἀριθμόν, τουτέστι μὴ ὅμοιοι ἐπίπεδοι, καὶ γεγονέτω ὡς ὁ Β πρὸς τὸν Γ, οὕτως τὸ ἀπὸ τῆς Α τετράγωνον πρὸς τὸ ἀπὸ τῆς Δ τετράγωνον· ἐμάθομεν γάρ· σύμμετρον ἄρα τὸ ἀπὸ τῆς Α τῷ ἀπὸ τῆς Δ. καὶ ἐπεὶ ὁ Β πρὸς τὸν Γ λόγον οὐκ ἔχει, ὃν τετράγωνος ἀριθμὸς πρὸς τετράγωνον ἀριθμόν, οὐδ᾿ ἄρα τὸ ἀπὸ τῆς Α πρὸς τὸ ἀπὸ τῆς Δ λόγον ἔχει, ὃν τετράγωνος ἀριθμὸς πρὸς τετράγωνον ἀριθμόν· ἀσύμμετρος ἄρα ἐστὶν ἡ Α τῇ Δ μήκει. εἰλήφθω τῶν Α, Δ μέση ἀνάλογον ἡ Ε· ἔστιν ἄρα ὡς ἡ Α πρὸς τὴν Δ, οὕτως τὸ ἀπὸ τῆς Α τετράγωνον πρὸς τὸ ἀπὸ τῆς Ε. ἀσύμμετρος δέ ἐστιν ἡ Α τῇ Δ μήκει· ἀσύμμετρον ἄρα ἐστὶ καὶ τὸ ἀπὸ τῆς Α τετράγωνον τῷ ἀπὸ τῆς Ε τετραγώνῳ· ἀσύμμετρος ἄρα ἐστὶν ἡ Α τῇ Ε δυνάμει.],
    [For let two numbers, $B$ and $C$, not having to one another the ratio which (some) square number (has) to (some) square number---that is to say, not (being) similar plane (numbers)---be taken. And let it be contrived that as $B$ (is) to $C$, so the square on $A$ (is) to the square on $D$. For we learned (how to do this) [Prop.~10.6 corr.]. Thus, the (square) on $A$ (is) commensurable with the (square) on $D$ [Prop.~10.6]. And since $B$ does not have to $C$ the ratio which (some) square number (has) to (some) square number, the (square) on $A$ thus does not have to the (square) on $D$ the ratio which (some) square number (has) to (some) square number either. Thus, $A$ is incommensurable in length with $D$ [Prop.~10.9]. Let the (straight-line) $E$ (which is) in mean proportion to $A$ and $D$ be taken [Prop.~6.13]. Thus, as $A$ is to $D$, so the square on $A$ (is) to the (square) on $E$ [Def.~5.9]. And $A$ is incommensurable in length with $D$. Thus, the square on $A$ is also incommensurable with the square on $E$ [Prop.~10.11]. Thus, $A$ is incommensurable in square with $E$.],
  )
  #parallel(
    [Τῂ ἄρα προτεθείσῃ εὐθείᾳ τῇ Α προσεύρηνται δύο εὐθεῖαι ἀσύμμετροι αἱ Δ, Ε, μήκει μὲν μόνον ἡ Δ, δυνάμει δὲ καὶ μήκει δηλαδὴ ἡ Ε [ὅπερ ἔδει δεῖξαι].],
    [Thus, two straight-lines, $D$ and $E$, (which are) incommensurable with the given straight-line $A$, have been found, the one, $D$, (incommensurable) in length only, the other, $E$, (incommensurable) in square, and, clearly, also in length. [(Which is) the very thing it was required to show.]],
  )
]
#lean-proof("/lean/Elements/Book10/Prop010.lean")
