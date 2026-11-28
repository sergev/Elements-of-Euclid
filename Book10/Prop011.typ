#import "../functions.typ": *

#content-box[
  #parallel-proposition(11)
  #parallel(
    [Ἐὰν τέσσαρα μεγέθη ἀνάλογον ᾖ, τὸ δὲ πρῶτον τῷ δευτέρῳ σύμμετρον ᾖ, καὶ τὸ τρίτον τῷ τετάρτῳ σύμμετρον ἔσται· κἂν τὸ πρῶτον τῷ δευτέρῳ ἀσύμμετρον ᾖ, καὶ τὸ τρίτον τῷ τετάρτῳ ἀσύμμετρον ἔσται.],
    [If four magnitudes are proportional, and the first is commensurable with the second, then the third will also be commensurable with the fourth. And if the first is incommensurable with the second, then the third will also be incommensurable with the fourth.],
  )
  #parallel-image("/Book10/fig011", 0.5in)
  #parallel(
    [Ἔστωσαν τέσσαρα μεγέθη ἀνάλογον τὰ Α, Β, Γ, Δ, ὡς τὸ Α πρὸς τὸ Β, οὕτως τὸ Γ πρὸς τὸ Δ, τὸ Α δὲ τῷ Β σύμμετρον ἔστω· λέγω, ὅτι καὶ τὸ Γ τῷ Δ σύμμετρον ἔσται.],
    [Let $A$, $B$, $C$, $D$ be four proportional magnitudes, (such that) as $A$ (is) to $B$, so $C$ (is) to $D$. And let $A$ be commensurable with $B$. I say that $C$ will also be commensurable with $D$.],
  )
  #parallel(
    [Ἐπεὶ γὰρ σύμμετρόν ἐστι τὸ Α τῷ Β, τὸ Α ἄρα πρὸς τὸ Β λόγον ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν. καί ἐστιν ὡς τὸ Α πρὸς τὸ Β, οὕτως τὸ Γ πρὸς τὸ Δ· καὶ τὸ Γ ἄρα πρὸς τὸ Δ λόγον ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν· σύμμετρον ἄρα ἐστὶ τὸ Γ τῷ Δ.],
    [For since $A$ is commensurable with $B$, $A$ thus has to $B$ the ratio which (some) number (has) to (some) number [Prop.~10.5]. And as $A$ is to $B$, so $C$ (is) to $D$. Thus, $C$ also has to $D$ the ratio which (some) number (has) to (some) number. Thus, $C$ is commensurable with $D$ [Prop.~10.6].],
  )
  #parallel(
    [Ἀλλὰ δὴ τὸ Α τῷ Β ἀσύμμετρον ἔστω· λέγω, ὅτι καὶ τὸ Γ τῷ Δ ἀσύμμετρον ἔσται. ἐπεὶ γὰρ ἀσύμμετρόν ἐστι τὸ Α τῷ Β, τὸ Α ἄρα πρὸς τὸ Β λόγον οὐκ ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν. καί ἐστιν ὡς τὸ Α πρὸς τὸ Β, οὕτως τὸ Γ πρὸς τὸ Δ· οὐδὲ τὸ Γ ἄρα πρὸς τὸ Δ λόγον ἔχει, ὃν ἀριθμὸς πρὸς ἀριθμόν· ἀσύμμετρον ἄρα ἐστὶ τὸ Γ τῷ Δ.],
    [And so let $A$ be incommensurable with $B$. I say that $C$ will also be incommensurable with $D$. For since $A$ is incommensurable with $B$, $A$ thus does not have to $B$ the ratio which (some) number (has) to (some) number [Prop.~10.7]. And as $A$ is to $B$, so $C$ (is) to $D$. Thus, $C$ does not have to $D$ the ratio which (some) number (has) to (some) number either. Thus, $C$ is incommensurable with $D$ [Prop.~10.8].],
  )
  #parallel(
    [Ἐὰν ἄρα τέσσαρα μεγέθη, καὶ τὰ ἑξῆς.],
    [Thus, if four magnitudes, and so on ....],
  )
]
#lean-proof("/lean/Elements/Book10/Prop011.lean")
