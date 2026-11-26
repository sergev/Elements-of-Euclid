#import "../functions.typ": *

#content-box[
  #parallel-proposition(1, note: [This theorem is the basis of the so-called method of exhaustion, and is generally attributed to Eudoxus of Cnidus.])
  #parallel(
    [Δύο μεγεθῶν ἀνίσων ἐκκειμένων, ἐὰν ἀπὸ τοῦ μείζονος ἀφαιρεθῇ μεῖζον ἢ τὸ ἥμισυ καὶ τοῦ καταλειπομένου μεῖζον ἢ τὸ ἥμισυ, καὶ τοῦτο ἀεὶ γίγνηται, λειφθήσεταί τι μέγεθος, ὃ ἔσται ἔλασσον τοῦ ἐκκειμένου ἐλάσσονος μεγέθους.],
    [If, from the greater of two unequal magnitudes (which are) laid out, (a part) greater than half is subtracted, and (if from) the remainder (a part) greater than half (is subtracted), and (if) this happens continually, then some magnitude will (eventually) be left which will be less than the lesser laid out magnitude.],
  )
  #parallel(
    [Ἔστω δύο μεγέθη ἄνισα τὰ ΑΒ, Γ, ὧν μεῖζον τὸ ΑΒ· λέγω, ὅτι, ἐαν ἀπὸ τοῦ ΑΒ ἀφαιρεθῇ μεῖζον ἢ τὸ ἥμισυ καὶ τοῦ καταλειπομένου μεῖζον ἢ τὸ ἥμισυ, καὶ τοῦτο ἀεὶ γίγνηται, λειφθήσεταί τι μέγεθος, ὃ ἔσται ἔλασσον τοῦ Γ μεγέθους.],
    [Let $A B$ and $C$ be two unequal magnitudes, of which (let) $A B$ (be) the greater. I say that if (a part) greater than half is subtracted from $A B$, and (if a part) greater than half (is subtracted) from the remainder, and (if) this happens continually, then some magnitude will (eventually) be left which will be less than the magnitude $C$.],
  )
  #parallel-image("/Book10/fig001", 1.1in)
  #parallel(
    [Τὸ Γ γὰρ πολλαπλασιαζόμενον ἔσται ποτὲ τοῦ ΑΒ μεῖζον. πεπολλαπλασιάσθω, καὶ ἔστω τὸ ΔΕ τοῦ μὲν Γ πολλαπλάσιον, τοῦ δὲ ΑΒ μεῖζον, καὶ διῃρήσθω τὸ ΔΕ εἰς τὰ τῷ Γ ἴσα τὰ ΔΖ, ΖΗ, ΗΕ, καὶ ἀφῃρήσθω ἀπὸ μὲν τοῦ ΑΒ μεῖζον ἢ τὸ ἥμισυ τὸ ΒΘ, ἀπὸ δὲ τοῦ ΑΘ μεῖζον ἢ τὸ ἥμισυ τὸ ΘΚ, καὶ τοῦτο ἀεὶ γιγνέσθω, ἕως ἂν αἱ ἐν τῷ ΑΒ διαιρέσεις ἰσοπληθεῖς γένωνται ταῖς ἐν τῷ ΔΕ διαιρέσεσιν.],
    [For $C$, when multiplied (by some number), will sometimes be greater than $A B$ [Def.~5.4]. Let it be (so) multiplied. And let $D E$ be (both) a multiple of $C$, and greater than $A B$. And let $D E$ be divided into the (divisions) $D F$, $F G$, $G E$, equal to $C$. And let $B H$, (which is) greater than half, be subtracted from $A B$. And (let) $H K$, (which is) greater than half, (be subtracted) from $A H$. And let this happen continually, until the divisions in $A B$ become equal in number to the divisions in $D E$.],
  )
  #parallel(
    [Ἔστωσαν οὖν αἱ ΑΚ, ΚΘ, ΘΒ διαιρέσεις ἰσοπληθεῖς οὖσαι ταῖς ΔΖ, ΖΗ, ΗΕ· καὶ ἐπεὶ μεῖζόν ἐστι τὸ ΔΕ τοῦ ΑΒ, καὶ ἀφῄρηται ἀπὸ μὲν τοῦ ΔΕ ἔλασσον τοῦ ἡμίσεως τὸ ΕΗ, ἀπὸ δὲ τοῦ ΑΒ μεῖζον ἢ τὸ ἥμισυ τὸ ΒΘ, λοιπὸν ἄρα τὸ ΗΔ λοιποῦ τοῦ ΘΑ μεῖζόν ἐστιν. καὶ ἐπεὶ μεῖζόν ἐστι τὸ ΗΔ τοῦ ΘΑ, καὶ ἀφῄρηται τοῦ μὲν ΗΔ ἥμισυ τὸ ΗΖ, τοῦ δὲ ΘΑ μεῖζον ἢ τὸ ἥμισυ τὸ ΘΚ, λοιπὸν ἄρα τὸ ΔΖ λοιποῦ τοῦ ΑΚ μεῖζόν ἐστιν. ἴσον δὲ τὸ ΔΖ τῷ Γ· καὶ τὸ Γ ἄρα τοῦ ΑΚ μεῖζόν ἐστιν. ἔλασσον ἄρα τὸ ΑΚ τοῦ Γ.],
    [Therefore, let the divisions (in $A B$) be $A K$, $K H$, $H B$, being equal in number to $D F$, $F G$, $G E$. And since $D E$ is greater than $A B$, and $E G$, (which is) less than half, has been subtracted from $D E$, and $B H$, (which is) greater than half, from $A B$, the remainder $G D$ is thus greater than the remainder $H A$. And since $G D$ is greater than $H A$, and the half $G F$ has been subtracted from $G D$, and $H K$, (which is) greater than half, from $H A$, the remainder $D F$ is thus greater than the remainder $A K$. And $D F$ (is) equal to $C$. $C$ is thus also greater than $A K$. Thus, $A K$ (is) less than $C$.],
  )
  #parallel(
    [Καταλείπεται ἄρα ἀπὸ τοῦ ΑΒ μεγέθους τὸ ΑΚ μέγεθος ἔλασσον ὂν τοῦ ἐκκειμένου ἐλάσσονος μεγέθους τοῦ Γ· ὅπερ ἔδει δεῖξαι. --- ὁμοίως δὲ δειχθήσεται, κἂν ἡμίση ᾖ τὰ ἀφαιρούμενα.],
    [Thus, the magnitude $A K$, which is less than the lesser laid out magnitude $C$, is left over from the magnitude $A B$. (Which is) the very thing it was required to show. --- (The theorem) can similarly be proved even if the (parts) subtracted are halves.],
  )
]
