#import "../functions.typ": *

#content-box[
  #chapter(
    [Definitions],
    parallel(
      [Ὅροι.],
      [Definitions]
    ),
    depth: 2,
  )
  #parallel(
    [Μέρος ἐστὶ μέγεθος μεγέθους τὸ ἔλασσον τοῦ μείζονος, ὅταν καταμετρῇ τὸ μεῖζον.],
    [A magnitude is a part of a(nother) magnitude, the lesser of the greater, when it measures the greater.#content-box-note[In other words, $alpha$ is said to be a part of $beta$ if $beta = m thin alpha$.]],
    n: 1,
  )
  #parallel(
    [Πολλαπλάσιον δὲ τὸ μεῖζον τοῦ ἐλάττονος, ὅταν καταμετρῆται ὑπὸ τοῦ ἐλάττονος.],
    [And the greater (magnitude is) a multiple of the lesser when it is measured by the lesser.],
    n: 2,
  )
  #parallel(
    [Λόγος ἐστὶ δύο μεγεθῶν ὁμογενῶν ἡ κατὰ πηλικότητά ποια σχέσις.],
    [A ratio is a certain type of relation with respect to size of two magnitudes of the same kind.#content-box-note[In modern notation, the ratio of two magnitudes, $alpha$ and $beta$, is denoted $alpha : beta$.]],
    n: 3,
  )
  #parallel(
    [Λόγον ἔχειν πρὸς ἄλληλα μεγέθη λέγεται, ἃ δύναται πολλαπλασιαζόμενα ἀλλήλων ὑπερέχειν.],
    [(Those) magnitudes are said to have a ratio with respect to one another which, being multiplied, are capable of exceeding one another.#content-box-note[In other words, $alpha$ has a ratio with respect to $beta$ if $m thin alpha > beta$ and $n thin beta > alpha$, for some $m$ and $n$.]],
    n: 4,
  )
  #parallel(
    [Ἐν τῷ αὐτῷ λόγῳ μεγέθη λέγεται εἶναι πρῶτον πρὸς δεύτερον καὶ τρίτον πρὸς τέταρτον, ὅταν τὰ τοῦ πρώτου καί τρίτου ἰσάκις πολλαπλάσια τῶν τοῦ δευτέρου καὶ τετάρτου ἰσάκις πολλαπλασίων καθ᾿ ὁποιονοῦν πολλαπλασιασμὸν ἑκάτερον ἑκατέρου ἢ ἅμα ὑπερέχῃ ἢ ἅμα ἴσα ᾖ ἢ ἅμα ἐλλείπῇ ληφθέντα κατάλληλα.],
    [Magnitudes are said to be in the same ratio, the first to the second, and the third to the fourth, when equal multiples of the first and the third either both exceed, are both equal to, or are both less than, equal multiples of the second and the fourth, respectively, being taken in corresponding order, according to any kind of multiplication whatever.#content-box-note[In other words, $alpha : beta :: gamma : delta$ if and only if $m thin alpha >n thin beta$ whenever $m thin gamma >n thin delta$, and $m thin alpha =n thin beta$ whenever $m thin gamma =n thin delta$, and $m thin alpha < n thin beta$ whenever $m thin gamma < n thin delta$, for all $m$ and $n$. This definition is the kernel of Eudoxus' theory of proportion, and is valid even if $alpha$, $beta$, etc., are irrational.]],
    n: 5,
  )
  #parallel(
    [Τὰ δὲ τὸν αὐτὸν ἔχοντα λόγον μεγέθη ἀνάλογον καλείσθω.],
    [And let magnitudes having the same ratio be called proportional.#content-box-note[Thus if $alpha$ and $beta$ have the same ratio as $gamma$ and $delta$ then they are proportional. In modern notation, $alpha : beta :: gamma : delta$.]],
    n: 6,
  )
  #parallel(
    [Ὅταν δὲ τῶν ἰσάκις πολλαπλασίων τὸ μὲν τοῦ πρώτου πολλαπλάσιον ὑπερέχῃ τοῦ τοῦ δευτέρου πολλαπλασίου, τὸ δὲ τοῦ τρίτου πολλαπλάσιον μὴ ὑπερέχῃ τοῦ τοῦ τετάρτου πολλαπλασίου, τότε τὸ πρῶτον πρὸς τὸ δεύτερον μείζονα λόγον ἔχειν λέγεται, ἤπερ τὸ τρίτον πρὸς τὸ τέταρτον.],
    [And when for equal multiples (as in Def.~5), the multiple of the first (magnitude) exceeds the multiple of the second, and the multiple of the third (magnitude) does not exceed the multiple of the fourth, (then) the first (magnitude) is said to have a greater ratio to the second than the third (magnitude has) to the fourth.],
    n: 7,
  )
  #parallel(
    [Ἀναλογία δὲ ἐν τρισὶν ὅροις ἐλαχίστη ἐστίν.],
    [And a proportion in three terms is the smallest (possible).#content-box-note[In modern notation, a proportion in three terms---$alpha$, $beta$, and $gamma$---is written: $alpha : beta :: beta : gamma$.]],
    n: 8,
  )
  #parallel(
    [Ὅταν δὲ τρία μεγέθη ἀνάλογον ᾖ, τὸ πρῶτον πρὸς τὸ τρίτον διπλασίονα λόγον ἔχειν λέγεται ἤπερ πρὸς τὸ δεύτερον.],
    [And when three magnitudes are proportional, the first is said to have to the third the squared#content-box-note[Literally, "double".] ratio of that (it has) to the second.#content-box-note[In other words, if $alpha : beta :: beta : gamma$ then $alpha : gamma :: alpha ^(2): beta ^(2)$.]],
    n: 9,
  )
  #parallel(
    [Ὅταν δὲ τέσσαρα μεγέθη ἀνάλογον ᾖ, τὸ πρῶτον πρὸς τὸ τέταρτον τριπλασίονα λόγον ἔχειν λέγεται ἤπερ πρὸς τὸ δεύτερον, καὶ ἀεὶ ἑξῆς ὁμοίως, ὡς ἂν ἡ ἀναλογία ὑπάρχῃ.],
    [And when four magnitudes are (continuously) proportional, the first is said to have to the fourth the cubed#content-box-note[Literally, "triple".] ratio of that (it has) to the second.#content-box-note[In other words, if $alpha : beta :: beta : gamma :: gamma : delta$ then $alpha : delta :: alpha ^(3): beta ^(3)$.] And so on, similarly, in successive order, whatever the (continuous) proportion might be.],
    n: 10,
  )
  #parallel(
    [Ὁμόλογα μεγέθη λέγεται τὰ μὲν ἡγούμενα τοῖς ἡγουμένοις τὰ δὲ ἑπόμενα τοῖς ἑπομένοις.],
    [These magnitudes are said to be corresponding (magnitudes): the leading to the leading (of two ratios), and the following to the following.],
    n: 11,
  )
  #parallel(
    [Ἐναλλὰξ λόγος ἐστὶ λῆψις τοῦ ἡγουμένου πρὸς τὸ ἡγούμενον καὶ τοῦ ἑπομένου πρὸς τὸ ἑπόμενον.],
    [An alternate ratio is a taking of the (ratio of the) leading (magnitude) to the leading (of two equal ratios), and (setting it equal to) the (ratio of the) following (magnitude) to the following.#content-box-note[In other words, if $alpha : beta :: gamma : delta$ then the alternate ratio corresponds to $alpha : gamma :: beta : delta$.]],
    n: 12,
  )
  #parallel(
    [Ἀνάπαλιν λόγος ἐστὶ λῆψις τοῦ ἑπομένου ὡς ἡγουμένου πρὸς τὸ ἡγούμενον ὡς ἑπόμενον.],
    [An inverse ratio is a taking of the (ratio of the) following (magnitude) as the leading and the leading (magnitude) as the following.#content-box-note[In other words, if $alpha : beta$ then the inverse ratio corresponds to $beta : alpha$.]],
    n: 13,
  )
  #parallel(
    [Σύνθεσις λόγου ἐστὶ λῆψις τοῦ ἡγουμένου μετὰ τοῦ ἑπομένου ὡς ἑνὸς πρὸς αὐτὸ τὸ ἑπόμενον.],
    [A composition of a ratio is a taking of the (ratio of the) leading plus the following (magnitudes), as one, to the following (magnitude) by itself.#content-box-note[In other words, if $alpha : beta$ then the composed ratio corresponds to $alpha + beta : beta$.]],
    n: 14,
  )
  #parallel(
    [Διαίρεσις λόγου ἐστὶ λῆψις τῆς ὑπεροχῆς, ᾗ ὑπερέχει τὸ ἡγούμενον τοῦ ἑπομένου, πρὸς αὐτὸ τὸ ἑπόμενον.],
    [A separation of a ratio is a taking of the (ratio of the) excess by which the leading (magnitude) exceeds the following to the following (magnitude) by itself.#content-box-note[In other words, if $alpha : beta$ then the separated ratio corresponds to $alpha - beta : beta$.]],
    n: 15,
  )
  #parallel(
    [Ἀναστροφὴ λόγου ἐστὶ λῆψις τοῦ ἡγουμένου πρὸς τὴν ὑπεροχήν, ᾗ ὑπερέχει τὸ ἡγούμενον τοῦ ἑπομένου.],
    [A conversion of a ratio is a taking of the (ratio of the) leading (magnitude) to the excess by which the leading (magnitude) exceeds the following.#content-box-note[In other words, if $alpha : beta$ then the converted ratio corresponds to $alpha : alpha - beta$.]],
    n: 16,
  )
  #parallel(
    [Δι᾿ ἴσου λόγος ἐστὶ πλειόνων ὄντων μεγεθῶν καὶ ἄλλων αὐτοῖς ἴσων τὸ πλῆθος σύνδυο λαμβανομένων καὶ ἐν τῷ αὐτῷ λόγῳ, ὅταν ᾖ ὡς ἐν τοῖς πρώτοις μεγέθεσι τὸ πρῶτον πρὸς τὸ ἔσχατον, οὕτως ἐν τοῖς δευτέροις μεγέθεσι τὸ πρῶτον πρὸς τὸ ἔσχατον· ἢ ἄλλως· λῆψις τῶν ἄκρων καθ᾿ ὑπεξαίρεσιν τῶν μέσων.],
    [There being several magnitudes, and other (magnitudes) of equal number to them, (which are) also in the same ratio taken two by two, a ratio via equality (i.e., ex aequali) occurs when as the first is to the last in the first (set of) magnitudes, so the first (is) to the last in the second (set of) magnitudes. Or alternately, (it is) a taking of the (ratio of the) outer (magnitudes) by the removal of the inner (magnitudes).#content-box-note[In other words, if $alpha , beta , gamma$ are the first set of magnitudes, and $delta , epsilon , zeta$ the second set, and $alpha : beta : gamma :: delta : epsilon : zeta$, then the ratio via equality (i.e., ex aequali) corresponds to $alpha : gamma :: delta : zeta$.]],
    n: 17,
  )
  #parallel(
    [Τεταραγμένη δὲ ἀναλογία ἐστίν, ὅταν τριῶν ὄντων μεγεθῶν καὶ ἄλλων αὐτοῖς ἴσων τὸ πλῆθος γίνηται ὡς μὲν ἐν τοῖς πρώτοις μεγέθεσιν ἡγούμενον πρὸς ἐπόμενον, οὕτως ἐν τοῖς δευτέροις μεγέθεσιν ἡγούμενον πρὸς ἑπόμενον, ὡς δὲ ἐν τοῖς πρώτοις μεγέθεσιν ἑπόμενον πρὸς ἄλλο τι, οὕτως ἐν τοῖς δευτέροις ἄλλο τι πρὸς ἡγούμενον.],
    [There being three magnitudes, and other (magnitudes) of equal number to them, a perturbed proportion occurs when as the leading is to the following in the first (set of) magnitudes, so the leading (is) to the following in the second (set of) magnitudes, and as the following (is) to some other (i.e., the remaining magnitude) in the first (set of) magnitudes, so some other (is) to the leading in the second (set of) magnitudes.#content-box-note[In other words, if $alpha , beta , gamma$ are the first set of magnitudes, and $delta , epsilon , zeta$ the second set, and $alpha : beta :: delta : epsilon$ as well as $beta : gamma :: zeta : delta$, then the proportion is said to be perturbed.]],
    n: 18,
  )
]
