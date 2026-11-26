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
    [Μονάς ἐστιν, καθ᾿ ἣν ἕκαστον τῶν ὄντων ἓν λέγεται.],
    [A unit is (that) according to which each existing (thing) is said (to be) one.],
    n: 1,
  )
  #parallel(
    [Ἀριθμὸς δὲ τὸ ἐκ μονάδων συγκείμενον πλῆθος.],
    [And a number (is) a multitude composed of units.#content-box-note[In other words, a "number" is a positive integer greater than unity.]],
    n: 2,
  )
  #parallel(
    [Μέρος ἐστὶν ἀριθμὸς ἀριθμοῦ ὁ ἐλάσσων τοῦ μείζονος, ὅταν καταμετρῇ τὸν μείζονα.],
    [A number is part of a(nother) number, the lesser of the greater, when it measures the greater.#content-box-note[In other words, a number $a$ is part of another number $b$ if there exists some number $n$ such that $n thin a = b$.]],
    n: 3,
  )
  #parallel(
    [Μέρη δέ, ὅταν μὴ καταμετρῇ.],
    [But (the lesser is) parts (of the greater) when it does not measure it.#content-box-note[In other words, a number $a$ is parts of another number $b$ (where $a<b$) if there exist distinct numbers, $m$ and $n$, such that $n thin a=m thin b$.]],
    n: 4,
  )
  #parallel(
    [Πολλαπλάσιος δὲ ὁ μείζων τοῦ ἐλάσσονος, ὅταν καταμετρῆται ὑπὸ τοῦ ἐλάσσονος.],
    [And the greater (number is) a multiple of the lesser when it is measured by the lesser.],
    n: 5,
  )
  #parallel(
    [Ἄρτιος ἀριθμός ἐστιν ὁ δίχα διαιρούμενος.],
    [An even number is one (which can be) divided in half.],
    n: 6,
  )
  #parallel(
    [Περισσὸς δὲ ὁ μὴ διαιρούμενος δίχα ἢ [ὁ] μονάδι διαφέρων ἀρτίου ἀριθμοῦ.],
    [And an odd number is one (which can)not (be) divided in half, or which differs from an even number by a unit.],
    n: 7,
  )
  #parallel(
    [Ἀρτιάκις ἄρτιος ἀριθμός ἐστιν ὁ ὑπὸ ἀρτίου ἀριθμοῦ μετρούμενος κατὰ ἄρτιον ἀριθμόν.],
    [An even-times-even number is one (which is) measured by an even number according to an even number.#content-box-note[In other words, an even-times-even number is the product of two even numbers.]],
    n: 8,
  )
  #parallel(
    [Ἄρτιάκις δὲ περισσός ἐστιν ὁ ὑπὸ ἀρτίου ἀριθμοῦ μετρούμενος κατὰ περισσὸν ἀριθμόν.],
    [And an even-times-odd number is one (which is) measured by an even number according to an odd number.#content-box-note[In other words, an even-times-odd number is the product of an even and an odd number.]],
    n: 9,
  )
  #parallel(
    [Περισσάκις δὲ περισσὸς ἀριθμός ἐστιν ὁ ὑπὸ περισσοῦ ἀριθμοῦ μετρούμενος κατὰ περισσὸν ἀριθμόν.],
    [And an odd-times-odd number is one (which is) measured by an odd number according to an odd number.#content-box-note[In other words, an odd-times-odd number is the product of two odd numbers.]],
    n: 10,
  )
  #parallel(
    [Πρῶτος ἀριθμός ἐστιν ὁ μονάδι μόνῃ μετρούμενος.],
    [A prime#content-box-note[Literally, "first".] number is one (which is) measured by a unit alone.],
    n: 11,
  )
  #parallel(
    [Πρῶτοι πρὸς ἀλλήλους ἀριθμοί εἰσιν οἱ μονάδι μόνῃ μετρούμενοι κοινῷ μέτρῳ.],
    [Numbers prime to one another are those (which are) measured by a unit alone as a common measure.],
    n: 12,
  )
  #parallel(
    [Σύνθετος ἀριθμός ἐστιν ὁ ἀριθμῷ τινι μετρούμενος.],
    [A composite number is one (which is) measured by some number.],
    n: 13,
  )
  #parallel(
    [Σύνθετοι δὲ πρὸς ἀλλήλους ἀριθμοί εἰσιν οἱ ἀριθμῷ τινι μετρούμενοι κοινῷ μέτρῳ.],
    [And numbers composite to one another are those (which are) measured by some number as a common measure.],
    n: 14,
  )
  #parallel(
    [Ἀριθμὸς ἀριθμὸν πολλαπλασιάζειν λέγεται, ὅταν, ὅσαι εἰσὶν ἐν αὐτῷ μονάδες, τοσαυτάκις συντεθῇ ὁ πολλαπλασιαζόμενος, καὶ γένηταί τις.],
    [A number is said to multiply a(nother) number when the (number being) multiplied is added (to itself) as many times as there are units in the former (number), and (thereby) some (other number) is produced.],
    n: 15,
  )
  #parallel(
    [Ὅταν δὲ δύο ἀριθμοὶ πολλαπλασιάσαντες ἀλλήλους ποιῶσί τινα, ὁ γενόμενος ἐπίπεδος καλεῖται, πλευραὶ δὲ αὐτοῦ οἱ πολλαπλασιάσαντες ἀλλήλους ἀριθμοί.],
    [And when two numbers multiplying one another make some (other number then) the (number so) created is called plane, and its sides (are) the numbers which multiply one another.],
    n: 16,
  )
  #parallel(
    [Ὅταν δὲ τρεῖς ἀριθμοὶ πολλαπλασιάσαντες ἀλλήλους ποιῶσί τινα, ὁ γενόμενος στερεός ἐστιν, πλευραὶ δὲ αὐτοῦ οἱ πολλαπλασιάσαντες ἀλλήλους ἀριθμοί.],
    [And when three numbers multiplying one another make some (other number then) the (number so) created is (called) solid, and its sides (are) the numbers which multiply one another.],
    n: 17,
  )
  #parallel(
    [Τετράγωνος ἀριθμός ἐστιν ὁ ἰσάκις ἴσος ἢ [ὁ] ὑπὸ δύο ἴσων ἀριθμῶν περιεχόμενος.],
    [A square number is an equal times an equal, or (a plane number) contained by two equal numbers.],
    n: 18,
  )
  #parallel(
    [Κύβος δὲ ὁ ἰσάκις ἴσος ἰσάκις ἢ [ὁ] ὑπὸ τριῶν ἴσων ἀριθμῶν περιεχόμενος.],
    [And a cube (number) is an equal times an equal times an equal, or (a solid number) contained by three equal numbers.],
    n: 19,
  )
  #parallel(
    [Ἀριθμοὶ ἀνάλογόν εἰσιν, ὅταν ὁ πρῶτος τοῦ δευτέρου καὶ ὁ τρίτος τοῦ τετάρτου ἰσάκις ᾖ πολλαπλάσιος ἢ τὸ αὐτὸ μέρος ἢ τὰ αὐτὰ μέρη ὦσιν.],
    [Numbers are proportional when the first is the same multiple, or the same part, or the same parts, of the second that the third (is) of the fourth.],
    n: 20,
  )
  #parallel(
    [Ὅμοιοι ἐπίπεδοι καὶ στερεοὶ ἀριθμοί εἰσιν οἱ ανάλογον ἔχοντες τὰς πλευράς.],
    [Similar plane and solid numbers are those having proportional sides.],
    n: 21,
  )
  #parallel(
    [Τέλειος ἀριθμός ἐστιν ὁ τοῖς ἑαυτοῦ μέρεσιν ἴσος ὤν.],
    [A perfect number is that which is equal to its own parts.#content-box-note[In other words, a perfect number is equal to the sum of its own factors.]],
    n: 22,
  )
]
