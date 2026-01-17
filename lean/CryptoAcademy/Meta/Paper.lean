/-
  CryptoAcademy/Meta/Paper.lean

  Bibliography infrastructure for tracking paper references.
  Every non-trivial theorem should cite its source paper.
-/

namespace CryptoAcademy.Meta

/-- A reference to an academic paper -/
structure Paper where
  /-- Short citation key (e.g., "Regev05", "PLONK19") -/
  key : String
  /-- Full paper title -/
  title : String
  /-- List of authors -/
  authors : List String
  /-- Publication year -/
  year : Nat
  /-- Publication venue (conference, journal) -/
  venue : Option String := none
  /-- Direct URL to paper -/
  url : Option String := none
  /-- ePrint or arXiv identifier -/
  eprint : Option String := none
  /-- DOI if available -/
  doi : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- Generate a short citation string -/
def Paper.cite (p : Paper) : String :=
  s!"[{p.key}]"

/-- Generate a full citation string -/
def Paper.fullCite (p : Paper) : String :=
  let authorStr := String.intercalate ", " p.authors
  let venueStr := p.venue.map (s!" In {·}.") |>.getD ""
  s!"{authorStr}. \"{p.title}\".{venueStr} {p.year}."

/-! ## Foundational Papers -/

/-- Regev's seminal LWE paper -/
def Regev2005 : Paper := {
  key := "Regev05"
  title := "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography"
  authors := ["Oded Regev"]
  year := 2005
  venue := some "STOC 2005"
  url := some "https://cims.nyu.edu/~regev/papers/qcrypto.pdf"
  doi := some "10.1145/1060590.1060603"
}

/-- Peikert's classical LWE reduction -/
def Peikert2009 : Paper := {
  key := "Peikert09"
  title := "Public-Key Cryptosystems from the Worst-Case Shortest Vector Problem"
  authors := ["Chris Peikert"]
  year := 2009
  venue := some "STOC 2009"
  eprint := some "2008/481"
}

/-- LPR ring-LWE paper -/
def LPR2010 : Paper := {
  key := "LPR10"
  title := "On Ideal Lattices and Learning with Errors over Rings"
  authors := ["Vadim Lyubashevsky", "Chris Peikert", "Oded Regev"]
  year := 2010
  venue := some "EUROCRYPT 2010"
  eprint := some "2012/230"
}

/-! ## Commitment Schemes -/

/-- KZG polynomial commitment paper -/
def KZG2010 : Paper := {
  key := "KZG10"
  title := "Constant-Size Commitments to Polynomials and Their Applications"
  authors := ["Aniket Kate", "Gregory M. Zaverucha", "Ian Goldberg"]
  year := 2010
  venue := some "ASIACRYPT 2010"
  eprint := some "2010/315"
}

/-! ## Zero-Knowledge Proofs -/

/-- Groth16 SNARK paper -/
def Groth2016 : Paper := {
  key := "Groth16"
  title := "On the Size of Pairing-based Non-interactive Arguments"
  authors := ["Jens Groth"]
  year := 2016
  venue := some "EUROCRYPT 2016"
  eprint := some "2016/260"
}

/-- PLONK paper -/
def PLONK2019 : Paper := {
  key := "PLONK19"
  title := "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge"
  authors := ["Ariel Gabizon", "Zachary J. Williamson", "Oana Ciobotaru"]
  year := 2019
  eprint := some "2019/953"
}

/-- Nova folding scheme paper -/
def Nova2022 : Paper := {
  key := "Nova22"
  title := "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes"
  authors := ["Abhiram Kothapalli", "Srinath Setty", "Ioanna Tzialla"]
  year := 2022
  venue := some "CRYPTO 2022"
  eprint := some "2021/370"
}

/-! ## Signatures -/

/-- Schnorr signature paper -/
def Schnorr1991 : Paper := {
  key := "Schnorr91"
  title := "Efficient Signature Generation by Smart Cards"
  authors := ["Claus-Peter Schnorr"]
  year := 1991
  venue := some "Journal of Cryptology"
  doi := some "10.1007/BF00196725"
}

/-- Dilithium (ML-DSA) paper -/
def Dilithium2018 : Paper := {
  key := "Dilithium18"
  title := "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme"
  authors := ["Léo Ducas", "Eike Kiltz", "Tancrède Lepoint", "Vadim Lyubashevsky",
              "Peter Schwabe", "Gregor Seiler", "Damien Stehlé"]
  year := 2018
  venue := some "TCHES 2018"
  eprint := some "2017/633"
}

end CryptoAcademy.Meta
