import Fugue.E8Lattice

/-!
# Direct sums of even unimodular lattices (the "direct sum" question)

What the direct sum `L ⊕ M` does, precisely:

* Gram matrices combine **block-diagonally**: `G(L ⊕ M) = [[G(L), 0], [0, G(M)]]`
  (`Matrix.fromBlocks`). So `det G(L⊕M) = det G(L) · det G(M)`, and diagonal entries stay even:
  **even unimodular ⊕ even unimodular is even unimodular** (`e8e8_det`, `e8e8_diag`). Rank adds
  (8 + 8 = 16), and the theta series multiply (`Fugue.theta_directSum`, `thetaE8_sq_eq_E₈`), so the
  modular weight adds (4 + 4 = 8).
* "Genus" has two standard meanings, and the direct sum changes neither in the way of "raising the
  genus": the **degree** `g` of a Siegel theta series (number of vectors paired at once) stays the
  same — `Θ^{(g)}_{L⊕M} = Θ^{(g)}_L · Θ^{(g)}_M` at every degree — and the **genus of a lattice**
  (its local equivalence class) is *shared* by `E8 ⊕ E8` and `D16⁺`: they are the two classes in the
  genus of even unimodular rank-16 lattices, with equal degree-1 theta series (`thetaD16_eq_thetaE8_sq`).
-/

open Matrix

namespace Fugue

/-- The Gram matrix of `E8 ⊕ E8`: the block-diagonal direct sum of two E8 Cartan matrices. -/
def e8e8Gram : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℤ :=
  fromBlocks (CartanMatrix.E 8) 0 0 (CartanMatrix.E 8)

/-- **Unimodular:** `det(E8 ⊕ E8) = det E8 · det E8 = 1`. -/
theorem e8e8_det : e8e8Gram.det = 1 := by
  rw [e8e8Gram, det_fromBlocks_zero₂₁, CartanMatrix.E₈_det, mul_one]

/-- **Even:** every diagonal entry of the Gram matrix of `E8 ⊕ E8` is `2`. -/
theorem e8e8_diag (i : Fin 8 ⊕ Fin 8) : e8e8Gram i i = 2 := by
  rcases i with i | i <;> simp [e8e8Gram]

/-- **Symmetric.** -/
theorem e8e8_symm : e8e8Gram.transpose = e8e8Gram := by
  rw [e8e8Gram, fromBlocks_transpose, CartanMatrix.E_transpose]; simp

end Fugue
